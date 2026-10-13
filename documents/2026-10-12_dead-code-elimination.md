# Dead-code elimination: how it works and where the techniques come from

**Date:** 2026-10-12 (rewritten after the loop analysis and the value sets were added; replaces the first
version, which only had three syntactic rules)

## 1. The general idea

Two different things are called "dead code" in compilers:

- **Unreachable code**: code that no execution can reach (code after a `return`, a branch whose condition
  is always false). It is found from control flow and from what is known about the values of variables.
- **Dead stores**: assignments whose value is never read. They are found with liveness analysis.

Issy's extracted programs mostly suffer from the first kind. The program is a dispatch loop over a
location variable (`prog_counter`): one guarded block per recorded solver step, nested loops for
sub-games, and an `abort()` at the end of every loop for "no guard matched". The guards are never
compared with each other or with what the program has already done. Measured with the end-to-end test
on the real programs of 2026-10-12 (statements of `main()` that no run executed, 300 reads per run):
`bounded-loop` 31 of 61, `count-up` 31 of 61, `swap` 17 of 33, `buechi-cycle` 23 of 53,
`walk-to-diagonal` 45 of 61.

## 2. The pass (`eliminate_dead_code`)

It works directly on Issy's `Prog` tree (`Cond`, `Sequence`, `InfLoop`, `Break`, `Continue`, `Abort`,
`Read`, `Declare`, `PAssign`), without building a control-flow graph. It is a forward analysis that
walks the program in execution order and keeps, for the current point, what is known about the state:

| Part of the knowledge | Meaning | Comes from |
|---|---|---|
| `env` | variable -> the set of at most 6 constants it can have | guards `v == k`, assignments of constants (also `ite` of constants) |
| `true` | guards known to hold | enclosing `if` guards |
| `false` | guards known not to hold | guards that were skipped |

With that knowledge it applies these rules.

**R1. Fold terms.** A variable with exactly one possible value is replaced by it; constant arithmetic,
comparisons, `and`/`or`/`not`/`ite` are folded; a comparison of a variable with a constant is decided if it
has the same answer for every possible value (`pc` in {0, 1}: `pc == 2` is false); a guard that is
remembered as true/false becomes `true`/`false`.

**R2. Decide guards.** `if (true) S` becomes `S`. `if (false) S` is removed. An `if` whose body became
empty is removed (guards have no side effects).

**R3. A guard is a fact.** Inside `if (c) S` the pass knows `c`. If `S` never falls through (it ends in
`break`, `continue` or `abort`) then everything after the `if` is reached only when `c` was false, so the
pass knows `not c`. For `v == k` this removes `k` from the possible values of `v`:

    if (pc == 1) { ...; continue; }     // afterwards pc != 1
    if (pc == 0) { ...; continue; }     // afterwards pc != 0
    if (pc == 1) { ... }                // pc cannot be 1 here: removed
    abort();                            // pc is in {0, 1} (known at the loop head): unreachable, removed

**R4. Nothing runs after a jump.** In a sequence everything after an item that never finishes normally
is removed (`Break`, `Continue`, `Abort`, a sequence containing one, an infinite loop with no `Break`
aimed at it).

**R5. Merge points keep what holds on both paths.** After an `if` whose body falls through, the pass keeps
only what holds both when the body ran and when it was skipped: for `env` the union of the value sets (a
variable unknown on one path is unknown), for `true`/`false` the facts present on both.

**R6. Loops are analysed until nothing changes** (`_dce_loop`). What is known at a loop head is what
holds when the loop is entered and at every back edge (every `continue` and the end of the body). The pass
starts with what is known before the loop, analyses the body, joins the states reaching the back edges
into the head, and repeats until the head no longer changes. After the loop it knows what holds at all
`break`s. This is constant propagation (here: with small value sets) as a data-flow fixed point. If no
fixed point is reached in 8 rounds, the loop falls back to "forget everything the loop may change".
Example: if `prog_counter` is 0 before a loop and the loop only ever assigns 0 to it, `prog_counter` is
still 0 at the head, and the whole dispatch on it disappears (`saturating-input`, `trailing-value`,
`bool-handshake`).

**R7. Remove no-op assignments.** `x := x`, and `x := k` when `x` is known to be `k`. (This is what makes
the loop in the previous example stable: inside `if (pc == 0)` the assignment `pc := 0` does nothing.)

**R8. Remove dead local variables** (`_drop_dead_locals`). A variable introduced with `Declare` is printed
inside `main()` and is invisible to `read_inputs()`. If it is never used in a guard, and never in the
right-hand side of an assignment to a variable that matters, its assignments and its declaration are
removed (this includes `prog_counter` once all guards on it are gone). State and input variables are
never touched: `read_inputs()` can read them.

The rules run together and are repeated (at most 10 rounds) with the structural clean-up
(`optimize_prog_structure`) until the program no longer changes.

Nothing in the pass refers to variable names, constants of the specification or the specification
itself, only to the shape of the tree and the operators of the term language.

## 3. Why it is correct

The knowledge at a point is a description that holds for every state in which execution can reach that
point (an over-approximation, as in abstract interpretation). Every rule keeps this true:

- Assigning to a variable, `Declare`, and `Read` (for input variables) remove what is known about the
  variable; assignments of constants add it. The right-hand sides of a parallel assignment are evaluated in
  the state before the assignment.
- Entering `if (c)`: `c` holds. Skipping it: `not c` holds.
- A merge is a join: it keeps only what holds on both paths, so it describes both.
- The loop head is the join of the entry state and all back edges, computed as a fixed point. The knowledge
  can only get weaker in each round (value sets only grow up to a bound, fact lists only shrink), so the
  iteration ends; the bound and the fallback make sure it always does.
- Removed code was either never reached (decided guard, after a jump) or did nothing (no-op assignment,
  unused local).

Assumptions (check them if the language of Issy's programs grows):

1. Guard terms have no side effects and cannot fail (no division by zero). True for `+`, `*`, comparisons,
   `and`, `or`, `not`, `ite`; re-check if `/` or `mod` is added (the C printer already knows `mod`).
2. `Read` changes only input variables. The pass takes "input variable" to mean "used but never assigned
   in the program". A state variable that is never assigned counts as an input (this only makes the pass
   more careful).
3. Integer constants are folded only when the result has absolute value below 2^31, so no overflow of
   the C `int` is hidden.
4. A `Declare`d variable is local (printer: `Declare` is emitted inside `main()`).

## 4. What it does not do

- Guards are compared structurally. `x < 2` and `not (2 <= x)` are not recognised as the same fact.
  A solver (SMT) would be needed for that.
- Relations between variables (`x == y`, `x < y`) and ranges (`0 <= x < 11`) are not tracked, only
  constants and small sets of constants. Branches that are dead only because of such facts stay (for
  example one branch in `bounded-loop`).
- Remaining `abort()` statements are those the pass cannot prove unreachable. They are sentinels
  ("this should never be reached") and also removing a reachable one would change behaviour.
- State variables are never removed (observable through `read_inputs()`), so there is no liveness-based
  removal of dead stores to them.
- The `ite` lowering (`sound_lower`) turns `x := ite(c, a, b)` into a declaration and two guarded
  assignments. This makes specs with `ite` terms longer (see section 5). The C printer can print `?:`
  directly, so the lowering is not needed for correctness; whether to keep it is a design decision for
  the thesis.
- Applying the whole pipeline twice can still change terms (Egglog rewrites a negated conjunction into
  a disjunction in the second round). `eliminate_dead_code` alone is idempotent (checked on 18000 random
  programs).

## 5. Results

All figures: every optimized program behaves exactly like the original in all scenarios.

**Real `issy`, 2026-10-12, author's machine, first version of the pass (no loop analysis, no value sets).**
Statements of `main()` never executed in any scenario, original -> optimized: `bounded-loop` 31 of 61 ->
1 of 36, `count-up` 31 of 61 -> 0 of 33, `swap` 17 of 33 -> 0 of 15, `buechi-cycle` 23 of 53 -> 0 of 33,
`walk-to-diagonal` 45 of 61 -> 43 of 59, `test.issy` 26 of 57 -> 14 of 52.

**Final version, on the ASTs (`ast.json`) of that real run, with a stand-in for the C printer. Not yet run
with the real `issy` binary.** Never executed, original -> optimized, and `abort()` statements:

| Spec | Never executed | `abort()` | Statements of the AST |
|---|---|---|---|
| bounded-loop | 31 of 61 -> 1 of 33 | 5 -> 1 | 74 -> 38 |
| count-up | 31 of 61 -> 0 of 30 | 5 -> 1 | 74 -> 35 |
| swap | 17 of 33 -> 0 of 15 | 3 -> 2 | 44 -> 21 |
| buechi-cycle | 23 of 53 -> 0 of 30 | 5 -> 1 | 64 -> 36 |
| walk-to-diagonal | 45 of 61 -> 0 of 13 | 5 -> 0 | 84 -> 15 |
| two-phase (*) | 110 of 142 -> 8 of 36 | 10 -> 2 | 169 -> 43 |
| test.issy | 26 of 57 -> 3 of 40 | 4 -> 3 | 72 -> 51 |
| saturating-input | 0 of 7 -> 0 of 12 | 1 -> 0 | 10 -> 13 |
| trailing-value | 0 of 7 -> 0 of 12 | 1 -> 0 | 12 -> 15 |
| bool-handshake | 0 of 7 -> 0 of 9 | 1 -> 0 | 11 -> 11 |

(*) Issy's own program for `two-phase` ends in `abort()` after 4 reads (bug-and-fix document, 6.3), so
the numbers describe only these 4 reads.
The last three specs have `ite` terms in their assignments: the dispatch on `prog_counter`, its
`abort()` and the variable itself are gone, but the `ite` lowering makes the assignment longer.
"Statements of the AST" counts every assigned variable, `if`, loop, `read`, jump and `abort`.

**Soundness tests.**

- `python3 tests/dce_fuzz.py real 18000`: 18000 random programs, the pruned program behaves like the
  original in all of them (values of all state and input variables at every `Read`, and how the run ends),
  and a second application changes nothing.
- `python3 tests/dce_fuzz.py pipeline 300`: the whole optimizer on 300 random programs, 0 differ; the legacy
  pipeline (before the fix, `optimize_ast_with_egglog_legacy`) differed on 6 of 75.
- `python3 tests/dce_fuzz.py mutants 3000`: 40 deliberately wrong variants of the pass (a kill, a join, a
  polarity, a loop rule changed). 37 are detected. The 3 that are not detected only make the pass less
  precise (they stay sound), which no behaviour test can notice. Some variants needed up to 9 times more
  programs; the test increases the number by itself.
- `python3 tests/e2e.py`: the original and optimized C of Issy's real output are run in 1 to 11 scenarios
  (input profiles zero, one, min, max, alternating, random, sticky) and compared at every `read_inputs()`.
  Checked with a stand-in `issy` on the real ASTs: with the legacy pipeline the comparison fails for
  `swap`, `trailing-value`, `bounded-loop` and `count-up`; with the new one it passes for all. With
  `--self-test` the test also damages the optimized program on purpose and checks that this is noticed
  (5 to 8 of 8 damaged copies per spec).

Both kinds of test sample behaviour; neither proves equivalence.

## 6. Code

`optimizer_simple_egglog.py`, section 11c (line `1150`):

| What | Line |
|---|---|
| `_Ctx` (the knowledge), `_join` | `1232`, `1259` |
| `_known`, `_fold_junction`, `_fold`, `_values`, `_decide`, `_simp` (R1) | `1271`, `1293`, `1321`, `1364`, `1377`, `1404` |
| `_narrow`, `_assume` (R3) | `1423`, `1432` |
| `_has_free_break`, `_diverges` (R4) | `1464`, `1475` |
| `_dce` (R2, R5, R7) | `1486` |
| `_dce_loop` (R6) | `1559` |
| dead locals (R8): `_declared` ... `_drop_dead_locals` | `1605` ... `1654` |
| `eliminate_dead_code` (driver) | `1676` |
| pipeline that calls it | `optimize_ast_with_egglog`, `1695` |

Tests: `tests/e2e.py`, `tests/dce_fuzz.py`.

## 7. Sources and what each one supports

The specific algorithm above is a small, own combination of standard ideas. The sources support the ideas,
they do not describe this exact algorithm. Entries were written from memory: check the details (pages,
sections, editions) before putting them in the thesis.

**Unreachable-code and dead-code elimination (the technique)**
- S. S. Muchnick. *Advanced Compiler Design and Implementation*. Morgan Kaufmann, 1997. The chapter on
  control-flow and low-level optimizations covers unreachable-code elimination; the dead-code
  elimination section covers dead stores.
- A. V. Aho, M. S. Lam, R. Sethi, J. D. Ullman. *Compilers: Principles, Techniques, and Tools*, 2nd ed.
  Addison-Wesley, 2006. Dead-code elimination, data-flow analysis (liveness, reachability), constant
  propagation as a data-flow problem (R8 is the simplest case of liveness).
- K. D. Cooper, L. Torczon. *Engineering a Compiler*, 2nd ed. Morgan Kaufmann, 2011, chapter 10 (scalar
  optimizations): eliminating useless and unreachable code.

**Constant propagation as a data-flow fixed point, and conditions as knowledge (R1, R3, R5, R6)**
- G. A. Kildall. A unified approach to global program optimization. POPL 1973, pp. 194-206.
  (iterating to a fixed point over joins of the states of all paths; the loop analysis)
- M. N. Wegman, F. K. Zadeck. Constant propagation with conditional branches. *ACM TOPLAS* 13(2):181-210,
  1991. (branch conditions decide which code can execute; code found unreachable is dropped)
- P. Cousot, R. Cousot. Abstract interpretation: a unified lattice model for static analysis of programs
  by construction or approximation of fixpoints. POPL 1977, pp. 238-252. (the knowledge as an abstract
  state, the join, the bound on the number of values as a way to get a finite domain)

**"Cannot complete normally" / terminating statements (R4)**
- J. Gosling, B. Joy, G. Steele, G. Bracha, A. Buckley, D. Smith, G. Bierman. *The Java Language
  Specification* (use the edition you cite, for example Java SE 21): section 14.1 (normal and abrupt
  completion) and section 14.22 (unreachable statements). `break`, `continue`, `return` and `throw` cannot
  complete normally; a statement in a block is reachable only if the previous one can complete normally;
  a `while (true)` loop can complete normally only if a reachable `break` exits it.
  <https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html>
- The Go Programming Language Specification, section "Terminating statements". A `for` loop without
  condition is terminating if no `break` refers to it. <https://go.dev/ref/spec#Terminating_statements>

**Stronger implication checks (possible extension)**
- L. de Moura, N. Bjorner. Z3: An efficient SMT solver. TACAS 2008, LNCS 4963, pp. 337-340.

**Validating the pass**
- W. M. McKeeman. Differential testing for software. *Digital Technical Journal* 10(1):100-107, 1998.
- X. Yang, Y. Chen, E. Eide, J. Regehr. Finding and understanding bugs in C compilers. PLDI 2011,
  pp. 283-294. (random programs plus comparison of behaviour)
- R. A. DeMillo, R. J. Lipton, F. G. Sayward. Hints on test data selection: Help for the practicing
  programmer. *IEEE Computer* 11(4):34-41, 1978. and Y. Jia, M. Harman. An analysis and survey of the
  development of mutation testing. *IEEE Trans. Software Engineering* 37(5):649-678, 2011. (the wrong
  variants of the pass in `dce_fuzz.py mutants`)
- A. Pnueli, M. Siegel, E. Singerman. Translation validation. TACAS 1998, LNCS 1384, pp. 151-166. (the
  formal version of what behaviour-comparison tests approximate)

**The program representation**
- P. Heim, R. Dimitrova. Issy: A Comprehensive Tool for Specification and Synthesis of Infinite-State
  Reactive Systems. CAV 2025, LNCS 15934, pp. 298-312.
