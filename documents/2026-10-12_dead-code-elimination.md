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

**Final version. First computed on the ASTs (`ast.json`) of that real run with a stand-in for the C printer,
then confirmed with the real `issy` binary on 2026-10-13 (author's Mac, `python3 tests/e2e.py --self-test
--show-dead --exhaustive --prove`, 81 of 81 checks passed; every number below is identical in the real run).**
Never executed, original -> optimized, and `abort()` statements:

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
  `swap`, `trailing-value`, `bounded-loop` and `count-up`; with the new one it passes for all (also with the
  real `issy`, section 6.2). With `--self-test` the test also damages the optimized program on purpose and
  checks that this is noticed (all damaged copies for 8 specs, 6 of 8 and 2 of 5 for the other two in the real run).

These tests sample behaviour; they do not prove equivalence. Section 6 does.

## 6. Proving that the optimized program is equivalent (2026-10-13)

Sampling cannot show that two programs are the same, so three further checks were added. They answer
different doubts and were built independently of each other.

**What "equivalent" means here.** For every sequence of values that `read_inputs()` delivers, the original and
the optimized program show the environment the same values of all input and state variables at every `Read`,
and they end the same way (`abort()`, leaving the outermost loop, or looping without ever reading again).
Variables declared inside `main()` (`Declare`) are not visible to the environment.

### 6.1 The three checks

**A. SMT proof on the ASTs: `tests/equiv_check.py`** (needs `pip install z3-solver`). Translation validation:
the optimized program is checked against the original one, the optimizer itself is not trusted. Both programs
are turned into control-flow graphs and executed symbolically in lockstep, from `Read` to `Read`, with one
fresh symbolic input vector per `Read`. At each `Read` the solver (Z3) must not be able to find a history of
inputs that makes the two states differ. What a verdict covers:

- `PROVED for all lengths`: all integer and boolean input values, runs of any length. The proof is closed in
  one of three ways: every path of both programs ends within k reads; or the spec has no inputs and the pair
  of states repeats (so the future repeats); or Spacer (Z3's solver for constrained Horn clauses, a
  property-directed-reachability engine) finds an inductive invariant that relates the two programs at every
  pair of `Read` statements and implies equal observations.
- `PROVED up to K reads`: no difference for any input sequence of at most K reads (K = 20); no proof beyond.
- `DIFFERENT`: a concrete input sequence is printed and replayed by a second, independent interpreter; a
  verdict whose replay shows no difference is reported as a checker bug.
- `INCONCLUSIVE`: solver timeout, time budget used up, or a stretch of code without `Read` whose end cannot
  be decided. It is never counted as success.

Local variables: in C an uninitialised local holds garbage. The checker gives each `Declare`d variable an
unknown value (one constant per name, the same in both programs), so equivalence is proved for **every** value
of the garbage. A program that reads a local before writing it is reported `DIFFERENT`. (The first version
started locals at 0 and accepted such a program; a test with a local that is read before it is written found
this, see the self-test below.)

**B. Every input sequence on the compiled C: `tests/c_exhaustive.py`.** `read_inputs()` is replaced by a driver
that enumerates *all* input sequences up to a depth K, with integer inputs from a small domain (default
-2..2) and booleans both ways, and records for each sequence a hash of everything the environment sees plus
how the run ended. A run that stops after n < K reads stands for all sequences with the same first n values,
so the enumeration is a complete tree. The two programs must give the same number of runs and the same
combined hash; on a difference both are re-run in lockstep and the first differing sequence is printed. The
C is compiled with `-O0 -fwrapv`, and the stack is filled with 0x00, 0x5a and 0xff before each run, so a
program that depends on an uninitialised local differs between the three runs. Cheap, and independent of the
modelling in A: it uses the real C compiler and the C printer of Synthesis.hs (a Python copy of the printer is
used when only an AST is available).

**C. Negative controls (the checks must be able to fail).**
- The old pipeline (`optimize_ast_with_egglog_legacy`, unsound) must be rejected where it is wrong.
- `python3 tests/equiv_check.py self-test N`: for N random programs shaped like Issy's output, (1) the old
  optimizer: those it breaks must be reported `DIFFERENT` with a confirmed input sequence; (2) the current
  optimizer: never `DIFFERENT`; (3) three mutants of the optimized program per seed (one constant, operator,
  guard, statement, jump or right-hand side changed): rejected, or, if not, no random run and no brute-force
  run over all sequences of 5 reads (integers -1..2) may show a difference.
- `python3 tests/c_exhaustive.py --negative`: old optimizer and damaged copies of the optimized program on the C
  level.

### 6.2 Results

**Real `issy`, 2026-10-13, author's Mac** (`python3 tests/e2e.py --self-test --show-dead --exhaustive --prove
--keep tests/out`; the log `tests/out/run.log` stays on the author's machine and is not committed): 81 of 81 checks passed on all ten specs. Per spec, with the C
programs that `issy` itself prints and the final optimizer called by `Synthesis.hs`: the optimized program
behaves like the original in 1 to 11 sampled scenarios; every input sequence up to the depth bound gives the
same observations (same depths and sequence counts as in the table below); the SMT proof holds for all
lengths (0.0 to 1.9 s); the dead-statement counts of section 5 are reproduced; the self-test detects all damaged
copies of the optimized program for 8 specs, 6 of 8 for `bounded-loop` and 2 of 5 for `walk-to-diagonal` (the
others change nothing the environment sees). All C programs compile, so nothing from the optimizer ends up in
`issy`'s output.

**Sandbox, same day, same ten ASTs.** The table and the numbers below were first obtained in the sandbox, where
`issy` cannot be built: the ASTs are the ones extracted by the real `issy`, and the C programs are printed by
a copy of the printer in Synthesis.hs. The comparison with the old optimizer (last column) was only done
there, because the real `issy` always runs the current optimizer.

| Spec | A: SMT proof, current optimizer | B: C, current optimizer | Old optimizer: A / B |
|---|---|---|---|
| bool-handshake | all lengths (invariant) | 262144 sequences, bool input, 18 reads | equal / equal |
| bounded-loop | all lengths (invariant) | no input: 1 run, 300 reads | DIFFERENT after 11 reads / found |
| buechi-cycle | all lengths (invariant) | no input: 1 run, 300 reads | DIFFERENT after 4 reads / found |
| count-up | all lengths (invariant) | no input: 1 run, 300 reads | DIFFERENT after 6 reads / found |
| saturating-input | all lengths (invariant) | 78125 sequences (5^7, -2..2), 7 reads | equal / equal |
| swap | all lengths (state pair repeats after 2 reads) | no input: 1 run, 300 reads | DIFFERENT after 2 reads / found |
| test.issy | all lengths (invariant) | 262144 sequences, bool input, 18 reads | equal / equal |
| trailing-value | all lengths (invariant) | 78125 sequences (5^7, -2..2), 7 reads | DIFFERENT after 2 reads / found |
| two-phase | all lengths (all paths end within 4 reads) | 1 run, ends in `abort()` after 4 reads | DIFFERENT after 4 reads / found |
| walk-to-diagonal | all lengths (state pair repeats after 2 reads) | no input: 1 run, 300 reads | equal / equal |

- The SMT proof needs 0.0 to 5 seconds per spec.
- A and B agree on all 20 verdicts (10 specs x 2 optimizers): they were built separately (a Z3 model of the
  semantics versus the C compiler), so a mistake in the modelling of `break`, `continue`, parallel assignment or
  `Declare` would have shown up as a disagreement.
- The old optimizer is wrong on 6 of the 10 real programs; the counterexamples of A are confirmed by the
  independent interpreter.
- Self-test, seeds 0..31 (32 random programs, final version of the checker): the old optimizer is rejected on
  19, each time with a confirmed input sequence; the current optimizer is never rejected (23 proved for all
  lengths, 5 up to 12 reads, 4 inconclusive); 58 damaged copies of the optimized programs are rejected, 33 are
  not rejected and none of them is contradicted by 60 random runs or by brute force, 5 are inconclusive.
- 48 further random programs (seeds 3000..3047) through the current optimizer: 0 `DIFFERENT`, 36 proved for
  all lengths, 6 proved up to 20 reads, 6 `INCONCLUSIVE` (15 s budget used up, or code that loops without
  reading). The inconclusive ones are not counted as proofs.
- B, damaged copies of the optimized program (8 per spec): 4 to 7 of 8 are found; the others do not change
  anything the environment sees within the domain and depth.

### 6.3 What this does not show

- Integers are mathematical integers in A (Issy's own semantics). The C int wraps at 2^31; B uses small
  values, so no program here overflows. The optimizer folds a constant only if the result is below 2^31, but a
  rewrite that is only valid for unbounded integers (for example `x < x + 1`) would not be noticed at the
  bounds of the C type.
- B covers all sequences up to the depth bound over the small domain, not all integers and not longer runs.
  A covers those, but only on the model of the semantics.
- Only "optimized program = Issy's original program" is checked, not "Issy's program satisfies the
  specification" (see `two-phase`, where Issy's own program aborts) and not the Haskell printer.
- Guards are assumed to have no side effects and to be total; `double` variables are not supported by B.
- Equality with more than two arguments is evaluated as a chain of equalities in A; the C printer would print
  `(a == b == c)`. The optimizer's term conversion (`egg_repr_to_term_ast`) builds `FEq` with two arguments.
- `INCONCLUSIVE` and `PROVED up to K reads` verdicts are weaker than a proof. None occurred on the ten real
  programs.

### 6.4 How to run

```
pip install z3-solver egglog
python3 tests/equiv_check.py program.json ...        # optimize each AST and prove it
python3 tests/equiv_check.py --pair ast.json ast_optimized.json
python3 tests/equiv_check.py self-test 32            # the checker must be able to fail
python3 tests/c_exhaustive.py --negative program.json ...
python3 tests/e2e.py --exhaustive --prove            # real issy: both checks on every spec
```

## 7. Code

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

Tests: `tests/e2e.py`, `tests/dce_fuzz.py`, and for section 6 `tests/equiv_check.py` (`CFG`, `segment`, `verify`,
`prove_unbounded`, `self_test`) and `tests/c_exhaustive.py` (`driver`, `compare`, `ast_to_c`).

## 8. Sources and what each one supports

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

**Proving equivalence (section 6)**
- G. C. Necula. Translation validation for an optimizing compiler. PLDI 2000, pp. 83-94. (checking each
  run of an optimizer instead of trusting it; same idea as `equiv_check.py`)
- A. Pnueli, M. Siegel, E. Singerman. Translation validation. TACAS 1998 (see above).
- N. Lopes, J. Lee, C. Hur, Z. Liu, J. Regehr. Alive2: bounded translation validation for LLVM. PLDI 2021,
  pp. 65-79. (an SMT-based checker that is itself tested against known wrong transformations)
- G. Barthe, J. M. Crespo, C. Kunz. Relational verification using product programs. FM 2011, LNCS 6664,
  pp. 200-214. (running two programs in lockstep as one: the pair of `Read` statements is the product state)
- B. Godlin, O. Strichman. Regression verification. DAC 2009, pp. 466-471. (proving two program versions
  equivalent by relating their states at synchronisation points)
- J. C. King. Symbolic execution and program testing. *Communications of the ACM* 19(7):385-394, 1976.
  (the symbolic execution from `Read` to `Read`)
- A. Komuravelli, A. Gurfinkel, S. Chaki. SMT-based model checking for recursive programs. CAV 2014, LNCS
  8559, pp. 17-34 (Spacer); K. Hoder, N. Bjorner. Generalized property directed reachability. SAT 2012,
  LNCS 7317, pp. 157-171; A. R. Bradley. SAT-based model checking without unrolling. VMCAI 2011, LNCS 6538,
  pp. 70-87 (IC3, the idea behind inductive invariants found by Spacer).
- N. Bjorner, A. Gurfinkel, K. McMillan, A. Rybalchenko. Horn clause solvers for program verification. In
  *Fields of Logic and Computation II*, LNCS 9300, pp. 24-51, 2015. (programs as constrained Horn clauses,
  the form given to Spacer)
- D. Jackson. *Software Abstractions: Logic, Language, and Analysis*. MIT Press, 2006. (the small scope
  hypothesis: most errors show up on small inputs; the idea behind checking all sequences over a small
  domain)
- ISO/IEC 9899:2011 (C11), 6.7.9 paragraph 10 (an automatic object without initializer has an indeterminate
  value) and 6.5 paragraph 5 (signed integer overflow is undefined); the GCC option `-fwrapv`.

**The program representation**
- P. Heim, R. Dimitrova. Issy: A Comprehensive Tool for Specification and Synthesis of Infinite-State
  Reactive Systems. CAV 2025, LNCS 15934, pp. 298-312.
