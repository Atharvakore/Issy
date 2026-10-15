# Dead-code elimination: how it works and where the techniques come from

**Date:** 2026-10-12 (rewritten after the loop analysis and the value sets were added; replaces the first
version, which only had three syntactic rules)

**Updated 2026-10-15:** ranges and relations between variables (rule R9 in section 2); results and tests in
section 5, code in section 7, sources in section 8.

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
| `true` | guards known to hold | enclosing `if` guards; also `v == t` after an assignment `v := t` of a linear term `t` (R9) |
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

**R9. Ranges and relations between variables** (`_entailed`, 2026-10-15). A comparison of linear integer
terms (`<`, `<=`, `==`) that R1 cannot decide is answered from the facts of the context when they contradict
its negation. Examples: `5 < x` is known and the question is `3 < x` (true); `x < y` is known and the question is
`x <= y` (true); after `y := x` the question `x == y` (true); `x + y <= 10`, `0 <= x`, `0 <= y` are known and
the question is `x <= 10` (true). The facts are the guards in `true` and `false`, the bounds of the variables in
`env`, and `v == t` recorded after an assignment `v := t` where `t` is linear and no variable of `t` is changed by
the same assignment. Facts and negated question become constraints `sum(c_i * v_i) + c <= 0`; Fourier-Motzkin
elimination, rounding every derived constraint to the integers (Pugh 1992 for the integer extension), looks for a
contradiction. Only the facts connected to the question through shared variables are used (at most 24), the
elimination stops at 200 constraints, and a question splits into at most 4 alternatives; beyond that the
question stays undecided. Terms that are not linear (a product of two variables, `ite`, reals) are ignored.

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
- R9 is a proof by contradiction. Every constraint it derives is a non-negative combination of constraints
  that hold, and rounding a constraint to the integers is valid because all variables are integers. If the
  facts and the negated question lead to `0 < c` with `c > 0`, no state satisfies both, so the question has
  the same answer in every state the facts describe. An equality `v == t` after `v := t` is only recorded when
  no variable of `t` is changed by the same (parallel) assignment, and it is removed like every other fact
  when a variable in it changes. When the limits are exceeded nothing is concluded.

Assumptions (check them if the language of Issy's programs grows):

1. Guard terms have no side effects and cannot fail (no division by zero). True for `+`, `*`, comparisons,
   `and`, `or`, `not`, `ite`; re-check if `/` or `mod` is added (the C printer already knows `mod`).
2. `Read` changes only input variables. The pass takes "input variable" to mean "used but never assigned
   in the program". A state variable that is never assigned counts as an input (this only makes the pass
   more careful).
3. Integer constants are folded only when the result has absolute value below 2^31, so no overflow of
   the C `int` is hidden.
4. A `Declare`d variable is local (printer: `Declare` is emitted inside `main()`).
5. Integer arithmetic in R9 is exact, like Issy's own semantics. If a sum overflows the C `int`, a guard can
   evaluate differently in C than R9 concludes (R1 folds a constant only below 2^31 for the same reason, but
   R9 cannot check magnitudes). The C comparison of section 6 uses `-fwrapv` and small values; no program
   there overflows.

## 4. What it does not do

- Other boolean structure is compared as written: a known `a or b` does not answer the question `b or a`.
  Comparisons of linear terms are decided by R9 whatever their written form (with `x < 2` known,
  `not (2 <= x)` is true).
- Facts about numbers come from guards and assignments on the path (R9), not from what the body of a loop does
  to a variable. Not tracked: ranges that hold at a loop head because of the body (a counter that goes from
  0 to 10 needs an interval analysis with widening, Cousot and Cousot 1977); facts that hold for some values of
  another variable only (`prog_counter != 0` implies `x1 == 0` in `cav25-heim-test-09`, so its final `abort()`
  stays; this needs separate states per value of `prog_counter`); non-linear terms, `mod`, reals.
- R9 is sound and not complete: Fourier-Motzkin over the rationals with rounding. On 9,509 random questions that
  Z3 can decide it decides 8,472.

  What the pass tracks, and how it relates to the standard analyses:

  | Level | Tracks | Source | In the pass |
  |---|---|---|---|
  | Constant sets | `x` in {1, 4} | Kildall 1973; Cousot and Cousot 1977 | yes (at most 6 values, R1, R5, R6) |
  | Intervals | `5 < x` | Cousot and Cousot 1977 | from guards and copies on the path (R9); not across loop iterations (no widening) |
  | Octagons | `+-x +-y <= c`, so `x < y` and `x + y <= 10` | Mine | the same facts from guards and copies (R9); no octagon domain, no join or widening |
  | Polyhedra | any linear constraint, such as `2x + 3y <= 12` | Cousot and Halbwachs 1978 | linear facts from guards and copies (R9); not the polyhedra domain |

  Checked on small programs: inside `5 < x` the test `3 < x`, inside `x < y` the test `x <= y`, after `y = x` the
  test `x == y`, and inside `x + y <= 10 && 0 <= x && 0 <= y` the test `x <= 10` are now decided; before R9 none of
  them was. The facts live in the same lists as the other guards, so a merge keeps only those that are on both paths.

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
--show-dead --exhaustive --prove`, 81 of 81 checks passed; every number below was identical in the real run, except the four rows that R9 changed
on 2026-10-15, see the note under the table).**
Never executed, original -> optimized, and `abort()` statements:

| Spec | Never executed | `abort()` | Statements of the AST |
|---|---|---|---|
| bounded-loop | 31 of 61 -> 0 of 30 | 5 -> 1 | 74 -> 35 |
| count-up | 31 of 61 -> 0 of 29 | 5 -> 1 | 74 -> 33 |
| swap | 17 of 33 -> 0 of 15 | 3 -> 2 | 44 -> 21 |
| buechi-cycle | 23 of 53 -> 0 of 29 | 5 -> 1 | 64 -> 34 |
| walk-to-diagonal | 45 of 61 -> 0 of 13 | 5 -> 0 | 84 -> 15 |
| two-phase (*) | 110 of 142 -> 8 of 35 | 10 -> 2 | 169 -> 40 |
| test.issy | 26 of 57 -> 3 of 40 | 4 -> 3 | 72 -> 51 |
| saturating-input | 0 of 7 -> 0 of 12 | 1 -> 0 | 10 -> 13 |
| trailing-value | 0 of 7 -> 0 of 12 | 1 -> 0 | 12 -> 15 |
| bool-handshake | 0 of 7 -> 0 of 9 | 1 -> 0 | 11 -> 11 |

(*) Issy's own program for `two-phase` ends in `abort()` after 4 reads (bug-and-fix document, 6.3), so
the numbers describe only these 4 reads.
The last three specs have `ite` terms in their assignments: the dispatch on `prog_counter`, its
`abort()` and the variable itself are gone, but the `ite` lowering makes the assignment longer.
"Statements of the AST" counts every assigned variable, `if`, loop, `read`, jump and `abort`.

**Four rows changed on 2026-10-15 (R9, section 2).** Before: `bounded-loop` 1 of 33 and 74 -> 38, `count-up` 0 of 30 and
74 -> 35, `buechi-cycle` 0 of 30 and 64 -> 36, `two-phase` 8 of 36 and 169 -> 43; the table shows the new numbers. They were
computed on the same `ast.json` files with the stand-in printer (`tests/c_exhaustive.py`), not with the real `issy`;
the numbers of the original programs reproduce the real run exactly, and the other six rows did not change.
`bounded-loop` no longer keeps its last never-executed statement, the one that needed a range fact.

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

**Ranges and relations (R9), 2026-10-15.** Old pass against the pass with R9 on the 25 specifications of the batch
(input: the program after the `ite` lowering; every other stage unchanged):

| Measure | Old pass | With R9 | Change |
|---|---|---|---|
| Lines of C | 10,700 | 10,491 | -209 (-2.0%) |
| Statements | 7,277 | 7,123 | -154 (-2.1%) |
| Term nodes | 37,105 | 35,133 | -1,972 (-5.3%) |
| `if` statements | 2,303 | 2,239 | -64 |
| `abort()` | 155 | 150 | -5 |
| Loops, `prog_counter` references | 182, 753 | 182, 753 | 0 |
| Time of the pass, 25 specs | 1.3 s | 2.5 s | +1.2 s |

9 of the 25 programs change (6 get shorter, 3 only lose term nodes); the largest change is `cav25-heim-test-11`
(2,670 -> 2,530 lines). The gain is small: most dead code that remains is not decided by a guard or a copy on the
path (section 4 gives the two typical reasons).

**Soundness tests with R9 (2026-10-15).** `dce_fuzz.py` now makes half of its programs relational (guards such as
`x < y` and `x + y <= 2`, assignments such as `y = x + 1`), so its seeds give different programs than before.

- `python3 tests/dce_fuzz.py oracle 20000`: 20,000 random fact sets and questions; every yes/no answer of `_entailed` is
  checked with Z3: 0 wrong; 8,472 of the 9,509 questions Z3 can decide are decided by the pass.
- `python3 tests/dce_fuzz.py real 18000`: 0 programs behave differently, 0 not idempotent (406,269 -> 194,765 statements).
- `python3 tests/dce_fuzz.py pipeline 300`: 0 differ (legacy pipeline: 9 of 75).
- `python3 tests/dce_fuzz.py mutants 3000`: 53 deliberately wrong variants (the 40 earlier ones and 13 for R9: `<` read as `<=`,
  a wrong rounding, a copy fact kept although the same assignment changes a variable in it, and so on): 50 detected,
  3 only make the pass less precise.
- Z3 equivalence of the 25 optimized programs (protocol of section 6): 18 proved for all lengths, 7 up to 6 reads,
  0 different, 0 inconclusive. Before: 17 and 8; the difference is `ranking-choice-2`, whose all-lengths attempt gave no
  result in the earlier run (time limit) and finished here after 107 s.
- Exhaustive comparison of the C programs (section 6): 25 of 25 identical, 3,484,910 input sequences.
- The ten specifications of this repository (table above), `python3 tests/e2e.py --exhaustive --prove` with the stand-in
  printer instead of `issy`: 71 of 71 checks passed (same observations in all scenarios and for every input sequence up to
  the depth bound; Z3 proves all ten for all lengths, 0.0 to 2.2 s). `--self-test` was not repeated for R9.

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

Many specifications at once (for example the 144 `.issy` files of
[phheim/infinite-state-reactive-synthesis-benchmarks](https://github.com/phheim/infinite-state-reactive-synthesis-benchmarks),
folder `benchmarks/`): `tests/batch_issy.py` runs `issy --solve --synt` on every file, each in its own folder
(Issy writes `ast.json` there and starts `optimizer_simple_egglog.py` by its relative name), and keeps per
specification the original and optimized C, the two ASTs, a diff, and one `ai_review.md` with everything in it.

```
python3 tests/batch_issy.py --spec-dir ../benchmarks/benchmarks --out-dir ../issy-batch --jobs 4 --timeout 300
python3 tests/batch_issy.py --spec-dir ../benchmarks/benchmarks --out-dir ../issy-batch --jobs 4 --timeout 300 --resume --verify
```

The second call does not run Issy again; it adds the checks of 6.1 to every finished pair and writes the verdict
(`proved`, `bounded`, `different`, `unverified`) to `manifest.csv` and `SUMMARY.md`. Only `proved` is a proof.

## 7. Code

`optimizer_simple_egglog.py`, section 11c (line `1151`):

| What | Line |
|---|---|
| `_Ctx` (the knowledge), `_join` | `1235`, `1262` |
| `_known`, `_fold_junction`, `_fold`, `_values`, `_decide`, `_simp` (R1) | `1274`, `1296`, `1324`, `1367`, `1380`, `1407` |
| `_narrow`, `_assume` (R3) | `1428`, `1437` |
| relations between variables (R9): `_con`, `_lin`, `_diff`, `_alternatives`, `_constraints_of`, `_facts_near`, `_infeasible`, `_entailed` | `1489`, `1502`, `1534`, `1542`, `1574`, `1596`, `1625`, `1670` |
| `_has_free_break`, `_diverges` (R4) | `1685`, `1696` |
| `_dce` (R2, R5, R7; the copy facts of R9) | `1707` |
| `_dce_loop` (R6) | `1786` |
| dead locals (R8): `_declared` ... `_drop_dead_locals` | `1832` ... `1881` |
| `eliminate_dead_code` (driver) | `1903` |
| pipeline that calls it | `optimize_ast_with_egglog`, `1923` |

Tests: `tests/e2e.py`, `tests/dce_fuzz.py` (modes `real`, `pipeline`, `oracle`, `mutants`), `tests/batch_issy.py` (many specifications, 6.4), and for section 6 `tests/equiv_check.py` (`CFG`, `segment`, `verify`,
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

**Relations between variables (R9, section 2) and the analyses that are not implemented (section 4)**
- W. Pugh. The Omega test: a fast and practical integer programming algorithm for dependence analysis. Communications of
  the ACM, August 1992, pp. 102-114 (expanded version of the Supercomputing '91 paper; volume and number not checked).
  (Fourier-Motzkin elimination extended to integers. R9 uses only the rounding of constraints, not the complete Omega
  test, so it is incomplete.)
- Not implemented: P. Cousot, N. Halbwachs. Automatic discovery of linear restraints among variables of a program. POPL
  1978, pp. 84-97 (polyhedra); A. Mine. The octagon abstract domain. arXiv:cs/0703084 (add the journal details of the
  published version before citing); intervals with widening: Cousot and Cousot 1977, listed above.

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
