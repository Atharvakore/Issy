# The ITE-lowering bug and its fix

**Date:** 2026-10-12

## 1. What the bug was

The optimizer pipeline (`ast.json` -> `optimizer_simple_egglog.py` -> `ast_optimized.json`) turned the
extracted program into a different program. The faulty step was `lower_ite_assignments_in_prog`, which
removes `ite` (if-then-else) expressions from assignments. It had two faults.

**Fault 1: the guard is evaluated twice, on different states.** It rewrote

    x := ite(c, a, b)       into       if (c)  x := a;
                                       if (!c) x := b;

The second guard `!c` is evaluated after the first branch already changed `x`. If `c` reads `x`, both
branches can run, or the wrong one runs.

Real case (`bounded-loop.issy`, at `x == 1`):

    if ((x == 1))     x = 0;
    if ((!(x == 1)))  { ... x = -1 + x; }     // x is now 0, so !(x == 1) is true: x becomes -1

The program then fails every guard and reaches `abort()`. The unoptimized program counts `x` from 10 to 0
and stays at 0.

**Fault 2: parallel assignment became sequential.** A `PAssign` with several variables means
"evaluate all right-hand sides, then assign" (this is also how the generated C works, with `temp_copy_*`
variables). The lowering turned it into one assignment after another, so a later right-hand side saw
the already-changed variable. Smallest counterexample from an earlier randomized experiment (see Evidence):

    y := (.. + i); x := y        // parallel: x gets the OLD y; after lowering: x gets the NEW y

## 2. How it was found

1. The optimized program was compiled to C (with a small JSON-to-C printer written for the
   investigation, no longer in the repository) and run next to the unoptimized one. Its trace
   stopped at `x = 1` with `abort()`.
2. A spec-independent randomized experiment then showed that the problem is general, not specific to
   this example: random programs were run before and after each pass and their behaviour compared. That
   experiment is now `tests/dce_fuzz.py` (`pipeline` mode, see section 5), so it can be repeated.

## 3. How it was fixed

Each `ite` result is computed into a fresh temporary, and the real assignment happens once, in parallel,
at the end:

    declare t
    if (c)  t := a;
    if (!c) t := b;
    x := t                 // together with the other assignments of the same PAssign, in parallel

The guards only read original variables, because `t` is fresh and nothing else changes before the final
assignment. Nested `ite`s recurse into the same temporary. Assignments without `ite` stay in the parallel
group unchanged. The temporary's name is chosen so it cannot clash with any name in the program.

Cost: the lowered program is larger than the one with `ite` expressions (for example `saturating-input`
goes from 7 to 12 statements in the AST). The C printer of Issy prints `ite` as `c ? a : b`, so for the
generated C code the lowering is not needed for correctness; it is kept because the dead-code pass
(see `2026-10-12_dead-code-elimination.md`) reasons about plain statements. Dropping the lowering is a
design decision for the author (it would make these specs smaller again).

## 4. Where the fix is

| What | Where |
|---|---|
| Fixed lowering | `optimizer_simple_egglog.py`: `sound_lower` (line 1103), helper `_ite_into` (line 1089) |
| Pipeline that uses it | `optimizer_simple_egglog.py`: `optimize_ast_with_egglog` (line 1695); it now also runs the dead-code pass `eliminate_dead_code` (line 1676), described in `2026-10-12_dead-code-elimination.md` |
| Old, unsound code (kept so the bug can be reproduced) | `lower_ite_assignments_in_prog` (line 1009), `optimize_ast_with_egglog_legacy` (line 1713) |
| How Issy calls it | `src/lib/Issy/Solver/Synthesis.hs`: `optimizeProgWithEgglog` runs `python3 optimizer_simple_egglog.py`. No Haskell change was needed. |
| Tests | `tests/e2e.py` (end-to-end with the real `issy`, specs in `tests/specs/`), `tests/dce_fuzz.py` (random programs, optimizer only) |

`main` (line 1738) writes `ast_optimized.json`. On 2026-10-13 `origin/main` had added a `flattener.py` step (dispatch loop to `switch`) after it. It is not
used: Issy cannot read or print a `Switch`, and no `switch` is wanted in the generated C code. `Synthesis.hs`
is back to the optimizer-only version and `flattener.py` and its output files are deleted on this branch. To revert: `git checkout optimizer_simple_egglog.py`.

## 5. Evidence

All numbers below come from runs on 2026-10-12. Both kinds of test sample behaviour; neither proves
equivalence.

### 5.1 Real runs (author's Mac, real `issy`)

- **Run 1** (`python3 tests/e2e.py`, optimizer from before the fixes of 6.1/6.2 and before the new
  dead-code pass): `bounded-loop`, `count-up`, `swap`, `saturating-input`, `trailing-value`,
  `bool-handshake`, `buechi-cycle` and `test.issy` behave identically in original and optimized C
  (5 seeded input streams, 301 reads each). `two-phase` failed to compile because of the stdout bug of
  6.2. `walk-to-diagonal` was rejected by Issy ("transition from l to l already defined": at most one
  transition per pair of locations), and the spec was corrected. `docs/sample.issy` did not finish
  within 900 s. 36 of 39 checks passed; the 3 failures are exactly these three.
- **Run 2** (`python3 tests/e2e.py --self-test --show-dead --keep tests/out`, with an earlier version of
  the dead-code pass): all ten quick specs compile and behave identically in 1 to 11 scenarios
  (deterministic ones once; with inputs: all zero, all one, min, max, alternating, random, sticky),
  including `two-phase` (same 4 reads, same abort, see 6.3) and `walk-to-diagonal` after the spec fix.
  The self-test (the harness itself damages the optimized program in 7-8 ways and must notice) caught
  5 to 8 of the 7-8 damaged copies per spec (all of them for 5 of the 10 specs); the undetected ones
  changed something that no later `read_inputs()` shows, so they are not observable.
  `docs/sample.issy` again did not finish; it is no longer in the default list (run it with
  `--timeout 3600`).
- The final version of the optimizer (section 4) has **not** yet been run with the real `issy`;
  re-run `python3 tests/e2e.py --self-test --show-dead --keep tests/out` to do so.

### 5.2 Real extracted programs, stand-in printer (sandbox)

`issy` cannot be built in the sandbox, so the ASTs saved by run 2 (`tests/out/<spec>/ast.json`) were fed
through the real `optimizer_simple_egglog.py`, printed to C by a small stand-in printer for the Prog
AST, and tested with the same `tests/e2e.py` checks. With the fixed optimizer all 51 checks pass. With
the old optimizer (`git show HEAD:optimizer_simple_egglog.py`) the behaviour check fails for four specs:
the optimized program reaches `abort()` after 10 reads (`bounded-loop`), 5 reads (`count-up`) and
1 read (`swap`), where the original runs on; in `trailing-value` it computes a wrong value
(`1 1 1 1` instead of `1 1 1 0`, a variable gets the NEW instead of the OLD value, Fault 2).

### 5.3 Random programs (reproducible)

`python3 tests/dce_fuzz.py pipeline 300` generates random programs in the Prog language (parallel
assignments, `ite`, nested loops, `Break`, `Continue`, `Read`, locals), runs each before and after the
whole optimizer pipeline on several input streams, and compares the final state and the reads:

| Pipeline | Programs | Behave differently |
|---|---|---|
| fixed (`optimize_ast_with_egglog`) | 300 | 0 |
| old (`optimize_ast_with_egglog_legacy`) | 75 | 6 |

(Run on 2026-10-12: about one minute for the whole command. Earlier, a first version of this experiment
that is no longer in the repository found 160 of 300 programs different for the old lowering alone
and 60 of 100 for the old full pipeline; those numbers cannot be reproduced and should not be cited.)
`bounded-loop.issy`: the old optimized program crashed; the fixed one follows the same `x` sequence as
the unoptimized program for 1001 steps.

## 6. Two more bugs found with the new specs

### 6.1 Crash on repeated sub-expressions

While running specs with a repeated sub-expression (for example `x + i` in `saturating-input.issy`), the
optimizer crashed (`SyntaxError`) and Issy aborted. This was already the case in the committed version.

Cause: `optimize_term_with_egglog` turns the extracted Egglog term into text (`str(...)`) and
`egg_repr_to_term_ast` parsed it as ONE Python expression. When a sub-expression occurs more than once,
Egglog prints it as a let-binding first:

    _EggTerm_1 = EggTerm.Add(EggTerm.Var("x"), EggTerm.Var("i"))
    EggTerm.Lt(EggTerm.Num(10), _EggTerm_1)

which is two statements, not an expression.

Fix: `egg_repr_to_term_ast` (line 750) now parses the text as a module, collects the `name = term`
bindings, and substitutes them by name when converting the final expression. The old single-expression
form still works. On the two real programs available (`bounded-loop.issy`, `test.issy`) the optimizer
output is byte-identical before and after this change.

### 6.2 The optimizer wrote into Issy's output

`optimizer_simple_egglog.py` ended with `print("Wrote optimized AST to: ...")` on standard output. Issy runs
the script with `callProcess`, which lets the child share Issy's standard output, and Issy's own output
(the C program) is the thing a user redirects into a file. Issy's output is buffered and flushed in blocks,
so the message ended up in the middle of a line of the original C program. Real failure from the first run
of the end-to-end test on `tests/specs/two-phase.issy`:

    original.c:234:68: error: invalid suffix 'Wrote' on integer constant
    int temp_copy_x = ((x == 1) ? 0 : (-1Wrote optimized AST to: ast_optimized.json

Whether and where it hit depended on the size of the output, so most specs passed by luck.

Fix: all output of the script now goes to standard error (the final message and the optional debug
prints behind `PRINT_CHANGED_TERMS`). The test reproduced the failure with a stand-in `issy` that flushes
mid-line and passes after the change; the test prints a hint if "Wrote optimized AST" shows up in the C
code.

### 6.3 `two-phase.issy`: Issy's own program aborts (not an optimizer bug)

With the real `issy`, the C program printed for `tests/specs/two-phase.issy` reads 4 inputs and then
reaches `abort()`: at `x == 3` it enters the inner loop of the second phase, which only accepts
`prog_counter == 0`, while `prog_counter` is 1. The optimized program does exactly the same (4 reads,
then `abort()`), so the optimizer preserved the behaviour, and the test reports "1 runs end in abort
(same in both)" as information. The cause is therefore in the program Issy extracts, not in the
optimizer. A possible explanation is the mapping of locations to `prog_counter` values for nested loops
in the extraction (`extractPG`/`SyBoLoop`), but this was not verified. It should be checked against
Issy's source or reported to its authors before it is written up as a fact. The spec stays as an
input that exercises the `abort()` path.

## 7. Sources

Entries were written from memory: check the details before putting them in the thesis.

- E. W. Dijkstra. *A Discipline of Programming*. Prentice-Hall, 1976. (simultaneous/multiple assignment)
- E. W. Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. *Communications of
  the ACM* 18(8):453-457, 1975. (guarded commands, the form the `ite` lowering produces)
- M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock, P. Panchekha. egg: Fast and extensible equality
  saturation. *Proc. ACM Program. Lang.* 5(POPL), 2021. (technique behind the existing term optimizer)
- Y. Zhang, Y. R. Wang, O. Flatt, D. Cao, P. Zucker, E. Rosenthal, Z. Tatlock, M. Willsey. Better
  Together: Unifying Datalog and Equality Saturation. *Proc. ACM Program. Lang.* 7(PLDI), 2023. (egglog)
- P. Heim, R. Dimitrova. Issy: A Comprehensive Tool for Specification and Synthesis of Infinite-State
  Reactive Systems. CAV 2025, LNCS 15934, pp. 298-312. (the tool that produces the program)
- W. M. McKeeman. Differential testing for software. *Digital Technical Journal* 10(1):100-107, 1998.
- X. Yang, Y. Chen, E. Eide, J. Regehr. Finding and understanding bugs in C compilers. PLDI 2011,
  pp. 283-294. (random programs plus comparison of behaviour, the idea behind the test)
