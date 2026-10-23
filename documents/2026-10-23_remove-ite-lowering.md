# 2026-10-23: the ite lowering is removed from the pipeline

## What changed

`optimizer_simple_egglog.py`, function `optimize_ast_with_egglog`:

| | Pipeline |
|---|---|
| Before | Egglog terms, dead-code elimination, clean-up, **ite lowering**, clean-up, dead-code elimination, clean-up |
| Now | Egglog terms, dead-code elimination, clean-up |

- `FIte` terms stay in the program. The C printer prints them as `c ? a : b` (`printTerm`, `("ite", [c, th, el])` in `Synthesis.hs`).
- The lowering code (sections 11 and 11b, `sound_lower`, `lower_ite_assignments_in_prog`) and `optimize_ast_with_egglog_legacy` are **still in the file**, unchanged, because `tests/dce_fuzz.py`, `tests/equiv_check.py` and `tests/c_exhaustive.py` call the legacy pipeline. A NOTE comment at both section headers says they are no longer used by the pipeline.
- Not touched: the Egglog rules, `eliminate_dead_code`, `optimize_prog_structure`, the Haskell code.
- `documents/2026-10-12_dead-code-elimination.md` still describes the pipeline with the lowering; this document replaces that part.

## Why

On the 25 programs the lowering was the largest remaining cost: `if (g) t = a; if (!(g)) t = b;` prints the guard twice, and every lowered assignment adds a temporary and a `temp_copy_` block.

## Effect on the 25 programs (original ASTs of the 15 Oct run, commit `ad2b95d`)

| | C lines | C characters |
|---|---|---|
| Original (Issy) | 27,413 | 1,379,351 |
| Before (with lowering) | 6,075 | 254,768 |
| Now | 3,986 (-34%) | 157,226 (-38%) |

The new output has 419 `FIte` terms and no `ite_tmp_` variable. Every function in it is one that `printTerm` prints.

## Checked

- Original against the new output on random input sequences, from the all-zero start and from random start states, comparing the values of all global variables at every read and the way the run ends: 4,977 runs, 129,413 reads, 0 differences. 23 random-start runs were skipped because the original reads an uninitialised local (fault-tolerance).
- The comparison uses an evaluator written from the Haskell sources (not `tests/equiv_check.py`).
- `python3 tests/dce_fuzz.py pipeline 12`: 0 of 12 programs behave differently (the legacy pipeline still shows its known faults).

## Not checked

- The run with the real `issy` binary: it prints the C text, and I could only run the Python optimizer. Run `python3 tests/run_finished_specs.py` to produce the new original and optimized C programs.

## Undo

`git checkout optimizer_simple_egglog.py` before committing, or revert the commit afterwards.
