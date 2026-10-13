# Optimizer and flattener.py together: three problems and their fixes

**Date:** 2026-10-13

## 1. What changed in `main` and what was tested

`origin/main` got three commits (`0cda25e`, `066a11d`, `426748a`). They add `flattener.py` and change the
Haskell function `optimizeProgWithEgglog` (`src/lib/Issy/Solver/Synthesis.hs`, line 328) to this pipeline:

    ast.json  ->  optimizer_simple_egglog.py  ->  ast_optimized.json
              ->  flattener.py                ->  ast_switch_atomic.json   (read back by Issy)

`flattener.py` turns the dispatch loop on `prog_counter` into `Switch`/`Case`/`Default` nodes and makes every
case update its variables "atomically" (copy the variables to `__tmp_*`, write to the copies, copy back
before `Continue`/`Break`). The branch `dead-code-elimination` was merged with `origin/main` (merge commit
`6f846ae`, no conflicts: the two sides touch different files). The question was whether the output of the
optimizer survives the flattener.

It did not. Running both steps on the ten real programs and on random programs and comparing behaviour
(section 4) showed three problems. They are all fixed in `flattener.py`; the optimizer was not changed.

## 2. The three problems

### 2.1 Temporaries of the optimizer were redirected to stale copies (optimizer + flattener)

`sound_lower` (see `2026-10-12_bug-and-fix.md`) lowers `x := ite(c, a, b)` to

    declare t;  if (c) t := a;  if (!c) t := b;  x := t

The flattener redirects EVERY assigned variable to its `__tmp_` copy, also `t`. Then `t := a` writes
`__tmp_t`, but `x := t` still reads `t`, which was never written. `x` gets a stale value.

Real case (`test.issy`, input profile "min"): `prog_counter := ite_tmp_prog_counter_1` read the stale
temporary, `prog_counter` became 0 again and the program looped without ever reading (it "spins" after 5
reads, while the original keeps reading). The same would happen to any local variable that is written and
read in the same case body, for example Issy's own `init_x`.

Fix (`flattener.py`): `collect_declared_variables` (line 797) collects every `Declare`d name and
`semantically_equivalent_switch_transform` (line 1090) removes them from the set of redirected variables.
`prog_counter` is declared too but must stay atomic, so it is added back. Locals therefore keep the normal
sequential meaning, which is what the Prog language defines.

### 2.2 A nested loop lost its updates (flattener alone)

If a case body contains a loop that is not itself converted, the loop writes the real variables, but the
case ends with "copy `__tmp_*` back", and the copies are older than the loop. All updates of the loop are
overwritten.

Real cases, flattener alone, no optimizer involved (the flattened program differs from the one Issy
printed): `bounded-loop` (state 10 instead of 0 at read 10), `count-up` (0 instead of 5 at read 5),
`two-phase` (0 instead of 3 at read 3).

Fix (`flattener.py`, `rewrite_sequence_atomic`, lines 932-939): before a nested loop the pending copies are
written back, after it a new snapshot is taken. The loop itself runs with the sequential meaning.

### 2.3 Blocks that change `prog_counter` and fall through (flattener alone)

Issy prints, at the head of inner loops, blocks like `if (prog_counter == 2) { prog_counter = 0; }` that
do NOT end in `continue`: the following blocks (`if (prog_counter == 0) ...`) then see the new value in the
same pass. A `Case` cannot express that, because the switch value is read once at the top of the loop and
the update is delayed. Converting such a loop changes the program.

Found with random programs only (the ten real programs do not trigger it, `count-up` has this shape but
its guards are too complex for the flattener to convert).

Fix (`flattener.py`, `writes_variable` line 570, `fallthrough_states` line 587,
`falls_through_after_pc_write` line 625, used in `convert_dispatcher_sequence_to_switch` at line 687): a
dispatch loop is not converted when some path of one of its blocks writes `prog_counter` and then leaves the
block normally (not through `continue`, `break` or `abort`). The loop then stays a loop, which is correct
after fix 2.2.

## 3. Interplay in the other direction

The dead-code pass of the optimizer removes exactly the fall-through blocks of 2.3 when it can decide them
(after `prog_counter := 2` the later guard `prog_counter == 0` is known to be false). After the optimizer
most real programs no longer contain a dispatch loop at all, so the flattener has nothing to do: only
`swap` (2 switches) and `test` (2 switches) still produce a `Switch`; without the optimizer 7 of the 10
programs do.

## 4. Test and results

New files: `tests/ast_interp.py` (interpreter for the Prog JSON including `Switch`, with the meaning of
the C printer: parallel assignment, `Break`/`Continue` refer to the innermost loop), `tests/flatten_check.py`
(runs the two Python steps of the pipeline and compares behaviour on 8 input profiles) and
`tests/fixtures/*.ast.json` (the ten `ast.json` files that the real `issy` printed for the specs of
`tests/specs/`, `bounded-loop.issy` and `test.issy` on 2026-10-12).

    python3 tests/flatten_check.py                          # the ten real programs, about 10 s
    python3 tests/flatten_check.py fuzz 50 1000             # 50 random programs shaped like Issy's output
    python3 tests/flatten_check.py fuzz 40 2000 --resets    # ... with fall-through blocks (2.3)
    python3 tests/flatten_check.py --flattener DIR          # use DIR/flattener.py, e.g. the version of main

| Test | flattener of `main` | with the fixes |
|---|---|---|
| ten real programs: optimizer alone differs | 0 | 0 |
| ten real programs: flattener alone differs | 3 (`bounded-loop`, `count-up`, `two-phase`) | 0 |
| ten real programs: optimizer + flattener differs | 1 (`test`) | 0 |
| random, seeds 1100-1199, no fall-through blocks: programs that read at least 3 times | 85 | 85 |
| ... optimizer + flattener differs | 31 (flattener alone: 0) | 0 |
| random, seeds 1000-1199 (166 programs, 71 with a `Switch` after the optimizer): any difference | not run | 0 |
| random with fall-through blocks, seeds 2000-2039: flattener alone / optimizer + flattener differs | 4 / 16 | 0 / 0 |
| random with fall-through blocks, seeds 2000-2079 (65 programs, 28 with a `Switch`) | not run | 0 |

Run on 2026-10-13 in the sandbox; the optimizer alone never differed in any of these runs. The test
samples behaviour (8 input profiles, up to 120 reads); it does not prove equivalence. The random programs
are produced by `Gen` in `tests/flatten_check.py`: a dispatch loop with 4 `prog_counter` values, nested
loops, parallel assignments with `ite`, reads and the `abort()` sentinel. The interpreter was checked against
the real programs: the original and the optimized program give identical traces.

## 5. Open points (not changed)

- **Issy cannot read a `Switch` yet.** The Haskell type `Prog` (`Synthesis.hs`, line 261) has no `Switch`
  constructor, so `eitherDecodeFileStrict "ast_switch_atomic.json"` fails with "Failed to parse flattened
  Prog" for every program in which the flattener produces a `Switch` (with the optimizer: `swap` and `test`).
  This is the "add switch to the DSL" step that the commit message of `0cda25e` names as next. Read from the
  source, not run: the Haskell code could not be built in the sandbox.
- **`break` inside a C `switch`.** In the AST `Break` leaves the loop. In C a plain `break` inside a
  `switch` only leaves the switch, so the C printer for `Switch` must print `Break` as a `goto` or a flag,
  otherwise the generated program loops forever.
- **`sound_lower` is not needed for correctness once the atomic rewrite exists**, but it is needed when the
  flattener does not convert a loop (the normal sequential meaning applies there). Keeping both is correct.
- The flattener's switch conversion assumes that blocks with the same `prog_counter` value run one after the
  other in a case. This holds for the programs tested; it is not proved.

## 6. Where

| What | Where |
|---|---|
| Fixes | `flattener.py`: lines 570-636, 687, 797, 932-939, 1090 |
| Pipeline | `src/lib/Issy/Solver/Synthesis.hs`: `optimizeProgWithEgglog` (line 328) |
| Test | `tests/flatten_check.py`, `tests/ast_interp.py`, `tests/fixtures/` |
| Commit | the commit after the merge `6f846ae` on `dead-code-elimination` |

To revert the fixes: `git checkout origin/main -- flattener.py`.

## 7. Sources

Entries were written from memory: check the details before putting them in the thesis.

- E. W. Dijkstra. *A Discipline of Programming*. Prentice-Hall, 1976. (simultaneous assignment, the model
  behind the atomic update)
- W. M. McKeeman. Differential testing for software. *Digital Technical Journal* 10(1):100-107, 1998.
- X. Yang, Y. Chen, E. Eide, J. Regehr. Finding and understanding bugs in C compilers. PLDI 2011.
  (random programs and comparison of behaviour, the idea behind `fuzz`)
- P. Heim, R. Dimitrova. Issy: A Comprehensive Tool for Specification and Synthesis of Infinite-State
  Reactive Systems. CAV 2025. (the tool that prints the programs)
