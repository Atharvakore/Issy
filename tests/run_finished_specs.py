#!/usr/bin/env python3
"""Run Issy and the optimizer on the 40 benchmark specifications that finished within 300 s, and keep
the original and the optimized C program of each one in a folder a reviewer can analyze.

The 40 names are in tests/finished_specs.txt (25 with a program, 15 unrealizable). The other 104 of the
144 benchmarks did not finish in the earlier batch run and are not started again.

  Step 1: synthesize, optimize, save                (takes a few minutes; the slowest spec needed ~4 min)
      python3 tests/run_finished_specs.py
  Step 2, later: check original against optimized   (Z3 on the programs' ASTs + exhaustive run of the C files)
      python3 tests/run_finished_specs.py --verify   (does not run Issy again; it only adds the checks)

Needs, as for tests/batch_issy.py: the built ./issy, `pip3 install egglog`, and for --verify `pip3 install z3-solver`.

Result in --out-dir (default ../issy-batch-finished):
  README_FOR_AI.md        what the folder contains and how to review it (read this file first)
  SUMMARY.md, manifest.csv, manifest.jsonl, run_info.json
  cases/<spec>/original.c, optimized.c, diff.patch, ast.json, ast_optimized.json, ai_review.md, ...
  cases/<spec>/equivalence_smt.txt, equivalence_c.txt   (after --verify)
Unrealizable specs have only the specification and Issy's output: there is no program to compare.

Without --verify nothing says that the two programs are equivalent. Only a result "proved" is a proof;
documents/2026-10-12_dead-code-elimination.md, section 6, states what the checks do and do not show.
"""

import argparse
import csv
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
LIST = HERE / "finished_specs.txt"
DONE = ("pair_ready", "unrealizable")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--spec-dir", type=Path, default=REPO.parent / "benchmarks" / "benchmarks",
                    help="folder with the .issy benchmarks (default: ../benchmarks/benchmarks next to the repository)")
    ap.add_argument("--out-dir", type=Path, default=REPO.parent / "issy-batch-finished",
                    help="where the results are written (default: ../issy-batch-finished)")
    ap.add_argument("--timeout", type=int, default=600,
                    help="seconds per spec for Issy (default 600; the slowest spec needed 234 s in the earlier run)")
    ap.add_argument("--jobs", type=int, default=4, help="specs in parallel (default 4)")
    ap.add_argument("--verify", action="store_true",
                    help="add the equivalence checks to an earlier run in --out-dir without running Issy again")
    ap.add_argument("--verify-timeout", type=int, default=180, help="seconds for each of the two checks (default 180)")
    ap.add_argument("--extra-options", default="", help="additional Issy flags, quoted as one string")
    args = ap.parse_args()

    cmd = [sys.executable, str(HERE / "batch_issy.py"),
           "--issy-dir", str(REPO), "--spec-dir", str(args.spec_dir), "--out-dir", str(args.out_dir),
           "--only", str(LIST), "--timeout", str(args.timeout), "--jobs", str(args.jobs),
           "--verify-timeout", str(args.verify_timeout)]
    if args.extra_options:
        cmd += ["--extra-options", args.extra_options]
    if args.verify:
        cmd += ["--resume", "--verify"]
    print("Running:", " ".join(cmd), "\n", flush=True)
    rc = subprocess.call(cmd)

    manifest = args.out_dir / "manifest.csv"
    if rc == 0 and manifest.is_file():
        rows = list(csv.DictReader(manifest.open(encoding="utf-8")))
        counts = {}
        for r in rows:
            counts[r["status"]] = counts.get(r["status"], 0) + 1
        print("\nStatus of the", len(rows), "specs:", counts)
        not_done = [r["spec"] for r in rows if r["status"] not in DONE]
        if not_done:
            print("Not finished this time (timeout/error): " + ", ".join(not_done)
                  + "\n  -> see cases/<spec>/stderr.txt; try a larger --timeout.")
        if not args.verify:
            print("Equivalence is not checked yet:  python3 tests/run_finished_specs.py --verify")
    return rc


if __name__ == "__main__":
    sys.exit(main())
