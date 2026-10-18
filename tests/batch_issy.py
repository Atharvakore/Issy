#!/usr/bin/env python3
"""Run Issy on many .issy specifications and keep everything needed to compare the program Issy
synthesizes with the program the optimizer (optimizer_simple_egglog.py) produces from it.

For every specification a folder  <out-dir>/cases/<spec>/  is written:

    spec.issy             the specification that was run
    original.c            the C program Issy synthesizes (before the optimizer)
    optimized.c           the C program after optimizer_simple_egglog.py
    diff.patch            unified diff original.c -> optimized.c
    ast.json              the program as Issy hands it to the optimizer
    ast_optimized.json    the program the optimizer returns
    stdout.txt, stderr.txt, metadata.json
    ai_review.md          one self-contained file for a reviewer: spec, both programs, diff,
                          machine-checked verdicts and the questions to answer
    equivalence_smt.txt   (with --verify) Z3 translation validation of ast.json against ast_optimized.json
    equivalence_c.txt     (with --verify) exhaustive run of original.c and optimized.c on all inputs sequences
                          up to a depth bound

and in <out-dir>:  manifest.csv, manifest.jsonl, SUMMARY.md, README_FOR_AI.md, run_info.json.

Typical use (from the root of the Issy repository, after `make` and `pip3 install egglog z3-solver`):

  git clone https://github.com/phheim/infinite-state-reactive-synthesis-benchmarks ../benchmarks
  python3 tests/batch_issy.py --spec-dir ../benchmarks/benchmarks --out-dir ../issy-batch \\
          --jobs 4 --timeout 300                      # 1. synthesize and optimize everything
  python3 tests/batch_issy.py --spec-dir ../benchmarks/benchmarks --out-dir ../issy-batch \\
          --jobs 4 --timeout 300 --resume --verify    # 2. add the equivalence checks, nothing is re-run

Only some specifications (--only): a list file restricts the run, so that the specifications Issy cannot
solve within the time limit are not started again. tests/finished_specs.txt lists the 40 of the 144
benchmarks that finished within 300 s (25 with a program, 15 unrealizable);
tests/run_finished_specs.py runs exactly these.

Why each case runs in its own folder: Issy writes ast.json and ast_optimized.json into its current
directory and starts `python3 optimizer_simple_egglog.py` by that relative name (Synthesis.hs,
optimizeProgWithEgglog). The runner therefore puts a copy of the optimizer into the case folder for the
duration of the run, so parallel runs (--jobs) cannot overwrite each other's files.

Without --verify the result only packages the programs for review; it does NOT show that they are
equivalent. See documents/2026-10-12_dead-code-elimination.md, section 6, for what --verify proves and
what it does not.
"""

import argparse
import concurrent.futures as cf
import csv
import difflib
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time
import traceback
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
OPTIMIZER = "optimizer_simple_egglog.py"
FALLBACK_STEPS = 6  # reads covered by the cheap second SMT attempt (check_smt)

ORIGINAL_MARKER = re.compile(r"(?im)^\s*={3,}\s*ORIGINAL\s+C\s+PROGRAM\s*={3,}\s*$")
RESULT_MARKER = re.compile(r"(?im)^\s*(Unrealizable|Realizable)\s*$")
OPTIMIZED_MARKER = re.compile(r"(?im)^\s*={3,}\s*OPTIMIZED\s+C\s+PROGRAM\s*={3,}\s*$")
AST_MESSAGE = re.compile(r"(?im)^\s*Wrote optimized AST to:.*$")
C_START = re.compile(r"(?m)^\s*(?:#\s*include\b|(?:int|void)\s+main\s*\()")
SMT_VERDICT = re.compile(r"PROVED for all lengths|PROVED up to \d+ reads|DIFFERENT|INCONCLUSIVE")

STATUSES = ("pair_ready", "unrealizable", "timeout", "error", "optimizer_error", "unknown_verdict",
            "incomplete_pair")


# ----------------------------------------------------------------------------------------------
# small helpers
# ----------------------------------------------------------------------------------------------
def sha256_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fp:
        for chunk in iter(lambda: fp.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def write_text(path, value):
    path.write_text(value, encoding="utf-8")


def tail(text, n=400):
    text = (text or "").strip()
    return text[-n:]


_ACTIVE = set()
_LOCK = threading.Lock()


def kill_group(pid):
    try:
        os.killpg(pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def kill_all():
    with _LOCK:
        pids = list(_ACTIVE)
    for pid in pids:
        kill_group(pid)


def run_group(cmd, cwd, timeout):
    """Run `cmd` in a process group of its own, so that a timeout also stops the solver processes that
    Issy starts. Returns (returncode, stdout, stderr, timed_out, error)."""
    try:
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                encoding="utf-8", errors="replace", start_new_session=True)
    except OSError as e:
        return None, "", "", False, str(e)
    with _LOCK:
        _ACTIVE.add(proc.pid)
    timed_out = False
    try:
        try:
            out, err = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            kill_group(proc.pid)
            out, err = proc.communicate()
    finally:
        with _LOCK:
            _ACTIVE.discard(proc.pid)
    return proc.returncode, out, err, timed_out, None


def describe_exit(rc):
    if rc is None:
        return "could not be started"
    if rc < 0:
        try:
            name = signal.Signals(-rc).name
        except ValueError:
            name = f"signal {-rc}"
        return f"killed by {name} (return code {rc})"
    return f"exit code {rc}"


def last_line(text):
    lines = [l.strip() for l in (text or "").splitlines() if l.strip()]
    return lines[-1] if lines else ""


# ----------------------------------------------------------------------------------------------
# reading Issy's output
# ----------------------------------------------------------------------------------------------
def c_code(text):
    """Drop leading log lines, but do not 'fix' or rewrite C code."""
    match = C_START.search(text)
    if not match:
        return None
    program = text[match.start():].strip()
    return program + "\n" if program else None


def extract_programs(stdout, stderr):
    """Issy prints '===== ORIGINAL C PROGRAM =====', the original C, then 'Realizable', then the optimized C.
    Nothing is guessed: a missing program stays None."""
    combined_status = list(RESULT_MARKER.finditer(stdout))
    if not combined_status:
        combined_status = list(RESULT_MARKER.finditer(stderr))
    verdict = combined_status[-1].group(1) if combined_status else "Unknown"

    original = None
    optimized = None
    for stream in (stdout, stderr):
        m = ORIGINAL_MARKER.search(stream)
        if not m:
            continue
        boundaries = [len(stream)]
        for pattern in (AST_MESSAGE, RESULT_MARKER, OPTIMIZED_MARKER):
            n = pattern.search(stream, m.end())
            if n:
                boundaries.append(n.start())
        original = c_code(stream[m.end():min(boundaries)])
        if original:
            break

    if verdict == "Realizable":
        for stream in (stdout, stderr):
            matches = list(RESULT_MARKER.finditer(stream))
            if not matches:
                continue
            n = matches[-1]
            if n.group(1).lower() != "realizable":
                continue
            optimized = c_code(stream[n.end():])
            if optimized:
                break
        if not optimized:  # an explicitly marked optimized program, if Issy prints one
            for stream in (stdout, stderr):
                n = OPTIMIZED_MARKER.search(stream)
                if n:
                    optimized = c_code(stream[n.end():])
                    if optimized:
                        break

    return verdict, original, optimized


def make_diff(original, optimized, spec_name):
    if original is None or optimized is None:
        return None, None
    a, b = original.splitlines(keepends=True), optimized.splitlines(keepends=True)
    diff = "".join(difflib.unified_diff(a, b, fromfile=f"{spec_name}/original.c",
                                        tofile=f"{spec_name}/optimized.c", n=3))
    similarity = difflib.SequenceMatcher(None, a, b, autojunk=True).ratio()
    return diff, similarity


# ----------------------------------------------------------------------------------------------
# equivalence checks (--verify)
# ----------------------------------------------------------------------------------------------
def check_smt(case_dir, tools, timeout):
    """Z3 translation validation, tests/equiv_check.py --pair ast.json ast_optimized.json.
    -> (verdict, detail, seconds); verdict in PROVED_ALL, PROVED_BOUNDED, DIFFERENT, INCONCLUSIVE,
    TIMEOUT, ERROR, NO_AST.

    Large programs often exhaust the time of the full check (20 reads and a proof for all lengths). Then a
    second, cheap attempt proves equivalence only for input sequences of up to FALLBACK_STEPS reads, which is
    still worth more than no answer (the verdict is PROVED_BOUNDED and the detail says so)."""
    a, b = case_dir / "ast.json", case_dir / "ast_optimized.json"
    if not (a.is_file() and b.is_file()):
        return "NO_AST", "ast.json or ast_optimized.json is missing", 0.0
    start = time.monotonic()
    log = []

    def attempt(extra, limit):
        cmd = [sys.executable, str(tools / "equiv_check.py"), "--pair", "ast.json", "ast_optimized.json",
               "--budget", str(max(10, limit - 30))] + extra
        rc, out, err, timed_out, error = run_group(cmd, case_dir, limit)
        log.append(f"$ {shlex.join(cmd)}\n\n{out}\n--- stderr ---\n{err}\n")
        if error:
            return "ERROR", error
        if timed_out:
            return "TIMEOUT", f"no verdict within {limit}s"
        m = SMT_VERDICT.search(out)
        if not m:
            return "ERROR", tail(err or out)
        kind = m.group(0)
        verdict = ("PROVED_ALL" if kind.startswith("PROVED for") else
                   "PROVED_BOUNDED" if kind.startswith("PROVED up") else kind)
        return verdict, next((l for l in out.splitlines() if kind in l), kind).strip()

    verdict, detail = attempt([], timeout)
    if verdict in ("INCONCLUSIVE", "TIMEOUT"):
        v2, d2 = attempt(["--steps", str(FALLBACK_STEPS), "--no-unbounded"], min(timeout, 120))
        if v2 in ("PROVED_BOUNDED", "DIFFERENT"):
            verdict, detail = v2, f"{d2}  [full check: {detail}]"
    secs = round(time.monotonic() - start, 3)
    write_text(case_dir / "equivalence_smt.txt", "\n".join(log))
    return verdict, detail, secs


def check_c(case_dir, tools, timeout):
    """Run original.c and optimized.c on every input sequence up to a depth bound (tests/c_exhaustive.py).
    -> (verdict, detail, seconds); verdict in OK, FAIL, UNSUPPORTED, TIMEOUT, ERROR, NO_C."""
    a, b = case_dir / "original.c", case_dir / "optimized.c"
    if not (a.is_file() and b.is_file()):
        return "NO_C", "original.c or optimized.c is missing", 0.0
    start = time.monotonic()
    cmd = [sys.executable, str(tools / "c_exhaustive.py"), "original.c", "optimized.c"]
    rc, out, err, timed_out, error = run_group(cmd, case_dir, timeout)
    secs = round(time.monotonic() - start, 3)
    write_text(case_dir / "equivalence_c.txt", f"$ {shlex.join(cmd)}\n\n{out}\n--- stderr ---\n{err}\n")
    if error:
        return "ERROR", error, secs
    if timed_out:
        return "TIMEOUT", f"no result within {timeout}s", secs
    first = out.strip().splitlines()[0] if out.strip() else ""
    if first.startswith("OK"):
        return "OK", first[2:].strip(), secs
    if first.startswith("FAIL"):
        return "FAIL", first[4:].strip(), secs
    if "ValueError" in err:
        return "UNSUPPORTED", tail(err.strip().splitlines()[-1], 300), secs
    return "ERROR", tail(err or out), secs


def combine(smt, c):
    """One word per case. 'proved' only when the SMT check proves it for all input lengths."""
    if smt == "DIFFERENT" or c == "FAIL":
        return "different"
    if smt == "PROVED_ALL":
        return "proved"
    if smt == "PROVED_BOUNDED" or c == "OK":
        return "bounded"
    return "unverified"


def verify_case(case_dir, tools, timeout, meta):
    smt, smt_detail, smt_secs = check_smt(case_dir, tools, timeout)
    c, c_detail, c_secs = check_c(case_dir, tools, timeout)
    meta.update({
        "smt_verdict": smt, "smt_detail": smt_detail, "smt_seconds": smt_secs,
        "c_verdict": c, "c_detail": c_detail, "c_seconds": c_secs,
        "equivalence": combine(smt, c),
    })


# ----------------------------------------------------------------------------------------------
# the review packet
# ----------------------------------------------------------------------------------------------
def write_packet(case_dir, spec_name, source, original, optimized, diff, metadata):
    checked = metadata.get("equivalence") is not None
    if checked:
        machine = (
            "\n## Machine-checked results\n\n"
            f"- **Overall: {metadata['equivalence']}**  (`proved` = Z3 proves it for input sequences of every "
            "length; `bounded` = proved up to a number of reads, or no difference in the exhaustive C run; "
            "`different` = a counterexample exists; `unverified` = the tools gave no answer)\n"
            f"- SMT translation validation of `ast.json` against `ast_optimized.json`: "
            f"{metadata['smt_verdict']} - {metadata['smt_detail']}  (`equivalence_smt.txt`)\n"
            f"- Every input sequence up to a depth bound on `original.c` and `optimized.c`: "
            f"{metadata['c_verdict']} - {metadata['c_detail']}  (`equivalence_c.txt`)\n"
            "- A `different` verdict comes with an input sequence that an independent interpreter replays; "
            "check it by hand before reporting it.\n"
            "- Do not turn `bounded` or `unverified` into 'equivalent'.\n")
    else:
        machine = ("\n## Machine-checked results\n\nNot run (use `--verify`). Text similarity and "
                   "compilation do not prove equivalence.\n")
    packet = (
        f"# Review package: {spec_name}\n\n"
        "**Important:** textual similarity and compilation do not prove semantic "
        "equivalence. Check all inputs, reachable states, side effects, aborts, "
        "termination/divergence and infinite traces where relevant. If proof is "
        "unavailable, state 'unverified', not 'equivalent'.\n\n"
        "## Execution facts\n\n"
        f"- Issy verdict: {metadata['verdict']}\n"
        f"- Return code: {metadata['return_code']}\n"
        f"- Timed out: {metadata['timed_out']}\n"
        f"- Elapsed seconds: {metadata['elapsed_seconds']}\n"
        f"- Lines of C: original {metadata['original_lines']}, optimized {metadata['optimized_lines']}\n"
        f"{machine}"
        "\n## Original specification\n\n```text\n"
        f"{source}\n```\n\n"
        "## Original C\n\n```c\n"
        f"{original}\n```\n\n"
        "## Optimized C\n\n```c\n"
        f"{optimized}\n```\n\n"
        "## Unified diff\n\n```diff\n"
        f"{diff or '(no textual difference)'}\n```\n\n"
        "## Review questions\n\n"
        "1. Are the observable input/output traces and side effects preserved?\n"
        "2. Was any branch removed that is reachable in the original?\n"
        "3. Have aborts, infinite loops, state updates, or input reads changed?\n"
        "4. Can you provide a concrete counterexample if they differ?\n"
        "5. What requires formal verification beyond source inspection?\n"
    )
    write_text(case_dir / "ai_review.md", packet)


# ----------------------------------------------------------------------------------------------
# one case
# ----------------------------------------------------------------------------------------------
def run_case(spec_path, spec_dir, output_root, issy_dir, options, timeout, resume, verify, verify_timeout,
             tools):
    issy_binary = issy_dir / "issy"
    relative = spec_path.relative_to(spec_dir)
    case_dir = output_root / "cases" / relative.with_suffix("")
    meta_file = case_dir / "metadata.json"
    spec_data = spec_path.read_bytes()
    spec_hash = sha256_bytes(spec_data)

    if resume and meta_file.exists():
        try:
            old = json.loads(meta_file.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            old = None
        if old and old.get("spec_sha256") == spec_hash and old.get("status") in ("pair_ready", "unrealizable"):
            if verify and old["status"] == "pair_ready" and old.get("equivalence") is None:
                # Issy has already run; only add the equivalence checks.
                verify_case(case_dir, tools, verify_timeout, old)
                write_text(meta_file, json.dumps(old, indent=2, ensure_ascii=False) + "\n")
                write_packet(case_dir, relative.name,
                             (case_dir / "spec.issy").read_text(encoding="utf-8", errors="replace"),
                             (case_dir / "original.c").read_text(encoding="utf-8"),
                             (case_dir / "optimized.c").read_text(encoding="utf-8"),
                             (case_dir / "diff.patch").read_text(encoding="utf-8")
                             if (case_dir / "diff.patch").exists() else "", old)
            return old, True

    case_dir.mkdir(parents=True, exist_ok=True)
    # Prevent stale artifacts from an earlier run being mistaken for fresh output.
    for name in ("original.c", "optimized.c", "diff.patch", "ai_review.md", "ast.json", "ast_optimized.json",
                 "stdout.txt", "stderr.txt", "equivalence_smt.txt", "equivalence_c.txt", OPTIMIZER):
        target = case_dir / name
        if target.is_file():
            target.unlink()
    shutil.copy2(spec_path, case_dir / "spec.issy")
    # Issy starts `python3 optimizer_simple_egglog.py` relative to its current directory.
    shutil.copy2(issy_dir / OPTIMIZER, case_dir / OPTIMIZER)

    cmd = [str(issy_binary), "--solve", "--synt"] + options + [str(spec_path)]
    started = time.monotonic()
    return_code, stdout, stderr, timed_out, error = run_group(cmd, case_dir, timeout)
    elapsed = round(time.monotonic() - started, 3)
    try:
        (case_dir / OPTIMIZER).unlink()
    except OSError:
        pass

    write_text(case_dir / "stdout.txt", stdout)
    write_text(case_dir / "stderr.txt", stderr)
    verdict, original, optimized = extract_programs(stdout, stderr)
    if original is not None:
        write_text(case_dir / "original.c", original)
    if optimized is not None:
        write_text(case_dir / "optimized.c", optimized)
    diff, similarity = make_diff(original, optimized, relative.name)
    if diff is not None:
        write_text(case_dir / "diff.patch", diff)

    if timed_out:
        status = "timeout"
    elif error or return_code != 0:
        status = "error"
        if "Traceback (most recent call last)" in stderr or OPTIMIZER in stderr:
            status = "optimizer_error"  # Issy synthesized a program, the Python optimizer failed
        if not error:
            error = describe_exit(return_code) + (f": {last_line(stderr)}" if last_line(stderr) else ", no output")
    elif verdict == "Unrealizable":
        status = "unrealizable"  # No program pair expected.
    elif verdict != "Realizable":
        status = "unknown_verdict"
    elif original is None or optimized is None:
        status = "incomplete_pair"  # Do not fabricate a missing program.
    else:
        status = "pair_ready"  # Ready for review.

    meta = {
        "spec": str(relative),
        "spec_sha256": spec_hash,
        "case_dir": str(case_dir),
        "status": status,
        "verdict": verdict,
        "return_code": return_code,
        "timed_out": timed_out,
        "elapsed_seconds": elapsed,
        "original_available": original is not None,
        "optimized_available": optimized is not None,
        "textually_identical": original == optimized if original is not None and optimized is not None else None,
        "line_similarity_ratio": round(similarity, 6) if similarity is not None else None,
        "original_lines": len(original.splitlines()) if original is not None else None,
        "optimized_lines": len(optimized.splitlines()) if optimized is not None else None,
        "original_sha256": sha256_bytes(original.encode()) if original else None,
        "optimized_sha256": sha256_bytes(optimized.encode()) if optimized else None,
        "ast_available": (case_dir / "ast.json").exists(),
        "optimized_ast_available": (case_dir / "ast_optimized.json").exists(),
        "command": cmd,
        "error": error,
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "equivalence": None,
    }
    if verify and status == "pair_ready":
        verify_case(case_dir, tools, verify_timeout, meta)
    write_text(meta_file, json.dumps(meta, indent=2, ensure_ascii=False) + "\n")
    if original is not None and optimized is not None:
        write_packet(case_dir, relative.name,
                     (case_dir / "spec.issy").read_text(encoding="utf-8", errors="replace"),
                     original, optimized, diff, meta)
    return meta, False


def safe_run_case(spec, *args):
    try:
        return run_case(spec, *args)
    except Exception:  # never lose the whole batch because of one case
        spec_dir = args[0]
        rel = spec.relative_to(spec_dir)
        return {"spec": str(rel), "status": "error", "verdict": "Unknown", "return_code": None,
                "timed_out": False, "elapsed_seconds": 0, "original_available": False,
                "optimized_available": False, "optimized_ast_available": False, "ast_available": False,
                "case_dir": "", "error": "runner failure: " + traceback.format_exc()[-600:],
                "equivalence": None}, False


# ----------------------------------------------------------------------------------------------
# indexes
# ----------------------------------------------------------------------------------------------
README_FOR_AI = """# How to read this folder

Every Issy specification that was run has a folder `cases/<name>/`. `manifest.csv` / `manifest.jsonl`
list all of them with a status:

- `pair_ready`: Issy found a program, the optimizer ran, `original.c` and `optimized.c` exist.
- `unrealizable`: Issy proved there is no program. Nothing to compare.
- `timeout`, `error`, `unknown_verdict`, `incomplete_pair`: no usable pair; `stderr.txt` says why.
- `optimizer_error`: Issy produced a program but `optimizer_simple_egglog.py` failed (Python traceback in
  `stderr.txt`). These cases are the most interesting for fixing the optimizer.

For a `pair_ready` case, `ai_review.md` has everything in one file: specification, original C,
optimized C, diff and the machine-checked results. `ast.json` / `ast_optimized.json` are the same two
programs before they are printed as C.

## Rules for the review

1. Judge equivalence of the two C programs: for every sequence of inputs both must give the same sequence
   of states at each `read_inputs()` and must end (or loop forever, or call `abort()`) in the same way.
2. A smaller or different text is not a difference. Removing code that can never run is the purpose of
   the optimizer.
3. If `equivalence` in the manifest is `proved`, Z3 has proven it for all input lengths; do not contradict
   it without a concrete input sequence. `bounded` and `unverified` are not proofs; say so.
4. Report a difference only with an input sequence (one value per `read_inputs()` call) and the state
   where the two programs first disagree.
5. Uninitialised local variables have no value in C; ignore differences that only appear in them.

## Suggested output per case

`name | equivalent / different / cannot tell | one-sentence reason | counterexample if different`
"""


def write_indexes(results, out_dir):
    results = sorted(results, key=lambda m: m["spec"])
    columns = [
        "spec", "status", "equivalence", "smt_verdict", "c_verdict", "verdict", "return_code", "timed_out",
        "elapsed_seconds", "original_lines", "optimized_lines", "textually_identical",
        "line_similarity_ratio", "original_available", "optimized_available", "ast_available",
        "optimized_ast_available", "case_dir",
    ]
    with (out_dir / "manifest.csv").open("w", encoding="utf-8", newline="") as fp:
        writer = csv.DictWriter(fp, fieldnames=columns, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(results)
    with (out_dir / "manifest.jsonl").open("w", encoding="utf-8") as fp:
        for meta in results:
            fp.write(json.dumps(meta, ensure_ascii=False) + "\n")
    counts = {name: sum(m["status"] == name for m in results) for name in STATUSES}
    eq = {}
    for m in results:
        if m.get("equivalence"):
            eq[m["equivalence"]] = eq.get(m["equivalence"], 0) + 1

    doc = ["# Issy batch summary", "", f"Benchmarks processed: {len(results)}", ""]
    doc.extend(f"- {status}: {n}" for status, n in counts.items())
    if eq:
        doc += ["", "Equivalence checks of the `pair_ready` cases:", ""]
        doc.extend(f"- {k}: {v}" for k, v in sorted(eq.items()))
    doc += ["", "`pair_ready` means both C files were extracted. Only `equivalence = proved` is a proof "
            "(Z3, all input lengths); without `--verify` nothing is claimed.", ""]
    pairs = [m for m in results if m["status"] == "pair_ready"]
    if pairs:
        doc += ["## Pairs", "", "| spec | orig. lines | opt. lines | equivalence | SMT | C run |",
                "|---|---:|---:|---|---|---|"]
        for m in pairs:
            doc.append(f"| {m['spec']} | {m.get('original_lines')} | {m.get('optimized_lines')} | "
                       f"{m.get('equivalence') or '-'} | {m.get('smt_verdict') or '-'} | "
                       f"{m.get('c_verdict') or '-'} |")
        doc.append("")
    others = [m for m in results if m["status"] not in ("pair_ready", "unrealizable")]
    if others:
        doc += ["## Cases without a pair", "", "| spec | status | reason |", "|---|---|---|"]
        for m in others:
            lines = [l.strip() for l in (m.get("error") or "").splitlines() if l.strip()]
            reason = (lines[-1] if lines else "").replace("|", "/")[:160]  # last line: the actual message
            doc.append(f"| {m['spec']} | {m['status']} | {reason} |")
        doc.append("")
    doc += ["Each `cases/<benchmark>/ai_review.md` packages the specification, original C, optimized C, "
            "diff and machine-checked results. `README_FOR_AI.md` explains the layout to a reviewer.", ""]
    write_text(out_dir / "SUMMARY.md", "\n".join(doc))
    return counts


def load_existing(out_dir):
    """Metadata of all cases already in the output folder, so that a run on a subset (--limit, --prefix)
    does not drop the other cases from the index."""
    found = {}
    for f in (out_dir / "cases").rglob("metadata.json"):
        try:
            m = json.loads(f.read_text(encoding="utf-8"))
            found[m["spec"]] = m
        except (OSError, ValueError, KeyError):
            pass
    return found


def git_commit(directory):
    try:
        r = subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"], capture_output=True, text=True,
                           timeout=10)
        return r.stdout.strip() if r.returncode == 0 else None
    except (OSError, subprocess.SubprocessError):
        return None


def python_can_import(module):
    r = subprocess.run([sys.executable, "-c", f"import {module}"], capture_output=True, text=True)
    return r.returncode == 0


def read_name_list(path):
    """Names from a list file: one per line, .issy optional, '#' starts a comment."""
    names = []
    for line in path.read_text(encoding="utf-8").splitlines():
        name = line.split("#", 1)[0].strip()
        if name:
            names.append(name if name.endswith(".issy") else name + ".issy")
    return names


def select_only(specs, list_file, parser):
    """Keep the specs named in list_file. A listed name that matches no spec (or several) is an error,
    because silently running fewer specs than listed would make the result look complete."""
    list_file = list_file.expanduser()
    if not list_file.is_file():
        parser.error(f"--only: {list_file} does not exist")
    wanted = read_name_list(list_file)
    if not wanted:
        parser.error(f"--only: {list_file} lists no specifications")
    by_name = {}
    for p in specs:
        by_name.setdefault(p.name, []).append(p)
    missing = [n for n in wanted if n not in by_name]
    ambiguous = [n for n in wanted if len(by_name.get(n, [])) > 1]
    if missing:
        parser.error(f"--only: {len(missing)} of {len(wanted)} listed specs are not in --spec-dir "
                     f"(or excluded by --prefix): {', '.join(missing[:8])}{' ...' if len(missing) > 8 else ''}")
    if ambiguous:
        parser.error(f"--only: name exists more than once under --spec-dir: {', '.join(ambiguous[:8])}")
    chosen = {by_name[n][0] for n in wanted}
    return [p for p in specs if p in chosen]


# ----------------------------------------------------------------------------------------------
def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--issy-dir", type=Path, default=HERE.parent,
                        help="Issy repository with the built ./issy and optimizer_simple_egglog.py "
                             "(default: the repository this script is in)")
    parser.add_argument("--spec-dir", type=Path, required=True, help="Folder containing .issy files (searched recursively)")
    parser.add_argument("--out-dir", type=Path, default=Path("issy-batch-results"), help="Folder for all outputs")
    parser.add_argument("--timeout", type=int, default=1200, help="Seconds per benchmark for Issy (default 1200 = 20 min)")
    parser.add_argument("--limit", type=int, help="Run only first N specs (smoke test)")
    parser.add_argument("--prefix", default="", help="Only files whose name starts with this, e.g., cav25-heim-")
    parser.add_argument("--only", type=Path, metavar="FILE",
                        help="Only the specs named in FILE: one name per line, with or without .issy; blank lines and "
                             "text after # are ignored. A name that is not in --spec-dir is an error "
                             "(tests/finished_specs.txt lists the specs that finished within 300 s)")
    parser.add_argument("--resume", action="store_true",
                        help="Skip pair_ready/unrealizable cases if the spec has not changed; retry failures. "
                             "With --verify the missing equivalence checks are added without re-running Issy.")
    parser.add_argument("--extra-options", default="", help="Additional Issy flags, quoted as one string, e.g., '--pruning 2'")
    parser.add_argument("--jobs", type=int, default=1, help="Specs to run in parallel (default 1)")
    parser.add_argument("--verify", action="store_true",
                        help="Also check equivalence: Z3 on ast.json/ast_optimized.json and an exhaustive run of the C files")
    parser.add_argument("--verify-timeout", type=int, default=180, help="Seconds for each of the two checks (default 180)")
    parser.add_argument("--tools-dir", type=Path, default=HERE,
                        help="Folder with equiv_check.py and c_exhaustive.py (default: next to this script)")
    args = parser.parse_args()

    issy_dir = args.issy_dir.expanduser().resolve()
    spec_dir = args.spec_dir.expanduser().resolve()
    out_dir = args.out_dir.expanduser().resolve()
    tools = args.tools_dir.expanduser().resolve()
    binary = issy_dir / "issy"
    if not binary.is_file():
        parser.error(f"Issy executable not found at {binary}. Run 'make' in the Issy repository first.")
    if not (issy_dir / OPTIMIZER).is_file():
        parser.error(f"{OPTIMIZER} not found in {issy_dir} (Issy needs it for the optimized program).")
    if not spec_dir.is_dir():
        parser.error(f"Specification directory does not exist: {spec_dir}")
    if args.timeout < 1 or args.jobs < 1 or args.verify_timeout < 1 or (args.limit is not None and args.limit < 1):
        parser.error("--timeout, --jobs, --verify-timeout and --limit must be positive")
    if not python_can_import("egglog"):
        parser.error("python3 cannot import 'egglog' (Issy runs the optimizer with it): pip3 install egglog")
    if args.verify:
        for f in ("equiv_check.py", "c_exhaustive.py"):
            if not (tools / f).is_file():
                parser.error(f"{f} not found in {tools} (needed for --verify)")
        if not python_can_import("z3"):
            parser.error("python3 cannot import 'z3' (needed for --verify): pip3 install z3-solver")
    # Smoke test: a binary that cannot start (wrong CPU, missing library, macOS code signature) would
    # otherwise fail the same way on every one of the specifications.
    rc, out, err, timed_out, error = run_group([str(binary), "--help"], issy_dir, 60)
    if error or timed_out or rc is None or rc < 0:
        why = error or ("did not answer within 60 s" if timed_out else describe_exit(rc))
        hint = ""
        if platform.system() == "Darwin":
            hint = (f"\nOn macOS this usually means the binary was copied from another Mac or downloaded, and the "
                    f"system refuses to start it. Build it on this Mac (`make` in {issy_dir}), or try\n"
                    f"  xattr -cr {binary} && codesign --force --sign - {binary}\n"
                    f"and check that `{binary} --help` prints a help text.")
        parser.error(f"`{binary} --help` {why}.{hint}")
    specs = sorted(p for p in spec_dir.rglob("*.issy") if p.is_file() and p.name.startswith(args.prefix))
    if args.only:
        specs = select_only(specs, args.only, parser)
    if args.limit:
        specs = specs[:args.limit]
    if not specs:
        parser.error("No matching .issy files found")
    try:
        extra = shlex.split(args.extra_options)
    except ValueError as e:
        parser.error(str(e))
    out_dir.mkdir(parents=True, exist_ok=True)
    write_text(out_dir / "README_FOR_AI.md", README_FOR_AI)
    shutil.copy2(issy_dir / OPTIMIZER, out_dir / OPTIMIZER)  # the optimizer these results were made with
    write_text(out_dir / "run_info.json", json.dumps({
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "machine": platform.platform(),
        "python": sys.version.split()[0],
        "issy_dir": str(issy_dir),
        "issy_git_commit": git_commit(issy_dir),
        "issy_binary_sha256": sha256_file(binary),
        "optimizer_sha256": sha256_file(issy_dir / OPTIMIZER),
        "spec_dir": str(spec_dir),
        "spec_count": len(specs),
        "issy_timeout_seconds": args.timeout,
        "extra_options": extra,
        "jobs": args.jobs,
        "verify": args.verify,
    }, indent=2) + "\n")
    print(f"Issy: {binary}\nSpecs: {len(specs)} from {spec_dir}\nOutput: {out_dir}\n"
          f"Parallel jobs: {args.jobs}{'  verify: on' if args.verify else ''}\n", flush=True)

    records = load_existing(out_dir)  # spec -> metadata
    counts = {}
    worker_args = (spec_dir, out_dir, issy_dir, extra, args.timeout, args.resume, args.verify,
                   args.verify_timeout, tools)
    ex = cf.ThreadPoolExecutor(max_workers=args.jobs)
    try:
        futures = {ex.submit(safe_run_case, spec, *worker_args): spec for spec in specs}
        for done, fut in enumerate(cf.as_completed(futures), start=1):
            meta, skipped = fut.result()
            records[meta["spec"]] = meta
            counts = write_indexes(list(records.values()), out_dir)  # Index stays valid if interrupted.
            eq = f", {meta['equivalence']}" if meta.get("equivalence") else ""
            print(f"[{done}/{len(specs)}] {futures[fut].name}: {'RESUMED ' if skipped else ''}"
                  f"{meta['status']}{eq} ({meta['elapsed_seconds']}s)", flush=True)
    except KeyboardInterrupt:
        kill_all()
        ex.shutdown(wait=False, cancel_futures=True)
        write_indexes(list(records.values()), out_dir)
        print("\nInterrupted. Finished cases are kept; run again with --resume.", flush=True)
        return 130
    ex.shutdown(wait=True)
    print("\nAll cases in the output folder:", counts, "\nIndexes: manifest.csv, manifest.jsonl, SUMMARY.md", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
