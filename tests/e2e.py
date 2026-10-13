#!/usr/bin/env python3
"""
End-to-end tests for Issy's program synthesis, including the Python AST optimizer.

For every specification it does what a user does:

    make                                   # build (skip with --no-build)
    ./issy --solve --synt <spec>           # prints the ORIGINAL C program, then "Realizable" and the
                                           # OPTIMIZED C program (after optimizer_simple_egglog.py)

and then checks the two C programs against each other in several scenarios:

  1. issy exits with 0 and says what the test expects (Realizable / Unrealizable);
  2. the Python optimizer really ran (ast_optimized.json was rewritten by this run);
  3. both C programs compile;
  4. EQUIVALENCE. Both programs are run in every scenario of the spec. A scenario is an input profile
     (what read_inputs() delivers) and, for the random profiles, a seed:

         zero    every int 0, every bool false          one     every int 1, every bool true
         min     every int -3, every bool false         max     every int 3, every bool true
         alt     values alternate between -3 and 3 (bool: 0/1) from read to read
         rand    uniformly random in -3..3 (bool: coin flip), one run per seed
         sticky  random, but a value is held for ~8 reads on average, one run per seed
                 (reaches long phases of the program that rapidly changing inputs never reach)

     (min/max are dropped for specs whose inputs are all bool; a spec without inputs has one scenario).
     Per scenario the values of ALL input and state variables at every read_inputs() call and the way
     the run ends (exit status, e.g. abort) must be identical in the two programs;
  5. DEAD CODE. Both programs are instrumented with a counter per statement (assignment, if, for(;;),
     break, continue, read_inputs, abort). A statement that was never executed in any scenario is
     reported as dead. `abort();` statements are counted separately: Issy puts them where control
     "should never be reached", so they are sentinels, not removable code. For specs marked
     dead_code_removed the optimized program must have strictly fewer never-executed statements than
     the original (only meaningful for specs without inputs, where every run executes the same code).
  6. --self-test: the optimized program is damaged on purpose (one executed assignment or guard at a
     time) and the equivalence check must notice; this shows that the check in 4. is able to fail.
  7. --exhaustive: instead of sampled scenarios, EVERY input sequence up to a depth K (integers from a small
     domain, booleans both ways) is run on both C programs and all observations are compared
     (tests/c_exhaustive.py; read its header for what this does and does not cover).
  8. --prove: the two ASTs that Issy wrote (ast.json, ast_optimized.json) are compared with the SMT solver Z3
     for ALL input sequences of ANY length (tests/equiv_check.py, needs `pip install z3-solver`).

Usage (from the repository root or anywhere):

    python3 tests/e2e.py                          # all specs in SPECS
    python3 tests/e2e.py --no-build               # reuse the existing ./issy
    python3 tests/e2e.py tests/specs/swap.issy    # only this spec (relative to --root)
    python3 tests/e2e.py --self-test --show-dead  # also run 6. and list the dead statements
    python3 tests/e2e.py --keep tests/out         # keep C files, traces, coverage and both ASTs
    python3 tests/e2e.py --exhaustive --prove     # also 7. and 8.

Needs: make + stack (to build), python3 with the `egglog` package (pip install egglog), a C compiler
(gcc or clang). Coverage is measured by the instrumentation added here, no gcov is needed.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))

# (spec path relative to the repo root, expected result, options)
#   expected: "realizable" | "unrealizable" | "auto" (accept either; program is checked if realizable)
#   dead_code_removed: assert the optimized program has fewer never-executed statements than the original
#                      (only for specs without inputs; for the other specs the numbers are just reported)
SPECS = [
    ("bounded-loop.issy", "realizable", {"dead_code_removed": True}),
    ("tests/specs/count-up.issy", "realizable", {"dead_code_removed": True}),
    ("tests/specs/two-phase.issy", "realizable", {}),  # Issy's own program aborts after 4 reads, see below
    ("tests/specs/walk-to-diagonal.issy", "realizable", {"dead_code_removed": True}),
    ("tests/specs/swap.issy", "realizable", {"dead_code_removed": True}),
    ("tests/specs/saturating-input.issy", "realizable", {}),
    ("tests/specs/trailing-value.issy", "realizable", {}),
    ("tests/specs/bool-handshake.issy", "realizable", {}),
    ("tests/specs/buechi-cycle.issy", "realizable", {"dead_code_removed": True}),
    ("test.issy", "auto", {}),
]
# docs/sample.issy is not in the list: Issy needs more than 15 minutes for it. It can still be passed
# on the command line: python3 tests/e2e.py --timeout 3600 docs/sample.issy

MARKER = "===== ORIGINAL C PROGRAM ====="
DECL = re.compile(r"^\s*(int|double|bool)\s+([A-Za-z_]\w*)\s*;\s*$")
DECL_INIT = re.compile(r"^(\s*)(int|double|bool)\s+([A-Za-z_]\w*)\s*=\s*(.*);\s*$")
ASSIGN = re.compile(r"^(\s*)([A-Za-z_]\w*)\s*=\s*(.*);\s*$")
IF = re.compile(r"^(\s*)if\s*(\(.*\))\s*$")
LOOP = re.compile(r"^(\s*)for\s*\(\s*;\s*;\s*\)\s*$")

PROFILES = ["zero", "one", "min", "max", "alt", "rand", "sticky"]  # index = value of e2e_profile in C


# ----------------------------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------------------------
def sh(cmd, cwd=None, timeout=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)


def find_cc():
    for cc in [os.environ.get("CC"), "gcc", "cc", "clang"]:
        if cc and shutil.which(cc):
            return cc
    return None


class Report:
    def __init__(self):
        self.rows = []

    def add(self, spec, name, ok, detail=""):
        self.rows.append((spec, name, ok, detail))
        print(f"  [{'PASS' if ok is True else 'INFO' if ok is None else 'FAIL'}] {name}"
              + (f": {detail}" if detail else ""))
        sys.stdout.flush()

    @property
    def failures(self):
        return [r for r in self.rows if r[2] is False]


# ----------------------------------------------------------------------------------------------
# parsing Issy's output and the generated C
# ----------------------------------------------------------------------------------------------
def parse_issy_output(out):
    """Return (result, original_c, optimized_c). result is 'realizable'/'unrealizable'/None."""
    lines = out.splitlines()
    res_idx = next((i for i, l in enumerate(lines) if l.strip() in ("Realizable", "Unrealizable")), None)
    if res_idx is None:
        return None, None, None
    result = lines[res_idx].strip().lower()
    mark = next((i for i, l in enumerate(lines) if l.strip() == MARKER), None)
    if mark is None or mark > res_idx:
        return result, None, None
    original = "\n".join(lines[mark + 1:res_idx]).strip("\n") + "\n"
    optimized = "\n".join(lines[res_idx + 1:]).strip("\n") + "\n"
    return result, original, optimized


def split_c(text):
    """Split Issy's C output into (inputs, states, first_body_line_index, body_lines).
    Declarations are (type, name)."""
    lines = text.splitlines()
    try:
        ri = next(i for i, l in enumerate(lines) if "void read_inputs()" in l)
        mi = next(i for i, l in enumerate(lines) if re.match(r"\s*void main\(\)\s*\{", l))
    except StopIteration:
        raise ValueError("C output has no 'void read_inputs()' / 'void main()'")
    inputs = [m.groups() for m in map(DECL.match, lines[:ri]) if m]
    states = [m.groups() for m in map(DECL.match, lines[ri + 1:mi]) if m]
    return inputs, states, mi + 1, lines[mi + 1:]


def count_lines(text):
    return len([l for l in text.splitlines() if l.strip()])


# ----------------------------------------------------------------------------------------------
# instrumentation: input profiles and one coverage counter per statement
# ----------------------------------------------------------------------------------------------
def instrument_body(body, first_line):
    """Add a counter to every statement of main(). Returns (new_lines, stmts, unknown) where stmts is a
    list of dicts(kind, text, line) indexed by counter number and `unknown` the lines not recognised.

    The printer of Issy (Synthesis.hs, printStmt) only produces: `for(;;)`, `if (<term>)`, `{`, `}`,
    `x = <term>;`, `break;`, `continue;`, `abort();`, `read_inputs();`, `;`, declarations, and for
    parallel assignments a block `{ T c_x = <term>; ... x = c_x; ... }`. A parallel assignment counts as
    one statement (counted at its first temporary copy)."""
    out, stmts, unknown = [], [], []
    in_parallel = False
    for off, line in enumerate(body):
        s = line.strip()
        lineno = first_line + off

        def new(kind):
            stmts.append({"kind": kind, "text": s, "line": lineno})
            return len(stmts) - 1

        if s in ("", ";", "{") or DECL.match(line):
            out.append(line)
        elif s == "}":
            in_parallel = False
            out.append(line)
        elif LOOP.match(line):
            out.append(f"{LOOP.match(line).group(1)}for (e2e_cov[{new('loop')}]++;;)")
        elif IF.match(line):
            m = IF.match(line)
            out.append(f"{m.group(1)}if ((e2e_cov[{new('if')}]++), {m.group(2)})")
        elif s in ("break;", "continue;"):
            out.append(f"{line[:len(line) - len(line.lstrip())]}{{ e2e_cov[{new('jump')}]++; {s} }}")
        elif s == "read_inputs();":
            out.append(f"{line[:len(line) - len(line.lstrip())]}{{ e2e_cov[{new('read')}]++; read_inputs(); }}")
        elif s == "abort();":
            n = new("abort")
            out.append(f"{line[:len(line) - len(line.lstrip())]}{{ e2e_cov[{n}]++; e2e_cov_dump(); abort(); }}")
        elif DECL_INIT.match(line):
            m = DECL_INIT.match(line)
            if in_parallel:
                out.append(line)
            else:
                in_parallel = True
                out.append(f"{m.group(1)}{m.group(2)} {m.group(3)} = (e2e_cov[{new('assign')}]++, {m.group(4)});")
        elif ASSIGN.match(line):
            m = ASSIGN.match(line)
            if in_parallel:
                out.append(line)  # the copy-back of a parallel assignment, already counted
            else:
                out.append(f"{m.group(1)}{m.group(2)} = {m.group(3)}, e2e_cov[{new('assign')}]++;")
        else:
            unknown.append(s)
            out.append(line)
    return out, stmts, unknown


def instrument(text, max_reads):
    """Return (c_source, stmts, unknown). The source reads its input profile and seed from argv[1] and
    argv[2], prints a trace line per read_inputs() call and writes the counters to the file argv[3]."""
    inputs, states, first, body = split_c(text)
    allv = inputs + states
    body, stmts, unknown = instrument_body(body, first)
    fmt = {"int": '"%lld"', "bool": '"%d"', "double": '"%.17g"'}
    cast = {"int": "(long long)", "bool": "(int)", "double": ""}
    draw = {"int": "(int)e2e_draw", "bool": "e2e_drawb", "double": "(double)e2e_draw"}
    out = ["#include <stdlib.h>", "#include <stdio.h>", "#include <stdint.h>", "#include <stdbool.h>"]
    out += [f"{t} {n};" for t, n in allv]
    out += [
        "static uint64_t e2e_rs = 88172645463325252ULL;",
        "static uint64_t e2e_next(void) { e2e_rs ^= e2e_rs << 13; e2e_rs ^= e2e_rs >> 7; e2e_rs ^= e2e_rs << 17; return e2e_rs; }",
        "static int e2e_profile = 5;",
        "static long e2e_nreads = 0;",
        f"static unsigned long e2e_cov[{max(len(stmts), 1)}];",
        "static const char *e2e_covpath = 0;",
        "static void e2e_cov_dump(void) {",
        "  FILE *f; unsigned long k;",
        "  if (!e2e_covpath || !(f = fopen(e2e_covpath, \"w\"))) return;",
        f"  for (k = 0; k < {len(stmts)}; k++) fprintf(f, \"%lu \", e2e_cov[k]);",
        "  fprintf(f, \"\\n\"); fclose(f);",
        "}",
        f"static long long e2e_held[{len(inputs) + 1}];",
        "static long long e2e_draw(int idx) {",
        "  switch (e2e_profile) {",
        "    case 0: return 0;",
        "    case 1: return 1;",
        "    case 2: return -3;",
        "    case 3: return 3;",
        "    case 4: return ((e2e_nreads + idx) & 1) ? 3 : -3;",
        "    case 5: return (long long)(e2e_next() % 7) - 3;",
        "    default:",
        "      if (e2e_nreads == 1 || (e2e_next() & 7) == 0) e2e_held[idx] = (long long)(e2e_next() % 7) - 3;",
        "      return e2e_held[idx];",
        "  }",
        "}",
        "static int e2e_drawb(int idx) {",
        "  switch (e2e_profile) {",
        "    case 0: case 2: return 0;",
        "    case 1: case 3: return 1;",
        "    case 4: return (int)((e2e_nreads + idx) & 1);",
        "    case 5: return (int)((e2e_next() >> 5) & 1);",
        "    default:",
        "      if (e2e_nreads == 1 || (e2e_next() & 7) == 0) e2e_held[idx] = (long long)((e2e_next() >> 5) & 1);",
        "      return (int)e2e_held[idx];",
        "  }",
        "}",
        "void read_inputs(void) {",
        '  printf("%ld", e2e_nreads);',
    ]
    out += [f'  printf(" " {fmt[t]}, {cast[t]}{n});' for t, n in allv]
    out += ['  printf("\\n"); fflush(stdout);',
            f"  if (++e2e_nreads > {max_reads}) exit(0);"]
    out += [f"  {n} = {draw[t]}({k});" for k, (t, n) in enumerate(inputs)]
    out += ["}",
            "int main(int argc, char **argv) {",
            "  e2e_profile = argc > 1 ? atoi(argv[1]) : 5;",
            "  e2e_rs ^= (uint64_t)(argc > 2 ? atoll(argv[2]) : 1) * 2654435761ULL;",
            "  e2e_covpath = argc > 3 ? argv[3] : 0;",
            "  atexit(e2e_cov_dump);"] + body
    return "\n".join(out) + "\n", stmts, unknown


def scenarios(inputs, seeds):
    """[(label, profile index, seed)] for a program with these inputs."""
    if not inputs:
        return [("deterministic", 5, 1)]
    names = [p for p in PROFILES if not (p in ("min", "max") and all(t == "bool" for t, _ in inputs))]
    out = []
    for name in names:
        if name in ("rand", "sticky"):
            out += [(f"{name}#{s}", PROFILES.index(name), s) for s in range(1, seeds + 1)]
        else:
            out.append((name, PROFILES.index(name), 1))
    return out


# ----------------------------------------------------------------------------------------------
# compiling and running
# ----------------------------------------------------------------------------------------------
def build_program(cc, work, name, text, max_reads):
    src = os.path.join(work, f"{name}.c")
    code, stmts, unknown = instrument(text, max_reads)
    open(src, "w").write(code)
    exe = os.path.join(work, name)
    r = sh([cc, "-O0", "-w", "-std=gnu11", src, "-o", exe], cwd=work)
    return exe, stmts, unknown, r


def run_program(exe, profile, seed, covfile, timeout=30):
    if os.path.exists(covfile):
        os.remove(covfile)
    try:
        r = subprocess.run([exe, str(profile), str(seed), covfile], capture_output=True, text=True, timeout=timeout)
        code, out = r.returncode, r.stdout
    except subprocess.TimeoutExpired as e:
        code, out = "timeout", (e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or ""))
    counts = []
    if os.path.exists(covfile):
        counts = [int(x) for x in open(covfile).read().split()]
    return code, out, counts


def compare_scenarios(progs, scens, work, tag_a="original", tag_b="optimized", save=False):
    """Run both programs in every scenario. Returns (mismatch or None, reads per run, covered ids per program)."""
    covered = {tag_a: set(), tag_b: set()}
    reads, aborted = [], 0
    for label, profile, seed in scens:
        res = {}
        for tag in (tag_a, tag_b):
            res[tag] = run_program(progs[tag][0], profile, seed, os.path.join(work, f"{tag}.cov"))
            for i, c in enumerate(res[tag][2]):
                if c:
                    covered[tag].add(i)
            if save:
                open(os.path.join(work, f"{tag}_{label.replace('#', '')}.trace"), "w").write(
                    f"exit={res[tag][0]}\n{res[tag][1]}")
        a, b = res[tag_a][:2], res[tag_b][:2]
        reads.append(a[1].count("\n"))
        aborted += a[0] not in (0,)
        if a != b or "timeout" in (a[0], b[0]):
            la, lb = a[1].splitlines(), b[1].splitlines()
            k = next((i for i in range(min(len(la), len(lb))) if la[i] != lb[i]), min(len(la), len(lb)))
            why = ("a run timed out (infinite loop without read_inputs?)" if "timeout" in (a[0], b[0]) else
                   f"{tag_a} ends {a[0]} after {len(la)} reads, {tag_b} ends {b[0]} after {len(lb)} reads; "
                   f"first difference at read {k}: {tag_a}={la[k] if k < len(la) else '-'!r} "
                   f"{tag_b}={lb[k] if k < len(lb) else '-'!r}")
            return f"scenario {label}: {why}", reads, covered, aborted
    return None, reads, covered, aborted


def dead_summary(stmts, covered):
    real = [(i, s) for i, s in enumerate(stmts) if s["kind"] != "abort"]
    sentinels = [(i, s) for i, s in enumerate(stmts) if s["kind"] == "abort"]
    dead = [(i, s) for i, s in real if i not in covered]
    return dict(total=len(real), dead=dead, sentinels=len(sentinels),
                sentinels_hit=sum(1 for i, _ in sentinels if i in covered))


# ----------------------------------------------------------------------------------------------
# --self-test: damage the optimized program and require that the equivalence check notices
# ----------------------------------------------------------------------------------------------
def make_mutants(optimized, stmts, covered, limit):
    """Mutated copies of the optimized C text: one executed assignment or guard changed at a time."""
    inputs, states, first, body = split_c(optimized)
    types = {n: t for t, n in inputs + states}
    for l in body:  # locals such as `int init_x;`
        m = DECL.match(l)
        if m:
            types[m.group(2)] = m.group(1)
    lines = optimized.splitlines()
    cands = []
    for i, s in enumerate(stmts):
        if i not in covered:
            continue
        line = lines[s["line"]]
        if s["kind"] == "if" and IF.match(line):
            m = IF.match(line)
            cands.append((s["line"], f"{m.group(1)}if (!{m.group(2)})"))
        elif s["kind"] == "assign":
            m = DECL_INIT.match(line)
            if m:
                typ, ind, lhs, rhs = m.group(2), m.group(1), m.group(3), m.group(4)
                new = f"{ind}{typ} {lhs} = {'!' if typ == 'bool' else ''}({rhs}){'' if typ == 'bool' else ' + 1'};"
                cands.append((s["line"], new))
                continue
            m = ASSIGN.match(line)
            if m and m.group(2) in types:
                ind, lhs, rhs = m.group(1), m.group(2), m.group(3)
                new = f"{ind}{lhs} = {'!' if types[lhs] == 'bool' else ''}({rhs}){'' if types[lhs] == 'bool' else ' + 1'};"
                cands.append((s["line"], new))
    if len(cands) > limit:
        step = len(cands) / limit
        cands = [cands[int(k * step)] for k in range(limit)]
    out = []
    for ln, new in cands:
        mutated = list(lines)
        mutated[ln] = new
        out.append((ln, new.strip(), "\n".join(mutated) + "\n"))
    return out


# ----------------------------------------------------------------------------------------------
# one spec
# ----------------------------------------------------------------------------------------------
def prove_spec(rep, spec, root):
    """SMT proof on the ASTs of this run: optimized program == original program for all input sequences."""
    try:
        import equiv_check
    except (SystemExit, ImportError) as e:
        return rep.add(spec, "SMT proof of equivalence", None, f"skipped: {e}")
    try:
        a = equiv_check.load(os.path.join(root, "ast.json"))
        b = equiv_check.load(os.path.join(root, "ast_optimized.json"))
        t = time.time()
        res = equiv_check.verify(a, b)
    except (OSError, ValueError, KeyError) as e:
        return rep.add(spec, "SMT proof of equivalence", None, f"skipped: {e}")
    ok = True if res.ok else (False if res.status == "DIFFERENT" else None)
    rep.add(spec, "SMT proof: optimized == original for all input sequences", ok, f"{res} [{time.time() - t:.1f} s]")
    if res.status == "DIFFERENT":
        equiv_check.show(spec, res, 0)


def test_spec(args, rep, cc, spec, expected, opts):
    print(f"\n== {spec}")
    root = args.root
    spec_path = os.path.join(root, spec)
    if not os.path.exists(spec_path):
        return rep.add(spec, "spec file exists", False, spec_path)

    ast_opt = os.path.join(root, "ast_optimized.json")
    start = time.time() - 1
    try:
        r = sh([args.issy, "--solve", "--synt", spec], cwd=root, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        return rep.add(spec, "issy finishes", False, f"timeout after {args.timeout}s")
    except OSError as e:
        return rep.add(spec, "issy can be started", False, str(e))
    if r.returncode != 0:
        return rep.add(spec, "issy exits with 0", False, (r.stderr or r.stdout).strip()[-400:])
    result, original, optimized = parse_issy_output(r.stdout)
    if result is None:
        return rep.add(spec, "issy prints Realizable/Unrealizable", False, r.stdout.strip()[-200:])
    ok = expected == "auto" or result == expected
    rep.add(spec, f"result is {expected if expected != 'auto' else 'any'}", ok, result)
    if not ok or result != "realizable":
        return
    if original is None or optimized is None:
        return rep.add(spec, "issy prints original and optimized C program", False,
                       "missing marker or program after 'Realizable'")
    fresh = os.path.exists(ast_opt) and os.path.getmtime(ast_opt) >= start
    rep.add(spec, "optimizer ran (ast_optimized.json rewritten)", fresh,
            "" if fresh else "file missing or older than this run")

    name = os.path.splitext(os.path.basename(spec))[0]
    work = os.path.join(args.keep, name) if args.keep else tempfile.mkdtemp(prefix="issy-e2e-")
    os.makedirs(work, exist_ok=True)
    try:
        for tag, text in (("original", original), ("optimized", optimized)):
            open(os.path.join(work, f"{tag}_issy_output.c"), "w").write(text)
        if args.keep:
            for f in ("ast.json", "ast_optimized.json"):
                if os.path.exists(os.path.join(root, f)):
                    shutil.copy(os.path.join(root, f), os.path.join(work, f))
        progs = {}
        for tag, text in (("original", original), ("optimized", optimized)):
            try:
                exe, stmts, unknown, cr = build_program(cc, work, tag, text, args.reads)
            except ValueError as e:
                return rep.add(spec, f"{tag} C program has the expected shape", False, str(e))
            if cr.returncode != 0:
                hint = ("\n    hint: the text 'Wrote optimized AST' in the C code means the optimizer printed to stdout"
                        if "Wrote optimized AST" in text else "")
                return rep.add(spec, f"{tag} C program compiles", False, cr.stderr.strip()[-400:] + hint)
            progs[tag] = (exe, stmts)
            if unknown:
                rep.add(spec, f"{tag}: every line of main() understood by the instrumentation", False,
                        f"unrecognised: {unknown[:3]}")
        rep.add(spec, "both C programs compile", True,
                f"{count_lines(original)} lines original, {count_lines(optimized)} lines optimized")

        inputs = split_c(original)[0]
        scens = scenarios(inputs, args.seeds)
        bad, reads, covered, aborted = compare_scenarios(progs, scens, work, save=bool(args.keep))
        if bad:
            rep.add(spec, "optimized behaves like original", False, bad)
        else:
            rep.add(spec, "optimized behaves like original", True,
                    f"{len(scens)} scenarios ({', '.join(l for l, _, _ in scens)}); reads per run "
                    f"{min(reads)}..{max(reads)}" + (f"; {aborted} runs end in abort (same in both)" if aborted else ""))

        if args.exhaustive and not bad:
            import c_exhaustive
            try:
                ok, detail = c_exhaustive.compare(original, optimized, work, cc)
            except ValueError as e:
                ok, detail = None, str(e)
            rep.add(spec, "exhaustive: every input sequence up to the depth bound gives the same observations", ok, detail)
        if args.prove:
            prove_spec(rep, spec, root)

        so = dead_summary(progs["original"][1], covered["original"])
        sp = dead_summary(progs["optimized"][1], covered["optimized"])
        detail = (f"never executed: original {len(so['dead'])} of {so['total']}, "
                  f"optimized {len(sp['dead'])} of {sp['total']}; abort sentinels: {so['sentinels']} -> {sp['sentinels']}"
                  f"{' (some reached!)' if so['sentinels_hit'] or sp['sentinels_hit'] else ''}")
        if so["sentinels_hit"] and not inputs:
            rep.add(spec, "Issy's own program reaches abort()", None,
                    f"the original program (before the optimizer) already ends in abort() after {min(reads)} reads "
                    f"although the spec has no inputs; the optimized program does the same, so only these reads "
                    f"were compared and the dead-statement numbers below are not representative")
        if bad:
            rep.add(spec, "dead statements", None, "not compared: behaviour check failed")
        elif opts.get("dead_code_removed"):
            rep.add(spec, "dead code removed", len(sp["dead"]) < len(so["dead"]), detail)
        else:
            rep.add(spec, "dead statements", None, detail)
        if args.show_dead and not bad:
            for tag, sm in (("original", so), ("optimized", sp)):
                for _, s in sm["dead"]:
                    print(f"      dead in {tag}: {s['text']}")
        if args.keep:
            with open(os.path.join(work, "dead_statements.txt"), "w") as f:
                for tag, sm in (("original", so), ("optimized", sp)):
                    f.write(f"== {tag}: {len(sm['dead'])} of {sm['total']} never executed\n")
                    f.writelines(f"{s['line'] + 1}: {s['text']}\n" for _, s in sm["dead"])

        if args.self_test and not bad:
            killed = survived = 0
            mutants = make_mutants(optimized, progs["optimized"][1], covered["optimized"], args.mutants)
            for k, (ln, text, mtext) in enumerate(mutants):
                try:
                    exe, st, _, cr = build_program(cc, work, "mutant", mtext, args.reads)
                except ValueError:
                    continue
                if cr.returncode != 0:
                    continue
                diff, *_ = compare_scenarios({"original": progs["original"], "mutant": (exe, st)}, scens, work,
                                             tag_b="mutant")
                killed += diff is not None
                survived += diff is None
            if mutants:
                rep.add(spec, "self-test: the equivalence check notices damaged programs", killed > 0,
                        f"{killed} of {killed + survived} damaged copies of the optimized program were detected "
                        f"(the rest changed something that no later read_inputs() shows)")
            else:
                rep.add(spec, "self-test: the equivalence check notices damaged programs", None,
                        "no executed assignment or guard to damage")
    finally:
        if not args.keep:
            shutil.rmtree(work, ignore_errors=True)


# ----------------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("specs", nargs="*", help="spec files (relative to --root); default: the built-in list")
    ap.add_argument("--root", default=os.path.dirname(HERE), help="repository root (default: parent of tests/)")
    ap.add_argument("--issy", default=None, help="issy executable (default: <root>/issy)")
    ap.add_argument("--no-build", action="store_true", help="do not run make")
    ap.add_argument("--seeds", type=int, default=3, help="seeds for the rand and sticky profiles (default 3)")
    ap.add_argument("--reads", type=int, default=300, help="read_inputs() calls per run (default 300)")
    ap.add_argument("--timeout", type=int, default=900, help="seconds allowed for one issy run")
    ap.add_argument("--keep", default=None, help="directory to keep C files, traces, coverage and both ASTs")
    ap.add_argument("--show-dead", action="store_true", help="list the statements that were never executed")
    ap.add_argument("--self-test", action="store_true", help="also check that damaged programs are detected")
    ap.add_argument("--mutants", type=int, default=8, help="damaged copies per spec for --self-test (default 8)")
    ap.add_argument("--exhaustive", action="store_true", help="also run every input sequence up to a depth (c_exhaustive.py)")
    ap.add_argument("--prove", action="store_true", help="also prove equivalence of the two ASTs with Z3 (equiv_check.py)")
    args = ap.parse_args()
    args.root = os.path.abspath(args.root)
    args.issy = os.path.abspath(args.issy) if args.issy else os.path.join(args.root, "issy")
    if args.keep:
        args.keep = os.path.abspath(args.keep)

    cc = find_cc()
    if not cc:
        sys.exit("error: no C compiler found (install gcc or clang, or set CC)")
    if sh(["python3", "-c", "import egglog"]).returncode != 0:
        sys.exit("error: python3 cannot import 'egglog' (Issy runs optimizer_simple_egglog.py with it): "
                 "pip install egglog")
    print(f"root: {args.root}\nissy: {args.issy}\nC compiler: {cc}")

    if not args.no_build:
        print("\n== make")
        r = sh(["make"], cwd=args.root)
        if r.returncode != 0:
            print((r.stdout + r.stderr)[-1500:])
            sys.exit("FAIL: make failed")
        print("  build ok")
    if not os.access(args.issy, os.X_OK):
        sys.exit(f"error: {args.issy} not found or not executable (run make, or pass --issy)")

    known = {os.path.normpath(p): (e, o) for p, e, o in SPECS}
    chosen = [(s, *known.get(os.path.normpath(s), ("auto", {}))) for s in args.specs] if args.specs else SPECS
    rep = Report()
    for spec, expected, opts in chosen:
        test_spec(args, rep, cc, spec, expected, opts)

    total, bad = len(rep.rows), len(rep.failures)
    print(f"\n{total - bad} of {total} checks passed" + ("" if not bad else f", {bad} FAILED"))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
