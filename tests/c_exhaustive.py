#!/usr/bin/env python3
"""Exhaustive comparison of two compiled C programs (Issy's original and the optimized one).

The SMT checker (tests/equiv_check.py) proves equivalence on the AST. This script is the independent check on
the C code that is really compiled: it replaces read_inputs() by a driver that tries EVERY sequence of input
values up to a depth K, with the integer inputs taken from a small domain, and compares, for every sequence,
what the environment can see:

    * the values of all input and state variables at every read_inputs() call, and
    * how the run ends: main() returns, abort() is called, K reads are done, or the program loops without
      reading (more than 200000 loop iterations in one run).

A sequence is not extended once the program has stopped, and a run that stops after n < K reads stands for all
sequences that start with the same n values, so the enumeration is a complete tree, not a sample. Per run a
hash of the observations is computed; the two programs must produce the same number of runs and the same
combined hash (on a difference both programs are run again in lockstep and the first differing input sequence
is printed). Every program is run three times, with the stack filled with 0x00, 0x5a and 0xff before each run,
so a program that read an uninitialised local variable would behave differently from run to run.

What this covers, precisely: ALL input sequences of length <= K over the given domain (not all integers, not
longer runs; the SMT checker covers those). The C is compiled with -O0 -fwrapv, so int overflow wraps, which is
what the SMT checker (mathematical integers) does not model; with the default domain (small numbers) no program
here overflows.

Usage:
    python3 tests/c_exhaustive.py ORIGINAL.c OPTIMIZED.c            # two programs as Issy prints them
    python3 tests/c_exhaustive.py --ast PROGRAM.json ...            # optimize each AST with the repository's
                                                                    # optimizer, print both as C (a copy of the
                                                                    # printer in Synthesis.hs) and compare
    python3 tests/c_exhaustive.py --negative PROGRAM.json ...       # the comparison must also FAIL for damaged
                                                                    # copies of the optimized program
    options: --depth K  --domain -2,-1,0,1,2  --max-runs N
e2e.py --exhaustive runs the same comparison on the C programs that ./issy prints.
"""
import argparse
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import e2e                                      # split_c, LOOP, find_cc (same directory)

SALTS = (0x00, 0x5A, 0xFF)
TICKS = 200000                                  # loop iterations in one run before it counts as "loops forever"
CTYPE = {"SInt": "int", "SBool": "bool", "SReal": "double"}


# ----------------------------------------------------------------------------------------------
# the driver
# ----------------------------------------------------------------------------------------------
def plan(inputs, domain=None, depth=None, max_runs=300_000):
    """-> (domain, depth). The domain is shrunk when there are many inputs, the depth is the largest for which
    the number of sequences stays below max_runs."""
    if any(t == "double" for t, _ in inputs):
        raise ValueError("real-valued inputs cannot be enumerated")
    ints, bools = sum(t == "int" for t, _ in inputs), sum(t == "bool" for t, _ in inputs)
    if domain is None:
        for dom in ([-2, -1, 0, 1, 2], [-1, 0, 1], [0, 1]):
            if len(dom) ** ints * 2 ** bools <= 300:
                break
        domain = dom
    m = len(domain) ** ints * 2 ** bools
    if depth is None:
        depth = 300 if m == 1 else max(3, min(20, int(math.log(max_runs) / math.log(m))))
    return list(domain), depth


def driver(text, domain, depth):
    """C source of the driver around Issy's program `text`."""
    inputs, states, _, body = e2e.split_c(text)
    allv = inputs + states
    if any(t == "double" for t, _ in allv):
        raise ValueError("real-valued variables are not supported")
    body = [e2e.LOOP.sub(lambda m: m.group(1) + "for (;; ex_tick())", l) if e2e.LOOP.match(l) else l for l in body]
    nd = len(domain)
    m = nd ** sum(t == "int" for t, _ in inputs) * 2 ** sum(t == "bool" for t, _ in inputs)
    out = ["#include <stdlib.h>", "#include <stdio.h>", "#include <string.h>", "#include <setjmp.h>",
           "#include <stdbool.h>", "#undef abort"]
    out += [f"{t} {n};" for t, n in allv]
    out += [
        f"static const long long ex_dom[{nd}] = {{{', '.join(str(d) for d in domain)}}};",
        "static jmp_buf ex_jb;",
        "static int ex_end, ex_depth, ex_nreads;",
        f"static int ex_digit[{depth + 2}];",
        "static unsigned long long ex_h;",
        "static unsigned long ex_ticks;",
        "static void ex_mix(unsigned long long v) { ex_h ^= v; ex_h *= 1099511628211ULL; }",
        "static void ex_abort(void) { ex_end = 1; longjmp(ex_jb, 1); }",
        "#define abort() ex_abort()",
        f"static void ex_tick(void) {{ if (++ex_ticks > {TICKS}UL) {{ ex_end = 3; longjmp(ex_jb, 1); }} }}",
        "void read_inputs(void) {",
    ]
    out += [f"  ex_mix((unsigned long long)(long long){n});" for _, n in allv]
    out += ["  ex_mix(0x9e3779b97f4a7c15ULL);",
            "  if (ex_nreads >= ex_depth) { ex_end = 2; longjmp(ex_jb, 1); }",
            "  { int d = ex_digit[ex_nreads++]; (void)d;"]
    for t, n in inputs:
        if t == "int":
            out.append(f"    {n} = (int)ex_dom[d % {nd}]; d /= {nd};")
        else:
            out.append(f"    {n} = d % 2; d /= 2;")
    out += ["  }", "}",
            "static void ex_main(void) {"] + body + [
            "static void ex_scribble(int salt) { volatile char buf[2048]; int i; for (i = 0; i < 2048; i++) buf[i] = (char)salt; }",
            "static void ex_reset(void) {"]
    out += [f"  {n} = 0;" for _, n in allv]
    out += ["}",
            "int main(int argc, char **argv) {",
            "  int verbose = argc > 2 ? atoi(argv[2]) : 0, salt = argc > 3 ? atoi(argv[3]) : 0, i;",
            "  unsigned long long agg = 14695981039346656037ULL, runs = 0, ends[4] = {0, 0, 0, 0};",
            "  ex_depth = argc > 1 ? atoi(argv[1]) : 8;",
            "  memset(ex_digit, 0, sizeof ex_digit);",
            "  for (;;) {",
            "    ex_reset(); ex_h = 14695981039346656037ULL; ex_nreads = 0; ex_end = 0; ex_ticks = 0;",
            "    ex_scribble(salt);",
            "    if (setjmp(ex_jb) == 0) { ex_main(); ex_end = 0; }",
            "    ex_mix((unsigned long long)ex_end); ex_mix((unsigned long long)ex_nreads);",
            "    agg = (agg ^ ex_h) * 1099511628211ULL; ends[ex_end]++; runs++;",
            "    if (verbose) {",
            "      for (i = 0; i < ex_nreads; i++) printf(\"%d \", ex_digit[i]);",
            "      printf(\"-> end=%d reads=%d h=%016llx\\n\", ex_end, ex_nreads, ex_h);",
            "    }",
            "    i = ex_nreads - 1;",
            f"    while (i >= 0) {{ if (++ex_digit[i] < {m}) break; ex_digit[i] = 0; i--; }}",
            "    if (i < 0) break;",
            "    for (i = i + 1; i <= ex_depth; i++) ex_digit[i] = 0;",
            "  }",
            "  printf(\"runs=%llu returned=%llu aborted=%llu depth=%llu looped=%llu hash=%016llx\\n\",",
            "         runs, ends[0], ends[1], ends[2], ends[3], agg);",
            "  return 0;",
            "}"]
    return "\n".join(out) + "\n"


def build(cc, work, name, text, domain, depth):
    src, exe = os.path.join(work, name + "_ex.c"), os.path.join(work, name + "_ex")
    open(src, "w").write(driver(text, domain, depth))
    r = subprocess.run([cc, "-O0", "-w", "-std=gnu11", "-fwrapv", src, "-o", exe], capture_output=True, text=True)
    return exe, r


def run(exe, depth, verbose=0, salt=0, timeout=600):
    r = subprocess.run([exe, str(depth), str(verbose), str(salt)], capture_output=True, text=True, timeout=timeout)
    return r.stdout.strip()


def first_difference(exe_a, exe_b, depth, salt, domain, inputs):
    """Run both drivers in lockstep with one line per run; -> description of the first differing run."""
    pa = subprocess.Popen([exe_a, str(depth), "1", str(salt)], stdout=subprocess.PIPE, text=True)
    pb = subprocess.Popen([exe_b, str(depth), "1", str(salt)], stdout=subprocess.PIPE, text=True)
    try:
        for la, lb in zip(pa.stdout, pb.stdout):
            if la != lb:
                def decode(line):
                    left = line.split("->")[0].split()
                    seq = []
                    for d in map(int, left):
                        vec = {}
                        for t, n in inputs:
                            if t == "int":
                                vec[n] = domain[d % len(domain)]
                                d //= len(domain)
                            else:
                                vec[n] = bool(d % 2)
                                d //= 2
                        seq.append(vec)
                    return seq
                return (f"input sequence {decode(la)}: original {la.split('->')[1].strip()}; optimized "
                        f"{lb.split('->')[1].strip()}" if la.split('->')[0] == lb.split('->')[0] else
                        f"the programs read a different number of times: original {la.strip()} / optimized {lb.strip()}")
        return "the programs differ only in the number of runs"
    finally:
        pa.kill(); pb.kill()


def compare(original, optimized, work, cc, domain=None, depth=None, max_runs=300_000, salts=SALTS):
    """Compare two programs as Issy prints them. -> (ok, detail)"""
    inputs, states = e2e.split_c(original)[:2]
    domain, depth = plan(inputs, domain, depth, max_runs)
    exes = {}
    for tag, text in (("original", original), ("optimized", optimized)):
        if e2e.split_c(text)[:2] != (inputs, states):
            return False, "the two programs declare different input/state variables"
        exe, r = build(cc, work, tag, text, domain, depth)
        if r.returncode:
            return False, f"{tag} driver does not compile: {r.stderr.strip()[-300:]}"
        exes[tag] = exe
    results = {}
    for salt in salts:
        a, b = run(exes["original"], depth, 0, salt), run(exes["optimized"], depth, 0, salt)
        results[salt] = (a, b)
        if a != b:
            return False, (f"stack filled with {salt:#04x}: original [{a}] optimized [{b}]; "
                           + first_difference(exes["original"], exes["optimized"], depth, salt, domain, inputs))
    a0 = results[salts[0]][0]
    for salt in salts[1:]:
        if results[salt][0] != a0:
            return False, f"the original program behaves differently with the stack filled with {salt:#04x} (reads an uninitialised local)"
    runs = re.search(r"runs=(\d+) returned=(\d+) aborted=(\d+) depth=(\d+) looped=(\d+)", a0)
    n, ret, ab, dp, lp = map(int, runs.groups())
    kind = (("integer inputs from " + str(domain)) if any(t == "int" for t, _ in inputs) else
            "boolean inputs, both values") if inputs else "no inputs"
    return True, (f"{n} input sequences ({kind}, up to {depth} reads, complete tree): identical observations; "
                  f"runs end: {dp} at the depth bound, {ab} in abort(), {ret} by returning, {lp} looping forever; "
                  f"stack fill {', '.join(f'{s:#04x}' for s in salts)}")


# ----------------------------------------------------------------------------------------------
# a copy of the C printer of Synthesis.hs (printCProg), to get C from an AST without running Issy
# ----------------------------------------------------------------------------------------------
_OPS = {"FAdd": "+", "FMul": "*", "FEq": "==", "FLt": "<", "FLte": "<=", "FAnd": "&&", "FOr": "||"}


def _term(t):
    tg = t["tag"]
    if tg == "Var":
        return t["contents"][0]
    if tg == "Const":
        c = t["contents"]
        if c["tag"] == "CBool":
            return "true" if c["contents"] else "false"
        if c["tag"] == "CInt":
            return str(c["contents"])
        raise ValueError("real constants are not supported")
    f, args = t["contents"]
    op = f["tag"]
    if op == "FNot":
        return "(!(" + _term(args[0]) + "))"
    if op == "FIte":
        return "(" + _term(args[0]) + " ? " + _term(args[1]) + " : " + _term(args[2]) + ")"
    return "(" + _term(args[0]) + " " + "".join(_OPS[op] + " " + _term(y) for y in args[1:]) + ")"


def _symbols(t, out):
    if t["tag"] == "Var":
        out.add(t["contents"][0])
    elif t["tag"] == "Func":
        for x in t["contents"][1]:
            _symbols(x, out)
    return out


def _stmt(p):
    t, c = p["tag"], p.get("contents")
    ind = lambda ls: ["  " + l for l in ls]
    if t == "Declare":
        return [f"{CTYPE[c[1]['tag']]} {c[0]};"]
    if t == "InfLoop":
        return ["for(;;)"] + ind(_stmt(c))
    if t == "Cond":
        return ["if (" + _term(c[0]) + ")"] + ind(_stmt(c[1]))
    if t == "Sequence":
        return ["{"] + ind([l for q in c for l in _stmt(q)]) + ["}"]
    if t == "PAssign":
        if not c:
            return [";"]
        if len(c) == 1:
            return [f"{c[0][0]} = {_term(c[0][2])};"]
        syms = set()
        for v, _, e in c:
            syms |= _symbols(e, {v})
        pre = "temp_copy_"
        while any(s.startswith(pre) for s in syms):
            pre = "_" + pre
        return (["{"] + [f"{CTYPE[s['tag']]} {pre}{v} = {_term(e)};" for v, s, e in c]
                + [f"{v} = {pre}{v};" for v, _, _ in c] + ["}"])
    return {"Break": ["break;"], "Continue": ["continue;"], "Abort": ["abort();"], "Read": ["read_inputs();"]}[t]


def ast_to_c(ast, info):
    decl = lambda v: f"{CTYPE[info.sorts[v]]} {v};"
    lines = ["#include <stdlib.h>"] + [decl(v) for v in info.inputs] + ["void read_inputs() { /* INSERT HERE */ }"]
    lines += [decl(v) for v in info.state if v not in info.declared]
    lines += ["void main() {"] + ["  " + l for l in _stmt(ast)] + ["}"]
    return "\n".join(lines) + "\n"


def pair_from_ast(ast, optimized):
    sys.path.insert(0, HERE)
    import equiv_check as E
    info = E.Info(ast, optimized)
    info.declared = E.scan(ast)[0] | E.scan(optimized)[0]
    return ast_to_c(ast, info), ast_to_c(optimized, info)


# ----------------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+")
    ap.add_argument("--ast", action="store_true", help="the files are ASTs (ast.json format)")
    ap.add_argument("--negative", action="store_true", help="ASTs; also compare damaged copies of the optimized program")
    ap.add_argument("--depth", type=int)
    ap.add_argument("--domain", help="comma separated integer values, e.g. -2,-1,0,1,2")
    ap.add_argument("--max-runs", type=int, default=300_000)
    ap.add_argument("--mutants", type=int, default=12)
    args = ap.parse_args()
    domain = [int(x) for x in args.domain.split(",")] if args.domain else None
    cc = e2e.find_cc()
    if not cc:
        sys.exit("error: no C compiler found")
    work = tempfile.mkdtemp(prefix="c-exhaustive-")
    failures = 0
    try:
        if not (args.ast or args.negative):
            ok, detail = compare(open(args.files[0]).read(), open(args.files[1]).read(), work, cc, domain, args.depth,
                                 args.max_runs)
            print(("OK   " if ok else "FAIL ") + detail)
            return 0 if ok else 1
        import equiv_check as E
        for path in args.files:
            name = os.path.basename(path).replace(".json", "").replace(".ast", "")
            ast = E.load(path)
            opt = E.optimize(ast)
            o_c, p_c = pair_from_ast(ast, opt)
            ok, detail = compare(o_c, p_c, work, cc, domain, args.depth, args.max_runs)
            print(f"{'OK  ' if ok else 'FAIL'} {name:22s} optimizer     {detail}", flush=True)
            failures += not ok
            if args.negative:
                killed = alive = 0
                for seed in range(args.mutants):
                    m, what = E.mutate(opt, seed)
                    if m == opt:
                        continue
                    try:
                        o_c, m_c = pair_from_ast(ast, m)
                        ok3, _ = compare(o_c, m_c, work, cc, domain, args.depth, args.max_runs)
                    except (ValueError, KeyError):
                        continue
                    killed += not ok3
                    alive += ok3
                print(f"     {name:22s} damaged copies of the optimized program: {killed} found, {alive} not different "
                      f"in this domain/depth", flush=True)
        return 1 if failures else 0
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
