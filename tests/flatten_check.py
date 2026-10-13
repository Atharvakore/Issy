#!/usr/bin/env python3
"""Does the optimizer still work when flattener.py runs after it?

Issy's Synthesis.hs (optimizeProgWithEgglog) runs   ast.json -> optimizer_simple_egglog.py -> ast_optimized.json
-> flattener.py -> ast_switch_atomic.json   and reads the last file back. This script runs the same two
Python steps on programs and compares the behaviour of the programs with tests/ast_interp.py (no C compiler,
no Issy build needed).

    python3 tests/flatten_check.py                 # the 10 real programs in tests/fixtures (printed by Issy)
    python3 tests/flatten_check.py fuzz [N] [FIRST]   # N random programs that look like Issy's output
    python3 tests/flatten_check.py fuzz --resets   # ... including fall-through "if pc == a: pc = b" blocks
    python3 tests/flatten_check.py --flattener DIR # use DIR/flattener.py (e.g. an older copy) instead

For every program P four versions are compared with P:
    optimizer       optimizer(P)
    flattener       flattener(P)                (the flattener alone)
    both            flattener(optimizer(P))     (what Issy uses)
Exit status 1 if "optimizer" or "both" differ from P (or, for the real programs, "flattener" differs).
"""
import argparse, json, os, random, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import ast_interp as I


def optimize(ast):
    d = tempfile.mkdtemp(prefix="flat-opt-")
    try:
        json.dump(ast, open(os.path.join(d, "ast.json"), "w"))
        r = subprocess.run([sys.executable, os.path.join(ROOT, "optimizer_simple_egglog.py")], cwd=d,
                           capture_output=True, text=True)
        if r.returncode:
            raise RuntimeError("optimizer: " + r.stderr.strip()[-300:])
        return json.load(open(os.path.join(d, "ast_optimized.json")))
    finally:
        shutil.rmtree(d, ignore_errors=True)


def flatten(ast, flattener_dir):
    d = tempfile.mkdtemp(prefix="flat-flat-")
    try:
        json.dump(ast, open(os.path.join(d, "in.json"), "w"))
        code = (f"import sys; sys.path.insert(0, {flattener_dir!r}); import flattener; "
                "flattener.transform_file('in.json', 'out.json')")
        r = subprocess.run([sys.executable, "-c", code], cwd=d, capture_output=True, text=True)
        if r.returncode:
            raise RuntimeError("flattener: " + r.stderr.strip()[-300:])
        return json.load(open(os.path.join(d, "out.json")))
    finally:
        shutil.rmtree(d, ignore_errors=True)


def count(ast, t):
    n = 0
    stack = [ast]
    while stack:
        x = stack.pop()
        if isinstance(x, list):
            stack.extend(x)
        elif isinstance(x, dict):
            n += x.get("tag") == t
            stack.extend(x.values())
    return n


def check(p, flattener_dir, max_reads=120):
    """-> dict(optimizer=diff|None, flattener=..., both=..., switches=int)"""
    new = optimize(p)
    fp = flatten(p, flattener_dir)
    fn = flatten(new, flattener_dir)
    return dict(optimizer=I.compare(p, new, max_reads), flattener=I.compare(p, fp, max_reads),
                both=I.compare(p, fn, max_reads), switches=count(fn, "Switch"), switches_raw=count(fp, "Switch"))


# ---------------------------------------------------------------------------------------------
# random programs shaped like Issy's output
# ---------------------------------------------------------------------------------------------
INT, BOOL = {"tag": "SInt"}, {"tag": "SBool"}
def V(n, s=INT): return {"tag": "Var", "contents": [n, s]}
def C(k): return {"tag": "Const", "contents": {"tag": "CInt", "contents": k}}
def B(k): return {"tag": "Const", "contents": {"tag": "CBool", "contents": k}}
def F(op, *a): return {"tag": "Func", "contents": [{"tag": op}, list(a)]}
def seq(*s): return {"tag": "Sequence", "contents": list(s)}
def cond(g, b): return {"tag": "Cond", "contents": [g, b]}
def pa(*items): return {"tag": "PAssign", "contents": [[v, s, t] for v, s, t in items]}
def loop(b): return {"tag": "InfLoop", "contents": b}
def decl(n, s=INT): return {"tag": "Declare", "contents": [n, s]}
READ, BRK, CONT, ABORT = {"tag": "Read"}, {"tag": "Break"}, {"tag": "Continue"}, {"tag": "Abort"}


class Gen:
    """A dispatch loop on prog_counter (values 0..3) with nested loops, parallel assignments with ite, reads and
    the abort() sentinel, like the programs Issy prints. State: x, y (int), c (bool); input: i."""

    def __init__(self, seed, resets=False):
        self.r = random.Random(seed)
        self.resets = resets

    def ti(self, d=2):
        r = self.r
        if d == 0 or r.random() < .3:
            return r.choice([V("x"), V("y"), V("i"), C(r.randint(-2, 3))])
        k = r.random()
        if k < .3: return F("FAdd", self.ti(d - 1), self.ti(d - 1))
        if k < .5: return F("FMul", C(r.choice([-1, 2])), self.ti(d - 1))
        return F("FIte", self.tb(d - 1), self.ti(d - 1), self.ti(d - 1))

    def tb(self, d=2):
        r = self.r
        if d == 0 or r.random() < .3:
            return r.choice([V("c", BOOL), F("FLt", self.ti(0), self.ti(0)), F("FEq", self.ti(0), self.ti(0))])
        k = r.random()
        if k < .3: return F("FAnd", self.tb(d - 1), self.tb(d - 1))
        if k < .5: return F("FOr", self.tb(d - 1), self.tb(d - 1))
        if k < .7: return F("FNot", self.tb(d - 1))
        return F("FLte", self.ti(d - 1), self.ti(d - 1))

    def pc_is(self, k): return F("FEq", V("prog_counter"), C(k))

    def guard(self, k):
        r = self.r
        g = self.pc_is(k)
        if r.random() < .3: g = F("FOr", g, self.pc_is((k + 1) % 4))
        if r.random() < .5: g = F("FAnd", g, self.tb(1))
        return g

    def update(self, nxt):
        r = self.r
        pc = C(nxt) if r.random() < .5 else F("FIte", self.tb(1), C(nxt), C(r.randint(0, 3)))
        items = [("prog_counter", INT, pc)]
        if r.random() < .8: items.append(("x", INT, self.ti()))
        if r.random() < .4: items.append(("y", INT, self.ti()))
        if r.random() < .3: items.append(("c", BOOL, self.tb(1)))
        r.shuffle(items)
        return pa(*items)

    def leaf(self, inner):
        r = self.r
        stmts = [READ] if r.random() < .8 else []
        stmts.append(self.update(r.randint(0, 3)))
        stmts.append(BRK if (inner and r.random() < .15) else CONT)
        return seq(*stmts)

    def body(self, depth):
        r = self.r
        blocks = []
        if self.resets and r.random() < .3:           # as Issy prints at the head of an inner loop
            blocks.append(cond(self.pc_is(r.randint(0, 3)), pa(("prog_counter", INT, C(r.randint(0, 3))))))
        if depth > 0 or r.random() < .7:
            blocks.insert(0, cond(self.pc_is(r.randint(0, 3)),
                                  BRK if depth > 0 else seq(READ, self.update(r.randint(0, 3)), CONT)))
        for _ in range(r.randint(2, 4)):
            k = r.randint(0, 3)
            if depth < 2 and r.random() < .3:
                inner = [decl("init_x")] if r.random() < .5 else []
                inner += [pa(("init_x", INT, V("x")))] if inner and r.random() < .7 else []
                inner += [loop(self.body(depth + 1)), CONT]
                blocks.append(cond(self.guard(k), seq(*inner)))
            else:
                leaf = self.leaf(depth > 0)
                if r.random() < .25:
                    leaf = seq(cond(self.tb(1), seq(READ, self.update(r.randint(0, 3)), CONT)), leaf)
                blocks.append(cond(self.guard(k), leaf))
        for k in range(4):                            # every pc value has an unconditional block
            blocks.append(cond(self.pc_is(k), self.leaf(depth > 0)))
        return seq(*blocks, ABORT)

    def program(self):
        return seq(decl("prog_counter"), pa(("prog_counter", INT, C(0))), pa(("x", INT, C(self.r.randint(0, 3)))),
                   pa(("y", INT, C(0))), pa(("c", BOOL, B(False))), loop(self.body(0)))


# ---------------------------------------------------------------------------------------------
def real(flattener_dir):
    d = os.path.join(HERE, "fixtures")
    names = sorted(f[:-len(".ast.json")] for f in os.listdir(d) if f.endswith(".ast.json"))
    bad = 0
    print(f"{'program':20s} {'optimizer':10s} {'flattener':10s} {'both':10s} switches (flattener alone / after optimizer)")
    for n in names:
        res = check(json.load(open(os.path.join(d, n + ".ast.json"))), flattener_dir)
        show = lambda k: "same" if res[k] is None else "DIFFERENT"
        print(f"{n:20s} {show('optimizer'):10s} {show('flattener'):10s} {show('both'):10s} "
              f"{res['switches_raw']} / {res['switches']}")
        for k in ("optimizer", "flattener", "both"):
            if res[k]:
                print(f"    {k}: {res[k]}")
                bad += 1
    print(f"\n{len(names)} programs, {bad} differences")
    return bad == 0


def fuzz(n, first, resets, flattener_dir):
    st = dict(programs=0, with_reads=0, optimizer=0, flattener=0, both=0, interplay=0, with_switch=0)
    shown = 0
    t0 = time.time()
    for seed in range(first, first + n):
        p = Gen(seed, resets).program()
        if len(I.run(p, "rand", 0, 40)[0]) < 3:
            continue                                  # the original hardly reads: nothing to compare
        st["programs"] += 1
        res = check(p, flattener_dir, 40)
        st["optimizer"] += res["optimizer"] is not None
        st["flattener"] += res["flattener"] is not None
        st["both"] += res["both"] is not None
        st["interplay"] += res["flattener"] is None and res["both"] is not None
        st["with_switch"] += res["switches"] > 0
        if (res["optimizer"] or res["both"]) and shown < 5:
            shown += 1
            print(f"  seed {seed}: optimizer: {res['optimizer']}; both: {res['both']}")
    print(f"{st['programs']} programs that read at least 3 times (seeds {first}..{first + n - 1}, "
          f"{'with' if resets else 'without'} fall-through resets), {st['with_switch']} still have a Switch after the optimizer")
    print(f"  optimizer differs:               {st['optimizer']}")
    print(f"  flattener alone differs:         {st['flattener']}")
    print(f"  optimizer+flattener differs:     {st['both']}")
    print(f"  ... of these only after the optimizer (flattener alone was fine): {st['interplay']}")
    print(f"  ({round(time.time() - t0)} s)")
    return st["optimizer"] == 0 and st["interplay"] == 0 and st["both"] == 0 and st["flattener"] == 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", default="real", choices=["real", "fuzz"])
    ap.add_argument("n", nargs="?", type=int, default=60)
    ap.add_argument("first", nargs="?", type=int, default=0)
    ap.add_argument("--resets", action="store_true")
    ap.add_argument("--flattener", default=ROOT, help="directory with flattener.py (default: the repository)")
    a = ap.parse_args()
    ok = real(a.flattener) if a.mode == "real" else fuzz(a.n, a.first, a.resets, os.path.abspath(a.flattener))
    print("OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
