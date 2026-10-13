#!/usr/bin/env python3
"""
Soundness check of the dead-code elimination in optimizer_simple_egglog.py (no Issy needed).

  python3 tests/dce_fuzz.py real      [N]   N random programs: the program after eliminate_dead_code must do
                                            exactly what the original does (same values of all state and input
                                            variables at every Read, same way to end: finished / abort / cut off),
                                            and a second application must change nothing
  python3 tests/dce_fuzz.py pipeline  [N]   the same for the whole optimizer (Egglog terms, FIte lowering,
                                            dead-code elimination), and for the legacy pipeline for comparison
  python3 tests/dce_fuzz.py mutants   [N [FIRST LAST]]
                                            builds deliberately WRONG variants of the pass (a rule changed so that
                                            it is no longer sound) and checks that this test notices each of them;
                                            variants that only make the pass less precise cannot be noticed and are
                                            listed as such

A program is a tree of the Prog constructors (Read, Cond, Sequence, InfLoop, Break, Continue, Abort, Declare,
PAssign) over three int and two bool state variables, one int and one bool input, and two local variables.
Behaviour is compared on three random initial states times three random input streams per program.
"""
import importlib.util, random, re, sys, os, time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
spec = importlib.util.spec_from_file_location("opt", os.path.join(REPO, "optimizer_simple_egglog.py"))
M = importlib.util.module_from_spec(spec); sys.modules["opt"] = M; spec.loader.exec_module(M)
SRC = open(os.path.join(REPO, "optimizer_simple_egglog.py")).read()
a = SRC.index("# ============================================================\n# 11c.")
b = SRC.index("# ============================================================\n# 12.")
SECTION = SRC[a:b]

def pass_from(section_src):
    ns = dict(M.__dict__)
    exec(compile(section_src, "section", "exec"), ns)
    return ns["eliminate_dead_code"]

INT, BOOL = M.SInt(), M.SBool()
IVARS, BVARS = ["x", "y", "z"], ["b", "c"]
IIN, BIN = "i", "j"
KEEPG = set(IVARS + BVARS + ["i", "j"])   # state and input variables; locals (Declare) are not observable
def V(n, s): return M.Var(n, s)
def iv(n): return V(n, INT)
def bv(n): return V(n, BOOL)
def ic(k): return M.int_const(k)
def bc(k): return M.bool_const(k)
F = M.make_func

# ---------------- interpreter ----------------
def ev(t, st):
    if isinstance(t, M.Var): return st[t.name]
    if isinstance(t, M.Const): return t.const.value
    n = t.function.name; a = [ev(x, st) for x in t.args]
    if n == "FAdd": return sum(a)
    if n == "FMul":
        r = 1
        for v in a: r *= v
        return r
    if n == "FEq": return a[0] == a[1]
    if n == "FLt": return a[0] < a[1]
    if n == "FLte": return a[0] <= a[1]
    if n == "FAnd": return all(a)
    if n == "FOr": return any(a)
    if n == "FNot": return not a[0]
    if n == "FIte": return a[1] if a[0] else a[2]
    raise ValueError(n)

def run(prog, init, seed, max_reads=18, max_iters=250, keep=KEEPG):
    st = dict(init); rng = random.Random(seed); decl_count = {}
    trace = []; iters = 0
    def snap_():
        return tuple(sorted((k, v) for k, v in st.items() if keep is None or k in keep))
    def ex(p):
        nonlocal iters
        if isinstance(p, M.Abort): return "abort"
        if isinstance(p, M.Break): return "break"
        if isinstance(p, M.Continue): return "continue"
        if isinstance(p, M.Read):
            trace.append(snap_())
            if len(trace) >= max_reads: return "cap"
            st[IIN] = rng.randint(-1, 3); st[BIN] = rng.random() < 0.5
            return None
        if isinstance(p, M.Declare):
            c = decl_count[p.symbol] = decl_count.get(p.symbol, 0) + 1
            dr = random.Random(f"{seed}/{p.symbol}/{c}")
            st[p.symbol] = dr.randint(0, 3) if isinstance(p.sort, M.SInt) else dr.random() < 0.5
            return None
        if isinstance(p, M.PAssign):
            vals = [(s, ev(t, st)) for s, _, t in p.assigns]
            for s, v in vals: st[s] = v
            return None
        if isinstance(p, M.Sequence):
            for q in p.programs:
                s = ex(q)
                if s is not None: return s
            return None
        if isinstance(p, M.Cond):
            return ex(p.body) if ev(p.condition, st) else None
        if isinstance(p, M.InfLoop):
            while True:
                iters += 1
                if iters > max_iters: return "iters"
                s = ex(p.body)
                if s == "break": return None
                if s in ("abort", "cap", "iters"): return s
    s = ex(prog)
    trace.append(snap_())
    return trace, s or "done"

# ---------------- generator ----------------
class Gen:
    def __init__(self, r, small=False):
        self.r = r
        self.lvs = ["l1", "l2"]
        self.ivs = ["x"] if small else IVARS
        self.bvs = ["b"] if small else BVARS
        self.pool = [self.atom() for _ in range(r.randint(2, 3) if small else r.randint(3, 7))]
        self.dn = 0
    def ivar(self): return iv(self.r.choice(self.ivs + self.lvs + [IIN]))
    def atom(self):
        r = self.r; k = r.random()
        if k < 0.35: return F("FEq", [self.ivar(), ic(r.randint(-1, 3))])
        if k < 0.5: return F(r.choice(["FLt", "FLte"]), [self.ivar(), ic(r.randint(-1, 3))])
        if k < 0.6: return F("FEq", [iv(r.choice(self.ivs)), iv(r.choice(self.ivs))])
        if k < 0.65: return F(r.choice(["FLt", "FLte"]), [ic(r.randint(-1, 3)), self.ivar()])
        return bv(r.choice(self.bvs + [BIN]))
    def guard(self, d=2):
        r = self.r; k = r.random()
        if d == 0 or k < 0.45:
            g = r.choice(self.pool) if r.random() < 0.7 else self.atom()
            return F("FNot", [g]) if r.random() < 0.25 else g
        if k < 0.65: return F("FAnd", [self.guard(d - 1) for _ in range(r.randint(2, 3))])
        if k < 0.8: return F("FOr", [self.guard(d - 1) for _ in range(r.randint(2, 3))])
        if k < 0.9: return F("FNot", [self.guard(d - 1)])
        return bc(r.random() < 0.5)
    def iterm(self, d=2):
        r = self.r; k = r.random()
        if d == 0 or k < 0.5:
            return ic(r.randint(-1, 3)) if r.random() < 0.55 else self.ivar()
        if k < 0.7: return F("FAdd", [self.iterm(d - 1), self.iterm(d - 1)])
        if k < 0.8: return F("FMul", [self.iterm(d - 1), ic(r.randint(-1, 2))])
        return F("FIte", [self.guard(1), self.iterm(d - 1), self.iterm(d - 1)])
    def bterm(self):
        r = self.r; k = r.random()
        if k < 0.4: return bc(r.random() < 0.5)
        if k < 0.6: return bv(r.choice(self.bvs + [BIN]))
        return self.guard(1)
    def assign(self):
        r = self.r; n = r.choice([1, 1, 1, 2, 3])
        pool = self.ivs + self.lvs + self.bvs
        names = r.sample(pool, min(n, len(pool)))
        out = []
        for nm in names:
            if nm in IVARS or nm in self.lvs: out.append((nm, INT, self.iterm()))
            else: out.append((nm, BOOL, self.bterm()))
        return M.PAssign(out)
    def prog(self, d, in_loop, allow_abort=True):
        r = self.r; k = r.random()
        if d <= 0 or k < 0.26: return self.assign()
        if k < 0.52:
            body = self.prog(d - 1, in_loop)
            if in_loop and r.random() < 0.35:
                body = M.Sequence([body, r.choice([M.Break(), M.Continue(), M.Continue()])])
            if r.random() < 0.10:
                body = M.Sequence([M.Read(), body])          # conditional Read
            return M.Cond(self.guard(), body)
        if k < 0.68:
            return M.Sequence([self.prog(d - 1, in_loop) for _ in range(r.randint(1, 4))])
        if k < 0.80 and d > 1:                                # nested loop (with a way out most of the time)
            inner = [M.Read()] if r.random() < 0.7 else []
            inner += [self.prog(d - 2, True) for _ in range(r.randint(1, 3))]
            if r.random() < 0.7:
                inner.append(M.Cond(self.guard(), M.Break()))
            return M.InfLoop(M.Sequence(inner))
        if k < 0.86 and in_loop: return r.choice([M.Break(), M.Continue()])
        if k < 0.88 and allow_abort: return M.Abort()
        if k < 0.93: return M.Read()
        if k < 0.97:
            nm = r.choice(self.lvs)
            return M.Sequence([M.Declare(nm, INT), M.PAssign([(nm, INT, ic(r.randint(0, 3)))]) if r.random() < 0.5 else M.Sequence([])])
        self.dn += 1
        return M.Sequence([M.Declare(f"t{self.dn}", INT), M.PAssign([("x", INT, iv(f"t{self.dn}"))])])
    def top(self):
        r = self.r
        body = [M.Read()] + [self.prog(3, True) for _ in range(r.randint(1, 4))]
        body.append(M.Cond(self.guard(), M.Break()) if r.random() < 0.5 else M.Continue()) if r.random() < 0.6 else None
        pre = [M.Declare("l1", INT), M.Declare("l2", INT)]
        pre += [M.PAssign([(v, INT, ic(r.randint(0, 2))) for v in self.ivs[:r.randint(1, 3)]])] if r.random() < 0.7 else []
        pre += [self.assign() for _ in range(r.randint(0, 2))]
        post = [self.prog(2, False) for _ in range(r.randint(0, 3))]
        return M.Sequence(pre + [M.InfLoop(M.Sequence(body))] + post)

def size(p):
    if isinstance(p, M.Sequence): return sum(size(q) for q in p.programs)
    if isinstance(p, (M.Cond, M.InfLoop)): return 1 + size(p.body)
    if isinstance(p, M.PAssign): return len(p.assigns)
    return 1

def init_states(r, n=3):
    out = []
    for _ in range(n):
        st = {v: r.randint(-1, 3) for v in IVARS}; st.update({v: r.random() < 0.5 for v in BVARS})
        st[IIN] = r.randint(-1, 3); st[BIN] = r.random() < 0.5
        out.append(st)
    return out

def check(prune, nprog, seed0=0, quiet=True):
    bad = []; shrunk = 0; total = 0; changed = 0; idem_bad = 0
    for n in range(nprog):
        r = random.Random(seed0 + n)
        p = Gen(r, small=(n % 2 == 1)).top()
        q = prune(p)
        total += size(p); shrunk += size(p) - size(q); changed += (q != p)
        if prune(q) != q: idem_bad += 1
        for init in init_states(r):
            for sd in range(3):
                try:
                    ro = run(p, init, sd)
                except Exception as e:
                    ro = ("EXC", repr(e))
                try:
                    rq = run(q, init, sd)
                except Exception as e:
                    rq = ("EXC", repr(e))
                if ro != rq:
                    bad.append((seed0 + n, init, sd)); break
            else: continue
            break
    return dict(programs=nprog, mismatches=len(bad), first=bad[:3], stmts=total, removed=shrunk, changed=changed, not_idempotent=idem_bad)

MUTANTS = [
 ("read-no-kill", "ctx.kill(inputs)\n        return prog", "pass\n        return prog"),
 ("passign-no-kill", "ctx.kill({symbol for symbol, _, _ in kept})", "pass"),
 ("assume-polarity", "_assume(cond, False, skipped)", "_assume(cond, True, skipped)"),
 ("cond-merge-ignores-body", "ctx.assign_from(_join(skipped, body_ctx))", "ctx.assign_from(skipped)"),
 ("join-set-intersect", "env[name] = values | b.env[name]", "env[name] = values & b.env[name]"),
 ("join-ignores-b-values", "env[name] = values | b.env[name]", "env[name] = values"),
 ("decide-any", "return outcomes.pop() if len(outcomes) == 1 else None", "return (True in outcomes) if outcomes else None"),
 ("decide-operands-swapped", "left, right = (x, y) if var_left else (y, x)", "left, right = (y, x) if var_left else (x, y)"),
 ("assume-false-keeps", "_narrow(ctx, var.name, drop={const})", "_narrow(ctx, var.name, keep={const})"),
 ("values-ite-left-only", "            return a | b\n    return None", "            return a\n    return None"),
 ("narrow-keep-union", "else values & frozenset(keep)", "else values | frozenset(keep)"),
 ("join-true-union", "[f for f in a.true if f in b.true]", "a.true + [f for f in b.true if f not in a.true]"),
 ("join-false-union", "[f for f in a.false if f in b.false]", "a.false + [f for f in b.false if f not in a.false]"),
 ("loop-ignores-backedges", "        for back in frame.back:\n            new_head = _join(new_head, back)\n", ""),
 ("loop-end-not-backedge", "frame.back.append(trial)  # falling off", "pass  # falling off"),
 ("continue-not-recorded", "ctx.loops[-1].back.append(ctx.copy())", "pass"),
 ("break-not-recorded", "ctx.loops[-1].exits.append(ctx.copy())", "pass"),
 ("after-loop-first-exit-only", "for e in frame.exits[1:]:\n                    after = _join(after, e)", "pass"),
 ("fixpoint-accepts-early", "if new_head.same_as(head):", "if True:"),
 ("fallback-no-kill", "_MAX_LOOP_ROUNDS = 8", "_MAX_LOOP_ROUNDS = 1"),   # combined with the next line below
 ("declare-no-kill", "ctx.kill({prog.symbol})", "pass"),
 ("diverges-cond", "return False  # a Cond may skip its body", "return isinstance(prog, Cond) and _diverges(prog.body)"),
 ("freebreak-ignores-cond", "    if isinstance(prog, Cond):\n        return _has_free_break(prog.body)", "    if isinstance(prog, Cond):\n        return False"),
 ("drop-any-const-assign", "or (isinstance(term, Const) and ctx.env.get(symbol) == frozenset([term])))", "or isinstance(term, Const))"),
 ("stored-values-from-wrong-state", "stored = {symbol: _values(term, ctx) for symbol, _, term in new}", "stored = {symbol: frozenset([term]) if isinstance(term, Const) else None for symbol, _, term in new}"),
 ("assume-or-true", 'if name == "FOr" and not truth:', 'if name == "FOr" and truth:'),
 ("assume-and-false", 'if name == "FAnd" and truth:', 'if name == "FAnd":'),
 ("junction-neutral", "if is_cbool(a, neutral):\n            continue", "if is_cbool(a, absorbing):\n            continue"),
 ("fold-lt", "nums[0] < nums[1] if name == \"FLt\" else nums[0] <= nums[1]", "nums[0] <= nums[1] if name == \"FLt\" else nums[0] < nums[1]"),
 ("facts-never-killed", "        self.true = [f for f in self.true if not (_free_vars(f) & names)]\n        self.false = [f for f in self.false if not (_free_vars(f) & names)]", "        pass"),
 ("break-not-divergent", "if isinstance(prog, (Break, Continue, Abort)):\n        return True", "if isinstance(prog, (Continue, Abort)):\n        return True"),
 ("loop-diverges-always", "return not _has_free_break(prog.body)", "return True"),
 ("known-result-wrong", "return result if k is None else bool_const(k)", "return result if k is None else bool_const(not k)"),
 ("known-swapped", "    if term in ctx.true:\n        return True\n    if term in ctx.false:\n        return False\n    return None", "    if term in ctx.true:\n        return False\n    if term in ctx.false:\n        return True\n    return None"),
 ("contradiction-wrong", "if any(_negation(a) in out for a in out):\n        return bool_const(absorbing)", "if any(_negation(a) in out for a in out):\n        return bool_const(neutral)"),
 ("ite-swapped", "if is_cbool(args[0], True):\n            return args[1]", "if is_cbool(args[0], True):\n            return args[2]"),
 ("locals-ignore-guards", "    _guard_reads(prog, needed)\n", "    pass\n"),
 ("locals-no-chain", "    changed = True\n    while changed:", "    changed = False\n    while changed:"),
 ("locals-treat-globals-as-local", "    local = _declared(prog)\n    if not local:", "    local = _declared(prog) | {\"x\", \"y\", \"z\", \"b\", \"c\"}\n    if not local:"),
 ("locals-ignore-rhs-of-globals", "        if target not in local:\n            needed |= reads", "        if False:\n            needed |= reads"),
]
# "fallback-no-kill" is meaningful only together with this second edit (the fallback forgets nothing)
EXTRA = {"fallback-no-kill": ("    ctx.kill(changed)\n    return InfLoop(body)", "    return InfLoop(body)")}

PRECISION_ONLY = {"break-not-divergent", "stored-values-from-wrong-state", "narrow-keep-union"}


def pipeline(n, seed0=0):
    res = {}
    for which, fn in (("new", M.optimize_ast_with_egglog), ("legacy", M.optimize_ast_with_egglog_legacy)):
        bad = []; sz0 = sz1 = 0
        count = n if which == "new" else max(50, n // 4)
        for k in range(count):
            r = random.Random(seed0 + k)
            p = Gen(r, small=(k % 2 == 1)).top()
            q = fn(p)
            sz0 += size(p); sz1 += size(q)
            if any(run(p, init, sd, keep=KEEPG) != run(q, init, sd, keep=KEEPG)
                   for init in init_states(r, 2) for sd in range(2)):
                bad.append(seed0 + k)
        res[which] = (count, len(bad), bad[:5], sz0, sz1)
        print(f"pipeline {which:6}: {count} programs, {len(bad)} behave differently {bad[:5]}, size {sz0} -> {sz1}", flush=True)
    return res["new"][1] == 0


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "real"
    n = int(sys.argv[2]) if len(sys.argv) > 2 else {"real": 3000, "pipeline": 300, "mutants": 3000}.get(mode, 3000)
    t = time.time()
    ok = True
    if mode == "real":
        r = check(M.eliminate_dead_code, n)
        print(f"{r['programs']} programs: {r['mismatches']} behave differently {r['first']}, not idempotent: "
              f"{r['not_idempotent']}, statements {r['stmts']} -> {r['stmts'] - r['removed']} ({time.time() - t:.0f}s)")
        ok = r["mismatches"] == 0 and r["not_idempotent"] == 0
    elif mode == "pipeline":
        ok = pipeline(n)
    elif mode == "mutants":
        missed = []
        lo, hi = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, len(MUTANTS))
        for name, old, new in MUTANTS[lo:hi]:
            assert SECTION.count(old) == 1, (name, SECTION.count(old))
            src = SECTION.replace(old, new)
            if name in EXTRA:
                assert src.count(EXTRA[name][0]) == 1, name
                src = src.replace(*EXTRA[name])
            variant = pass_from(src)
            base, found = max(300, n // 3), False
            for factor in ((1,) if name in PRECISION_ONLY else (1, 3, 9)):  # rare cases need more programs
                found = check(variant, base * factor, seed0=1_000_000 * factor)["mismatches"] > 0
                if found:
                    break
            kind = "caught" if found else ("not noticed (only less precise)" if name in PRECISION_ONLY else "NOT NOTICED")
            print(f"{kind:34} {name}" + (f"  (needed {base * factor} programs)" if found and factor > 1 else ""), flush=True)
            if not found and name not in PRECISION_ONLY:
                missed.append(name)
        print(f"{len(MUTANTS[lo:hi]) - len(missed)} of {len(MUTANTS[lo:hi])} variants accounted for"
              + (f"; not noticed with N={n}: {missed} (try a larger N)" if missed else ""))
        ok = not missed
    else:
        sys.exit(__doc__)
    sys.exit(0 if ok else 1)
