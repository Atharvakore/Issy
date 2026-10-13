#!/usr/bin/env python3
"""Equivalence checking of Issy's programs with an SMT solver (Z3): is the optimized program the same program?

Two programs are equivalent when, for EVERY sequence of input values, they show the environment the same
global state at every Read (what read_inputs() sees in the C code) and end the same way (abort() or leaving
the outermost loop). The inputs are symbolic integers/booleans, so one query covers all of them; nothing is
sampled. This is "translation validation" of the optimizer: the optimized program is checked against the
original one that Issy printed, instead of trusting the optimizer.

How: both programs are translated to control-flow graphs and run in lockstep, from Read to Read, with a
symbolic state (Z3 terms) and one fresh symbolic input vector per Read. At every Read the solver must find
no input history that makes the two states differ. Paths that lead to the same pair of Read statements are
merged. Result, per pair of programs:

  PROVED for all lengths   the lockstep exploration closed: either both programs end on every path, or (when
                           there are no inputs) a pair of states repeated, or the solver (Spacer, a CHC
                           engine) found an inductive invariant relating the two programs;
  PROVED up to K reads     no difference for any input sequence of length <= K (K = --steps), not decided beyond;
  DIFFERENT                a concrete input sequence is printed and replayed with an independent interpreter;
  INCONCLUSIVE             the solver gave up (timeout) or a stretch of code without Read did not end.

Assumptions: integers are mathematical integers (no 32-bit wrap-around; the optimizer folds a constant only
when |result| < 2^31); a Declare'd variable is a local that is invisible to the environment and starts with an
UNKNOWN value (garbage, as in C): equivalence is proved for every value of it, so a program that reads a local
before writing it is reported DIFFERENT; guards have no side effects; a global variable that is never assigned
and only read is an input.

    python3 tests/equiv_check.py PROGRAM.json ...        # run the optimizer on each program and check its output
    python3 tests/equiv_check.py --pair ORIG.json OPT.json
    python3 tests/equiv_check.py --dir tests/out         # ast.json against ast_optimized.json, as kept by e2e.py --keep
    python3 tests/equiv_check.py fuzz [N [FIRST]]        # random programs that look like Issy's output
    python3 tests/equiv_check.py mutants PROGRAM.json ... # change optimized programs in one place; the checker must notice
    python3 tests/equiv_check.py self-test [N [FIRST]]   # the checker must reject broken programs (it can fail)

Needs:  pip install z3-solver
"""
import argparse, itertools, json, os, random, shutil, subprocess, sys, tempfile, time

try:
    import z3
except ImportError:
    sys.exit("needs the Z3 Python package:  pip install z3-solver")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


# ----------------------------------------------------------------------------------------------
# the AST (Issy's Prog as JSON)
# ----------------------------------------------------------------------------------------------
def tag(n):
    return n.get("tag") if isinstance(n, dict) else None


def scan(ast):
    """-> (declared, assigned, used, sorts)"""
    declared, assigned, used, sorts = set(), set(), set(), {}

    def walk(n):
        if isinstance(n, list):
            for x in n:
                walk(x)
        elif isinstance(n, dict):
            t = tag(n)
            if t == "Declare":
                declared.add(n["contents"][0])
                sorts[n["contents"][0]] = n["contents"][1]["tag"]
            elif t == "PAssign":
                for a in n["contents"]:
                    assigned.add(a[0])
                    sorts[a[0]] = a[1]["tag"]
            elif t == "Var":
                used.add(n["contents"][0])
                sorts.setdefault(n["contents"][0], n["contents"][1]["tag"])
            for v in n.values():
                walk(v)

    walk(ast)
    return declared, assigned, used, sorts


class Info:
    """What the two programs share: variable names/sorts, inputs, observed globals."""

    def __init__(self, a, b):
        da, aa, ua, sa = scan(a)
        db, ab, ub, sb = scan(b)
        self.sorts = dict(sa)
        for v, s in sb.items():
            if self.sorts.setdefault(v, s) != s:
                raise ValueError(f"variable {v} has sort {self.sorts[v]} in one program and {s} in the other")
        declared, assigned, used = da | db, aa | ab, ua | ub
        self.inputs = sorted(used - assigned - declared)
        self.observed = sorted((assigned | used) - declared - set(self.inputs))
        self.names = sorted(self.sorts)
        self.state = [v for v in self.names if v not in self.inputs]


# What a Declare'd local holds right after its declaration. In C it is garbage, so no correct program reads it
# before writing it. The symbolic executor therefore gives every Declare'd local an unknown value, one fixed
# unknown constant per variable name ("U!name", the same in both programs and at every Declare), so equivalence
# is proved for ALL values of the garbage; a program that depended on it would be reported DIFFERENT. The concrete
# interpreter uses LOCAL_VALUES (filled from the solver's model when it replays a counterexample), else 0/false.
SYMBOLIC_LOCALS = [True]
LOCAL_VALUES = {}


def default_py(sort):
    return False if sort == "SBool" else 0


def local_py(name, sort):
    return LOCAL_VALUES.get(name, default_py(sort))


def _is_garbage(x):
    return z3.is_const(x) and x.decl().kind() == z3.Z3_OP_UNINTERPRETED and x.decl().name().startswith("U!")


def local_z3(name, sort):
    return z3_const(f"U!{name}", sort) if SYMBOLIC_LOCALS[0] else default_z3(sort)


def default_z3(sort):
    return z3.BoolVal(False) if sort == "SBool" else (z3.RealVal(0) if sort == "SReal" else z3.IntVal(0))


def z3_const(name, sort):
    return z3.Bool(name) if sort == "SBool" else (z3.Real(name) if sort == "SReal" else z3.Int(name))


# ----------------------------------------------------------------------------------------------
# an independent concrete interpreter (used to replay counterexamples and to cross-check the solver)
# ----------------------------------------------------------------------------------------------
class _Abort(Exception): pass
class _Brk(Exception): pass
class _Cont(Exception): pass
class _Stop(Exception): pass
class _Fuel(Exception): pass


def ev(t, env):
    tg = t["tag"]
    if tg == "Var":
        return env[t["contents"][0]]
    if tg == "Const":
        return t["contents"]["contents"]
    f, args = t["contents"]
    op, a = f["tag"], [ev(x, env) for x in args]
    if op == "FAdd": return sum(a)
    if op == "FMul":
        r = 1
        for x in a:
            r *= x
        return r
    if op == "FEq": return all(a[0] == x for x in a[1:])
    if op == "FLt": return a[0] < a[1]
    if op == "FLte": return a[0] <= a[1]
    if op == "FAnd": return all(a)
    if op == "FOr": return any(a)
    if op == "FNot": return not a[0]
    if op == "FIte": return a[1] if a[0] else a[2]
    raise ValueError("unknown operator " + op)


def replay(ast, info, provider, max_reads, fuel=200000):
    """Run `ast`; provider(j) -> {input: value} for the j-th Read. -> (observations, end)
    observations has one tuple per Read executed (taken BEFORE the inputs are drawn); end is
    "abort", "exit" or "limit" (max_reads reads executed) or "spin"."""
    env = {v: default_py(info.sorts[v]) for v in info.names}
    obs, left = [], [fuel]

    def ex(p):
        left[0] -= 1
        if left[0] < 0:
            raise _Fuel()
        t, c = tag(p), p.get("contents")
        if t == "Abort":
            raise _Abort()
        if t == "Read":
            if len(obs) >= max_reads:
                raise _Stop()
            obs.append(tuple(env[v] for v in info.observed))
            env.update(provider(len(obs) - 1))
        elif t == "Declare":
            env[c[0]] = local_py(c[0], c[1]["tag"])
        elif t == "Cond":
            if ev(c[0], env):
                ex(c[1])
        elif t == "Sequence":
            for q in c:
                ex(q)
        elif t == "PAssign":
            vals = [(v, ev(e, env)) for v, _, e in c]
            for v, x in vals:
                env[v] = x
        elif t == "Break":
            raise _Brk()
        elif t == "Continue":
            raise _Cont()
        elif t == "InfLoop":
            while True:
                try:
                    ex(c)
                except _Cont:
                    continue
                except _Brk:
                    break
        else:
            raise ValueError("unsupported statement " + str(t))

    try:
        ex(ast)
        end = "exit"
    except _Abort:
        end = "abort"
    except _Stop:
        end = "limit"
    except _Fuel:
        end = "spin"
    except (_Brk, _Cont):
        end = "exit"
    return obs, end


def first_difference(a, b, info, provider, max_reads, fuel=200000):
    """-> None or a description of the first difference between two programs for one input sequence."""
    oa, ea = replay(a, info, provider, max_reads, fuel)
    ob, eb = replay(b, info, provider, max_reads, fuel)
    for i, (x, y) in enumerate(zip(oa, ob)):
        if x != y:
            return f"read {i}: state {dict(zip(info.observed, x))} vs {dict(zip(info.observed, y))}"
    if len(oa) != len(ob) or ea != eb:
        return f"first program ends '{ea}' after {len(oa)} reads, second ends '{eb}' after {len(ob)} reads"
    return None


# ----------------------------------------------------------------------------------------------
# control-flow graph
# ----------------------------------------------------------------------------------------------
class CFG:
    """Nodes with one of:  ("read", next)  ("skip", next)  ("declare", var, sort, next)
    ("assign", [(var, sort, term)], next)  ("branch", guard, then_node, else_node).
    ABORT and EXIT are the terminal nodes."""

    def __init__(self, ast):
        self.ast = ast
        self.out, self.n = {}, 0
        self.ABORT, self.EXIT = self.new(), self.new()
        self.entry = self.compile(ast, self.EXIT, self.EXIT, self.EXIT)
        self.reads = sorted(n for n, o in self.out.items() if o[0] == "read")

    def new(self):
        self.n += 1
        return self.n - 1

    def compile(self, p, nxt, brk, cont):
        t, c = tag(p), p.get("contents")
        if t == "Abort": return self.ABORT
        if t == "Break": return brk
        if t == "Continue": return cont
        if t == "Read":
            n = self.new(); self.out[n] = ("read", nxt); return n
        if t == "Declare":
            n = self.new(); self.out[n] = ("declare", c[0], c[1]["tag"], nxt); return n
        if t == "PAssign":
            if not c:
                return nxt
            n = self.new(); self.out[n] = ("assign", c, nxt); return n
        if t == "Cond":
            n = self.new(); self.out[n] = ("branch", c[0], self.compile(c[1], nxt, brk, cont), nxt); return n
        if t == "Sequence":
            e = nxt
            for q in reversed(c):
                e = self.compile(q, e, brk, cont)
            return e
        if t == "InfLoop":
            h = self.new()
            self.out[h] = ("skip", self.compile(c, h, nxt, h))
            return h
        raise ValueError("unsupported statement " + str(t))


def zterm(t, st):
    tg = t["tag"]
    if tg == "Var":
        return st[t["contents"][0]]
    if tg == "Const":
        c = t["contents"]
        if c["tag"] == "CInt": return z3.IntVal(c["contents"])
        if c["tag"] == "CBool": return z3.BoolVal(c["contents"])
        return z3.RealVal(str(c["contents"]))
    f, args = t["contents"]
    op, a = f["tag"], [zterm(x, st) for x in args]
    if op == "FAdd": return a[0] if len(a) == 1 else z3.Sum(a)
    if op == "FMul":
        r = a[0]
        for x in a[1:]:
            r = r * x
        return r
    if op == "FEq": return a[0] == a[1] if len(a) == 2 else z3.And([a[0] == x for x in a[1:]])
    if op == "FLt": return a[0] < a[1]
    if op == "FLte": return a[0] <= a[1]
    if op == "FAnd": return z3.And(a) if a else z3.BoolVal(True)
    if op == "FOr": return z3.Or(a) if a else z3.BoolVal(False)
    if op == "FNot": return z3.Not(a[0])
    if op == "FIte": return z3.If(a[0], a[1], a[2])
    raise ValueError("unknown operator " + op)


def check(S, conds, model=False):
    """-> "sat" / "unsat" / "unknown" (and the model if asked and sat)"""
    S.push()
    try:
        S.add(*conds)
        r = S.check()
        m = S.model() if (model and r == z3.sat) else None
    finally:
        S.pop()
    return (str(r), m) if model else str(r)


def _store_key(st, skip):
    """Identity of the store without the variables in `skip`: Z3 terms are hash-consed, so equal ids mean the
    very same (structurally identical) term, and equal stores give equal futures."""
    return tuple(st[v].get_id() for v in sorted(st) if v not in skip)


_VC = itertools.count()


class _Timeout(Exception):
    pass


_DEADLINE = [None]                         # time.time() after which segment() gives up


def _never_exits(cfg, n, st, ps, S, inputs, maxsteps):
    """Is it provable that the loop with head `n`, entered with store `st` under the path conditions `ps`, never
    reaches a Read, an abort or the end? V is a general store at the loop head and N(V) = "no path from the
    head leaves the loop". If N holds now and is preserved by every way round the loop (N(V) and the path
    condition G of that way imply N(f(V))), the loop never ends. Only this one-step induction is tried; a loop
    that needs a stronger invariant stays undecided."""
    names = sorted(st)
    V = {v: z3.Const(f"V{next(_VC)}_{v}", st[v].sort()) for v in names}
    outs = segment(cfg, n, V, S, [], maxsteps, inputs, stop=n, silent=False)
    if any(o[0] == "spin" for o in outs):
        return False
    exits = [z3.And(o[2]) if o[2] else z3.BoolVal(True) for o in outs if o[0] in ("read", "abort", "exit")]
    NV = z3.Not(z3.Or(exits)) if exits else z3.BoolVal(True)

    def sub(expr, W):
        return z3.substitute(expr, *[(V[v], W[v]) for v in names])
    if check(S, list(ps) + [z3.Not(sub(NV, st))]) != "unsat":
        return False
    for o in outs:
        if o[0] == "cycle":
            G = z3.And(o[2]) if o[2] else z3.BoolVal(True)
            if check(S, [NV, G, z3.Not(sub(NV, o[3]))]) != "unsat":
                return False
    return True


def segment(cfg, node, store, S, pcs, maxsteps, inputs=(), stop=None, silent=True):
    """Run symbolically from `node` until the next Read, the end, or an abort. -> list of
    (kind, node, path conditions, store) with kind "read" (node = the Read node), "abort", "exit", "diverge"
    (this stretch never ends and never reads again: the same loop head twice with the very same store, or an
    inductive argument, see _never_exits) or "spin" (more than maxsteps steps; undecided). The inputs cannot
    change inside a stretch, so they are not part of the comparison. With `stop`, a path that comes back to
    that loop head ends there with kind "cycle" (used by _never_exits)."""
    out, work = [], [(node, store, list(pcs), 0, frozenset(), {})]
    while work:
        n, st, ps, steps, seen, heads = work.pop()
        while True:
            if _DEADLINE[0] is not None and time.time() > _DEADLINE[0]:
                raise _Timeout()
            if n == cfg.ABORT: out.append(("abort", n, ps, st)); break
            if n == cfg.EXIT: out.append(("exit", n, ps, st)); break
            if steps > maxsteps:
                recent = sorted(heads.items(), key=lambda kv: -kv[1][0])[:3] if silent else []
                if any(_never_exits(cfg, h, hs, hp, S, inputs, maxsteps) for h, (_, hs, hp) in recent):
                    out.append(("diverge", n, ps, st))
                else:
                    out.append(("spin", n, ps, st))
                break
            o = cfg.out[n]
            k = o[0]
            steps += 1
            if k == "read": out.append(("read", n, ps, st)); break
            if k == "skip":
                if stop is not None and n == stop and steps > 1:
                    out.append(("cycle", n, ps, st)); break
                key = (n, _store_key(st, inputs))
                if key in seen:
                    out.append(("diverge", n, ps, st)); break
                seen = seen | {key}
                heads = {**heads, n: (steps, st, ps)}
                n = o[1]
            elif k == "declare":
                st = dict(st); st[o[1]] = local_z3(o[1], o[2]); n = o[3]
            elif k == "assign":
                new = dict(st)
                for v, _, t in o[1]:
                    new[v] = zterm(t, st)
                st, n = new, o[2]
            else:                                           # branch
                g = z3.simplify(zterm(o[1], st))
                if z3.is_true(g): n = o[2]
                elif z3.is_false(g): n = o[3]
                else:
                    ft, ff = check(S, ps + [g]) != "unsat", check(S, ps + [z3.Not(g)]) != "unsat"
                    if ft and ff:
                        work.append((o[3], st, ps + [z3.Not(g)], steps, seen, heads))
                        ps, n = ps + [g], o[2]
                    elif ft: n = o[2]
                    elif ff: n = o[3]
                    else: break
    return out


# ----------------------------------------------------------------------------------------------
# result
# ----------------------------------------------------------------------------------------------
class Result:
    def __init__(self, status, text, reads=0, ce=None):
        self.status, self.text, self.reads, self.ce = status, text, reads, ce

    @property
    def ok(self):
        return self.status in ("PROVED", "BOUNDED")

    def __str__(self):
        return {"PROVED": "PROVED for all lengths", "BOUNDED": "PROVED up to %d reads" % self.reads,
                "DIFFERENT": "DIFFERENT", "INCONCLUSIVE": "INCONCLUSIVE"}[self.status] + (f" ({self.text})" if self.text else "")


def num(v):
    if z3.is_true(v): return True
    if z3.is_false(v): return False
    if z3.is_int_value(v): return v.as_long()
    if z3.is_rational_value(v): return f"{v.numerator_as_long()}/{v.denominator_as_long()}"
    return str(v)


# ----------------------------------------------------------------------------------------------
# lockstep symbolic execution
# ----------------------------------------------------------------------------------------------
class Conf:
    __slots__ = ("key", "pc", "sa", "sb", "conc")

    def __init__(self, key, pc, sa, sb, conc):
        self.key, self.pc, self.sa, self.sb, self.conc = key, pc, sa, sb, conc


def verify(a, b, steps=20, timeout=30, maxsteps=400, unbounded=True, unb_timeout=60, info=None, budget=300):
    """Is `b` equivalent to `a`? -> Result. `timeout`: seconds per solver query; `unb_timeout`: seconds for the
    attempt at a proof for all lengths; `budget`: seconds for the whole comparison (INCONCLUSIVE when used up)."""
    _DEADLINE[0] = time.time() + budget
    try:
        return _verify(a, b, steps, timeout, maxsteps, unbounded, unb_timeout, info)
    except _Timeout:
        return Result("INCONCLUSIVE", f"time budget of {budget:.0f} s used up", -1)
    finally:
        _DEADLINE[0] = None


def _verify(a, b, steps, timeout, maxsteps, unbounded, unb_timeout, info):
    info = info or Info(a, b)
    cA, cB = CFG(a), CFG(b)
    S = z3.Solver()
    S.set("timeout", int(timeout * 1000))
    ctr = itertools.count()
    unknown = spins = 0
    history = []                                             # per step: [(pc, key, obsA, obsB)]
    inputs_at = []                                           # per Read: {name: z3 const}

    def define(e, hint):
        if z3.is_const(e):
            return e
        v = z3.Const(f"{hint}!{next(ctr)}", e.sort())
        S.add(v == e)
        return v

    def concrete(st):
        """Every value is a numeral, or the unknown start value U!name of a Declare'd local (a fixed constant,
        independent of the inputs and of the path)."""
        return all(z3.is_int_value(x) or z3.is_true(x) or z3.is_false(x) or _is_garbage(x) for x in st.values())

    def fail(kind, k, pc, model, desc):
        provider_vals = []
        for j in range(k + 1):
            provider_vals.append({v: _py(model.eval(inputs_at[j][v], model_completion=True)) for v in info.inputs}
                                 if j < len(inputs_at) else {v: default_py(info.sorts[v]) for v in info.inputs})
        prov = lambda j: provider_vals[j] if j < len(provider_vals) else {v: default_py(info.sorts[v]) for v in info.inputs}
        LOCAL_VALUES.clear()
        for v in scan(a)[0] | scan(b)[0]:
            LOCAL_VALUES[v] = _py(model.eval(z3_const(f"U!{v}", info.sorts[v]), model_completion=True))
        try:
            diff = first_difference(a, b, info, prov, k + 1)
        finally:
            garbage = {v: x for v, x in LOCAL_VALUES.items() if x not in (0, False)}
            LOCAL_VALUES.clear()
        trace = []
        for j in range(min(k + 1, len(history))):
            for pc_j, key, oa, ob in history[j]:
                if z3.is_true(model.eval(pc_j, model_completion=True)):
                    trace.append((j, [_py(model.eval(x, model_completion=True)) for x in oa],
                                  [_py(model.eval(x, model_completion=True)) for x in ob]))
                    break
        return Result("DIFFERENT", desc, k, dict(inputs=provider_vals, trace=trace, replay=diff, kind=kind, garbage=garbage))

    def pair(OA, OB, base_pc, base_conc, k):
        """Combine the outcomes of the two programs. -> (confs, failure or None)"""
        nonlocal unknown, spins
        groups = {}
        for oa in OA:
            for ob in OB:
                conds = list(oa[2]) + list(ob[2])
                if conds:
                    r, m = check(S, [base_pc] + conds, model=True)
                    if r == "unsat":
                        continue
                    if r == "unknown":
                        unknown += 1
                        continue
                pc = define(z3.And([base_pc] + conds), f"pc{k}") if conds else base_pc
                ka, kb = oa[0], ob[0]
                if "spin" in (ka, kb):
                    spins += 1
                elif ka == "read" and kb == "read":
                    conc = base_conc and not conds and concrete(oa[3]) and concrete(ob[3])
                    groups.setdefault((oa[1], ob[1]), []).append(Conf((oa[1], ob[1]), pc, oa[3], ob[3], conc))
                elif ka == kb:
                    pass                                      # both abort or both leave the program
                else:
                    if not conds:
                        r, m = check(S, [base_pc], model=True)
                        if r != "sat":
                            unknown += r == "unknown"
                            continue
                    return [], fail("end", k, pc, m, f"after {k} reads the first program does '{ka}' where the second does '{kb}'")
        confs = []
        for key, L in groups.items():
            if len(L) == 1:
                c = L[0]
                sa = {v: define(x, f"A{k}_{v}") for v, x in c.sa.items()}
                sb = {v: define(x, f"B{k}_{v}") for v, x in c.sb.items()}
                confs.append(Conf(key, c.pc, sa, sb, c.conc))
            else:
                pc = define(z3.Or([c.pc for c in L]), f"pc{k}m")
                def merge(sel, tagname):
                    out = {}
                    for v in info.names:
                        e = getattr(L[-1], sel)[v]
                        for c in reversed(L[:-1]):
                            e = z3.If(c.pc, getattr(c, sel)[v], e)
                        out[v] = define(e, f"{tagname}{k}_{v}")
                    return out
                confs.append(Conf(key, pc, merge("sa", "A"), merge("sb", "B"), False))
        return confs, None

    def observe(confs, k):
        """Solver check at the Read: the two states must agree. -> failure or None"""
        nonlocal unknown
        rec = []
        for c in confs:
            oa, ob = [c.sa[v] for v in info.observed], [c.sb[v] for v in info.observed]
            rec.append((c.pc, c.key, oa, ob))
        history.append(rec)
        for c, (_, _, oa, ob) in zip(confs, rec):
            if not oa:
                continue
            diff = z3.Or([x != y for x, y in zip(oa, ob)])
            if c.conc and z3.is_false(z3.simplify(diff)):
                continue
            r, m = check(S, [c.pc, diff], model=True)
            if r == "sat":
                return fail("state", k, c.pc, m, f"after {k} reads the global state differs")
            unknown += r == "unknown"
        return None

    store0 = {v: default_z3(info.sorts[v]) for v in info.names}
    t0 = time.time()
    OA = segment(cA, cA.entry, dict(store0), S, [], maxsteps, info.inputs)
    OB = segment(cB, cB.entry, dict(store0), S, [], maxsteps, info.inputs)
    confs, bad = pair(OA, OB, z3.BoolVal(True), True, 0)
    if bad:
        return bad
    bad = observe(confs, 0)
    if bad:
        return bad
    init_confs = list(confs)
    seen = {_ckey(c) for c in confs if c.conc}
    k = 0
    while confs and k < steps:
        k += 1
        ins = {v: z3_const(f"in_{k - 1}_{v}", info.sorts[v]) for v in info.inputs}
        inputs_at.append(ins)
        nxt = []
        for c in confs:
            sa, sb = dict(c.sa), dict(c.sb)
            sa.update(ins); sb.update(ins)
            OA = segment(cA, cA.out[c.key[0]][1], sa, S, [], maxsteps, info.inputs)
            OB = segment(cB, cB.out[c.key[1]][1], sb, S, [], maxsteps, info.inputs)
            new, bad = pair(OA, OB, c.pc, c.conc, k)
            if bad:
                return bad
            nxt.extend(new)
        # configurations of different predecessors with the same Read pair are merged
        by = {}
        for c in nxt:
            by.setdefault(c.key, []).append(c)
        confs = []
        for key, L in by.items():
            if len(L) == 1:
                confs.append(L[0])
            else:
                pc = define(z3.Or([c.pc for c in L]), f"pc{k}x")
                def merge(sel, tagname):
                    out = {}
                    for v in info.names:
                        e = getattr(L[-1], sel)[v]
                        for c in reversed(L[:-1]):
                            e = z3.If(c.pc, getattr(c, sel)[v], e)
                        out[v] = define(e, f"{tagname}{k}x_{v}")
                    return out
                confs.append(Conf(key, pc, merge("sa", "A"), merge("sb", "B"), False))
        bad = observe(confs, k)
        if bad:
            return bad
        if confs and all(c.conc for c in confs) and all(_ckey(c) in seen for c in confs):
            return _finish(unknown, spins, Result("PROVED", f"no input at all: the pair of states repeats after {k} reads", k))
        seen |= {_ckey(c) for c in confs if c.conc}
    if not confs:
        return _finish(unknown, spins, Result("PROVED", f"every path of both programs ends within {k} reads", k))
    res = Result("BOUNDED", f"{len(confs)} lockstep configuration(s) alive", k)
    if unbounded and not unknown and not spins:
        u = prove_unbounded(info, cA, cB, init_confs, maxsteps, unb_timeout)
        if u == "proved":
            return Result("PROVED", "inductive invariant found by Spacer", k)
        res.text += f"; unbounded proof: {u}"
    return _finish(unknown, spins, res)


def _finish(unknown, spins, res):
    if unknown or spins:
        return Result("INCONCLUSIVE", f"{unknown} solver timeouts, {spins} stretches of code without Read that did not end",
                      res.reads)
    return res


def _py(v):
    return num(v)


def _ckey(c):
    return (c.key, tuple(str(c.sa[v]) for v in sorted(c.sa)), tuple(str(c.sb[v]) for v in sorted(c.sb)))


# ----------------------------------------------------------------------------------------------
# unbounded proof: constrained Horn clauses solved by Spacer
# ----------------------------------------------------------------------------------------------
def prove_unbounded(info, cA, cB, init_confs, maxsteps, timeout):
    """Is there an invariant R(readA, readB, stateA, stateB) that holds initially, is preserved by one lockstep
    step with a shared arbitrary input, and implies equal observations? -> "proved" or a short reason."""
    outer = _DEADLINE[0]
    own = time.time() + timeout
    _DEADLINE[0] = own if outer is None else min(outer, own)
    try:
        return _prove_unbounded(info, cA, cB, init_confs, maxsteps, timeout)
    except _Timeout:
        if outer is not None and time.time() > outer:
            raise
        return "time limit reached while preparing the proof"
    finally:
        _DEADLINE[0] = outer


def _prove_unbounded(info, cA, cB, init_confs, maxsteps, timeout):
    state = info.state
    ga = {v: z3_const(f"a_{v}", info.sorts[v]) for v in info.names}
    gb = {v: z3_const(f"b_{v}", info.sorts[v]) for v in info.names}
    gi = {v: z3_const(f"i_{v}", info.sorts[v]) for v in info.inputs}
    S0 = z3.Solver()
    S0.set("timeout", 2000)

    def summaries(cfg, g):
        out = {}
        for r in cfg.reads:
            st = dict(g)
            st.update(gi)
            out[r] = segment(cfg, cfg.out[r][1], st, S0, [], maxsteps, info.inputs)
            if any(o[0] == "spin" for o in out[r]):
                return None
        return out

    SA, SB = summaries(cA, ga), summaries(cB, gb)
    if SA is None or SB is None:
        return "code without Read that does not end quickly"
    fp = z3.Fixedpoint()
    fp.set(engine="spacer")
    fp.set(timeout=int(timeout * 1000))
    rels = {}
    # The unknown start values U!v of the Declare'd locals are fixed for a whole run. Spacer does not accept such
    # constants, so each becomes a variable G_v that every relation carries along unchanged.
    gl = sorted(scan(cA.ast)[0] | scan(cB.ast)[0]) if SYMBOLIC_LOCALS[0] else []
    G = {v: z3_const(f"G_{v}", info.sorts[v]) for v in gl}
    pairs = [(z3_const(f"U!{v}", info.sorts[v]), G[v]) for v in gl]
    sub = (lambda e: z3.substitute(e, *pairs)) if pairs else (lambda e: e)

    def rel(ra, rb):
        if (ra, rb) not in rels:
            d = z3.Function(f"R_{ra}_{rb}", *([z3_sort(info.sorts[v]) for v in state] * 2),
                            *[z3_sort(info.sorts[v]) for v in gl], z3.BoolSort())
            fp.register_relation(d)
            rels[(ra, rb)] = d
        return rels[(ra, rb)]

    err = z3.Function("err", z3.BoolSort())
    fp.register_relation(err)
    fp.declare_var(*(list(ga.values()) + list(gb.values()) + list(gi.values()) + list(G.values())))
    args = lambda sa, sb: [sub(sa[v]) for v in state] + [sub(sb[v]) for v in state] + [G[v] for v in gl]
    todo, seen = [], set()
    for c in init_confs:
        if not c.conc:
            return "initial state not concrete"
        fp.rule(rel(*c.key)(*args(c.sa, c.sb)), [])
        todo.append(c.key)
        seen.add(c.key)
    while todo:
        ra, rb = todo.pop()
        head = rel(ra, rb)(*args(ga, gb))
        oa_, ob_ = [ga[v] for v in info.observed], [gb[v] for v in info.observed]
        if oa_:
            fp.rule(err(), [head, z3.Or([x != y for x, y in zip(oa_, ob_)])])
        for oa in SA[ra]:
            for ob in SB[rb]:
                conds = list(oa[2]) + list(ob[2])
                if conds and check(S0, conds) == "unsat":
                    continue
                conds = [sub(x) for x in conds]
                ka, kb = oa[0], ob[0]
                if ka == "read" and kb == "read":
                    fp.rule(rel(oa[1], ob[1])(*args(oa[3], ob[3])), [head] + conds)
                    if (oa[1], ob[1]) not in seen:
                        seen.add((oa[1], ob[1]))
                        todo.append((oa[1], ob[1]))
                elif ka != kb:
                    fp.rule(err(), [head] + conds)
    r = fp.query(err())
    if r == z3.unsat:
        return "proved"
    if r == z3.sat:
        return "Spacer found a counterexample deeper than the bound"
    return "Spacer gave up (timeout or incomplete)"


def z3_sort(s):
    return z3.BoolSort() if s == "SBool" else (z3.RealSort() if s == "SReal" else z3.IntSort())


# ----------------------------------------------------------------------------------------------
# running the optimizer, loading programs
# ----------------------------------------------------------------------------------------------
def load(path):
    d = json.load(open(path))
    return d["ast"] if isinstance(d, dict) and "ast" in d and "tag" not in d else d


_OPT_MODULE = []


def _optimizer_module():
    if not _OPT_MODULE:
        sys.path.insert(0, ROOT)
        import optimizer_simple_egglog
        _OPT_MODULE.append(optimizer_simple_egglog)
    return _OPT_MODULE[0]


def optimize(ast, optimizer=None, legacy=False):
    """The optimized copy of `ast`. By default the repository's optimizer_simple_egglog.py is imported and its
    pipeline run in this process (the same calls as its main()); with `optimizer` the given script is run as a
    child process on an ast.json in a temporary directory, exactly as Synthesis.hs does. `legacy` selects the
    original, unsound pipeline (only used by the self-test, to have programs that really are wrong)."""
    if optimizer is None:
        O = _optimizer_module()
        pipeline = O.optimize_ast_with_egglog_legacy if legacy else O.optimize_ast_with_egglog
        return O.prog_to_json(pipeline(O.parse_prog(json.loads(json.dumps(ast)))))
    if legacy:
        raise ValueError("legacy and a custom optimizer script cannot be combined")
    d = tempfile.mkdtemp(prefix="equiv-opt-")
    try:
        json.dump(ast, open(os.path.join(d, "ast.json"), "w"))
        r = subprocess.run([sys.executable, optimizer], cwd=d, capture_output=True, text=True)
        if r.returncode:
            raise RuntimeError("optimizer: " + r.stderr.strip()[-300:])
        return json.load(open(os.path.join(d, "ast_optimized.json")))
    finally:
        shutil.rmtree(d, ignore_errors=True)


def show(name, res, t):
    print(f"{name:24s} {res}  [{t:.1f} s]")
    if res.status == "DIFFERENT" and res.ce:
        ce = res.ce
        print("    input sequence (one line per Read):")
        for j, v in enumerate(ce["inputs"]):
            print(f"      read {j}: {v}")
        for j, oa, ob in ce["trace"][-3:]:
            print(f"    state at read {j}: first {oa}  second {ob}")
        if ce.get("garbage"):
            print(f"    values of the uninitialised locals in this counterexample: {ce['garbage']}")
        print(f"    replay with the independent interpreter: {ce['replay'] or 'NO DIFFERENCE (checker bug!)'}")


def run_pair(name, a, b, args):
    t = time.time()
    res = verify(a, b, steps=args.steps, timeout=args.timeout, unbounded=not args.no_unbounded,
                 unb_timeout=args.unbounded_timeout, budget=args.budget)
    show(name, res, time.time() - t)
    return res


# ----------------------------------------------------------------------------------------------
# random programs shaped like Issy's output
# ----------------------------------------------------------------------------------------------
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
    """A dispatch loop on prog_counter (values 0..3) with nested loops, parallel assignments with ite, reads, the
    abort() sentinel and fall-through blocks, like the programs Issy prints. State x, y (int), c (bool); input i."""

    def __init__(self, seed):
        self.r = random.Random(seed)

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
        if r.random() < .3:
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
        for k in range(4):
            blocks.append(cond(self.pc_is(k), self.leaf(depth > 0)))
        return seq(*blocks, ABORT)

    def program(self):
        return seq(decl("prog_counter"), pa(("prog_counter", INT, C(0))), pa(("x", INT, C(self.r.randint(0, 3)))),
                   pa(("y", INT, C(0))), pa(("c", BOOL, B(False))), loop(self.body(0)))


# ----------------------------------------------------------------------------------------------
# mutants for the self-test
# ----------------------------------------------------------------------------------------------
def _is_bool(t):
    tg = t["tag"]
    if tg == "Var": return t["contents"][1]["tag"] == "SBool"
    if tg == "Const": return t["contents"]["tag"] == "CBool"
    op, args = t["contents"][0]["tag"], t["contents"][1]
    if op == "FIte": return _is_bool(args[1])
    return op in ("FAnd", "FOr", "FNot", "FEq", "FLt", "FLte")


def mutate(ast, seed):
    """One small random change to a copy of `ast` that keeps it well typed. -> (new ast, description)"""
    r = random.Random(seed)
    ast = json.loads(json.dumps(ast))
    sites = []

    def walk(n, parent, key):
        if isinstance(n, list):
            for i, x in enumerate(n):
                walk(x, n, i)
        elif isinstance(n, dict):
            t = tag(n)
            if t == "Const" and tag(n["contents"]) == "CInt":
                sites.append(("const", n, parent, key))
            elif t == "Func" and (n["contents"][0]["tag"] in ("FLt", "FLte", "FAnd", "FOr")
                                  or (n["contents"][0]["tag"] == "FEq" and not _is_bool(n["contents"][1][0]))):
                sites.append(("op", n, parent, key))
            elif t == "Cond":
                sites.append(("negate", n, parent, key))
            elif t == "Sequence" and len(n["contents"]) > 1:
                sites.append(("delete", n, parent, key))
            elif t in ("Break", "Continue"):
                sites.append(("jump", n, parent, key))
            elif t == "PAssign" and any(x[1] == y[1] for x, y in itertools.combinations(n["contents"], 2)):
                sites.append(("swap", n, parent, key))
            for k, v in n.items():
                walk(v, n, k)

    walk(ast, None, None)
    if not sites:
        return ast, "nothing to change"
    kind, n, parent, key = r.choice(sites)
    if kind == "const":
        n["contents"]["contents"] += r.choice([-1, 1])
        return ast, "constant changed by one"
    if kind == "op":
        sw = {"FLt": "FLte", "FLte": "FLt", "FAnd": "FOr", "FOr": "FAnd", "FEq": "FLt"}
        n["contents"][0]["tag"] = sw[n["contents"][0]["tag"]]
        return ast, "operator replaced"
    if kind == "negate":
        n["contents"][0] = F("FNot", n["contents"][0])
        return ast, "guard negated"
    if kind == "delete":
        del n["contents"][r.randrange(len(n["contents"]))]
        return ast, "statement deleted"
    if kind == "jump":
        n["tag"] = "Continue" if n["tag"] == "Break" else "Break"
        return ast, "break/continue swapped"
    items = n["contents"]
    i, j = r.choice([(i, j) for i, j in itertools.combinations(range(len(items)), 2) if items[i][1] == items[j][1]])
    items[i][2], items[j][2] = items[j][2], items[i][2]
    return ast, "right-hand sides swapped"


def cross_check(a, b, info, res, seed=0, tries=60, deep=30):
    """Compare a verdict with random concrete runs of the two programs. -> None if consistent, else a message.
    A verdict that is ok must not be contradicted by any run: PROVED holds for every length (runs of `deep`
    reads are used), BOUNDED for runs of up to res.reads reads."""
    if not res.ok:
        return None
    k = res.reads if res.status == "BOUNDED" else deep
    r = random.Random(seed)
    for t in range(tries):
        rng = random.Random(r.random())
        span = rng.choice([1, 2, 5, 40])
        cache = {}

        def prov(j):
            if j not in cache:
                cache[j] = {v: (rng.random() < .5 if info.sorts[v] == "SBool" else rng.randint(-span, span)) for v in info.inputs}
            return cache[j]
        d = first_difference(a, b, info, prov, k, fuel=20000)
        if d:
            return f"verdict '{res}' but a random run differs: {d}"
    return None


def exhaustive(a, b, info, length, domain=(-1, 0, 1, 2), budget=10.0):
    """Brute force, independent of the solver: EVERY input sequence of `length` reads whose integer inputs come
    from `domain` (booleans: both values). -> (first difference or None, number of sequences tried). Programs
    that loop a long time between two reads make a run slow, so after `budget` seconds it stops early (the
    number of sequences tried then is smaller than len(vecs) ** length)."""
    choices = [[False, True] if info.sorts[v] == "SBool" else list(domain) for v in info.inputs]
    vecs = [dict(zip(info.inputs, t)) for t in itertools.product(*choices)]
    runs = 0
    stop_at = time.time() + budget
    for idx in itertools.product(range(len(vecs)), repeat=length):
        if time.time() > stop_at:
            break
        runs += 1
        d = first_difference(a, b, info, lambda j: vecs[idx[j]], length, fuel=20000)
        if d:
            return d, runs
    return None, runs


# ----------------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("what", nargs="*", help="program files, or: fuzz [N [FIRST]] | self-test")
    ap.add_argument("--pair", nargs=2, metavar=("ORIG", "OPT"))
    ap.add_argument("--dir", help="directory with <spec>/ast.json and <spec>/ast_optimized.json (e2e.py --keep)")
    ap.add_argument("--optimizer", help="optimizer script to run instead of the repository's")
    ap.add_argument("--steps", type=int, default=20, help="number of Reads to explore (default 20)")
    ap.add_argument("--timeout", type=float, default=30, help="seconds per solver query (default 30)")
    ap.add_argument("--unbounded-timeout", type=float, default=60)
    ap.add_argument("--budget", type=float, default=300, help="seconds for one whole comparison (default 300)")
    ap.add_argument("--no-unbounded", action="store_true", help="skip the attempt at a proof for all lengths")
    ap.add_argument("--mutants", type=int, default=40, help="mutants per program for the `mutants` command (default 40)")
    args = ap.parse_args()
    results = []
    if args.pair:
        results.append(run_pair(os.path.basename(args.pair[0]), load(args.pair[0]), load(args.pair[1]), args))
    elif args.dir:
        for name in sorted(os.listdir(args.dir)):
            f1, f2 = (os.path.join(args.dir, name, f) for f in ("ast.json", "ast_optimized.json"))
            if os.path.exists(f1) and os.path.exists(f2):
                results.append(run_pair(name, load(f1), load(f2), args))
    elif args.what[:1] == ["fuzz"]:
        n = int(args.what[1]) if len(args.what) > 1 else 50
        first = int(args.what[2]) if len(args.what) > 2 else 0
        count = {}
        for seed in range(first, first + n):
            p = Gen(seed).program()
            res = run_quiet(p, optimize(p, args.optimizer), args)
            count[res.status] = count.get(res.status, 0) + 1
            if res.status in ("DIFFERENT", "INCONCLUSIVE"):
                print(f"seed {seed}: {res}")
            results.append(res)
        print(f"{n} random programs (seeds {first}..{first + n - 1}): {count}")
    elif args.what[:1] == ["self-test"]:
        return self_test(args)
    elif args.what[:1] == ["mutants"]:
        return mutants(args)
    else:
        for path in args.what:
            p = load(path)
            results.append(run_pair(os.path.basename(path), p, optimize(p, args.optimizer), args))
    ok = all(r.ok for r in results)
    print("OK" if ok else "NOT PROVED")
    sys.exit(0 if ok else 1)


def run_quiet(a, b, args):
    return verify(a, b, steps=args.steps, timeout=args.timeout, unbounded=not args.no_unbounded, unb_timeout=args.unbounded_timeout,
                  budget=args.budget)


def mutation_run(p, q, seeds, run, bad, label, counts):
    """Compare one-change mutants of the optimized program `q` with the original `p`. A mutant must be rejected
    (DIFFERENT, input sequence confirmed by the interpreter) or, if it is not, no random run and no brute-force
    run may show a difference. -> (number rejected, number not rejected); problems are appended to `bad`."""
    killed = survivors = 0
    for ms in seeds:
        m, what = mutate(q, ms)
        if m == q:
            continue
        try:
            infom = Info(p, m)
            rm = run(p, m, infom)
        except (ValueError, z3.Z3Exception) as e:
            counts["ILL-TYPED"] = counts.get("ILL-TYPED", 0) + 1
            continue
        counts[rm.status] = counts.get(rm.status, 0) + 1
        if rm.status == "DIFFERENT":
            killed += 1
            if not (rm.ce and rm.ce["replay"]):
                bad.append(f"{label} mutant {ms} ({what}): DIFFERENT but not confirmed by the interpreter")
        elif rm.ok:
            survivors += 1
            msg = cross_check(p, m, infom, rm, ms)
            if msg:
                bad.append(f"{label} mutant {ms} ({what}): {msg}")
            d, runs = exhaustive(p, m, infom, min(5, rm.reads) if rm.status == "BOUNDED" else 5)
            if d:
                bad.append(f"{label} mutant {ms} ({what}): verdict '{rm}' but brute force finds: {d}")
    return killed, survivors


def mutants(args):
    """mutants PROGRAM.json ... : change the optimized program in one place, many times, and check that the
    checker notices (a mutant that is not rejected must also survive random runs and brute force)."""
    count = args.mutants
    bad, tot_k, tot_s = [], 0, 0
    for path in args.what[1:]:
        p = load(path)
        q = optimize(p, args.optimizer)
        counts = {}
        run = lambda a, b, info: verify(a, b, steps=min(args.steps, 12), timeout=min(args.timeout, 10),
                                        unbounded=not args.no_unbounded, unb_timeout=min(args.unbounded_timeout, 15), info=info, budget=min(args.budget, 60))
        k, s_ = mutation_run(p, q, range(count), run, bad, os.path.basename(path), counts)
        tot_k += k; tot_s += s_
        print(f"{os.path.basename(path):24s} {count} mutants: {counts}", flush=True)
    for b in bad:
        print("FAILED:", b)
    print(f"{tot_k} mutants rejected, {tot_s} not rejected (and not contradicted by random runs or brute force)")
    return 1 if bad else 0


def self_test(args):
    """A checker that cannot fail proves nothing, so it is tried on programs that ARE different and on programs
    that are equal, with the verdicts checked against the independent interpreter:
      1. The first optimizer (unsound lowering of ite) on random programs: those it breaks must be reported
         DIFFERENT, each with an input sequence that the interpreter confirms.
      2. The current optimizer on the same programs: never DIFFERENT; the verdict must not be contradicted by
         random runs.
      3. Mutants of the current optimizer's output (one constant, operator, guard, statement, jump or
         assignment changed) compared with the original program: DIFFERENT with a confirmed input sequence, or,
         when the mutation is harmless, no difference may exist in random runs or in a brute-force run over
         all input sequences (integers from -1..2) of up to 5 reads."""
    n = int(args.what[1]) if len(args.what) > 1 else 30
    first = int(args.what[2]) if len(args.what) > 2 else 0
    steps = min(args.steps, 12)
    bad = []
    t0 = time.time()

    def run(a, b, info):
        return verify(a, b, steps=steps, timeout=min(args.timeout, 10), unbounded=not args.no_unbounded,
                      unb_timeout=min(args.unbounded_timeout, 15), info=info, budget=min(args.budget, 60))

    def confirmed(res):
        return res.status == "DIFFERENT" and bool(res.ce and res.ce["replay"])

    c1, c2, c3 = {}, {}, {}
    survivors = killed = 0
    for seed in range(first, first + n):
        p = Gen(seed).program()
        # 1. the unsound original optimizer
        q = optimize(p, legacy=True)
        info = Info(p, q)
        r = run(p, q, info)
        c1[r.status] = c1.get(r.status, 0) + 1
        if r.status == "DIFFERENT" and not confirmed(r):
            bad.append(f"seed {seed}: DIFFERENT but the interpreter sees no difference on the counterexample")
        msg = cross_check(p, q, info, r, seed)
        if msg:
            bad.append(f"seed {seed} (first optimizer): {msg}")
        # 2. the current optimizer
        q = optimize(p)
        info = Info(p, q)
        r = run(p, q, info)
        c2[r.status] = c2.get(r.status, 0) + 1
        if r.status == "DIFFERENT":
            bad.append(f"seed {seed}: the current optimizer's output is reported DIFFERENT: {r.text}")
        msg = cross_check(p, q, info, r, seed)
        if msg:
            bad.append(f"seed {seed} (current optimizer): {msg}")
        # 3. mutants of the optimized program
        k_, s_ = mutation_run(p, q, [seed * 10 + j for j in range(3)], run, bad, f"seed {seed}", c3)
        killed += k_
        survivors += s_
        if (seed - first + 1) % 10 == 0:
            print(f"  ... {seed - first + 1}/{n} programs, {time.time() - t0:.0f} s", flush=True)
    print(f"1. first optimizer, {n} random programs (seeds {first}..{first + n - 1}): {c1}")
    print(f"2. current optimizer, same programs:          {c2}")
    print(f"3. mutants of the optimized programs:         {c3}  ({killed} rejected, {survivors} not rejected and not "
          f"contradicted by random runs or by brute force)")
    if n >= 10:                                 # a few programs prove nothing about the rate
        if c1.get("DIFFERENT", 0) < n // 5:
            bad.append(f"only {c1.get('DIFFERENT', 0)} of {n} programs of the first optimizer rejected (expected at least {n // 5})")
        if not killed:
            bad.append("the checker rejected no mutant")
    for b in bad:
        print("FAILED:", b)
    print("SELF-TEST " + ("FAILED" if bad else "PASSED") + f"  [{time.time() - t0:.0f} s]")
    return 1 if bad else 0



if __name__ == "__main__":
    sys.exit(main() or 0)
