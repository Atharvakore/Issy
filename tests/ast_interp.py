"""Interpreter for the Prog AST that Issy writes to ast.json (and for the Switch/Case/Default nodes that
flattener.py adds). Used to compare programs before and after the optimizer and the flattener without
a C compiler.

Semantics, as in the C printer of Issy (Synthesis.hs): PAssign is a parallel assignment, Declare makes a local
variable, Read draws new values for the input variables, Abort stops the run. Break and Continue always refer
to the innermost InfLoop, also when they occur inside a Switch (the AST has no "break out of a switch").
Input variables are the variables that are read but neither assigned nor declared; everything else that is
not declared is a global state variable and is what the comparison looks at (like read_inputs() does in C).
"""
import random


class Abort(Exception): pass
class Brk(Exception): pass
class Cont(Exception): pass
class Stop(Exception): pass   # read budget used up
class Fuel(Exception): pass   # too many steps without finishing (a loop that never reads)


def tag(n):
    return n.get("tag") if isinstance(n, dict) else None


def scan(ast):
    """-> (declared, assigned, used, sorts)"""
    declared, assigned, used, sorts = set(), set(), set(), {}

    def walk(n):
        if isinstance(n, list):
            for x in n:
                walk(x)
            return
        if not isinstance(n, dict):
            return
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


def input_names(ast):
    d, a, u, _ = scan(ast)
    return sorted(u - a - d)


def ev(t, env):
    tg = t["tag"]
    if tg == "Var":
        return env[t["contents"][0]]
    if tg == "Const":
        return t["contents"]["contents"]
    f, args = t["contents"]
    op = f["tag"]
    a = [ev(x, env) for x in args]
    if op == "FAdd": return sum(a)
    if op == "FMul":
        r = 1
        for x in a:
            r *= x
        return r
    if op == "FEq": return a[0] == a[1]
    if op == "FLt": return a[0] < a[1]
    if op == "FLte": return a[0] <= a[1]
    if op == "FAnd": return all(a)
    if op == "FOr": return any(a)
    if op == "FNot": return not a[0]
    if op == "FIte": return a[1] if a[0] else a[2]
    raise ValueError("unknown operator " + op)


def default(sort):
    return False if sort == "SBool" else 0


def run(ast, profile, seed, max_reads=120, inputs=None, fuel=200000):
    """Run once. -> (trace, end, globals) where trace is one (inputs, globals) pair per Read and
    end is "done" (read budget used up), "exit" (left the outermost loop), "abort" or "spins" (no progress)."""
    declared, assigned, used, sorts = scan(ast)
    if inputs is None:
        inputs = sorted(used - assigned - declared)
    for v in inputs:
        sorts.setdefault(v, "SInt")
    globs = sorted((assigned | used) - declared - set(inputs))
    rnd = random.Random(seed)
    env = {v: default(sorts.get(v, "SInt")) for v in assigned | used | declared | set(inputs)}
    trace = []
    left = [fuel]

    def draw(v, k):
        if sorts[v] == "SBool":
            return {"zero": False, "one": True, "alt": bool(k % 2)}.get(profile, rnd.random() < .5)
        if profile == "rand":
            return rnd.randint(-3, 3)
        return {"zero": 0, "one": 1, "min": -3, "max": 3, "alt": k % 2}[profile]

    def ex(p):
        left[0] -= 1
        if left[0] < 0:
            raise Fuel()
        t, c = tag(p), p.get("contents")
        if t == "Abort":
            raise Abort()
        if t == "Read":
            if len(trace) >= max_reads:
                raise Stop()
            ins = {v: draw(v, len(trace)) for v in inputs}
            env.update(ins)
            trace.append((tuple(ins[v] for v in inputs), tuple(env[v] for v in globs)))
        elif t == "Declare":
            env[c[0]] = default(c[1]["tag"])
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
            raise Brk()
        elif t == "Continue":
            raise Cont()
        elif t == "InfLoop":
            while True:
                try:
                    ex(c)
                except Cont:
                    continue
                except Brk:
                    break
        elif t == "Switch":
            val, body = ev(c[0], env), None
            for cs in c[1]:
                if tag(cs) == "Case" and cs["contents"][0] == val:
                    body = cs["contents"][1]
                    break
            if body is None:
                for cs in c[1]:
                    if tag(cs) == "Default":
                        body = cs["contents"]
                        break
            if body is not None:
                ex(body)
        else:
            raise ValueError("unknown statement " + str(t))

    try:
        ex(ast)
        end = "exit"
    except Abort:
        end = "abort"
    except Stop:
        end = "done"
    except Fuel:
        end = "spins"
    except (Brk, Cont):
        end = "stray-jump"
    return trace, end, globs


PROFILES = ["zero", "one", "min", "max", "alt", "rand", "rand", "rand"]


def compare(a, b, max_reads=120):
    """First difference between two programs over all input profiles (the same input values are given to
    both, also for inputs that one of them no longer uses), or None."""
    ins = input_names(a)
    for k, prof in enumerate(PROFILES):
        ta, ea, ga = run(a, prof, k, max_reads, ins)
        tb, eb, gb = run(b, prof, k, max_reads, ins)
        if ga != gb:
            return f"{prof}: observable variables differ {ga} vs {gb}"
        for i, (x, y) in enumerate(zip(ta, tb)):
            if x != y:
                return f"{prof}: read {i}: state {x[1]} vs {y[1]} (inputs {x[0]})"
        if len(ta) != len(tb) or ea != eb:
            return f"{prof}: first program ends {ea} after {len(ta)} reads, second ends {eb} after {len(tb)} reads"
    return None
