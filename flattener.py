import json
import copy
from typing import Any, Dict, List, Optional, Tuple, Set

AST = Dict[str, Any]


# ============================================================
# Basic AST helpers
# ============================================================

def tag(n: Any) -> Optional[str]:
    return n.get("tag") if isinstance(n, dict) else None


def node(tag_name: str, contents: Any = None) -> AST:
    out = {"tag": tag_name}
    if contents is not None:
        out["contents"] = contents
    return out


def sint() -> AST:
    return node("SInt")


def seq(stmts: List[AST]) -> AST:
    return node("Sequence", stmts)


def switch(expr: AST, cases: List[AST]) -> AST:
    return node("Switch", [expr, cases])


def case(value: int, body: AST) -> AST:
    return node("Case", [value, body])


def default_case(body: AST) -> AST:
    return node("Default", body)


def var(name: str) -> AST:
    return node("Var", [name, sint()])


def cint(value: int) -> AST:
    return node("Const", node("CInt", value))


def cond(condition: AST, body: AST) -> AST:
    return node("Cond", [condition, body])


def func(op: str, args: List[AST]) -> AST:
    return node("Func", [node(op), args])


def make_and(a: AST, b: AST) -> AST:
    return func("FAnd", [a, b])


def assign(name: str, expr: AST) -> AST:
    return node("PAssign", [[name, sint(), expr]])


def declare(name: str) -> AST:
    return node("Declare", [name, sint()])


def cont() -> AST:
    return node("Continue")


def brk() -> AST:
    return node("Break")


# ============================================================
# Expression matching
# ============================================================

def is_var(expr: AST, name: str) -> bool:
    return (
        tag(expr) == "Var"
        and isinstance(expr.get("contents"), list)
        and len(expr["contents"]) >= 1
        and expr["contents"][0] == name
    )


def is_cint(expr: AST) -> Optional[int]:
    if tag(expr) != "Const":
        return None

    c = expr.get("contents")

    if tag(c) != "CInt":
        return None

    return c.get("contents")


def extract_direct_pc_eq(expr: AST, pc_name: str) -> Optional[int]:
    """
    Matches:
        FEq(Var(pc), Const(CInt(k)))
    or:
        FEq(Const(CInt(k)), Var(pc))
    """

    if tag(expr) != "Func":
        return None

    contents = expr.get("contents")

    if not isinstance(contents, list) or len(contents) != 2:
        return None

    op, args = contents

    if tag(op) != "FEq":
        return None

    if not isinstance(args, list) or len(args) != 2:
        return None

    a, b = args

    if is_var(a, pc_name):
        return is_cint(b)

    if is_var(b, pc_name):
        return is_cint(a)

    return None


def flatten_and_parts(expr: AST) -> List[AST]:
    """
    Converts:
        FAnd(a, FAnd(b, c))
    into:
        [a, b, c]
    """

    if tag(expr) == "Func":
        contents = expr.get("contents")

        if isinstance(contents, list) and len(contents) == 2:
            op, args = contents

            if tag(op) == "FAnd" and isinstance(args, list) and len(args) == 2:
                return flatten_and_parts(args[0]) + flatten_and_parts(args[1])

    return [expr]


def rebuild_and(parts: List[AST]) -> Optional[AST]:
    if not parts:
        return None

    result = parts[0]

    for p in parts[1:]:
        result = make_and(result, p)

    return result


def extract_pc_state_from_condition(
    condition_expr: AST,
    pc_name: str
) -> Optional[Tuple[int, Optional[AST]]]:
    """
    Examples:

        prog_counter == 1
            -> (1, None)

        prog_counter == 0 && x == 0
            -> (0, x == 0)

    The remaining condition is kept inside the Case body.
    """

    parts = flatten_and_parts(condition_expr)

    found_state: Optional[int] = None
    remaining_parts: List[AST] = []

    for part in parts:
        state = extract_direct_pc_eq(part, pc_name)

        if state is not None and found_state is None:
            found_state = state
        else:
            remaining_parts.append(part)

    if found_state is None:
        return None

    return found_state, rebuild_and(remaining_parts)


# ============================================================
# Step 1: Convert Cond dispatcher to Switch/Case
# ============================================================

def append_body(case_map: Dict[int, List[AST]], state: int, body: AST) -> None:
    if state not in case_map:
        case_map[state] = []

    if tag(body) == "Sequence":
        case_map[state].extend(body.get("contents", []))
    else:
        case_map[state].append(body)


def convert_dispatcher_sequence_to_switch(
    sequence_node: AST,
    pc_name: str
) -> Optional[AST]:
    """
    Converts:

        InfLoop(
          Sequence([
            Cond(prog_counter == 0, body0),
            Cond(prog_counter == 1, body1),
            Cond(prog_counter == 0 && x == 0, body2),
            Abort
          ])
        )

    into:

        InfLoop(
          Switch(prog_counter, [
            Case(0, Sequence([body0, Cond(x == 0, body2)])),
            Case(1, Sequence([body1])),
            Default(Abort)
          ])
        )
    """

    if tag(sequence_node) != "Sequence":
        return None

    statements = sequence_node.get("contents", [])

    case_map: Dict[int, List[AST]] = {}
    default_body: List[AST] = []
    found_dispatcher_case = False

    for stmt in statements:
        t = tag(stmt)

        if t == "Cond":
            contents = stmt.get("contents")

            if not isinstance(contents, list) or len(contents) != 2:
                return None

            condition_expr, body = contents
            extracted = extract_pc_state_from_condition(condition_expr, pc_name)

            if extracted is None:
                return None

            state, remaining_condition = extracted

            if remaining_condition is None:
                append_body(case_map, state, body)
            else:
                append_body(case_map, state, cond(remaining_condition, body))

            found_dispatcher_case = True

        elif t == "Abort":
            default_body.append(stmt)

        else:
            return None

    if not found_dispatcher_case:
        return None

    cases: List[AST] = []

    for state in sorted(case_map.keys()):
        cases.append(case(state, seq(case_map[state])))

    if default_body:
        cases.append(default_case(seq(default_body)))

    return switch(var(pc_name), cases)


def convert_infloop_dispatchers_to_switch(
    ast: AST,
    pc_name: str = "prog_counter"
) -> AST:
    ast = copy.deepcopy(ast)

    def walk(n: Any) -> Any:
        if isinstance(n, list):
            return [walk(x) for x in n]

        if not isinstance(n, dict):
            return n

        t = tag(n)

        if t == "InfLoop":
            body = walk(n.get("contents"))
            converted = convert_dispatcher_sequence_to_switch(body, pc_name)

            if converted is not None:
                return node("InfLoop", converted)

            return node("InfLoop", body)

        return {k: walk(v) for k, v in n.items()}

    return walk(ast)


# ============================================================
# Step 2: Atomic-update pass
# ============================================================

def collect_assigned_variables(ast: Any, exclude_prefix: str = "__tmp_") -> Set[str]:
    """
    Finds every variable written by PAssign.
    """

    assigned: Set[str] = set()

    def walk(n: Any) -> None:
        if isinstance(n, list):
            for x in n:
                walk(x)
            return

        if not isinstance(n, dict):
            return

        if tag(n) == "PAssign":
            for assignment in n.get("contents", []):
                if isinstance(assignment, list) and len(assignment) >= 1:
                    name = assignment[0]
                    if isinstance(name, str) and not name.startswith(exclude_prefix):
                        assigned.add(name)

        for v in n.values():
            walk(v)

    walk(ast)
    return assigned


def tmp_name(name: str) -> str:
    return f"__tmp_{name}"


def make_snapshot(vars_to_temp: Set[str]) -> List[AST]:
    """
    __tmp_x = x
    __tmp_prog_counter = prog_counter
    """

    return [
        assign(tmp_name(v), var(v))
        for v in sorted(vars_to_temp)
    ]


def make_commit(vars_to_temp: Set[str]) -> List[AST]:
    """
    x = __tmp_x
    prog_counter = __tmp_prog_counter
    """

    return [
        assign(v, var(tmp_name(v)))
        for v in sorted(vars_to_temp)
    ]


def rewrite_passign_to_temp(stmt: AST, vars_to_temp: Set[str]) -> AST:
    """
    Rewrites:

        x = expr

    to:

        __tmp_x = expr

    RHS expressions are intentionally not rewritten.
    Conditions and RHS must read the old state.
    """

    new_assignments = []

    for assignment_item in stmt.get("contents", []):
        if not isinstance(assignment_item, list) or len(assignment_item) != 3:
            new_assignments.append(assignment_item)
            continue

        name, typ, expr = assignment_item

        if name in vars_to_temp:
            new_assignments.append([tmp_name(name), typ, expr])
        else:
            new_assignments.append([name, typ, expr])

    return node("PAssign", new_assignments)


def rewrite_sequence_atomic(
    statements: List[AST],
    vars_to_temp: Set[str]
) -> Tuple[List[AST], bool]:
    """
    Rewrites a sequence so that assignments write to temps.

    Returns:
        (rewritten_statements, definitely_terminal)

    definitely_terminal means the sequence certainly ends with Continue/Break/Abort.
    """

    out: List[AST] = []

    for stmt in statements:
        t = tag(stmt)

        if t == "PAssign":
            out.append(rewrite_passign_to_temp(stmt, vars_to_temp))

        elif t == "Cond":
            condition_expr, body = stmt["contents"]

            rewritten_body, _ = rewrite_stmt_atomic(body, vars_to_temp)

            if len(rewritten_body) == 1:
                new_body = rewritten_body[0]
            else:
                new_body = seq(rewritten_body)

            out.append(cond(condition_expr, new_body))

        elif t == "Continue":
            out.extend(make_commit(vars_to_temp))
            out.append(cont())
            return out, True

        elif t == "Break":
            out.extend(make_commit(vars_to_temp))
            out.append(brk())
            return out, True

        elif t == "Abort":
            out.append(stmt)
            return out, True

        elif t == "InfLoop":
            # Nested loops are processed separately by the global walk.
            out.append(apply_atomic_update_to_cases(stmt, vars_to_temp))

        elif t == "Switch":
            # Nested switch is processed separately.
            out.append(apply_atomic_update_to_cases(stmt, vars_to_temp))

        elif t == "Sequence":
            inner, terminal = rewrite_sequence_atomic(
                stmt.get("contents", []),
                vars_to_temp
            )
            out.append(seq(inner))
            if terminal:
                return out, True

        else:
            out.append(stmt)

    return out, False


def rewrite_stmt_atomic(
    stmt: AST,
    vars_to_temp: Set[str]
) -> Tuple[List[AST], bool]:
    if tag(stmt) == "Sequence":
        return rewrite_sequence_atomic(stmt.get("contents", []), vars_to_temp)

    return rewrite_sequence_atomic([stmt], vars_to_temp)


def atomic_rewrite_case_body(case_body: AST, vars_to_temp: Set[str]) -> AST:
    """
    Turns a Case body into:

        __tmp_x = x
        __tmp_prog_counter = prog_counter

        rewritten body, where:
            x = expr            becomes __tmp_x = expr
            prog_counter = expr becomes __tmp_prog_counter = expr

        x = __tmp_x
        prog_counter = __tmp_prog_counter
        Continue
    """

    if tag(case_body) == "Sequence":
        original_statements = case_body.get("contents", [])
    else:
        original_statements = [case_body]

    rewritten, terminal = rewrite_sequence_atomic(original_statements, vars_to_temp)

    final_body: List[AST] = []
    final_body.extend(make_snapshot(vars_to_temp))
    final_body.extend(rewritten)

    if not terminal:
        final_body.extend(make_commit(vars_to_temp))
        final_body.append(cont())

    return seq(final_body)


def apply_atomic_update_to_cases(ast: Any, vars_to_temp: Set[str]) -> Any:
    """
    Walks AST and rewrites every Case body atomically.
    """

    if isinstance(ast, list):
        return [apply_atomic_update_to_cases(x, vars_to_temp) for x in ast]

    if not isinstance(ast, dict):
        return ast

    t = tag(ast)

    if t == "Case":
        contents = ast.get("contents")

        if not isinstance(contents, list) or len(contents) != 2:
            return ast

        value, body = contents
        new_body = atomic_rewrite_case_body(body, vars_to_temp)
        return case(value, new_body)

    if t == "Default":
        # Usually Default is Abort. Do not add temp commits there.
        return ast

    return {
        k: apply_atomic_update_to_cases(v, vars_to_temp)
        for k, v in ast.items()
    }


def hoist_temp_declarations(ast: AST, vars_to_temp: Set[str]) -> AST:
    """
    Adds:
        Declare __tmp_x
        Declare __tmp_prog_counter

    near the top-level Sequence.
    """

    temp_decls = [
        declare(tmp_name(v))
        for v in sorted(vars_to_temp)
    ]

    if tag(ast) == "Sequence":
        contents = ast.get("contents", [])
        return seq(temp_decls + contents)

    return seq(temp_decls + [ast])


# ============================================================
# Full semantically safer transformation
# ============================================================

def semantically_equivalent_switch_transform(
    ast: AST,
    pc_name: str = "prog_counter"
) -> AST:
    """
    Main transformation.

    1. Converts existing Cond dispatcher to Switch/Case.
    2. Finds assigned variables.
    3. Adds temp variables.
    4. Rewrites each Case so assignments are atomic.
    """

    ast = copy.deepcopy(ast)

    # Step 1: switch-case conversion
    switched = convert_infloop_dispatchers_to_switch(ast, pc_name=pc_name)

    # Step 2: collect variables that must be atomically updated
    assigned_vars = collect_assigned_variables(switched)

    # Keep prog_counter included.
    assigned_vars.add(pc_name)

    # Step 3: atomic case rewrite
    atomic = apply_atomic_update_to_cases(switched, assigned_vars)

    # Step 4: hoist temp declarations once
    final_ast = hoist_temp_declarations(atomic, assigned_vars)

    return final_ast


def transform_file(
    input_path: str,
    output_path: str,
    pc_name: str = "prog_counter"
) -> None:
    with open(input_path, "r", encoding="utf-8") as f:
        ast = json.load(f)

    transformed = semantically_equivalent_switch_transform(
        ast,
        pc_name=pc_name
    )

    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(transformed, f, indent=2)


# ============================================================
# Run
# ============================================================

if __name__ == "__main__":
    transform_file(
        "ast_optimized.json",
        "ast_switch_atomic.json",
        pc_name="prog_counter"
    )