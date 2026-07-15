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


def make_or(a: AST, b: AST) -> AST:
    return func("FOr", [a, b])


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


def rebuild_and(parts: List[AST]) -> Optional[AST]:
    """Builds a left-associated FAnd expression from a list of expressions."""

    if not parts:
        return None

    result = parts[0]

    for p in parts[1:]:
        result = make_and(result, p)

    return result


def rebuild_or(parts: List[AST]) -> Optional[AST]:
    """Builds a left-associated FOr expression from a list of expressions."""

    if not parts:
        return None

    result = parts[0]

    for p in parts[1:]:
        result = make_or(result, p)

    return result


def condition_to_dnf_terms(
    expr: AST,
    max_terms: int = 64
) -> Optional[List[List[AST]]]:
    """
    Converts an expression made from FAnd/FOr into DNF-like terms.

    Each returned inner list is one conjunction. The outer list represents
    disjunction. Non-FAnd/FOr expressions are treated as atomic predicates.

    Examples:
        a && (b || c) -> [[a, b], [a, c]]
        a || b        -> [[a], [b]]

    The term limit prevents exponential expansion for very large expressions.
    If the limit is exceeded, the dispatcher conversion is skipped safely.
    """

    if tag(expr) != "Func":
        return [[expr]]

    contents = expr.get("contents")
    if not isinstance(contents, list) or len(contents) != 2:
        return [[expr]]

    op, args = contents
    op_tag = tag(op)

    if op_tag not in {"FAnd", "FOr"}:
        return [[expr]]

    if not isinstance(args, list) or len(args) != 2:
        return None

    left_terms = condition_to_dnf_terms(args[0], max_terms=max_terms)
    right_terms = condition_to_dnf_terms(args[1], max_terms=max_terms)

    if left_terms is None or right_terms is None:
        return None

    if op_tag == "FOr":
        combined = left_terms + right_terms
        return combined if len(combined) <= max_terms else None

    # FAnd distributes over FOr.
    if len(left_terms) * len(right_terms) > max_terms:
        return None

    return [
        left + right
        for left in left_terms
        for right in right_terms
    ]


def _deduplicate_exprs(expressions: List[AST]) -> List[AST]:
    """Removes structurally identical AST expressions while preserving order."""

    seen: Set[str] = set()
    result: List[AST] = []

    for expr in expressions:
        key = json.dumps(expr, sort_keys=True, separators=(",", ":"))
        if key not in seen:
            seen.add(key)
            result.append(expr)

    return result


def extract_pc_states_from_condition(
    condition_expr: AST,
    pc_name: str,
    max_dnf_terms: int = 64
) -> Optional[List[Tuple[int, Optional[AST]]]]:
    """
    Extracts one or more dispatcher states from a condition containing AND/OR.

    Supported examples:

        prog_counter == 1
            -> [(1, None)]

        prog_counter == 0 && x == 0
            -> [(0, x == 0)]

        prog_counter == 0 || prog_counter == 1
            -> [(0, None), (1, None)]

        (prog_counter == 0 || prog_counter == 1) && x == 0
            -> [(0, x == 0), (1, x == 0)]

        (prog_counter == 0 && x == 0) ||
        (prog_counter == 1 && y == 0)
            -> [(0, x == 0), (1, y == 0)]

    Every OR branch must contain a direct equality for the program counter.
    A condition such as `(prog_counter == 0) || x == 1` is rejected because
    the second branch is not tied to a dispatcher state and cannot be moved
    safely into one Switch case.
    """

    terms = condition_to_dnf_terms(condition_expr, max_terms=max_dnf_terms)
    if terms is None:
        return None

    residuals_by_state: Dict[int, List[Optional[AST]]] = {}

    for term in terms:
        states: List[int] = []
        remaining_parts: List[AST] = []

        for part in term:
            state = extract_direct_pc_eq(part, pc_name)
            if state is None:
                remaining_parts.append(part)
            else:
                states.append(state)

        # Each disjunct must identify a dispatcher state.
        if not states:
            return None

        distinct_states = set(states)

        # pc == 0 && pc == 1 is contradictory, so that DNF term is false.
        if len(distinct_states) > 1:
            continue

        state = states[0]
        residual = rebuild_and(remaining_parts)
        residuals_by_state.setdefault(state, []).append(residual)

    if not residuals_by_state:
        return None

    extracted: List[Tuple[int, Optional[AST]]] = []

    for state in sorted(residuals_by_state):
        residuals = residuals_by_state[state]

        # An unconditional branch for a state dominates all conditional ones.
        if any(residual is None for residual in residuals):
            extracted.append((state, None))
            continue

        conditional_residuals = _deduplicate_exprs([
            residual for residual in residuals if residual is not None
        ])
        extracted.append((state, rebuild_or(conditional_residuals)))

    return extracted


def extract_pc_state_from_condition(
    condition_expr: AST,
    pc_name: str
) -> Optional[Tuple[int, Optional[AST]]]:
    """
    Backward-compatible single-state wrapper.

    Returns a result only when the condition resolves to exactly one state.
    New dispatcher conversion code uses extract_pc_states_from_condition()
    so that OR expressions can map one condition to multiple cases.
    """

    extracted = extract_pc_states_from_condition(condition_expr, pc_name)

    if extracted is None or len(extracted) != 1:
        return None

    return extracted[0]



# ============================================================
# Step 0: Preprocessing - hoist declarations
# ============================================================


def fresh_lifted_name(name: str, used_names: Set[str]) -> str:
    """
    Returns a variable name that is unique among already-hoisted declarations.

    The first declaration keeps its original name whenever possible.
    Later declarations with the same name are renamed to avoid collisions
    after hoisting.
    """

    if name not in used_names:
        used_names.add(name)
        return name

    i = 1
    while True:
        candidate = f"{name}__lift_{i}"
        if candidate not in used_names:
            used_names.add(candidate)
            return candidate
        i += 1


def rewrite_names_with_env(n: Any, env: Dict[str, str]) -> Any:
    """
    Rewrites variable references and assignment targets according to env.

    Example:
        env = {"x": "x__lift_1"}

        Var("x")          -> Var("x__lift_1")
        PAssign("x", e)   -> PAssign("x__lift_1", e)

    Declarations are not handled here. They are handled by the preprocessing
    pass, because declarations must be removed from their original position
    and hoisted to the beginning.
    """

    if isinstance(n, list):
        return [rewrite_names_with_env(x, env) for x in n]

    if not isinstance(n, dict):
        return n

    t = tag(n)

    if t == "Var":
        contents = n.get("contents", [])
        if isinstance(contents, list) and len(contents) >= 1:
            old_name = contents[0]
            if isinstance(old_name, str) and old_name in env:
                new_contents = list(contents)
                new_contents[0] = env[old_name]
                return node("Var", new_contents)
        return n

    if t == "PAssign":
        rewritten_assignments = []
        for assignment_item in n.get("contents", []):
            if not isinstance(assignment_item, list) or len(assignment_item) != 3:
                rewritten_assignments.append(
                    rewrite_names_with_env(assignment_item, env)
                )
                continue

            old_name, typ, expr = assignment_item
            new_name = env.get(old_name, old_name) if isinstance(old_name, str) else old_name
            rewritten_assignments.append([
                new_name,
                rewrite_names_with_env(typ, env),
                rewrite_names_with_env(expr, env)
            ])

        return node("PAssign", rewritten_assignments)

    return {
        k: rewrite_names_with_env(v, env)
        for k, v in n.items()
    }


def preprocess_sequence_declarations(
    statements: List[AST],
    env: Dict[str, str],
    used_names: Set[str],
    hoisted_declarations: List[AST]
) -> List[AST]:
    """
    Processes a Sequence in source order.

    Any Declare node is removed from its original position and added to
    hoisted_declarations. If hoisting would create a name collision, the
    declaration is renamed and all later references in the same lexical scope
    are rewritten.
    """

    current_env = dict(env)
    rewritten_statements: List[AST] = []

    for stmt in statements:
        if tag(stmt) == "Declare":
            contents = stmt.get("contents", [])
            if not isinstance(contents, list) or len(contents) != 2:
                # Keep malformed declarations untouched.
                rewritten_statements.append(rewrite_names_with_env(stmt, current_env))
                continue

            old_name, typ = contents
            if not isinstance(old_name, str):
                rewritten_statements.append(rewrite_names_with_env(stmt, current_env))
                continue

            new_name = fresh_lifted_name(old_name, used_names)
            current_env[old_name] = new_name
            hoisted_declarations.append(node("Declare", [new_name, typ]))
            continue

        rewritten_statements.append(
            preprocess_declarations_walk(
                rewrite_names_with_env(stmt, current_env),
                current_env,
                used_names,
                hoisted_declarations
            )
        )

    return rewritten_statements


def preprocess_declarations_walk(
    n: Any,
    env: Dict[str, str],
    used_names: Set[str],
    hoisted_declarations: List[AST]
) -> Any:
    """
    Recursively removes Declare nodes from nested Sequences and hoists them.
    """

    if isinstance(n, list):
        return [
            preprocess_declarations_walk(x, env, used_names, hoisted_declarations)
            for x in n
        ]

    if not isinstance(n, dict):
        return n

    t = tag(n)

    if t == "Sequence":
        # A sequence is treated as a lexical scope. Declarations inside it
        # affect only later statements in that sequence and nested children.
        rewritten_contents = preprocess_sequence_declarations(
            n.get("contents", []),
            dict(env),
            used_names,
            hoisted_declarations
        )
        return seq(rewritten_contents)

    # Any Declare outside a Sequence is unusual for this AST. Hoist it too.
    if t == "Declare":
        contents = n.get("contents", [])
        if isinstance(contents, list) and len(contents) == 2 and isinstance(contents[0], str):
            old_name, typ = contents
            new_name = fresh_lifted_name(old_name, used_names)
            hoisted_declarations.append(node("Declare", [new_name, typ]))
            return seq([])
        return n

    return {
        k: preprocess_declarations_walk(v, env, used_names, hoisted_declarations)
        for k, v in n.items()
    }


def preprocess_declarations(ast: AST) -> AST:
    """
    Paper-style declaration preprocessing for this JSON AST.

    It moves Declare nodes to the beginning of the top-level Sequence and
    removes them from their original positions. If multiple declarations with
    the same name would collide after hoisting, later declarations are renamed
    and references in the corresponding lexical scope are rewritten.

    Note: this AST has Declare(name, type) without initialization. Therefore,
    there is no declaration initializer to split into an assignment.
    """

    ast = copy.deepcopy(ast)
    hoisted_declarations: List[AST] = []
    used_names: Set[str] = set()

    rewritten_ast = preprocess_declarations_walk(
        ast,
        env={},
        used_names=used_names,
        hoisted_declarations=hoisted_declarations
    )

    if tag(rewritten_ast) == "Sequence":
        return seq(hoisted_declarations + rewritten_ast.get("contents", []))

    return seq(hoisted_declarations + [rewritten_ast])

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
            Cond(prog_counter == 1 || prog_counter == 2, shared_body),
            Abort
          ])
        )

    into:

        InfLoop(
          Switch(prog_counter, [
            Case(0, Sequence([body0, Cond(x == 0, body2)])),
            Case(1, Sequence([body1, shared_body])),
            Case(2, Sequence([shared_body])),
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
            extracted_states = extract_pc_states_from_condition(
                condition_expr,
                pc_name
            )

            if extracted_states is None:
                return None

            for state, remaining_condition in extracted_states:
                # One OR condition may map the same body to several states.
                # Copy the body so generated Case nodes do not share an AST object.
                body_for_state = copy.deepcopy(body)

                if remaining_condition is None:
                    append_body(case_map, state, body_for_state)
                else:
                    append_body(
                        case_map,
                        state,
                        cond(copy.deepcopy(remaining_condition), body_for_state)
                    )

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

    # Step 0: declaration preprocessing
    preprocessed = preprocess_declarations(ast)

    # Step 1: switch-case conversion
    switched = convert_infloop_dispatchers_to_switch(preprocessed, pc_name=pc_name)

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