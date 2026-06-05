import json
from egglog import EGraph, rewrite


def json_to_runtime_expr(node, egraph):
    tag = node["tag"]
    contents = node.get("contents")


    def wrap_literal(val):
        return egraph.let("Literal", val)


    if tag == "Declare":
        var_expr = wrap_literal(contents[0])
        sort_expr = wrap_literal(contents[1]["tag"])
        return egraph.let("Declare", [var_expr, sort_expr])


    if tag == "PAssign":
        assigns = []
        for v, s, t in contents:
            var_expr = wrap_literal(v)
            sort_expr = wrap_literal(s["tag"])
            term_expr = json_to_runtime_expr(t, egraph)
            assigns.append(egraph.let("Assign", [var_expr, sort_expr, term_expr]))

    if tag == "Sequence":
        children = [json_to_runtime_expr(c, egraph) for c in contents]
        return egraph.let("Sequence", children)

    if tag == "InfLoop":
        return egraph.let("InfLoop", json_to_runtime_expr(contents, egraph))


    if tag == "Cond":
        cond_expr, body_expr = contents
        return egraph.let("Cond", [json_to_runtime_expr(cond_expr, egraph),
                                   json_to_runtime_expr(body_expr, egraph)])


    if tag == "Read": return egraph.let("Read")
    if tag == "Break": return egraph.let("Break")
    if tag == "Continue": return egraph.let("Continue")
    if tag == "Abort": return egraph.let("Abort")


    if tag == "Func":
        func_name = contents[0]["tag"]
        args_exprs = [json_to_runtime_expr(arg, egraph) for arg in contents[1]]
        return egraph.let(func_name, args_exprs)

    # Constants
    if tag in ("Const", "CInt"):
        value = contents["contents"] if isinstance(contents, dict) else contents
        return wrap_literal(value)

    # Variables
    if tag == "Var":
        return wrap_literal(contents[0])

    raise NotImplementedError(f"Unknown tag: {tag}")

# === Load the uploaded JSON AST file ===
AST_FILE = "ast.json"
with open(AST_FILE, "r") as f:
    ast_json = json.load(f)

# === Create EGraph ===
egraph = EGraph()

# Convert JSON AST → properly wrapped RuntimeExpr tree
root_expr = json_to_runtime_expr(ast_json, egraph)

# === Example rewrite rules (can extend for loops, assignments, etc.) ===
@egraph.register
def add_zero_rule(a):
    yield rewrite(a + 0).to(a)

@egraph.register
def mul_one_rule(a):
    yield rewrite(a * 1).to(a)

egraph.run()

# === Extract optimized AST ===
optimized_expr = egraph.extract(root_expr)

# === Serialize optimized AST for Haskell / C code generation ===
with open("optimized_ast.json", "w") as f:
    json.dump(optimized_expr, f, indent=2)

print("Optimized AST written to optimized_ast.json")