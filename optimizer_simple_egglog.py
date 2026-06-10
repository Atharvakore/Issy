#!/usr/bin/env python3
"""
optimizer_simple_egglog.py

Simple no-CLI pipeline:

    Haskell JSON AST
        -> Python dataclass AST
        -> optimize embedded Term nodes with Egglog
        -> Python dataclass AST
        -> same Haskell JSON format

Put your Haskell JSON output in ast.json and run:

    python3 optimizer_simple_egglog.py

Output:

    ast_optimized.json

This version is inspired by the pycparser/Egglog example, but works directly on
your Haskell JSON AST format instead of C code.
"""

from __future__ import annotations

import ast as py_ast
import json
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from egglog import *


# ============================================================
# 0. Simple script configuration
# ============================================================

# === Load the uploaded JSON AST file ===
AST_FILE = "ast.json"

# === Write optimized AST back in the same JSON format ===
OUTPUT_FILE = "ast_optimized.json"

# Useful while debugging. If True, prints every changed term.
PRINT_CHANGED_TERMS = False

# Number of Egglog iterations per expression.
EGGLOG_ITERATIONS = 10


# ============================================================
# 1. Python AST dataclasses
# ============================================================

@dataclass(frozen=True)
class Sort:
    pass


@dataclass(frozen=True)
class SInt(Sort):
    pass


@dataclass(frozen=True)
class SBool(Sort):
    pass


@dataclass(frozen=True)
class Constant:
    pass


@dataclass(frozen=True)
class CInt(Constant):
    value: int


@dataclass(frozen=True)
class CBool(Constant):
    value: bool


@dataclass(frozen=True)
class Function:
    name: str


@dataclass(frozen=True)
class Term:
    pass


@dataclass(frozen=True)
class Var(Term):
    name: str
    sort: Sort


@dataclass(frozen=True)
class Const(Term):
    const: Constant


@dataclass(frozen=True)
class Func(Term):
    function: Function
    args: List[Term]


@dataclass(frozen=True)
class Prog:
    pass


@dataclass(frozen=True)
class Abort(Prog):
    pass


@dataclass(frozen=True)
class Read(Prog):
    pass


@dataclass(frozen=True)
class Break(Prog):
    pass


@dataclass(frozen=True)
class Continue(Prog):
    pass


@dataclass(frozen=True)
class InfLoop(Prog):
    body: Prog


@dataclass(frozen=True)
class Declare(Prog):
    symbol: str
    sort: Sort


@dataclass(frozen=True)
class Cond(Prog):
    condition: Term
    body: Prog


@dataclass(frozen=True)
class Sequence(Prog):
    programs: List[Prog]


@dataclass(frozen=True)
class PAssign(Prog):
    assigns: List[Tuple[str, Sort, Term]]


# ============================================================
# 2. JSON -> Python AST parser
#    Matches your actual Haskell output format.
# ============================================================

def expect_dict(node: Any, context: str) -> dict:
    if not isinstance(node, dict):
        raise TypeError(f"Expected object for {context}, got {type(node).__name__}: {node!r}")
    return node


def parse_sort(node: Any) -> Sort:
    node = expect_dict(node, "Sort")
    tag = node.get("tag")

    if tag == "SInt":
        return SInt()
    if tag == "SBool":
        return SBool()

    raise ValueError(f"Unknown Sort tag: {tag!r}")


def parse_constant(node: Any) -> Constant:
    node = expect_dict(node, "Constant")
    tag = node.get("tag")

    if tag == "CInt":
        return CInt(int(node["contents"]))
    if tag == "CBool":
        return CBool(bool(node["contents"]))

    raise ValueError(f"Unknown Constant tag: {tag!r}")


def parse_function(node: Any) -> Function:
    node = expect_dict(node, "Function")
    tag = node.get("tag")
    if not isinstance(tag, str):
        raise ValueError(f"Function must contain string tag, got: {node!r}")
    return Function(tag)


def parse_term(node: Any) -> Term:
    node = expect_dict(node, "Term")
    tag = node.get("tag")

    if tag == "Var":
        contents = node["contents"]
        if not (isinstance(contents, list) and len(contents) == 2):
            raise ValueError(f"Var expects [symbol, sort], got: {contents!r}")
        name, sort_json = contents
        return Var(str(name), parse_sort(sort_json))

    if tag == "Const":
        return Const(parse_constant(node["contents"]))

    if tag == "Func":
        contents = node["contents"]
        if not (isinstance(contents, list) and len(contents) == 2):
            raise ValueError(f"Func expects [function, args], got: {contents!r}")
        function_json, args_json = contents
        if not isinstance(args_json, list):
            raise ValueError(f"Func args must be a list, got: {args_json!r}")
        return Func(parse_function(function_json), [parse_term(arg) for arg in args_json])

    raise ValueError(f"Unknown Term tag: {tag!r}")


def parse_prog(node: Any) -> Prog:
    node = expect_dict(node, "Prog")
    tag = node.get("tag")

    if tag == "Abort":
        return Abort()
    if tag == "Read":
        return Read()
    if tag == "Break":
        return Break()
    if tag == "Continue":
        return Continue()

    if tag == "InfLoop":
        return InfLoop(parse_prog(node["contents"]))

    if tag == "Declare":
        contents = node["contents"]
        if not (isinstance(contents, list) and len(contents) == 2):
            raise ValueError(f"Declare expects [symbol, sort], got: {contents!r}")
        symbol, sort_json = contents
        return Declare(str(symbol), parse_sort(sort_json))

    if tag == "Cond":
        contents = node["contents"]
        if not (isinstance(contents, list) and len(contents) == 2):
            raise ValueError(f"Cond expects [term, prog], got: {contents!r}")
        condition_json, body_json = contents
        return Cond(parse_term(condition_json), parse_prog(body_json))

    if tag == "Sequence":
        contents = node.get("contents", [])
        if not isinstance(contents, list):
            raise ValueError(f"Sequence contents must be list, got: {contents!r}")
        return Sequence([parse_prog(p) for p in contents])

    if tag == "PAssign":
        contents = node.get("contents", [])
        if not isinstance(contents, list):
            raise ValueError(f"PAssign contents must be list, got: {contents!r}")

        assigns: List[Tuple[str, Sort, Term]] = []
        for item in contents:
            if not (isinstance(item, list) and len(item) == 3):
                raise ValueError(f"PAssign item expects [symbol, sort, term], got: {item!r}")
            symbol, sort_json, term_json = item
            assigns.append((str(symbol), parse_sort(sort_json), parse_term(term_json)))
        return PAssign(assigns)

    raise ValueError(f"Unknown Prog tag: {tag!r}")


# ============================================================
# 3. Python AST -> JSON serializer
#    Outputs the same shape as your Haskell input.
# ============================================================

def sort_to_json(sort: Sort) -> dict:
    if isinstance(sort, SInt):
        return {"tag": "SInt"}
    if isinstance(sort, SBool):
        return {"tag": "SBool"}
    raise ValueError(f"Unknown Sort object: {sort!r}")


def constant_to_json(const: Constant) -> dict:
    if isinstance(const, CInt):
        return {"tag": "CInt", "contents": const.value}
    if isinstance(const, CBool):
        return {"tag": "CBool", "contents": const.value}
    raise ValueError(f"Unknown Constant object: {const!r}")


def function_to_json(function: Function) -> dict:
    return {"tag": function.name}


def term_to_json(term: Term) -> dict:
    if isinstance(term, Var):
        return {
            "tag": "Var",
            "contents": [term.name, sort_to_json(term.sort)],
        }

    if isinstance(term, Const):
        return {
            "tag": "Const",
            "contents": constant_to_json(term.const),
        }

    if isinstance(term, Func):
        return {
            "tag": "Func",
            "contents": [
                function_to_json(term.function),
                [term_to_json(arg) for arg in term.args],
            ],
        }

    raise ValueError(f"Unknown Term object: {term!r}")


def prog_to_json(prog: Prog) -> dict:
    if isinstance(prog, Abort):
        return {"tag": "Abort"}
    if isinstance(prog, Read):
        return {"tag": "Read"}
    if isinstance(prog, Break):
        return {"tag": "Break"}
    if isinstance(prog, Continue):
        return {"tag": "Continue"}

    if isinstance(prog, InfLoop):
        return {
            "tag": "InfLoop",
            "contents": prog_to_json(prog.body),
        }

    if isinstance(prog, Declare):
        return {
            "tag": "Declare",
            "contents": [prog.symbol, sort_to_json(prog.sort)],
        }

    if isinstance(prog, Cond):
        return {
            "tag": "Cond",
            "contents": [term_to_json(prog.condition), prog_to_json(prog.body)],
        }

    if isinstance(prog, Sequence):
        return {
            "tag": "Sequence",
            "contents": [prog_to_json(p) for p in prog.programs],
        }

    if isinstance(prog, PAssign):
        return {
            "tag": "PAssign",
            "contents": [
                [symbol, sort_to_json(sort), term_to_json(term)]
                for symbol, sort, term in prog.assigns
            ],
        }

    raise ValueError(f"Unknown Prog object: {prog!r}")


# ============================================================
# 4. Egglog term language
# ============================================================

class EggTerm(Expr):
    @classmethod
    def Var(cls, name: StringLike) -> "EggTerm": ...

    @classmethod
    def Num(cls, value: i64Like) -> "EggTerm": ...

    @classmethod
    def Bool(cls, value: BoolLike) -> "EggTerm": ...

    @classmethod
    def Add(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Sub(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Mul(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Neg(cls, value: "EggTerm") -> "EggTerm": ...

    @classmethod
    def And(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Or(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Not(cls, value: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Eq(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Lt(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Le(cls, left: "EggTerm", right: "EggTerm") -> "EggTerm": ...

    @classmethod
    def Ite(cls, cond: "EggTerm", then_value: "EggTerm", else_value: "EggTerm") -> "EggTerm": ...


x, y, z = vars_("x y z", EggTerm)


# ============================================================
# 5. Egglog rewrite rules
#    Type-safety note:
#    - Bool rules use EggTerm.Bool(True/False)
#    - Integer rules use EggTerm.Num(...)
#    - Do NOT rewrite integer ITEs like cond ? 1 : 0 into booleans
#      unless you also track the expected sort. This simple optimizer does not.
# ============================================================

rules = ruleset(
    # ----------------------------
    # Addition
    # ----------------------------
    rewrite(EggTerm.Add(x, EggTerm.Num(0))).to(x),
    rewrite(EggTerm.Add(EggTerm.Num(0), x)).to(x),

    rewrite(EggTerm.Add(EggTerm.Num(-1), x)).to(EggTerm.Sub(x, EggTerm.Num(1))),
    rewrite(EggTerm.Add(x, EggTerm.Num(-1))).to(EggTerm.Sub(x, EggTerm.Num(1))),

    rewrite(EggTerm.Add(x, EggTerm.Neg(y))).to(EggTerm.Sub(x, y)),
    rewrite(EggTerm.Add(EggTerm.Neg(x), y)).to(EggTerm.Sub(y, x)),

    rewrite(EggTerm.Add(x, x)).to(EggTerm.Mul(EggTerm.Num(2), x)),

    # x + (-x) -> 0
    rewrite(EggTerm.Add(EggTerm.Neg(x), x)).to(EggTerm.Num(0)),
    rewrite(EggTerm.Add(x, EggTerm.Neg(x))).to(EggTerm.Num(0)),

    # ----------------------------
    # Subtraction
    # ----------------------------
    rewrite(EggTerm.Sub(x, EggTerm.Num(0))).to(x),
    rewrite(EggTerm.Sub(EggTerm.Num(0), x)).to(EggTerm.Neg(x)),
    rewrite(EggTerm.Sub(x, x)).to(EggTerm.Num(0)),
    rewrite(EggTerm.Sub(x, EggTerm.Neg(y))).to(EggTerm.Add(x, y)),
    rewrite(EggTerm.Sub(EggTerm.Neg(x), y)).to(EggTerm.Neg(EggTerm.Add(x, y))),

    # Cancellation
    rewrite(EggTerm.Add(EggTerm.Sub(x, y), y)).to(x),
    rewrite(EggTerm.Add(y, EggTerm.Sub(x, y))).to(x),
    rewrite(EggTerm.Sub(EggTerm.Add(x, y), y)).to(x),
    rewrite(EggTerm.Sub(EggTerm.Add(x, y), x)).to(y),
    rewrite(EggTerm.Sub(EggTerm.Add(y, x), x)).to(y),
    rewrite(EggTerm.Sub(x, EggTerm.Add(x, y))).to(EggTerm.Neg(y)),
    rewrite(EggTerm.Sub(x, EggTerm.Add(y, x))).to(EggTerm.Neg(y)),

    # ----------------------------
    # Negation
    # ----------------------------
    rewrite(EggTerm.Neg(EggTerm.Num(0))).to(EggTerm.Num(0)),
    rewrite(EggTerm.Neg(EggTerm.Num(1))).to(EggTerm.Num(-1)),
    rewrite(EggTerm.Neg(EggTerm.Num(-1))).to(EggTerm.Num(1)),
    rewrite(EggTerm.Neg(EggTerm.Neg(x))).to(x),
    rewrite(EggTerm.Neg(EggTerm.Sub(x, y))).to(EggTerm.Sub(y, x)),
    rewrite(EggTerm.Neg(EggTerm.Add(x, y))).to(EggTerm.Add(EggTerm.Neg(x), EggTerm.Neg(y))),
    rewrite(EggTerm.Neg(EggTerm.Mul(EggTerm.Num(-1), x))).to(x),
    rewrite(EggTerm.Neg(EggTerm.Mul(x, EggTerm.Num(-1)))).to(x),

    # ----------------------------
    # Multiplication
    # ----------------------------
    rewrite(EggTerm.Mul(x, EggTerm.Num(0))).to(EggTerm.Num(0)),
    rewrite(EggTerm.Mul(EggTerm.Num(0), x)).to(EggTerm.Num(0)),
    rewrite(EggTerm.Mul(x, EggTerm.Num(1))).to(x),
    rewrite(EggTerm.Mul(EggTerm.Num(1), x)).to(x),

    rewrite(EggTerm.Mul(x, EggTerm.Num(-1))).to(EggTerm.Neg(x)),
    rewrite(EggTerm.Mul(EggTerm.Num(-1), x)).to(EggTerm.Neg(x)),

    rewrite(EggTerm.Mul(EggTerm.Neg(x), EggTerm.Num(-1))).to(x),
    rewrite(EggTerm.Mul(EggTerm.Num(-1), EggTerm.Neg(x))).to(x),
    rewrite(EggTerm.Mul(EggTerm.Neg(x), EggTerm.Neg(y))).to(EggTerm.Mul(x, y)),

    # Extra constant cleanup
    rewrite(EggTerm.Mul(EggTerm.Num(2), EggTerm.Num(0))).to(EggTerm.Num(0)),
    rewrite(EggTerm.Mul(EggTerm.Num(-1), EggTerm.Num(0))).to(EggTerm.Num(0)),
    rewrite(EggTerm.Mul(EggTerm.Num(0), EggTerm.Num(-1))).to(EggTerm.Num(0)),

    # ----------------------------
    # Generated-program patterns from Issy/C-style output
    # ----------------------------
    # init_x + (-1 * x) -> init_x - x
    rewrite(EggTerm.Add(x, EggTerm.Mul(EggTerm.Num(-1), y))).to(EggTerm.Sub(x, y)),

    # -1 * (-1 + (-1 * x)) -> x + 1
    rewrite(
        EggTerm.Mul(
            EggTerm.Num(-1),
            EggTerm.Add(EggTerm.Num(-1), EggTerm.Mul(EggTerm.Num(-1), x)),
        )
    ).to(EggTerm.Add(x, EggTerm.Num(1))),

    # -1 * (1 + (-1 * x)) -> x - 1
    rewrite(
        EggTerm.Mul(
            EggTerm.Num(-1),
            EggTerm.Add(EggTerm.Num(1), EggTerm.Mul(EggTerm.Num(-1), x)),
        )
    ).to(EggTerm.Sub(x, EggTerm.Num(1))),

    # General Issy negation cleanup
    rewrite(EggTerm.Mul(EggTerm.Num(-1), EggTerm.Add(x, y))).to(
        EggTerm.Add(EggTerm.Neg(x), EggTerm.Neg(y))
    ),
    rewrite(EggTerm.Mul(EggTerm.Num(-1), EggTerm.Sub(x, y))).to(EggTerm.Sub(y, x)),
    rewrite(EggTerm.Mul(EggTerm.Num(-1), EggTerm.Mul(EggTerm.Num(-1), x))).to(x),
    rewrite(EggTerm.Mul(EggTerm.Mul(EggTerm.Num(-1), x), EggTerm.Num(-1))).to(x),

    # ----------------------------
    # Boolean AND
    # ----------------------------
    rewrite(EggTerm.And(x, EggTerm.Bool(True))).to(x),
    rewrite(EggTerm.And(EggTerm.Bool(True), x)).to(x),
    rewrite(EggTerm.And(x, EggTerm.Bool(False))).to(EggTerm.Bool(False)),
    rewrite(EggTerm.And(EggTerm.Bool(False), x)).to(EggTerm.Bool(False)),
    rewrite(EggTerm.And(x, x)).to(x),

    # ----------------------------
    # Boolean OR
    # ----------------------------
    rewrite(EggTerm.Or(x, EggTerm.Bool(False))).to(x),
    rewrite(EggTerm.Or(EggTerm.Bool(False), x)).to(x),
    rewrite(EggTerm.Or(x, EggTerm.Bool(True))).to(EggTerm.Bool(True)),
    rewrite(EggTerm.Or(EggTerm.Bool(True), x)).to(EggTerm.Bool(True)),
    rewrite(EggTerm.Or(x, x)).to(x),

    # ----------------------------
    # Boolean NOT + De Morgan
    # ----------------------------
    rewrite(EggTerm.Not(EggTerm.Not(x))).to(x),
    rewrite(EggTerm.Not(EggTerm.Bool(False))).to(EggTerm.Bool(True)),
    rewrite(EggTerm.Not(EggTerm.Bool(True))).to(EggTerm.Bool(False)),
    rewrite(EggTerm.Not(EggTerm.And(x, y))).to(EggTerm.Or(EggTerm.Not(x), EggTerm.Not(y))),
    rewrite(EggTerm.Not(EggTerm.Or(x, y))).to(EggTerm.And(EggTerm.Not(x), EggTerm.Not(y))),
    rewrite(EggTerm.Not(EggTerm.Le(x, y))).to(EggTerm.Lt(y, x)),
    rewrite(EggTerm.Not(EggTerm.Lt(x, y))).to(EggTerm.Le(y, x)),

    # ----------------------------
    # Boolean absorption
    # ----------------------------
    rewrite(EggTerm.And(x, EggTerm.Or(x, y))).to(x),
    rewrite(EggTerm.And(EggTerm.Or(x, y), x)).to(x),
    rewrite(EggTerm.Or(x, EggTerm.And(x, y))).to(x),
    rewrite(EggTerm.Or(EggTerm.And(x, y), x)).to(x),

    # ----------------------------
    # Boolean contradiction / tautology
    # ----------------------------
    rewrite(EggTerm.And(x, EggTerm.Not(x))).to(EggTerm.Bool(False)),
    rewrite(EggTerm.And(EggTerm.Not(x), x)).to(EggTerm.Bool(False)),
    rewrite(EggTerm.Or(x, EggTerm.Not(x))).to(EggTerm.Bool(True)),
    rewrite(EggTerm.Or(EggTerm.Not(x), x)).to(EggTerm.Bool(True)),

    # ----------------------------
    # Comparisons
    # ----------------------------
    rewrite(EggTerm.Eq(x, x)).to(EggTerm.Bool(True)),
    rewrite(EggTerm.Lt(x, x)).to(EggTerm.Bool(False)),
    rewrite(EggTerm.Le(x, x)).to(EggTerm.Bool(True)),

    # Comparison normalization for arithmetic-difference guards
    rewrite(EggTerm.Lt(EggTerm.Num(0), EggTerm.Sub(x, y))).to(EggTerm.Lt(y, x)),
    rewrite(EggTerm.Le(EggTerm.Sub(x, y), EggTerm.Num(0))).to(EggTerm.Le(x, y)),
    rewrite(EggTerm.Lt(EggTerm.Sub(x, y), EggTerm.Num(0))).to(EggTerm.Lt(x, y)),

    # ----------------------------
    # Equality boolean simplification
    # Only safe when FEq is used with boolean operands.
    # ----------------------------
    rewrite(EggTerm.Eq(EggTerm.Bool(True), x)).to(x),
    rewrite(EggTerm.Eq(x, EggTerm.Bool(True))).to(x),
    rewrite(EggTerm.Eq(EggTerm.Bool(False), x)).to(EggTerm.Not(x)),
    rewrite(EggTerm.Eq(x, EggTerm.Bool(False))).to(EggTerm.Not(x)),

    # ----------------------------
    # ITE simplification
    # ----------------------------
    rewrite(EggTerm.Ite(EggTerm.Bool(True), x, y)).to(x),
    rewrite(EggTerm.Ite(EggTerm.Bool(False), x, y)).to(y),
    rewrite(EggTerm.Ite(x, y, y)).to(y),

    # Boolean ITE simplification only.
    # Do not add Num(1)/Num(0) -> Bool rewrites without expected-sort tracking.
    rewrite(EggTerm.Ite(x, EggTerm.Bool(True), EggTerm.Bool(False))).to(x),
    rewrite(EggTerm.Ite(x, EggTerm.Bool(False), EggTerm.Bool(True))).to(EggTerm.Not(x)),
)


# ============================================================
# 6. Term AST <-> Egglog conversion
# ============================================================

def make_func(name: str, args: List[Term]) -> Term:
    return Func(Function(name), args)


def int_const(value: int) -> Const:
    return Const(CInt(value))


def bool_const(value: bool) -> Const:
    return Const(CBool(value))


def collect_var_sorts(term: Term, out: Optional[Dict[str, Sort]] = None) -> Dict[str, Sort]:
    if out is None:
        out = {}

    if isinstance(term, Var):
        out.setdefault(term.name, term.sort)
        return out

    if isinstance(term, Func):
        for arg in term.args:
            collect_var_sorts(arg, out)

    return out


def build_binary_egg(method, args: List[Any]) -> Any:
    if len(args) == 0:
        raise ValueError("Cannot build binary Egglog expression from empty args")
    if len(args) == 1:
        return args[0]

    result = args[-1]
    for arg in reversed(args[:-1]):
        result = method(arg, result)
    return result


def term_ast_to_egg(term: Term) -> Any:
    if isinstance(term, Var):
        return EggTerm.Var(term.name)

    if isinstance(term, Const):
        if isinstance(term.const, CInt):
            return EggTerm.Num(term.const.value)
        if isinstance(term.const, CBool):
            return EggTerm.Bool(term.const.value)

    if isinstance(term, Func):
        name = term.function.name
        args = [term_ast_to_egg(arg) for arg in term.args]

        if name == "FAdd":
            return build_binary_egg(EggTerm.Add, args)
        if name == "FSub":
            return EggTerm.Sub(args[0], args[1])
        if name == "FMul":
            return build_binary_egg(EggTerm.Mul, args)
        if name == "FAnd":
            return build_binary_egg(EggTerm.And, args)
        if name == "FOr":
            return build_binary_egg(EggTerm.Or, args)
        if name == "FNot":
            return EggTerm.Not(args[0])
        if name == "FEq":
            return EggTerm.Eq(args[0], args[1])
        if name == "FLt":
            return EggTerm.Lt(args[0], args[1])
        if name == "FLte":
            return EggTerm.Le(args[0], args[1])
        if name == "FIte":
            return EggTerm.Ite(args[0], args[1], args[2])

        raise ValueError(f"Unsupported function for Egglog: {name}")

    raise ValueError(f"Unsupported term AST: {term!r}")


# ============================================================
# 7. Egglog extracted repr -> Term AST
# ============================================================

def _py_ast_int(node: py_ast.AST) -> int:
    if isinstance(node, py_ast.Constant):
        return int(node.value)

    if isinstance(node, py_ast.UnaryOp) and isinstance(node.op, py_ast.USub):
        return -_py_ast_int(node.operand)

    raise ValueError(f"Unsupported integer AST: {py_ast.dump(node)}")


def _py_ast_bool(node: py_ast.AST) -> bool:
    if isinstance(node, py_ast.Constant) and isinstance(node.value, bool):
        return node.value
    raise ValueError(f"Unsupported bool AST: {py_ast.dump(node)}")


def sub_to_supported_term(left: Term, right: Term) -> Term:
    """
    Convert EggTerm.Sub(left, right) back into the original Haskell-compatible
    function set using FAdd and FMul, because your current AST definitely has
    FAdd/FMul. If your Haskell Function also has FSub, you can replace this with:

        return make_func("FSub", [left, right])
    """
    return make_func("FAdd", [left, make_func("FMul", [int_const(-1), right])])


def neg_to_supported_term(value: Term) -> Term:
    return make_func("FMul", [int_const(-1), value])


def not_to_supported_term(value: Term) -> Term:
    """
    If your Haskell Function has FNot, use that. Otherwise this keeps JSON valid
    only if FIte can return Bool in your Term language. Most Issy-style Term
    languages do support boolean terms, but check your Haskell Function type.
    """
    return make_func("FNot", [value])


def egg_repr_to_term_ast(expr_repr: str, var_sorts: Dict[str, Sort]) -> Term:
    """
    Converts extracted Egglog repr like:

        EggTerm.Add(EggTerm.Var("x"), EggTerm.Num(1))

    back into our Python Term dataclasses.
    """
    tree = py_ast.parse(expr_repr, mode="eval")

    def conv(node: py_ast.AST) -> Term:
        if not isinstance(node, py_ast.Call):
            raise ValueError(f"Expected call node, got: {py_ast.dump(node)}")

        if not isinstance(node.func, py_ast.Attribute):
            raise ValueError(f"Expected attribute call, got: {py_ast.dump(node)}")

        name = node.func.attr
        args = node.args

        if name == "Var":
            var_name = args[0].value  # type: ignore[attr-defined]
            return Var(str(var_name), var_sorts.get(str(var_name), SInt()))

        if name == "Num":
            return int_const(_py_ast_int(args[0]))

        if name == "Bool":
            return bool_const(_py_ast_bool(args[0]))

        if name == "Add":
            return make_func("FAdd", [conv(args[0]), conv(args[1])])

        if name == "Sub":
            return sub_to_supported_term(conv(args[0]), conv(args[1]))

        if name == "Mul":
            return make_func("FMul", [conv(args[0]), conv(args[1])])

        if name == "Neg":
            return neg_to_supported_term(conv(args[0]))

        if name == "And":
            return make_func("FAnd", [conv(args[0]), conv(args[1])])

        if name == "Or":
            return make_func("FOr", [conv(args[0]), conv(args[1])])

        if name == "Not":
            return not_to_supported_term(conv(args[0]))

        if name == "Eq":
            return make_func("FEq", [conv(args[0]), conv(args[1])])

        if name == "Lt":
            return make_func("FLt", [conv(args[0]), conv(args[1])])

        if name == "Le":
            return make_func("FLte", [conv(args[0]), conv(args[1])])

        if name == "Ite":
            return make_func("FIte", [conv(args[0]), conv(args[1]), conv(args[2])])

        raise ValueError(f"Unsupported Egglog constructor: {name}")

    return conv(tree.body)


# ============================================================
# 8. Run Egglog for one Term
# ============================================================

def run_rules(local_egraph: EGraph) -> None:
    # This matches the API style used in your inspiration code.
    local_egraph.run(EGGLOG_ITERATIONS, ruleset=rules)


def optimize_term_with_egglog(term: Term) -> Term:
    var_sorts = collect_var_sorts(term)
    egg_expr = term_ast_to_egg(term)

    local_egraph = EGraph()
    local_egraph.register(egg_expr)
    run_rules(local_egraph)

    minimized_egg = local_egraph.extract(egg_expr)
    minimized_repr = str(minimized_egg)

    optimized = egg_repr_to_term_ast(minimized_repr, var_sorts)

    if PRINT_CHANGED_TERMS and optimized != term:
        print("Changed term:")
        print("  before:", term)
        print("  egg:   ", minimized_repr)
        print("  after: ", optimized)

    return optimized


# ============================================================
# 9. Walk Prog and optimize embedded Terms with Egglog
# ============================================================

def optimize_prog_terms_with_egglog(prog: Prog) -> Prog:
    if isinstance(prog, Cond):
        return Cond(
            optimize_term_with_egglog(prog.condition),
            optimize_prog_terms_with_egglog(prog.body),
        )

    if isinstance(prog, PAssign):
        return PAssign([
            (symbol, sort, optimize_term_with_egglog(term))
            for symbol, sort, term in prog.assigns
        ])

    if isinstance(prog, InfLoop):
        return InfLoop(optimize_prog_terms_with_egglog(prog.body))

    if isinstance(prog, Sequence):
        return Sequence([optimize_prog_terms_with_egglog(p) for p in prog.programs])

    return prog


# ============================================================
# 10. Conservative structural cleanup after term optimization
# ============================================================

def is_cbool(term: Term, value: Optional[bool] = None) -> bool:
    if not isinstance(term, Const) or not isinstance(term.const, CBool):
        return False
    return value is None or term.const.value == value


def is_empty_sequence(prog: Prog) -> bool:
    return isinstance(prog, Sequence) and len(prog.programs) == 0


def optimize_prog_structure(prog: Prog) -> Prog:
    if isinstance(prog, InfLoop):
        return InfLoop(optimize_prog_structure(prog.body))

    if isinstance(prog, Cond):
        condition = prog.condition
        body = optimize_prog_structure(prog.body)

        if is_cbool(condition, True):
            return body
        if is_cbool(condition, False):
            return Sequence([])
        if is_empty_sequence(body):
            return Sequence([])

        return Cond(condition, body)

    if isinstance(prog, Sequence):
        new_programs: List[Prog] = []
        for p in prog.programs:
            p2 = optimize_prog_structure(p)
            if isinstance(p2, Sequence):
                new_programs.extend(p2.programs)
            else:
                new_programs.append(p2)

        # Remove empty Sequence([])
        new_programs = [p for p in new_programs if not is_empty_sequence(p)]
        return Sequence(new_programs)

    return prog


# ============================================================
# 11. Lower expression-level FIte assignments into guarded commands
# ============================================================

def negate_term(term: Term) -> Term:
    """
    Build a clean logical negation term.

    This avoids producing unnecessary FNot(FNot(x)) and folds boolean constants.
    """
    if isinstance(term, Func) and term.function.name == "FNot" and len(term.args) == 1:
        return term.args[0]

    if isinstance(term, Const) and isinstance(term.const, CBool):
        return bool_const(not term.const.value)

    return make_func("FNot", [term])


def lower_ite_assignment(symbol: str, sort: Sort, term: Term) -> Prog:
    """
    Convert an expression-level assignment with FIte into guarded commands.

    Input shape:

        x := FIte(cond, then_expr, else_expr)

    Output shape, because this Prog AST has Cond but no real IfElse:

        Sequence([
            Cond(cond, x := then_expr),
            Cond(Not(cond), x := else_expr),
        ])

    This is a guarded-command lowering, not a real IfElse node.
    It is safe here because Term is pure: Var, Const, and Func contain no side effects.
    """
    if not isinstance(term, Func):
        return PAssign([(symbol, sort, term)])

    if term.function.name != "FIte":
        return PAssign([(symbol, sort, term)])

    if len(term.args) != 3:
        return PAssign([(symbol, sort, term)])

    cond, then_expr, else_expr = term.args

    return Sequence([
        Cond(
            cond,
            lower_ite_assignment(symbol, sort, then_expr),
        ),
        Cond(
            negate_term(cond),
            lower_ite_assignment(symbol, sort, else_expr),
        ),
    ])


def lower_ite_assignments_in_prog(prog: Prog) -> Prog:
    """
    Walk a Prog AST and lower every PAssign term of the form FIte(...).
    """
    if isinstance(prog, PAssign):
        lowered_programs: List[Prog] = []

        for symbol, sort, term in prog.assigns:
            lowered_programs.append(
                lower_ite_assignment(symbol, sort, term)
            )

        if len(lowered_programs) == 1:
            return lowered_programs[0]

        return Sequence(lowered_programs)

    if isinstance(prog, Cond):
        return Cond(
            prog.condition,
            lower_ite_assignments_in_prog(prog.body),
        )

    if isinstance(prog, Sequence):
        return Sequence([
            lower_ite_assignments_in_prog(p)
            for p in prog.programs
        ])

    if isinstance(prog, InfLoop):
        return InfLoop(
            lower_ite_assignments_in_prog(prog.body)
        )

    return prog


# ============================================================
# 12. Full optimization pipeline
# ============================================================

def optimize_ast_with_egglog(prog: Prog) -> Prog:
    """
    Full pipeline:

    1. Use Egglog to simplify expression terms.
    2. Lower expression-level FIte assignments into guarded Cond/Sequence programs.
    3. Clean trivial program structure such as Cond(True), Cond(False), and empty Sequence.
    """
    optimized_terms = optimize_prog_terms_with_egglog(prog)
    lowered_ites = lower_ite_assignments_in_prog(optimized_terms)
    cleaned = optimize_prog_structure(lowered_ites)
    return cleaned


# ============================================================
# 13. Main script
# ============================================================

def load_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def write_json(path: str, data: Any) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
        f.write("\n")


def main() -> None:
    # === Load the uploaded JSON AST file ===
    with open(AST_FILE, "r", encoding="utf-8") as f:
        ast_json = json.load(f)

    # 1. JSON -> Python AST
    prog_ast = parse_prog(ast_json)

    # 2. Optimize embedded expressions through Egglog
    optimized_prog_ast = optimize_ast_with_egglog(prog_ast)

    # 3. Python AST -> same Haskell JSON format
    output_json = prog_to_json(optimized_prog_ast)

    # 4. Write output
    write_json(OUTPUT_FILE, output_json)
    print(f"Wrote optimized AST to: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
