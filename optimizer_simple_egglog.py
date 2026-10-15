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
import itertools
import json
import sys
from dataclasses import dataclass
from math import gcd as _gcd
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

    If a sub-expression occurs more than once, Egglog prints it as a let-binding first:

        _EggTerm_1 = EggTerm.Add(EggTerm.Var("x"), EggTerm.Var("i"))
        EggTerm.Lt(EggTerm.Num(10), _EggTerm_1)

    so the repr is parsed as a module: the bindings are collected and substituted by name.
    """
    tree = py_ast.parse(expr_repr, mode="exec")
    if not tree.body or not isinstance(tree.body[-1], py_ast.Expr):
        raise ValueError(f"Expected a final expression in Egglog repr, got: {expr_repr!r}")
    bindings: Dict[str, py_ast.AST] = {}
    for stmt in tree.body[:-1]:
        if (
            isinstance(stmt, py_ast.Assign)
            and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], py_ast.Name)
        ):
            bindings[stmt.targets[0].id] = stmt.value
        else:
            raise ValueError(f"Unexpected statement in Egglog repr: {py_ast.dump(stmt)}")
    converted: Dict[str, Term] = {}

    def conv(node: py_ast.AST) -> Term:
        if isinstance(node, py_ast.Name):
            if node.id not in bindings:
                raise ValueError(f"Unbound name in Egglog repr: {node.id}")
            if node.id not in converted:
                converted[node.id] = conv(bindings[node.id])
            return converted[node.id]

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

    return conv(tree.body[-1].value)


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
        print("Changed term:", file=sys.stderr)
        print("  before:", term, file=sys.stderr)
        print("  egg:   ", minimized_repr, file=sys.stderr)
        print("  after: ", optimized, file=sys.stderr)

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
    LEGACY, UNSOUND -- kept only so the regression test can reproduce the bug. Use sound_lower().

    Walk a Prog AST and lower every PAssign term of the form FIte(...).

    Known faults (see documents/2026-10-09_ite-lowering-bug-fix.md):
      * the guard of the second branch is evaluated after the first branch changed the state;
      * a parallel PAssign with several variables is turned into sequential assignments.
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
# 11b. Sound lowering of FIte / parallel assignment  (replaces section 11)
# ============================================================

def _has_ite(term: Term) -> bool:
    return isinstance(term, Func) and (
        term.function.name == "FIte" or any(_has_ite(a) for a in term.args)
    )


def _term_names(term: Term, out: set) -> None:
    if isinstance(term, Var):
        out.add(term.name)
    elif isinstance(term, Func):
        for a in term.args:
            _term_names(a, out)


def _prog_names(prog: Prog, out: set) -> set:
    """All variable names that occur anywhere in a Prog (used to pick fresh temporaries)."""
    if isinstance(prog, Declare):
        out.add(prog.symbol)
    elif isinstance(prog, PAssign):
        for symbol, _, term in prog.assigns:
            out.add(symbol)
            _term_names(term, out)
    elif isinstance(prog, Cond):
        _term_names(prog.condition, out)
        _prog_names(prog.body, out)
    elif isinstance(prog, Sequence):
        for q in prog.programs:
            _prog_names(q, out)
    elif isinstance(prog, InfLoop):
        _prog_names(prog.body, out)
    return out


def _ite_into(tmp: str, sort: Sort, term: Term) -> Prog:
    """
    Assign `term` to the fresh temporary `tmp`, branching on FIte. The guards only read original
    variables because `tmp` is fresh, so evaluating the second guard after the first branch is harmless.
    """
    if isinstance(term, Func) and term.function.name == "FIte" and len(term.args) == 3:
        cond, then_expr, else_expr = term.args
        return Sequence([
            Cond(cond, _ite_into(tmp, sort, then_expr)),
            Cond(negate_term(cond), _ite_into(tmp, sort, else_expr)),
        ])
    return PAssign([(tmp, sort, term)])


def sound_lower(prog: Prog, _used: Optional[set] = None, _counter=None) -> Prog:
    """
    Semantics-preserving replacement for lower_ite_assignments_in_prog.

        PAssign [(v1, e1), (v2, ite(c, a, b))]
      becomes
        Declare t;  Cond(c, t := a);  Cond(!c, t := b);  PAssign [(v1, e1), (v2, t)]

    The real assignment stays ONE parallel PAssign, evaluated after all temporaries are computed, so
    both the ITE guards and the other right-hand sides see the old state. Temporary names are fresh
    with respect to every name used in the program.
    """
    if _used is None:
        _used = _prog_names(prog, set())
        _counter = itertools.count()

    def fresh(base: str) -> str:
        while True:
            name = f"ite_tmp_{base}_{next(_counter)}"
            if name not in _used:
                _used.add(name)
                return name

    if isinstance(prog, PAssign):
        if len(prog.assigns) <= 1 and not any(_has_ite(t) for _, _, t in prog.assigns):
            return prog
        pre: List[Prog] = []
        final: List[Tuple[str, Sort, Term]] = []
        for symbol, sort, term in prog.assigns:
            if _has_ite(term):
                tmp = fresh(symbol)
                pre += [Declare(tmp, sort), _ite_into(tmp, sort, term)]
                final.append((symbol, sort, Var(tmp, sort)))
            else:
                final.append((symbol, sort, term))
        return Sequence(pre + [PAssign(final)])

    if isinstance(prog, Cond):
        return Cond(prog.condition, sound_lower(prog.body, _used, _counter))
    if isinstance(prog, Sequence):
        return Sequence([sound_lower(q, _used, _counter) for q in prog.programs])
    if isinstance(prog, InfLoop):
        return InfLoop(sound_lower(prog.body, _used, _counter))
    return prog


# ============================================================
# 11c. Dead-code elimination  (see documents/2026-10-12_dead-code-elimination.md)
# ============================================================
#
# A forward analysis that needs no knowledge of the specification. Walking the program in execution
# order it keeps, for the current point, what is known about the state:
#   env    variable -> the (at most _MAX_VALUES) constants it can have     (from `v == k` guards and
#                                                                          assignments of constants)
#   true   guards known to hold       (from enclosing `if` guards, and `v == t` after `v := t` for a linear t)
#   false  guards known not to hold   (from guards that were skipped)
# and uses it to
#   * fold guards and right-hand sides: a guard that is true is replaced by its body, one that is false
#     is removed together with its body; comparisons of linear integer terms are also decided from the
#     facts (ranges and relations between variables, see "relations between variables" below);
#   * remove assignments that store the value the variable already has;
#   * remove everything after an unconditional Break / Continue / Abort;
#   * remove assignments to, and declarations of, local variables (Declare) that are never needed.
# Two paths that meet (after an `if`, at a loop head, after a loop) keep only what holds on both; a loop
# is analysed until what is known at its head no longer changes (_dce_loop). Knowledge about a variable
# is dropped as soon as it may change (assignment, Declare, Read for input variables).
# Assumptions: guard terms are pure and total; Read only changes input variables, i.e. variables that are
# used but never assigned anywhere in the program; a variable declared with Declare is invisible to
# read_inputs() (the C printer declares it inside main()); integer arithmetic in the relational reasoning is
# exact, like Issy's own semantics (no wrap-around of the C int).

_INT_LIMIT = 2 ** 31


def _free_vars(term: Term, out: Optional[set] = None) -> set:
    if out is None:
        out = set()
    if isinstance(term, Var):
        out.add(term.name)
    elif isinstance(term, Func):
        for a in term.args:
            _free_vars(a, out)
    return out


def _vars_used(prog: Prog, out: Optional[set] = None) -> set:
    if out is None:
        out = set()
    if isinstance(prog, Cond):
        _free_vars(prog.condition, out)
        _vars_used(prog.body, out)
    elif isinstance(prog, PAssign):
        for _, _, term in prog.assigns:
            _free_vars(term, out)
    elif isinstance(prog, Sequence):
        for q in prog.programs:
            _vars_used(q, out)
    elif isinstance(prog, InfLoop):
        _vars_used(prog.body, out)
    return out


def _effects(prog: Prog) -> Tuple[set, bool]:
    """(variables `prog` may assign or declare, whether it may execute Read)"""
    if isinstance(prog, PAssign):
        return {symbol for symbol, _, _ in prog.assigns}, False
    if isinstance(prog, Declare):
        return {prog.symbol}, False
    if isinstance(prog, Read):
        return set(), True
    if isinstance(prog, (Cond, InfLoop)):
        return _effects(prog.body)
    if isinstance(prog, Sequence):
        assigned: set = set()
        reads = False
        for q in prog.programs:
            a, r = _effects(q)
            assigned |= a
            reads = reads or r
        return assigned, reads
    return set(), False


class _Loop:
    """States reaching the back edge (`continue`, end of body) and the exits (`break`) of one loop."""

    def __init__(self):
        self.back: List["_Ctx"] = []
        self.exits: List["_Ctx"] = []


class _Ctx:
    """What is known about the current state (see the comment above)."""

    def __init__(self, env=None, true=None, false=None, loops=None):
        self.env: Dict[str, frozenset] = dict(env or {})  # variable -> the few constants it can be
        self.true: List[Term] = list(true or [])
        self.false: List[Term] = list(false or [])
        self.loops: List[_Loop] = loops if loops is not None else []  # enclosing loops, innermost last

    def copy(self) -> "_Ctx":
        return _Ctx(self.env, self.true, self.false, self.loops)

    def assign_from(self, other: "_Ctx") -> None:
        self.env, self.true, self.false = dict(other.env), list(other.true), list(other.false)

    def same_as(self, other: "_Ctx") -> bool:
        return self.env == other.env and self.true == other.true and self.false == other.false

    def kill(self, names: set) -> None:
        if not names:
            return
        for name in names:
            self.env.pop(name, None)
        self.true = [f for f in self.true if not (_free_vars(f) & names)]
        self.false = [f for f in self.false if not (_free_vars(f) & names)]


def _join(a: _Ctx, b: _Ctx) -> _Ctx:
    """What holds in `a` AND in `b`, i.e. what is known after two paths merge (order of `a` is kept)."""
    env = {}
    for name, values in a.env.items():
        if name in b.env and len(values | b.env[name]) <= _MAX_VALUES:
            env[name] = values | b.env[name]  # after the merge the variable has one of the values of either path
    return _Ctx(env,
                [f for f in a.true if f in b.true],
                [f for f in a.false if f in b.false],
                a.loops)


def _known(term: Term, ctx: _Ctx) -> Optional[bool]:
    """True/False if the context decides this boolean term, else None.
    (`_assume` never stores a negation, so a stored fact is always a positive guard.)"""
    if term in ctx.true:
        return True
    if term in ctx.false:
        return False
    return None


def _negation(term: Term) -> Term:
    if isinstance(term, Func) and term.function.name == "FNot" and len(term.args) == 1:
        return term.args[0]
    return make_func("FNot", [term])


def _int_value(term: Term) -> Optional[int]:
    if isinstance(term, Const) and isinstance(term.const, CInt):
        return term.const.value
    return None


def _fold_junction(name: str, args: List[Term]) -> Term:
    """FAnd / FOr over simplified arguments: flatten, drop neutral and repeated arguments, detect
    an absorbing argument or a pair `a`, `!a`."""
    is_and = name == "FAnd"
    neutral, absorbing = is_and, not is_and
    flat: List[Term] = []
    for a in args:
        if isinstance(a, Func) and a.function.name == name:
            flat.extend(a.args)
        else:
            flat.append(a)
    out: List[Term] = []
    for a in flat:
        if is_cbool(a, neutral):
            continue
        if is_cbool(a, absorbing):
            return bool_const(absorbing)
        if a not in out:
            out.append(a)
    if any(_negation(a) in out for a in out):
        return bool_const(absorbing)
    if not out:
        return bool_const(neutral)
    if len(out) == 1:
        return out[0]
    return make_func(name, out)


def _fold(name: str, args: List[Term]) -> Term:
    """One function application over simplified arguments: constant folding and local identities."""
    nums = [_int_value(a) for a in args]
    all_num = all(n is not None for n in nums)

    if name in ("FAnd", "FOr"):
        return _fold_junction(name, args)
    if name == "FAdd" and all_num and abs(sum(nums)) < _INT_LIMIT:
        return int_const(sum(nums))
    if name == "FMul" and all_num:
        prod = 1
        for n in nums:
            prod *= n
        if abs(prod) < _INT_LIMIT:
            return int_const(prod)
    if name == "FEq" and len(args) == 2:
        if all(isinstance(a, Const) for a in args):
            return bool_const(args[0] == args[1])
        if args[0] == args[1]:
            return bool_const(True)
    if name in ("FLt", "FLte") and len(args) == 2:
        if all_num:
            return bool_const(nums[0] < nums[1] if name == "FLt" else nums[0] <= nums[1])
        if args[0] == args[1]:
            return bool_const(name == "FLte")
    if name == "FNot" and len(args) == 1:
        if isinstance(args[0], Const) and isinstance(args[0].const, CBool):
            return bool_const(not args[0].const.value)
        if isinstance(args[0], Func) and args[0].function.name == "FNot":
            return args[0].args[0]
    if name == "FIte" and len(args) == 3:
        if is_cbool(args[0], True):
            return args[1]
        if is_cbool(args[0], False):
            return args[2]
        if args[1] == args[2]:
            return args[1]
    return make_func(name, args)


_MAX_VALUES = 6  # a variable is tracked while it can have at most this many different constant values


def _values(term: Term, ctx: _Ctx) -> Optional[frozenset]:
    """The constants a simplified term can evaluate to, if that is a small known set."""
    if isinstance(term, Const):
        return frozenset([term])
    if isinstance(term, Var):
        return ctx.env.get(term.name)
    if isinstance(term, Func) and term.function.name == "FIte" and len(term.args) == 3:
        a, b = _values(term.args[1], ctx), _values(term.args[2], ctx)
        if a is not None and b is not None and len(a | b) <= _MAX_VALUES:
            return a | b
    return None


def _decide(name: str, args: List[Term], ctx: _Ctx) -> Optional[bool]:
    """`v == k`, `v < k`, `v <= k` (or with the operands swapped) for a variable v with a known set of
    values: the answer if it is the same for every value."""
    if name not in ("FEq", "FLt", "FLte") or len(args) != 2:
        return None
    a, b = args
    if isinstance(a, Var) and isinstance(b, Const):
        values, k, var_left = ctx.env.get(a.name), b, True
    elif isinstance(b, Var) and isinstance(a, Const):
        values, k, var_left = ctx.env.get(b.name), a, False
    else:
        return None
    if not values:
        return None
    outcomes = set()
    for v in values:
        if name == "FEq":
            outcomes.add(v == k)
            continue
        x, y = _int_value(v), _int_value(k)
        if x is None or y is None:
            return None
        left, right = (x, y) if var_left else (y, x)
        outcomes.add(left < right if name == "FLt" else left <= right)
    return outcomes.pop() if len(outcomes) == 1 else None


def _simp(term: Term, ctx: _Ctx) -> Term:
    """Simplify a term under the current knowledge: variables with a known value are replaced, the
    result is folded, and a (sub)term that the context decides becomes a constant."""
    if isinstance(term, Var):
        values = ctx.env.get(term.name)
        return next(iter(values)) if values is not None and len(values) == 1 else term
    if isinstance(term, Const):
        return term
    args = [_simp(a, ctx) for a in term.args]
    decided = _decide(term.function.name, args, ctx)
    if decided is not None:
        return bool_const(decided)
    result = _fold(term.function.name, args)
    if isinstance(result, Const):
        return result
    k = _known(result, ctx)
    if k is None:
        k = _entailed(result, ctx)  # ranges and relations between variables (see "relations between variables")
    return result if k is None else bool_const(k)


def _narrow(ctx: _Ctx, name: str, keep: Optional[set] = None, drop: Optional[set] = None) -> None:
    """The variable is (only) one of `keep`, resp. is none of `drop`, additionally to what was known."""
    values = ctx.env.get(name)
    if keep is not None:
        ctx.env[name] = frozenset(keep) if values is None else values & frozenset(keep)
    elif values is not None and drop is not None:
        ctx.env[name] = values - frozenset(drop)


def _assume(term: Term, truth: bool, ctx: _Ctx) -> None:
    """Record that the (already simplified) boolean `term` has value `truth`."""
    if isinstance(term, Const):
        return
    if isinstance(term, Var):
        _narrow(ctx, term.name, keep={bool_const(truth)})
        return
    name = term.function.name
    if name == "FNot" and len(term.args) == 1:
        _assume(term.args[0], not truth, ctx)
        return
    if name == "FAnd" and truth:
        for a in term.args:
            _assume(a, True, ctx)
        return
    if name == "FOr" and not truth:
        for a in term.args:
            _assume(a, False, ctx)
        return
    if name == "FEq" and len(term.args) == 2:
        a, b = term.args
        var, const = (a, b) if isinstance(a, Var) and isinstance(b, Const) else (b, a)
        if isinstance(var, Var) and isinstance(const, Const):
            if truth:
                _narrow(ctx, var.name, keep={const})
                return
            if var.name in ctx.env:
                _narrow(ctx, var.name, drop={const})
                return
    (ctx.true if truth else ctx.false).append(term)


# ---- relations between variables ---------------------------------------------------------------
# A guard that compares linear integer terms (`5 < x`, `x < y`, `x + y <= 10`) says something about
# several variables at once, and `y = x + 1` relates two variables after the assignment. `_entailed`
# asks whether the facts of the context decide such a comparison. The facts and the negation of the
# comparison become linear constraints  sum(c_i * v_i) + c <= 0  over the integers, and Fourier-Motzkin
# elimination (rounding every derived constraint, which is valid for integers) looks for a
# contradiction. A contradiction proves the answer. No contradiction proves nothing: the method is not
# complete, and it gives up when a question grows past the limits below. Standard analyses that track
# such facts are intervals (Cousot and Cousot 1977), octagons (Mine 2006) and polyhedra (Cousot and
# Halbwachs 1978); here the facts are the guards and assignments seen on the path.
# Integers are the mathematical integers of Issy's semantics, as in the rest of the pass (the C int wraps
# at 2^31, which a relational conclusion cannot see; constants are folded only below 2^31 for the same reason).

_MAX_FACTS = 24     # facts used for one question (those connected to it through shared variables)
_MAX_ROWS = 200     # constraints alive at the same time during the elimination
_MAX_ALTERNATIVES = 4  # a question may split into at most this many alternatives

_Con = Tuple[Tuple[Tuple[str, int], ...], int]  # (((variable, coefficient), ...), constant)  meaning  sum + constant <= 0


def _con(coefs: Dict[str, int], const: int) -> _Con:
    """The constraint, divided by the gcd of the coefficients with the constant rounded up (valid for integers)."""
    coefs = {v: c for v, c in coefs.items() if c}
    if coefs:
        g = 0
        for c in coefs.values():
            g = _gcd(g, abs(c))
        if g > 1:
            coefs = {v: c // g for v, c in coefs.items()}
            const = -((-const) // g)  # ceil(const / g)
    return tuple(sorted(coefs.items())), const


def _lin(term: Term) -> Optional[Tuple[Dict[str, int], int]]:
    """`term` as  sum(coefficient * variable) + constant  over integers, or None if it is not of that form."""
    if isinstance(term, Const):
        value = _int_value(term)
        return ({}, value) if value is not None else None
    if isinstance(term, Var):
        return ({term.name: 1}, 0) if isinstance(term.sort, SInt) else None
    if isinstance(term, Func) and term.function.name == "FAdd":
        coefs: Dict[str, int] = {}
        const = 0
        for a in term.args:
            part = _lin(a)
            if part is None:
                return None
            for v, c in part[0].items():
                coefs[v] = coefs.get(v, 0) + c
            const += part[1]
        return {v: c for v, c in coefs.items() if c}, const
    if isinstance(term, Func) and term.function.name == "FMul":
        coefs, const = {}, 1  # the product so far
        for a in term.args:
            part = _lin(a)
            if part is None or (coefs and part[0]):
                return None  # not linear: two factors with variables
            if part[0]:
                coefs, const = {v: c * const for v, c in part[0].items()}, part[1] * const
            else:
                coefs, const = {v: c * part[1] for v, c in coefs.items()}, const * part[1]
        return {v: c for v, c in coefs.items() if c}, const
    return None


def _diff(a: Tuple[Dict[str, int], int], b: Tuple[Dict[str, int], int], extra: int) -> _Con:
    """The constraint  a - b + extra <= 0."""
    coefs = dict(a[0])
    for v, c in b[0].items():
        coefs[v] = coefs.get(v, 0) - c
    return _con(coefs, a[1] - b[1] + extra)


def _alternatives(term: Term, truth: bool) -> Optional[List[List[_Con]]]:
    """"`term` has value `truth`" as an OR of ANDs of linear constraints, or None if it cannot be said that way."""
    if not isinstance(term, Func):
        return None
    name = term.function.name
    if name == "FNot" and len(term.args) == 1:
        return _alternatives(term.args[0], not truth)
    if name in ("FLt", "FLte", "FEq") and len(term.args) == 2:
        a, b = _lin(term.args[0]), _lin(term.args[1])
        if a is None or b is None:
            return None
        if name == "FLt":
            return [[_diff(a, b, 1)]] if truth else [[_diff(b, a, 0)]]
        if name == "FLte":
            return [[_diff(a, b, 0)]] if truth else [[_diff(b, a, 1)]]
        return [[_diff(a, b, 0), _diff(b, a, 0)]] if truth else [[_diff(a, b, 1)], [_diff(b, a, 1)]]
    if name in ("FAnd", "FOr"):
        parts = [_alternatives(a, truth) for a in term.args]
        if any(p is None for p in parts):
            return None
        if (name == "FAnd") != truth:  # one of the arguments holds: alternatives add up
            out = [alt for p in parts for alt in p]
            return out if len(out) <= _MAX_ALTERNATIVES else None
        out = [[]]  # all arguments hold: alternatives multiply
        for p in parts:
            out = [x + y for x in out for y in p]
            if len(out) > _MAX_ALTERNATIVES:
                return None
        return out
    return None


def _constraints_of(term: Term, truth: bool) -> List[_Con]:
    """Constraints that hold whenever `term` has value `truth` (parts that cannot be said linearly are left out)."""
    if isinstance(term, Func):
        name = term.function.name
        if name == "FNot" and len(term.args) == 1:
            return _constraints_of(term.args[0], not truth)
        if name in ("FAnd", "FOr") and (name == "FAnd") == truth:
            return [c for a in term.args for c in _constraints_of(a, truth)]
    alts = _alternatives(term, truth)
    return alts[0] if alts is not None and len(alts) == 1 else []


_CONSTRAINT_CACHE: Dict[Tuple[int, bool], Tuple[Term, List[_Con]]] = {}  # keyed by object identity; the term is kept alive here


def _cached_constraints(term: Term, truth: bool) -> List[_Con]:
    hit = _CONSTRAINT_CACHE.get((id(term), truth))
    if hit is None:
        hit = _CONSTRAINT_CACHE[(id(term), truth)] = (term, _constraints_of(term, truth))
    return hit[1]


def _facts_near(ctx: _Ctx, names: set) -> List[_Con]:
    """The constraints known in `ctx` that are connected to `names` (through shared variables), plus the
    bounds of the variables with a known set of values."""
    pool: List[_Con] = []
    for f in ctx.true:
        pool.extend(_cached_constraints(f, True))
    for f in ctx.false:
        pool.extend(_cached_constraints(f, False))
    seen, near = set(names), []
    grew = True
    while grew and pool and len(near) < _MAX_FACTS:
        grew, rest = False, []
        for con in pool:
            if len(near) < _MAX_FACTS and any(v in seen for v, _ in con[0]):
                near.append(con)
                seen.update(v for v, _ in con[0])
                grew = True
            else:
                rest.append(con)
        pool = rest
    for name in seen:
        values = ctx.env.get(name)
        ints = [_int_value(v) for v in values] if values else []
        if ints and None not in ints:
            near.append(_con({name: -1}, min(ints)))  # min <= name
            near.append(_con({name: 1}, -max(ints)))  # name <= max
    return near


def _infeasible(cons: List[_Con]) -> bool:
    """True only if the constraints have no integer solution (Fourier-Motzkin; False means unknown)."""
    rows: Dict[Tuple[Tuple[str, int], ...], int] = {}
    for coefs, const in cons:
        if not coefs:
            if const > 0:
                return True
            continue
        if coefs not in rows or const > rows[coefs]:
            rows[coefs] = const  # a larger constant is the stronger constraint
    while rows:
        count: Dict[str, List[int]] = {}
        for coefs in rows:
            for v, c in coefs:
                count.setdefault(v, [0, 0])[0 if c > 0 else 1] += 1
        var = min(count, key=lambda v: count[v][0] * count[v][1])
        upper, lower, rest = [], [], {}
        for coefs, const in rows.items():
            c = dict(coefs).get(var, 0)
            if c > 0:
                upper.append((coefs, const, c))
            elif c < 0:
                lower.append((coefs, const, -c))
            else:
                rest[coefs] = const
        for ucoefs, uconst, a in upper:
            for lcoefs, lconst, b in lower:
                comb: Dict[str, int] = {}
                for v, c in ucoefs:
                    comb[v] = comb.get(v, 0) + b * c
                for v, c in lcoefs:
                    comb[v] = comb.get(v, 0) + a * c
                new, const = _con(comb, b * uconst + a * lconst)  # the coefficient of `var` is a*b - a*b = 0
                if not new:
                    if const > 0:
                        return True
                    continue
                if new not in rest or const > rest[new]:
                    rest[new] = const
        rows = rest
        if len(rows) > _MAX_ROWS:
            return False
    return False


def _entailed(atom: Term, ctx: _Ctx) -> Optional[bool]:
    """True/False if the facts of `ctx` decide the comparison `atom` (`<`, `<=`, `==` of linear integer terms)."""
    if not (isinstance(atom, Func) and atom.function.name in ("FLt", "FLte", "FEq") and len(atom.args) == 2):
        return None
    if_false, if_true = _alternatives(atom, False), _alternatives(atom, True)
    if if_false is None or if_true is None:
        return None
    facts = _facts_near(ctx, _free_vars(atom))
    if all(_infeasible(facts + alt) for alt in if_false):
        return True  # the facts and "not atom" contradict each other
    if all(_infeasible(facts + alt) for alt in if_true):
        return False
    return None


def _has_free_break(prog: Prog) -> bool:
    """A Break that targets the loop directly enclosing `prog` (an inner InfLoop captures its own)."""
    if isinstance(prog, Break):
        return True
    if isinstance(prog, Cond):
        return _has_free_break(prog.body)
    if isinstance(prog, Sequence):
        return any(_has_free_break(q) for q in prog.programs)
    return False


def _diverges(prog: Prog) -> bool:
    """Conservative: True only if control can never fall off the end of `prog`."""
    if isinstance(prog, (Break, Continue, Abort)):
        return True
    if isinstance(prog, Sequence):
        return any(_diverges(q) for q in prog.programs)
    if isinstance(prog, InfLoop):
        return not _has_free_break(prog.body)
    return False  # a Cond may skip its body


def _dce(prog: Prog, ctx: _Ctx, inputs: set) -> Prog:
    """Simplified `prog`. `ctx` is updated in place to what is known after `prog` (fall-through path)."""
    if isinstance(prog, PAssign):
        new = [(symbol, sort, _simp(term, ctx)) for symbol, sort, term in prog.assigns]
        stored = {symbol: _values(term, ctx) for symbol, _, term in new}  # in the state before the assignment
        kept = [
            (symbol, sort, term) for symbol, sort, term in new
            if not ((isinstance(term, Var) and term.name == symbol)
                    or (isinstance(term, Const) and ctx.env.get(symbol) == frozenset([term])))
        ]  # an assignment that stores the value the variable already has does nothing
        assigned = {symbol for symbol, _, _ in kept}
        ctx.kill(assigned)
        for symbol, _, _ in kept:
            if stored[symbol] is not None and 0 < len(stored[symbol]) <= _MAX_VALUES:
                ctx.env[symbol] = stored[symbol]
        for symbol, sort, term in kept:
            # `symbol == term` holds afterwards if no variable of `term` was changed by this same assignment
            lin = _lin(term)
            if isinstance(sort, SInt) and lin is not None and lin[0] and not (_free_vars(term) & assigned):
                ctx.true.append(make_func("FEq", [Var(symbol, sort), term]))
        return PAssign(kept) if kept else Sequence([])

    if isinstance(prog, Declare):
        ctx.kill({prog.symbol})
        return prog

    if isinstance(prog, Read):
        ctx.kill(inputs)
        return prog

    if isinstance(prog, Sequence):
        out: List[Prog] = []
        for q in prog.programs:
            q2 = _dce(q, ctx, inputs)
            if is_empty_sequence(q2):
                continue
            out.append(q2)
            if _diverges(q2):
                break  # everything after an unconditional jump is unreachable
        return Sequence(out)

    if isinstance(prog, Cond):
        cond = _simp(prog.condition, ctx)
        if is_cbool(cond, False):
            return Sequence([])
        if is_cbool(cond, True):
            return _dce(prog.body, ctx, inputs)
        body_ctx = ctx.copy()
        _assume(cond, True, body_ctx)
        body = _dce(prog.body, body_ctx, inputs)
        if is_empty_sequence(body):
            return Sequence([])  # the guard is pure, so skipping it changes nothing
        skipped = ctx.copy()
        _assume(cond, False, skipped)  # the path that does not enter the body
        if _diverges(body):
            ctx.assign_from(skipped)  # reaching the next item means the guard was false
        else:
            ctx.assign_from(_join(skipped, body_ctx))
        return Cond(cond, body)

    if isinstance(prog, InfLoop):
        return _dce_loop(prog, ctx, inputs)

    if isinstance(prog, Break):
        if ctx.loops:
            ctx.loops[-1].exits.append(ctx.copy())
        return prog

    if isinstance(prog, Continue):
        if ctx.loops:
            ctx.loops[-1].back.append(ctx.copy())
        return prog

    return prog  # Abort


_MAX_LOOP_ROUNDS = 8


def _dce_loop(prog: InfLoop, ctx: _Ctx, inputs: set) -> Prog:
    """
    A loop head is reached from the code before the loop and from every back edge (`continue`, end of
    the body), so what is known there is what holds on all of them. Start with what is known before the
    loop, analyse the body, join the states that reach the back edge, and repeat until nothing changes
    (constant propagation, Kildall 1973). What is known after the loop is what holds at all `break`s.
    """
    entry = ctx.copy()
    head = entry.copy()
    for _ in range(_MAX_LOOP_ROUNDS):
        frame = _Loop()
        ctx.loops.append(frame)
        trial = head.copy()
        body = _dce(prog.body, trial, inputs)
        ctx.loops.pop()
        if not _diverges(body):
            frame.back.append(trial)  # falling off the end of the body jumps back to the head
        new_head = entry
        for back in frame.back:
            new_head = _join(new_head, back)
        if new_head.same_as(head):
            if frame.exits:
                after = frame.exits[0]
                for e in frame.exits[1:]:
                    after = _join(after, e)
                ctx.assign_from(after)
            return InfLoop(body)
        head = new_head
    # no fixed point within the bound: forget everything the loop may change
    assigned, reads = _effects(prog.body)
    changed = assigned | (inputs if reads else set())
    head = entry.copy()
    head.kill(changed)
    ctx.loops.append(_Loop())
    body = _dce(prog.body, head, inputs)
    ctx.loops.pop()
    ctx.kill(changed)
    return InfLoop(body)


# ---- dead local variables ---------------------------------------------------------------------
# `Declare v` is printed inside main(), so v is invisible to read_inputs() and to the caller. An
# assignment to such a variable matters only if the variable is read, directly in a guard or through
# the right-hand side of an assignment to a variable that matters (every variable that is not declared
# in the program, i.e. every state and input variable, always matters).

def _declared(prog: Prog, out: Optional[set] = None) -> set:
    if out is None:
        out = set()
    if isinstance(prog, Declare):
        out.add(prog.symbol)
    elif isinstance(prog, (Cond, InfLoop)):
        _declared(prog.body, out)
    elif isinstance(prog, Sequence):
        for q in prog.programs:
            _declared(q, out)
    return out


def _guard_reads(prog: Prog, out: set) -> None:
    if isinstance(prog, Cond):
        _free_vars(prog.condition, out)
        _guard_reads(prog.body, out)
    elif isinstance(prog, (InfLoop,)):
        _guard_reads(prog.body, out)
    elif isinstance(prog, Sequence):
        for q in prog.programs:
            _guard_reads(q, out)


def _assignments(prog: Prog, out: List[Tuple[str, set]]) -> None:
    if isinstance(prog, PAssign):
        for symbol, _, term in prog.assigns:
            out.append((symbol, _free_vars(term)))
    elif isinstance(prog, (Cond, InfLoop)):
        _assignments(prog.body, out)
    elif isinstance(prog, Sequence):
        for q in prog.programs:
            _assignments(q, out)


def _remove_locals(prog: Prog, dead: set) -> Prog:
    if isinstance(prog, Declare):
        return Sequence([]) if prog.symbol in dead else prog
    if isinstance(prog, PAssign):
        return PAssign([a for a in prog.assigns if a[0] not in dead])
    if isinstance(prog, Cond):
        return Cond(prog.condition, _remove_locals(prog.body, dead))
    if isinstance(prog, InfLoop):
        return InfLoop(_remove_locals(prog.body, dead))
    if isinstance(prog, Sequence):
        return Sequence([_remove_locals(q, dead) for q in prog.programs])
    return prog


def _drop_dead_locals(prog: Prog) -> Prog:
    local = _declared(prog)
    if not local:
        return prog
    needed: set = set()
    _guard_reads(prog, needed)
    assigns: List[Tuple[str, set]] = []
    _assignments(prog, assigns)
    for target, reads in assigns:
        if target not in local:
            needed |= reads
    changed = True
    while changed:
        changed = False
        for target, reads in assigns:
            if target in needed and not reads <= needed:
                needed |= reads
                changed = True
    dead = local - needed
    return _remove_locals(prog, dead) if dead else prog


def eliminate_dead_code(prog: Prog) -> Prog:
    """Dead-code elimination (see above), repeated until nothing changes."""
    _CONSTRAINT_CACHE.clear()
    for _ in range(10):
        prog1 = _drop_dead_locals(prog)
        inputs = _vars_used(prog1) - _effects(prog1)[0]
        new = optimize_prog_structure(_dce(prog1, _Ctx(), inputs))
        if new == prog:
            return new
        prog = new
    return prog


prune_dead_blocks = eliminate_dead_code  # old name


# ============================================================
# 12. Full optimization pipeline
# ============================================================

def optimize_ast_with_egglog(prog: Prog) -> Prog:
    """
    Full pipeline:

    1. Use Egglog to simplify expression terms.
    2. Lower expression-level FIte assignments soundly (fresh temporaries, one parallel assignment).
    3. Clean trivial program structure such as Cond(True), Cond(False), and empty Sequence.
    4. Eliminate dead code (eliminate_dead_code: unreachable branches, no-op assignments, code after
       jumps, unused locals).
    5. Clean up again.
    """
    optimized_terms = optimize_prog_terms_with_egglog(prog)
    lowered_ites = sound_lower(optimized_terms)
    cleaned = optimize_prog_structure(lowered_ites)
    pruned = eliminate_dead_code(cleaned)
    return optimize_prog_structure(pruned)


def optimize_ast_with_egglog_legacy(prog: Prog) -> Prog:
    """
    The original pipeline. UNSOUND (see lower_ite_assignments_in_prog); kept for regression tests
    and for reproducing the results in the thesis.
    """
    optimized_terms = optimize_prog_terms_with_egglog(prog)
    lowered_ites = lower_ite_assignments_in_prog(optimized_terms)
    return optimize_prog_structure(lowered_ites)


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
    # stderr, not stdout: Issy runs this script as a child process and its stdout is the C program
    print(f"Wrote optimized AST to: {OUTPUT_FILE}", file=sys.stderr)


if __name__ == "__main__":
    main()
