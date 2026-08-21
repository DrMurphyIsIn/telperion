"""Finite-decide certificate emitter — guarded ∀-facts over explicit tables,
proven in Lean by kernel `decide`.

Crystallizes the shape hand-rolled by gen_petersen_cert.py (2026-08-20): a
per-instance certificate whose entire content is a finite, decidable,
guarded universally-quantified fact over explicit ℕ/ℤ tables (bitmask sets,
sign tables), engineered for kernel feasibility:

  * sets are Nat bitmasks — symmetric difference is kernel-accelerated XOR;
  * ALL arithmetic is ℕ/ℤ (ℚ does NOT kernel-reduce: Rat.normalize bottoms
    out in well-founded Nat.gcd — the 2026-08-20 footgun);
  * popcount is FUELED (well-founded recursion does not kernel-reduce);
  * facts are direct decidable guarded Props — the Decidable instances
    short-circuit on failed guards, no Bool indirection needed.

The claim is written once in a tiny AST; the SAME structure is evaluated
exactly in Python (the certificate gate — a false claim is REFUSED before
any Lean is written) and rendered to Lean (`by decide`), eliminating the
text/semantics divergence channel.  The Lean kernel is the final gate.

AST:  ForallIn(var, table, body) · Imp(hyp, body) · Cmp(op, lhs, rhs)
      with op in {le, lt, eq, ne} and expressions built from
      Var/Lit/Xor/Pop (ℕ sort) and Lookup/Mul/Lit (ℤ sort, table lookups
      defaulting to 0 off-table).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Sequence, Union

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

POP_FUEL = 16  # handles masks < 2^16


# --------------------------------------------------------------- tables

@dataclass(frozen=True)
class NatTable:
    name: str
    values: tuple

    def __init__(self, name, values):
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "values", tuple(int(v) for v in values))


@dataclass(frozen=True)
class PairTable:
    """ℕ-keyed ℤ-valued lookup table; lookup defaults to 0 off-table."""
    name: str
    pairs: tuple

    def __init__(self, name, pairs):
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "pairs", tuple((int(a), int(b)) for a, b in pairs))


# ------------------------------------------------------------------ AST

@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Lit:
    value: int


@dataclass(frozen=True)
class Xor:
    lhs: object
    rhs: object


@dataclass(frozen=True)
class Pop:
    arg: object


@dataclass(frozen=True)
class Lookup:
    table: str
    key: object


@dataclass(frozen=True)
class Mul:
    lhs: object
    rhs: object


@dataclass(frozen=True)
class Cmp:
    op: str  # le | lt | eq | ne
    lhs: object
    rhs: object


@dataclass(frozen=True)
class Imp:
    hyp: object
    body: object


@dataclass(frozen=True)
class ForallIn:
    var: str
    table: str
    body: object


Node = Union[Var, Lit, Xor, Pop, Lookup, Mul, Cmp, Imp, ForallIn]


# ------------------------------------------------------- exact evaluation

def _eval_expr(node, env, tables):
    if isinstance(node, Var):
        return env[node.name]
    if isinstance(node, Lit):
        return node.value
    if isinstance(node, Xor):
        return _eval_expr(node.lhs, env, tables) ^ _eval_expr(node.rhs, env, tables)
    if isinstance(node, Pop):
        return bin(_eval_expr(node.arg, env, tables)).count("1")
    if isinstance(node, Lookup):
        key = _eval_expr(node.key, env, tables)
        for a, b in tables[node.table].pairs:
            if a == key:
                return b
        return 0
    if isinstance(node, Mul):
        return _eval_expr(node.lhs, env, tables) * _eval_expr(node.rhs, env, tables)
    raise ValueError(f"not an expression node: {node!r}")


_OPS = {"le": lambda a, b: a <= b, "lt": lambda a, b: a < b,
        "eq": lambda a, b: a == b, "ne": lambda a, b: a != b}


def _eval_prop(node, env, tables, counter):
    if isinstance(node, Cmp):
        counter[0] += 1
        return _OPS[node.op](_eval_expr(node.lhs, env, tables),
                             _eval_expr(node.rhs, env, tables))
    if isinstance(node, Imp):
        if not _eval_prop(node.hyp, env, tables, counter):
            return True
        return _eval_prop(node.body, env, tables, counter)
    if isinstance(node, ForallIn):
        table = tables[node.table]
        if not isinstance(table, NatTable):
            raise ValueError(f"ForallIn ranges over NatTable, got {node.table}")
        for v in table.values:
            if not _eval_prop(node.body, {**env, node.var: v}, tables, counter):
                return False
        return True
    raise ValueError(f"not a prop node: {node!r}")


# ------------------------------------------------------------- rendering

def _lean_expr(node, prefix):
    if isinstance(node, Var):
        return node.name
    if isinstance(node, Lit):
        return str(node.value) if node.value >= 0 else f"(-{-node.value})"
    if isinstance(node, Xor):
        return f"({_lean_expr(node.lhs, prefix)} ^^^ {_lean_expr(node.rhs, prefix)})"
    if isinstance(node, Pop):
        return f"pop {POP_FUEL} {_lean_expr(node.arg, prefix)}"
    if isinstance(node, Lookup):
        return f"{prefix}_{node.table}_get {_lean_expr(node.key, prefix)}"
    if isinstance(node, Mul):
        return f"({_lean_expr(node.lhs, prefix)} * {_lean_expr(node.rhs, prefix)})"
    raise ValueError(f"not an expression node: {node!r}")


_LEAN_OPS = {"le": "≤", "lt": "<", "eq": "=", "ne": "≠"}


def _lean_prop(node, prefix):
    if isinstance(node, Cmp):
        return (f"{_lean_expr(node.lhs, prefix)} {_LEAN_OPS[node.op]} "
                f"{_lean_expr(node.rhs, prefix)}")
    if isinstance(node, Imp):
        return f"{_lean_prop(node.hyp, prefix)} → {_lean_prop(node.body, prefix)}"
    if isinstance(node, ForallIn):
        return (f"∀ {node.var} ∈ {prefix}_{node.table}, "
                f"{_lean_prop(node.body, prefix)}")
    raise ValueError(f"not a prop node: {node!r}")


# ---------------------------------------------------------- certification

def certify_finite_decide_point(family, pt, name):
    """Evaluate the claim exactly in Python; refuse if false."""
    tables_list, prop = family.special[1](pt)
    tables = {t.name: t for t in tables_list}
    counter = [0]
    ok = _eval_prop(prop, {}, tables, counter)
    if not ok:
        raise ValueError(
            f"finite_decide instance '{name}' REFUSED: the claim is FALSE "
            "under exact evaluation — nothing to certify")
    if counter[0] == 0:
        raise ValueError(
            f"finite_decide instance '{name}' REFUSED: vacuous claim "
            "(no atomic comparison was ever evaluated)")
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(tuple(tables_list), prop),
    )
    return inst, counter[0]


@dataclass
class FiniteDecideEmitter(Emitter):
    """Emit table defs + `theorem <name> : <prop> := by decide` (ℤ/ℕ only)."""

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [
            "/-- Fueled popcount: structural in fuel, hence kernel-reducible. -/",
            "def pop : ℕ → ℕ → ℕ",
            "  | 0, _ => 0",
            "  | f + 1, n => if n = 0 then 0 else n % 2 + pop f (n / 2)",
            "",
        ]
        n_thm = 0
        for inst in fam.instances:
            tables_list, prop = inst.payload  # type: ignore[misc]
            prefix = inst.lean_name
            for t in tables_list:
                if isinstance(t, NatTable):
                    body = ", ".join(str(v) for v in t.values)
                    lines.append(
                        f"def {prefix}_{t.name} : List ℕ := [{body}]\n")
                else:
                    body = ", ".join(
                        f"({a}, {b if b >= 0 else f'(-{-b})'})" for a, b in t.pairs)
                    lines.append(
                        f"def {prefix}_{t.name} : List (ℕ × ℤ) := [{body}]\n"
                        f"def {prefix}_{t.name}_get (x : ℕ) : ℤ :=\n"
                        f"  ((({prefix}_{t.name}.find? "
                        f"(fun p => p.1 == x)).map Prod.snd).getD 0)\n")
            lines.append(
                f"-- {prefix}: finite decidable certificate (exact-evaluated "
                f"pre-emission; kernel decide is the final gate).\n"
                f"set_option maxRecDepth 100000 in\n"
                f"theorem {prefix} : {_lean_prop(prop, prefix)} := by decide\n")
            n_thm += 1
        return "\n".join(lines), n_thm

    def __post_init__(self):
        self.kind = "finite_decide"


def finite_decide_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a finite-decide family (kind='finite_decide').

    spec: ``pt -> (tables, prop)`` with ``tables`` a sequence of
    NatTable/PairTable and ``prop`` an AST over them.  The claim is evaluated
    exactly in Python at certification; the Lean kernel re-decides it.
    """
    n = sp.symbols("n")
    return InequalityFamily(
        name=name,
        symbols=(n,),
        grid=grid,
        lean_name=lean_name,
        special=("finite_decide", spec),
        constants=constants or {},
    )
