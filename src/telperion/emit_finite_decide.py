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
      with op in {le, lt, eq, ne, dvd} and expressions built from
      Var/Lit/Xor/Pop/Mod (ℕ sort) and Lookup/Mul/Lit (ℤ sort, table lookups
      defaulting to 0 off-table).

Range-completeness face (2026-10-22, CN-1 survey item N6): the same AST
also states that an explicit list covers a guarded initial segment of ℕ,

      ∀ m ∈ Finset.range N, guard m → m ∈ L,

through ForallRange(var, n, body) (the domain `Finset.range n`),
ForallIcc(var, lo, hi, body) (a bounded inner quantifier, `Finset.Icc lo hi`),
Not(body), And(lhs, rhs) and Mem/NotMem(elem, table) (list membership).
These nodes are consumed by `emit_range_completeness.py`, which adds the
surrogate-predicate bridge; `FiniteDecideEmitter` itself renders them too.
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
class Mod:
    """ℕ remainder `lhs % rhs` (rhs a positive literal; Lean's `%` on ℕ)."""
    lhs: object
    rhs: object


@dataclass(frozen=True)
class Cmp:
    op: str  # le | lt | eq | ne | dvd
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


# --- range-completeness face (N6) ---------------------------------------

@dataclass(frozen=True)
class ForallRange:
    """`∀ var ∈ Finset.range n, body` — the initial segment {0, …, n-1}."""
    var: str
    n: int
    body: object


@dataclass(frozen=True)
class ForallIcc:
    """`∀ var ∈ Finset.Icc lo hi, body` — the closed integer interval."""
    var: str
    lo: int
    hi: int
    body: object


@dataclass(frozen=True)
class Not:
    body: object


@dataclass(frozen=True)
class And:
    lhs: object
    rhs: object


@dataclass(frozen=True)
class Mem:
    """`elem ∈ table` for a NatTable (Lean `List ℕ` membership)."""
    elem: object
    table: str


@dataclass(frozen=True)
class NotMem:
    """`elem ∉ table` for a NatTable."""
    elem: object
    table: str


Node = Union[Var, Lit, Xor, Pop, Lookup, Mul, Mod, Cmp, Imp, ForallIn,
             ForallRange, ForallIcc, Not, And, Mem, NotMem]


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
    if isinstance(node, Mod):
        a, b = _eval_expr(node.lhs, env, tables), _eval_expr(node.rhs, env, tables)
        if a < 0 or b <= 0:
            raise ValueError(f"Mod is ℕ-sorted with a positive modulus, got {a} % {b}")
        return a % b
    raise ValueError(f"not an expression node: {node!r}")


def _dvd(a, b):
    """`a ∣ b` on ℕ, with Lean's convention `0 ∣ b ↔ b = 0`."""
    return b == 0 if a == 0 else b % a == 0


_OPS = {"le": lambda a, b: a <= b, "lt": lambda a, b: a < b,
        "eq": lambda a, b: a == b, "ne": lambda a, b: a != b,
        "dvd": _dvd}


def _nat_table(tables, name, who):
    table = tables[name]
    if not isinstance(table, NatTable):
        raise ValueError(f"{who} ranges over NatTable, got {name}")
    return table


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
        table = _nat_table(tables, node.table, "ForallIn")
        for v in table.values:
            if not _eval_prop(node.body, {**env, node.var: v}, tables, counter):
                return False
        return True
    if isinstance(node, ForallRange):
        for v in range(node.n):
            if not _eval_prop(node.body, {**env, node.var: v}, tables, counter):
                return False
        return True
    if isinstance(node, ForallIcc):
        for v in range(node.lo, node.hi + 1):
            if not _eval_prop(node.body, {**env, node.var: v}, tables, counter):
                return False
        return True
    if isinstance(node, Not):
        return not _eval_prop(node.body, env, tables, counter)
    if isinstance(node, And):
        return (_eval_prop(node.lhs, env, tables, counter)
                and _eval_prop(node.rhs, env, tables, counter))
    if isinstance(node, (Mem, NotMem)):
        counter[0] += 1
        table = _nat_table(tables, node.table, type(node).__name__)
        found = _eval_expr(node.elem, env, tables) in table.values
        return found if isinstance(node, Mem) else not found
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
    if isinstance(node, Mod):
        return f"({_lean_expr(node.lhs, prefix)} % {_lean_expr(node.rhs, prefix)})"
    raise ValueError(f"not an expression node: {node!r}")


_LEAN_OPS = {"le": "≤", "lt": "<", "eq": "=", "ne": "≠", "dvd": "∣"}


def _lean_atom(node, prefix):
    """Render a prop, parenthesised unless it is an atomic comparison / membership
    (an Imp hyp, a Not body or an And operand that is itself a binder or an
    arrow would otherwise re-associate)."""
    text = _lean_prop(node, prefix)
    return text if isinstance(node, (Cmp, Mem, NotMem)) else f"({text})"


def _lean_prop(node, prefix):
    if isinstance(node, Cmp):
        return (f"{_lean_expr(node.lhs, prefix)} {_LEAN_OPS[node.op]} "
                f"{_lean_expr(node.rhs, prefix)}")
    if isinstance(node, Imp):
        hyp = node.hyp
        hyp_text = (_lean_prop(hyp, prefix) if isinstance(hyp, (Cmp, Mem, NotMem, Not))
                    else f"({_lean_prop(hyp, prefix)})")
        return f"{hyp_text} → {_lean_prop(node.body, prefix)}"
    if isinstance(node, ForallIn):
        return (f"∀ {node.var} ∈ {prefix}_{node.table}, "
                f"{_lean_prop(node.body, prefix)}")
    if isinstance(node, ForallRange):
        return f"∀ {node.var} ∈ Finset.range {node.n}, {_lean_prop(node.body, prefix)}"
    if isinstance(node, ForallIcc):
        return (f"∀ {node.var} ∈ Finset.Icc {node.lo} {node.hi}, "
                f"{_lean_prop(node.body, prefix)}")
    if isinstance(node, Not):
        return f"¬ {_lean_atom(node.body, prefix)}"
    if isinstance(node, And):
        return f"{_lean_atom(node.lhs, prefix)} ∧ {_lean_atom(node.rhs, prefix)}"
    if isinstance(node, Mem):
        return f"{_lean_expr(node.elem, prefix)} ∈ {prefix}_{node.table}"
    if isinstance(node, NotMem):
        return f"{_lean_expr(node.elem, prefix)} ∉ {prefix}_{node.table}"
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
