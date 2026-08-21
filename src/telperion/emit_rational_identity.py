"""Rational-function identity emitter — `lhs = rhs` over ℚ on a ray.

Crystallizes the shape hand-rolled by the knapsack_sos Gram-bridge generator
(2026-08-20): identities between rational functions of one variable whose
denominators factor into rational-rooted linear factors, valid on a ray
`c0 < n` that keeps every factor nonzero.  The certificate is exact sympy
cancellation (`lhs − rhs = 0` as a rational function) plus the root audit
(every denominator root ≤ c0); the emitted Lean is the field_simp spine:

    theorem <name> : ∀ n : ℚ, (c0 : ℚ) < n → lhs = rhs := by
      intro n hn
      have h_i : n - a_i ≠ 0 := ne_of_gt (by linarith)   -- per root a_i
      field_simp
      all_goals ring

(`all_goals ring` because field_simp closes trivial instances outright —
the 2026-08-20 footgun.)  REFUSALS: a non-identity (nonzero cancellation);
a denominator root above the ray bound; a non-linear or irrational-rooted
denominator factor (outside this emitter's contract).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean


def _render(expr) -> str:
    """Structure-preserving Lean renderer: canonicalization is the PROOF's
    job (field_simp/ring); the STATEMENT must keep the user's two shapes
    distinct (the nonvacuity gate rejects the canonicalized X = X collapse)."""
    if isinstance(expr, sp.Symbol):
        return str(expr)
    if isinstance(expr, sp.Integer):
        return str(expr) if expr >= 0 else f"(-{-expr})"
    if isinstance(expr, sp.Rational):
        return f"({_render(sp.Integer(expr.p))} / {_render(sp.Integer(expr.q))})"
    if isinstance(expr, sp.Add):
        return "(" + " + ".join(_render(a) for a in expr.args) + ")"
    if isinstance(expr, sp.Pow):
        base, exp = expr.args
        if exp == -1:
            return f"(1 / {_render(base)})"
        if isinstance(exp, sp.Integer) and exp < -1:
            return f"(1 / {_render(base)} ^ {-int(exp)})"
        if isinstance(exp, sp.Integer) and exp > 0:
            return f"{_render(base)} ^ {int(exp)}"
        raise ValueError(f"unsupported exponent {exp} in {expr}")
    if isinstance(expr, sp.Mul):
        num, den = [], []
        for a in expr.args:
            if isinstance(a, sp.Pow) and isinstance(a.args[1], sp.Integer) \
                    and a.args[1] < 0:
                den.append(a.args[0] if a.args[1] == -1
                           else sp.Pow(a.args[0], -a.args[1]))
            elif isinstance(a, sp.Rational) and not isinstance(a, sp.Integer):
                num.append(sp.Integer(a.p))
                den.append(sp.Integer(a.q))
            else:
                num.append(a)
        num_s = " * ".join(_render(a) for a in num) if num else "1"
        if not den:
            return f"({num_s})"
        den_s = " * ".join(_render(a) for a in den)
        return f"(({num_s}) / ({den_s}))"
    raise ValueError(f"unsupported node {type(expr).__name__} in {expr}")


def _split_frac(expr):
    """Top-level (numerator-args, denominator-atoms) decomposition mirroring
    the renderer's Mul flattening.  Denominator atoms are the bases of
    negative powers (with multiplicity via repeated listing for powers)."""
    num, den = [], []
    args = expr.args if isinstance(expr, sp.Mul) else (expr,)
    for a in args:
        if isinstance(a, sp.Pow) and isinstance(a.args[1], sp.Integer) \
                and a.args[1] < 0:
            den.extend([a.args[0]] * int(-a.args[1]))
        elif isinstance(a, sp.Rational) and not isinstance(a, sp.Integer):
            num.append(sp.Integer(a.p))
            den.append(sp.Integer(a.q))
        else:
            num.append(a)
    return num, den


def _assert_no_variable_division(parts, name):
    """Refuse variable denominators hiding below the top level (outside the
    cross-multiplication contract)."""
    for part in parts:
        for sub in sp.preorder_traversal(part):
            if isinstance(sub, sp.Pow) and isinstance(sub.args[1], sp.Integer) \
                    and sub.args[1] < 0 and sub.args[0].free_symbols:
                raise ValueError(
                    f"rational_identity instance '{name}' REFUSED: variable "
                    f"denominator {sub.args[0]} below the top level — outside "
                    "the cross-multiplication contract (restructure as a "
                    "single top-level fraction)")


def _den_atoms(expr, out):
    """Collect non-numeric denominator atom subexpressions (renderer-aligned):
    the exact objects whose ne-zero facts field_simp will need."""
    if isinstance(expr, sp.Pow) and isinstance(expr.args[1], sp.Integer) \
            and expr.args[1] < 0:
        base = expr.args[0]
        if base.free_symbols:
            out.append(base)
        _den_atoms(base, out)
        return
    if isinstance(expr, (sp.Add, sp.Mul, sp.Pow)):
        for a in expr.args:
            _den_atoms(a, out)


from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


def _denominator_roots(expr, sym):
    """Rational roots of the linear factors of expr's denominator; refuse rest."""
    _num, den = sp.fraction(sp.together(expr))
    roots = []
    for factor, _mult in sp.factor_list(den)[1]:
        poly = sp.Poly(factor, sym)
        if poly.total_degree() == 0:
            continue
        if poly.total_degree() != 1:
            raise ValueError(
                f"denominator factor {factor} is not linear in {sym}")
        a, b = poly.all_coeffs()
        root = sp.Rational(-b, a) if a != 0 else None
        if root is None:
            raise ValueError(f"degenerate denominator factor {factor}")
        roots.append(sp.nsimplify(root))
    return roots


def certify_rational_identity_point(family, pt, name):
    """Certify one rational identity: (CertifiedInstance, n_checks)."""
    lhs, rhs, c0 = family.special[1](pt)
    lhs, rhs = sp.sympify(lhs), sp.sympify(rhs)
    c0 = sp.Rational(sp.sympify(c0))
    syms = tuple(family.symbols)
    if len(syms) != 1:
        raise ValueError("rational_identity families are univariate (one symbol)")
    sym = syms[0]

    diff = sp.cancel(sp.together(lhs - rhs))
    if diff != 0:
        raise ValueError(
            f"rational_identity instance '{name}' REFUSED: lhs − rhs does not "
            f"cancel to 0 (got {diff}) — not an identity")
    checks = 1

    roots = sorted(set(_denominator_roots(lhs, sym) + _denominator_roots(rhs, sym)))
    for a in roots:
        if not a.is_rational:
            raise ValueError(
                f"rational_identity instance '{name}' REFUSED: irrational "
                f"denominator root {a}")
        if a > c0:
            raise ValueError(
                f"rational_identity instance '{name}' REFUSED: denominator root "
                f"{a} exceeds the ray bound {c0} — the identity's domain does "
                "not contain the claimed ray")
        checks += 1

    for side in (lhs, rhs):
        num, _den = _split_frac(side)
        _assert_no_variable_division(num, name)
        checks += 1

    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(lhs, rhs, c0, roots),
    )
    return inst, checks


@dataclass
class RationalIdentityEmitter(Emitter):
    """Emit `∀ n : ℚ, c0 < n → lhs = rhs` via ne-zero haves + field_simp + ring."""

    def __post_init__(self):
        self.kind = "rational_identity"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        sym = tuple(fam.family.symbols)[0]
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            lhs, rhs, c0, roots = inst.payload  # type: ignore[misc]
            lhs_s = _render(lhs)
            rhs_s = _render(rhs)
            c0_s = expr_lean(sp.Rational(c0), (sym,))
            haves = []
            chains = []
            for tag, side in (("L", lhs), ("R", rhs)):
                _num, den = _split_frac(side)
                var_atoms = [a for a in den if a.free_symbols]
                for i, a in enumerate(var_atoms):
                    haves.append(
                        f"  have h{tag}{i} : ({_render(a)} : ℚ) ≠ 0 := "
                        f"ne_of_gt (by linarith)\n")
                if not den:
                    chains.append(None)
                else:
                    chain = None
                    j = 0
                    for a in den:
                        piece = (f"h{tag}{j}" if a.free_symbols
                                 else f"(by norm_num : ({_render(a)} : ℚ) ≠ 0)")
                        if a.free_symbols:
                            j += 1
                        chain = piece if chain is None \
                            else f"(mul_ne_zero {chain} {piece})"
                    chains.append(chain)
            hL, hR = chains
            if hL and hR:
                spine = f"  rw [div_eq_div_iff {hL} {hR}]\n  ring\n"
            elif hL:
                spine = f"  rw [div_eq_iff {hL}]\n  ring\n"
            elif hR:
                spine = f"  rw [eq_div_iff {hR}]\n  ring\n"
            else:
                spine = "  ring\n"
            lines.append(
                f"-- {inst.lean_name}: rational-function identity on the ray "
                f"{c0} < {sym} (denominator roots {[str(a) for a in roots]}).\n"
                f"theorem {inst.lean_name} : ∀ {sym} : ℚ, ({c0_s} : ℚ) < {sym} → "
                f"{lhs_s} = {rhs_s} := by\n"
                f"  intro {sym} hn\n"
                f"{''.join(haves)}"
                f"{spine}")
            n_thm += 1
        return "\n".join(lines), n_thm


def rational_identity_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a rational-identity family (kind='rational_identity').

    spec: ``pt -> (lhs, rhs, c0)`` — the claimed identity ``lhs = rhs`` of
    rational functions of the single family symbol, on the ray ``c0 < n``.
    """
    if len(tuple(symbols)) != 1:
        raise ValueError("rational_identity families require exactly one symbol")
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("rational_identity", spec),
        constants=constants or {},
    )
