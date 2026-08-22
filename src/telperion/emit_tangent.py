"""Tangent-line-trick emitter — a symmetric-sum (combinatorial) inequality.

Compete where the frontier is weakest: symmetric / combinatorial inequalities.
For a CONVEX polynomial ``f`` (degree 2 or 4) and reals ``x₁..xₙ`` with
``Σxᵢ = S``, the tangent line ``L`` at ``a = S/n`` gives the tangent-line (Jensen)
bound

    Σf(xᵢ) ≥ n·f(a) = B.

The surplus ``f(x) − L(x)`` has a double root at ``a`` and an EXACT RATIONAL
sum-of-squares form (for a quartic, ``f−L = (x−a)²·q`` with ``q`` a nonnegative
quadratic, split by completing the square).  So each per-term inequality is the
robust, search-free

    have hᵢ : 0 ≤ f(xᵢ) − L(xᵢ) := by
      have : f(xᵢ) − L(xᵢ) = Σ cⱼ·bⱼ(xᵢ)² := by ring
      rw [this]; positivity

and the whole claim assembles by ``linarith`` over the ``hᵢ`` and the linear
constraint ``hsum`` (``ΣL(xᵢ) = B`` uses ``Σxᵢ = S``).

NEGATIVE CONTROL: a non-convex ``f`` (surplus lacks a nonnegative-SOS form) is
refused at certification.  Degrees > 4 (nonnegative quartic-or-higher cofactor)
are named-open — the same identity extends with a rational SOS of the cofactor.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TangentCertificate:
    """A verified tangent-line certificate for a convex polynomial (deg 2 or 4)."""

    n: int
    f: sp.Expr
    x: sp.Symbol
    degree: int
    S: sp.Rational
    a: sp.Rational           # tangent point S/n
    slope: sp.Rational       # f'(a)
    intercept: sp.Rational   # f(a) − slope·a, so L(x) = intercept + slope·x
    B: sp.Rational           # n·f(a)
    sos_terms: tuple         # ((coeff, base), ...): f − L = Σ coeff·base²


def _rational_sos_of_surplus(fL, x, a):
    """Exact rational SOS of the tangent surplus ``fL = f − L`` (double root at
    ``a``).  Supports degree 2 (single square) and degree 4 (completing the
    square on the quadratic cofactor).  Returns ``[(coeff, base), ...]`` with
    every ``coeff ≥ 0``, or None if no such rational SOS exists (f not convex, or
    a cofactor of degree > 2)."""
    fL = sp.expand(fL)
    if fL == 0:
        return None  # a vacuous (constant-zero) surplus is not a real bound
    q, r = sp.div(fL, sp.expand((x - a) ** 2), x)
    if sp.expand(r) != 0:
        return None  # no double root at a
    q = sp.expand(q)
    pq = sp.Poly(q, x)
    if pq.degree() == 0:
        c = pq.coeff_monomial(1)
        return [(c, x - a)] if c > 0 else None
    if pq.degree() == 2:
        c2 = pq.coeff_monomial(x**2)
        c1 = pq.coeff_monomial(x)
        c0 = pq.coeff_monomial(1)
        if c2 <= 0:
            return None
        beta = sp.Rational(-c1, 2 * c2)
        gamma = c0 - c2 * beta**2
        if gamma < 0:
            return None  # cofactor not nonnegative → f not convex enough
        terms = [(c2, sp.expand((x - a) * (x - beta)))]
        if gamma != 0:
            terms.append((gamma, x - a))
        return terms
    return None  # cofactor degree > 2: named-open


def tangent_certificate(*, f, x, n, S) -> TangentCertificate:
    """Build and EXACTLY self-check a tangent-line certificate for a convex
    polynomial of degree 2 or 4.  Refuses a non-convex f (no nonneg SOS surplus),
    n < 2, or an unsupported degree."""
    f = sp.expand(sp.sympify(f))
    S = sp.nsimplify(S)
    n = int(n)
    if n < 2:
        raise ValueError("tangent-line trick needs n ≥ 2 terms")
    deg = sp.Poly(f, x).degree()
    if deg not in (2, 4):
        raise ValueError(
            f"tangent emitter supports convex degree 2 or 4; got degree {deg} "
            "(higher: the same identity extends with a rational SOS of the "
            "cofactor — named-open)"
        )
    a = sp.Rational(S, n)
    fa = f.subs(x, a)
    m = sp.diff(f, x).subs(x, a)
    intercept = sp.nsimplify(fa - m * a)
    slope = sp.nsimplify(m)
    B = sp.nsimplify(n * fa)
    fL = sp.expand(f - (intercept + slope * x))
    sos = _rational_sos_of_surplus(fL, x, a)
    if sos is None:
        raise ValueError(
            f"tangent surplus f−L is not a certifiable rational SOS (f is not "
            f"convex with a double root at a = {a}) — refused (negative control)"
        )
    # exact SOS self-check
    if sp.expand(fL - sum(c * base**2 for c, base in sos)) != 0:
        raise ValueError("tangent SOS self-check failed — certificate rejected")
    # exact assembly self-check: Σf − B = Σ(f−L) + slope·(Σx − S)
    xs = sp.symbols(f"x1:{n + 1}")
    lhs = sum(f.subs(x, xi) for xi in xs) - B
    rhs = sum(fL.subs(x, xi) for xi in xs) + slope * (sum(xs) - S)
    if sp.expand(lhs - rhs) != 0:
        raise ValueError("tangent assembly self-check failed — certificate rejected")
    return TangentCertificate(
        n=n, f=f, x=x, degree=deg, S=S, a=a, slope=slope,
        intercept=intercept, B=B, sos_terms=tuple(sos),
    )


def certify_tangent_point(family, pt, name):
    """Certify one tangent instance from ``family.special[1](pt) -> ((f, x), n, S)``."""
    (f, x), n, S = family.special[1](pt)
    cert = tangent_certificate(f=f, x=x, n=n, S=S)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, cert.n


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class TangentSumEmitter(Emitter):
    """Emit `B ≤ Σf(xᵢ)` (convex tangent-line bound) — one theorem per instance,
    per-term surplus by `ring`+`positivity`, assembled by `linarith` + `hsum`."""

    def __post_init__(self):
        self.kind = "tangent"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: TangentCertificate = inst.payload  # type: ignore[assignment]
            n = cert.n
            x = cert.x

            def xi(i):
                return sp.Symbol(f"x{i}")

            def f_at(i):
                return expr_lean(cert.f.subs(x, xi(i)), (xi(i),))

            def L_at(i):
                return f"({rat_lean(cert.intercept)} + {rat_lean(cert.slope)} * x{i})"

            def sos_at(i):
                return " + ".join(
                    f"{rat_lean(c)} * ({expr_lean(sp.expand(base.subs(x, xi(i))), (xi(i),))})^2"
                    for c, base in cert.sos_terms
                )

            binders = " ".join(f"x{i}" for i in range(1, n + 1))
            hsum_lhs = " + ".join(f"x{i}" for i in range(1, n + 1))
            fterms = " + ".join(f"({f_at(i)})" for i in range(1, n + 1))
            haves = "".join(
                f"  have h{i} : (0:ℝ) ≤ ({f_at(i)}) - {L_at(i)} := by\n"
                f"    have e{i} : ({f_at(i)}) - {L_at(i)} = {sos_at(i)} := by ring\n"
                f"    rw [e{i}]; positivity\n"
                for i in range(1, n + 1)
            )
            hint_names = ", ".join(f"h{i}" for i in range(1, n + 1))
            lines.append(
                f"theorem {inst.lean_name} ({binders} : ℝ) "
                f"(hsum : {hsum_lhs} = {rat_lean(cert.S)}) :\n"
                f"    ({rat_lean(cert.B)} : ℝ) ≤ {fterms} := by\n"
                f"{haves}"
                f"  linarith [{hint_names}, hsum]\n"
            )
            nthm += 1
        return "".join(lines), nthm


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def tangent_sum_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a tangent-line-trick family (kind='tangent').

    ``spec``: a callable ``pt -> ((f, x), n, S)`` where ``f`` is a convex
    polynomial (degree 2 or 4) in the symbol ``x``, ``n ≥ 2`` the number of
    terms, and ``S`` the sum-constraint value ``Σxᵢ = S``.  Refuses a non-convex
    f or unsupported degree (no Lean for a non-member)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("tangent", spec),
        constants=dict(constants or {}),
    )
