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


def _univariate_rational_sos(p, x):
    """Exact rational SOS of a univariate ``p ≥ 0``: returns ``[(coeff, base),
    ...]`` with every ``coeff > 0`` rational and ``p = Σ coeff·base²``, or None
    when no such factorization exists.

    Method (exact, sympy-only, ANY degree): factor ``p`` over ℚ.  A nonnegative
    ``p`` is a positive constant times even powers of real-linear factors and
    (any powers of) rational irreducible quadratics.  Each ``ℓ^{2k}`` is the
    square ``(ℓ^k)²``; each positive irreducible quadratic ``a₂(x−h)²+k``
    (``a₂,k>0``) is the weighted two-square ``a₂·(x−h)² + k·1²``; a product of
    weighted sums-of-squares distributes term-by-term (a product of squares is a
    square).  Refuses an odd-multiplicity real root (``p`` would change sign) or
    an irreducible factor of degree ≥ 3 (needs a Pourchet-style SOS — named-open)."""
    p = sp.expand(p)
    if p == 0:
        return None  # a constant-zero surplus is not a real bound
    const, facs = sp.factor_list(p)
    const = sp.nsimplify(const)
    if const <= 0:
        return None
    sos = [(const, sp.Integer(1))]  # const · 1²

    def _distribute(A, B):
        return [(sp.nsimplify(ca * cb), sp.expand(sa * sb))
                for ca, sa in A for cb, sb in B]

    for fac, mult in facs:
        fp = sp.Poly(fac, x)
        d = fp.degree()
        if d == 1:
            if mult % 2:
                return None  # odd-multiplicity real root → sign change
            fsos = [(sp.Integer(1), sp.expand(fac ** (mult // 2)))]
        elif d == 2:
            a2 = fp.coeff_monomial(x**2)
            a1 = fp.coeff_monomial(x)
            a0 = fp.coeff_monomial(1)
            if a2 <= 0 or a1**2 - 4 * a2 * a0 >= 0:
                return None  # not a positive-definite irreducible quadratic
            h = sp.Rational(-a1, 2 * a2)
            k = a0 - a2 * h**2
            base = [(a2, sp.expand(x - h)), (k, sp.Integer(1))]
            if mult % 2 == 0:
                fsos = [(sp.Integer(1), sp.expand(fac ** (mult // 2)))]
            else:
                carry = sp.expand(fac ** ((mult - 1) // 2))
                fsos = [(c, sp.expand(s * carry)) for c, s in base]
        else:
            return None  # irreducible degree ≥ 3: named-open
        sos = _distribute(sos, fsos)

    # combine like bases for a compact certificate
    merged: dict = {}
    for c, base in sos:
        merged[base] = merged.get(base, sp.Integer(0)) + c
    return [(c, base) for base, c in merged.items() if c != 0]


def tangent_certificate(*, f, x, n, S) -> TangentCertificate:
    """Build and EXACTLY self-check a tangent-line certificate for a convex
    polynomial of any even degree whose surplus f−L is a rational SOS.  Refuses a
    non-convex f (surplus lacks a rational SOS) or n < 2."""
    f = sp.expand(sp.sympify(f))
    S = sp.nsimplify(S)
    n = int(n)
    if n < 2:
        raise ValueError("tangent-line trick needs n ≥ 2 terms")
    deg = sp.Poly(f, x).degree()
    if deg < 2:
        raise ValueError(f"tangent-line trick needs a non-linear f; got degree {deg}")
    a = sp.Rational(S, n)
    fa = f.subs(x, a)
    m = sp.diff(f, x).subs(x, a)
    intercept = sp.nsimplify(fa - m * a)
    slope = sp.nsimplify(m)
    B = sp.nsimplify(n * fa)
    fL = sp.expand(f - (intercept + slope * x))
    sos = _univariate_rational_sos(fL, x)
    if sos is None:
        raise ValueError(
            f"tangent surplus f−L is not a certifiable rational SOS (f is not "
            f"convex, or its surplus has an irreducible factor of degree ≥ 3 — "
            f"named-open) — refused (negative control)"
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
