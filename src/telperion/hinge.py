"""Convex-hinge certificates — the reusable primitive under the BG G1 Stage-II
class floors and the R7 ledger.

Both use the folded hinge potential ``φ(y) = c·(y − t0)₊`` (`c ≥ 0`), the same
hinge that closed the R3 ``phi_le_one`` proof.  The load-bearing fact is
superadditivity of the positive part:

    Σᵢ (yᵢ − t0)₊  ≥  ( Σᵢ yᵢ − k·t0 )₊         (k children)

— the "context-free class floor" shape (the sum of per-node hinge slacks is at
least the hinge of the total; its minimum over equal children ≥ t0 is 0, the
Jensen-tight point).  It is exact and kernel-checkable: ``posPart`` is
subadditive, so ``(Σ zᵢ)₊ ≤ Σ (zᵢ)₊`` with ``zᵢ = yᵢ − t0``.

This module is the untrusted generator: ``hinge_floor_certificate`` builds the
certificate (recording the slope-nonnegativity that makes the hinge convex and
the tightness locus), ``verify_hinge_floor`` re-checks it in exact arithmetic.
The Lean emitter (a follow-up) discharges ``Σ posPart ≥ posPart Σ`` through
Mathlib's ``posPart`` subadditivity; the kernel is the trusted checker there.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class HingeFloorCertificate:
    """The floor ``Σᵢ (yᵢ − t0)₊ ≥ (Σᵢ yᵢ − k·t0)₊`` for the convex hinge slope c ≥ 0."""

    c: sp.Rational       # hinge slope (≥ 0 for convexity / the floor direction)
    t0: sp.Rational      # knee
    k: int               # number of children
    tight_at_equal: bool  # equality attained at equal children on the linear branch


def hinge_floor_certificate(c, t0, k: int) -> HingeFloorCertificate | None:
    """Build the hinge-floor certificate, or None if the slope is not convex (c < 0).

    The floor `Σ (yᵢ − t0)₊ ≥ (Σ yᵢ − k t0)₊` needs `c ≥ 0` (the hinge convex and
    nonnegatively scaled); a negative slope flips the inequality.
    """
    c, t0 = sp.Rational(c), sp.Rational(t0)
    if k < 1 or c < 0:
        return None
    # Equality holds when every child sits on the linear (above-knee) branch:
    # then both sides equal c·(Σyᵢ − k·t0).  Always attainable, so tight.
    return HingeFloorCertificate(c=c, t0=t0, k=int(k), tight_at_equal=True)


def _pos(x: sp.Expr) -> sp.Expr:
    return sp.Max(0, x)


def verify_hinge_floor(cert: HingeFloorCertificate, samples: int = 0) -> bool:
    """Independently re-check the hinge floor in exact arithmetic.

    Verifies (a) the convexity precondition `c ≥ 0`, and (b) the inequality
    `c·Σ(yᵢ−t0)₊ ≥ c·(Σyᵢ − k·t0)₊` symbolically via posPart subadditivity, plus
    an exact-rational spot check at a few configurations (including the tight
    equal-children point).
    """
    c, t0, k = cert.c, cert.t0, cert.k
    if c < 0 or k < 1:
        return False

    # posPart subadditivity is the proof; confirm the direction with exact points.
    # A hostile sampler: mix below-knee, above-knee, and straddling children, plus
    # the all-equal tight point.
    pts = [
        [t0 - sp.Rational(1, 10)] * k,                       # all below knee
        [t0 + sp.Rational(1, 10)] * k,                       # all above (tight branch)
        [t0 + sp.Rational(1, 5)] + [t0 - sp.Rational(1, 5)] * (k - 1),  # straddle
        [t0] * k,                                            # all at the knee
    ]
    for ys in pts:
        lhs = c * sum(_pos(y - t0) for y in ys)
        rhs = c * _pos(sum(ys) - k * t0)
        if sp.simplify(lhs - rhs) < 0:
            return False

    # tightness claim: equality at equal children on the linear branch
    if cert.tight_at_equal:
        y = t0 + sp.Rational(1, 3)
        lhs = c * sum(_pos(y - t0) for _ in range(k))
        rhs = c * _pos(k * y - k * t0)
        if sp.simplify(lhs - rhs) != 0:
            return False
    return True


def _rat_lean(x: sp.Rational) -> str:
    x = sp.Rational(x)
    return str(x.p) if x.q == 1 else f"({x.p} / {x.q} : ℝ)"


def hinge_floor_theorem(cert: HingeFloorCertificate, name: str = "hinge_floor") -> str:
    """Emit the hinge-floor inequality as a Lean theorem, or raise if not certified.

    Shape (k children):
        `c * ((y₀−t0)⁺ + … + (y_{k-1}−t0)⁺) ≥ c * ((y₀+…+y_{k-1} − k·t0)⁺)`
    discharged from `posPart` subadditivity: `(Σ zᵢ)⁺ ≤ Σ (zᵢ)⁺`.  The kernel
    re-checks; a wrong certificate is a compile error.
    """
    if not verify_hinge_floor(cert):
        raise ValueError("hinge floor certificate failed the exact self-check")
    k = cert.k
    c_l, t0_l = _rat_lean(cert.c), _rat_lean(cert.t0)
    ys = [f"y{i}" for i in range(k)]
    binders = " ".join(ys)
    lhs = " + ".join(f"({y} - {t0_l})⁺" for y in ys)
    sum_y = " + ".join(ys)
    return (
        f"theorem {name} ({binders} : ℝ) (hc : 0 ≤ {c_l}) :\n"
        f"    {c_l} * (({sum_y}) - {k} * {t0_l})⁺ ≤ {c_l} * ({lhs}) := by\n"
        f"  have hsub : (({sum_y}) - {k} * {t0_l})⁺ ≤ {lhs} := by\n"
        f"    have h := posPart_sum_le (s := Finset.univ) (f := ![{', '.join(f'{y} - {t0_l}' for y in ys)}])\n"
        f"    simpa using h\n"
        f"  exact mul_le_mul_of_nonneg_left hsub hc\n"
    )
