"""Pólya lifting: certify true-but-refused inequalities by multiplying through
by powers of (1 + Σ symbols).

Pólya's theorem: a form strictly positive on the standard simplex becomes,
after multiplication by (x₁ + ... + xₙ)^N for some finite N, a polynomial with
all-positive coefficients.  The inhomogeneous orthant version used here: if
``num`` is strictly positive on [0, ∞)ⁿ (including its top-degree behavior),
then ``num · (1 + Σxᵢ)^N`` has all-nonnegative coefficients for some N — and
the lifted num/den pair is again a Polya certificate, since (1 + Σxᵢ)^N is a
positive factor the denominator absorbs.

The honest boundary, which the campaign's own mathematics illustrates: if
``num`` has a ZERO on the closed orthant (an equality case — a tie), no finite
N works; the coefficients approach nonnegativity but never arrive.  Lifting
certifies strict positivity only.  The workflow for tie-touching claims is
subdivision (isolate the tie region) + lifting (certify the strict pieces) +
tie-aware treatment of the residual — see subdivide.py and METHODOLOGY.
"""
from __future__ import annotations

import sympy as sp


def polya_lift(num: sp.Expr, syms, max_n: int) -> tuple[int, sp.Expr] | None:
    """Find the smallest N ≤ max_n with num · (1 + Σsyms)^N all-nonneg-integer.

    Returns (N, lifted_num expanded) or None.  N = 0 means num already
    qualifies.  Coefficients grow like C(N + deg, deg) — keep max_n modest
    (the default knob is 8; certificates found at large N are usually a sign
    the claim is nearly tight and subdivision is the better tool).
    """
    lifter = 1 + sp.Add(*syms) if syms else sp.Integer(1)
    cur = sp.expand(num)
    for n in range(max_n + 1):
        try:
            p = sp.Poly(cur, *syms)
        except sp.PolynomialError:
            return None
        if all(c >= 0 and sp.Integer(c) == c for c in p.coeffs()):
            return n, cur
        cur = sp.expand(cur * lifter)
    return None
