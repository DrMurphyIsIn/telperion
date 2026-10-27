"""Rigorous rational margin of the degree-2 Jensen discriminant (engine-owned; flint-free).

Moved from telperion.rh_jensen.jensen in step 1 of the standalone extraction so the engine's
`emit_jensen_polynomial_hyperbolicity` does not import the RH lab. rh_jensen re-exports it.
"""
from __future__ import annotations

from fractions import Fraction


def disc2_margin(box: list[tuple[Fraction, Fraction]]) -> Fraction:
    """Rigorous rational lower bound on the d=2 discriminant D(c) = c_1^2 - 4*c_0*c_2.

    This is the discriminant b^2 - 4ac of the quadratic Jensen polynomial
    a*X^2 + b*X + c with a = c_2, b = c_1, c = c_0.

    Computes:
        lower(c_1^2) - 4 * upper(c_0 * c_2)

    where both extrema are taken over ALL c in the box. A positive return value
    certifies that every polynomial in the box has D(c) > 0, i.e., is real-rooted.

    Parameters
    ----------
    box : list of 3 (lo, hi) pairs as exact fractions.Fraction
        box[k] = (lo_k, hi_k) rigorous enclosure of c_k, k=0,1,2.

    Returns
    -------
    Fraction: a certified rational lower bound on min_{c in box} D(c).
    """
    if len(box) != 3:
        raise ValueError(f"disc2_margin requires a box of length 3, got {len(box)}")

    lo0, hi0 = box[0]
    lo1, hi1 = box[1]
    lo2, hi2 = box[2]

    # --- lower bound of c_1^2 over [lo1, hi1] ---
    # c_1^2 is a convex function. Its minimum over [lo1, hi1] is:
    #   0          if the interval straddles zero (lo1 <= 0 <= hi1)
    #   min(lo1^2, hi1^2) otherwise (the nearer endpoint to zero, squared)
    if lo1 <= Fraction(0) <= hi1:
        c1_sq_lower = Fraction(0)
    else:
        c1_sq_lower = min(lo1 * lo1, hi1 * hi1)

    # --- upper bound of c_0 * c_2 over [lo0, hi0] x [lo2, hi2] ---
    # The product of two interval variables achieves its extremes at the
    # four corners; we take the max.
    c0c2_upper = max(
        lo0 * lo2,
        lo0 * hi2,
        hi0 * lo2,
        hi0 * hi2,
    )

    return c1_sq_lower - Fraction(4) * c0c2_upper
