"""Rigorous edge argument-change enclosures for the T5 Turing band template.

Computes rational interval enclosures of the five RvM edge quantities consumed
by `TuringBand.band_count_eq`:

    AV(zeta, 2, T0, T1)          -- right vertical, Dirichlet-series regime
    AH(zeta, T1, 2, -1)          -- top horizontal (sigma from 2 down to -1)
    AH(zeta, T0, 2, -1)          -- bottom horizontal (shared with the band below)
    AV(GammaR, -1, T0, T1)       -- Archimedean vertical at sigma = -1
    AV(GammaR, 2, T0, T1)        -- Archimedean vertical at sigma = 2

Method per edge: adaptive subdivision into pieces whose CONTINUUM enclosure
(2nd-order Taylor for zeta via `enclose_zeta_segment`; acb ball for GammaR)
fits strictly inside a cardinal half-plane (witness w in {1, i, -1, -i}).
Within a piece the continuous argument relative to w stays in (-pi/2, pi/2),
so the piece's argument change equals the principal-arg difference of the
endpoint values relative to w -- enclosed by rigorous corner atan bounds
(flint arb.atan, exact dyadic extraction).  Piece intervals sum with outward
Fraction arithmetic.

The argChange definitions integrate UP verticals (T0 -> T1) and ALONG
horizontals x0 -> x1 (here 2 -> -1, i.e. right to left): we compute left-to-
right and negate.

Everything here is documented ARB NON-KERNEL INPUT -- the same trust class as
the previous route's boundary winding value.  conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction

from telperion.arb_enclosure import (
    _arb_ball_to_fractions,
    enclose_zeta_segment,
    _FLINT_AVAILABLE,
)

if _FLINT_AVAILABLE:
    import flint

__all__ = ["enclose_band_edges", "argchange_edge"]

# cardinal half-plane witnesses: multiply by conj(w) == rotate by -arg(w).
# w encoded as quadrant rotation r in {0,1,2,3}: w = i^r; z*conj(w) = rot_{-r}(z)
def _rot(box, r):
    """Rotate a rational box by -r quadrants: returns rotated box (re, im ranges)."""
    (x1, x2), (y1, y2) = box
    for _ in range(r % 4):
        # multiply by -i: (x + iy)(-i) = y - ix
        (x1, x2), (y1, y2) = (y1, y2), (-x2, -x1)
    return ((x1, x2), (y1, y2))


def _half_plane_witness(box):
    """Return r such that box rotated by -r lies strictly in {Re > 0}, else None."""
    for r in range(4):
        (x1, _x2), _ = _rot(box, r)
        if x1 > 0:
            return r
    return None


def _atan_bounds(q: Fraction, prec: int) -> tuple[Fraction, Fraction]:
    """Rigorous rational bounds on atan(q) via arb ball arithmetic."""
    x = flint.arb(q.numerator) / flint.arb(q.denominator)
    return _arb_ball_to_fractions(x.atan())


def _arg_bounds_right_half(box, prec: int) -> tuple[Fraction, Fraction]:
    """Rational bounds on arg over a box strictly in the right half-plane."""
    (x1, x2), (y1, y2) = box
    assert x1 > 0
    hi_at = y2 / x1 if y2 >= 0 else y2 / x2
    lo_at = y1 / x1 if y1 <= 0 else y1 / x2
    lo = _atan_bounds(lo_at, prec)[0]
    hi = _atan_bounds(hi_at, prec)[1]
    return lo, hi


def _piece_arg_interval(pbox, r, prec):
    """Arg interval of a tight point box relative to witness i^r (must fit)."""
    rb = _rot(pbox, r)
    if rb[0][0] <= 0:
        raise ValueError("point box escapes the piece's half-plane witness")
    return _arg_bounds_right_half(rb, prec)


def _gammaR_ball(s_re, im_lo, im_hi, prec):
    """acb ball enclosure of GammaR = pi^(-s/2) * Gamma(s/2) over a vertical piece."""
    ctx_prec = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        mid_im = (Fraction(im_lo) + Fraction(im_hi)) / 2
        rad_im = (Fraction(im_hi) - Fraction(im_lo)) / 2
        re_b = flint.arb(Fraction(s_re).numerator) / flint.arb(Fraction(s_re).denominator)
        im_b = flint.arb(
            flint.arb(mid_im.numerator) / flint.arb(mid_im.denominator),
            flint.arb(rad_im.numerator) / flint.arb(rad_im.denominator),
        )
        s = flint.acb(re_b, im_b)
        val = (-s / 2 * flint.arb.pi().log()).exp() * (s / 2).gamma()
        return (
            _arb_ball_to_fractions(val.real),
            _arb_ball_to_fractions(val.imag),
        )
    finally:
        flint.ctx.prec = ctx_prec


def _zeta_point(s_re, s_im, prec):
    ctx_prec = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        re_b = flint.arb(Fraction(s_re).numerator) / flint.arb(Fraction(s_re).denominator)
        im_b = flint.arb(Fraction(s_im).numerator) / flint.arb(Fraction(s_im).denominator)
        v = flint.acb(re_b, im_b).zeta()
        return (_arb_ball_to_fractions(v.real), _arb_ball_to_fractions(v.imag))
    finally:
        flint.ctx.prec = ctx_prec


def _gammaR_point(s_re, s_im, prec):
    return _gammaR_ball(s_re, s_im, s_im, prec)


def argchange_edge(kind, fixed, lo, hi, prec=192, seg_prec=192, max_depth=28):
    """Enclose the continuous argument change of zeta or GammaR along an edge.

    kind: 'zeta_vert' | 'zeta_horiz' | 'gammaR_vert'
    fixed: the fixed coordinate (sigma for verticals, T for horizontals)
    lo, hi: the varying coordinate range (increasing direction)
    Returns (L, H) Fractions with argChange in [L, H], where argChange follows
    the INCREASING direction of the varying coordinate.
    """
    fixed, lo, hi = Fraction(fixed), Fraction(lo), Fraction(hi)

    def seg_box(a, b):
        if kind == "zeta_vert":
            return enclose_zeta_segment(fixed, a, b, True, seg_prec)
        if kind == "zeta_horiz":
            return enclose_zeta_segment(fixed, a, b, False, seg_prec)
        return _gammaR_ball(fixed, a, b, seg_prec)

    def point_box(t):
        if kind == "zeta_vert":
            return _zeta_point(fixed, t, prec)
        if kind == "zeta_horiz":
            return _zeta_point(t, fixed, prec)
        return _gammaR_point(fixed, t, prec)

    # Seed the subdivision at a sane piece length BEFORE adaptive refinement:
    # evaluating the continuum enclosure over a whole 30-40-height edge means a
    # radius-20 ball through acb -- pathologically slow and hopelessly wide.
    # Seeds are sized to the argument speed of each edge kind:
    #   zeta_vert @ sigma=2 : arg wiggles slowly (Dirichlet regime)   -> ~2.0
    #   gammaR_vert         : arg rotates ~ (1/2) log(T/2pi) per unit -> ~0.5/logT
    #   zeta_horiz          : 3-unit strip crossing, zeros nearby      -> ~1/8
    import math as _m
    span = hi - lo
    if kind == "zeta_vert":
        seed_len = Fraction(2)
    elif kind == "gammaR_vert":
        logt = _m.log(max(float(lo), 8.0) / (2 * _m.pi))
        seed_len = Fraction(1, max(2, int(_m.ceil(logt))))
    else:
        seed_len = Fraction(1, 8)
    n_seed = max(1, int(_m.ceil(float(span / seed_len))))

    # adaptive piece list: (a, b, witness r)
    pieces = []
    stack = [(lo + span * k / n_seed, lo + span * (k + 1) / n_seed, 0)
             for k in range(n_seed)]
    while stack:
        a, b, depth = stack.pop()
        box = seg_box(a, b)
        r = _half_plane_witness(box)
        if r is None:
            if depth >= max_depth:
                raise RuntimeError(
                    f"argchange_edge[{kind}@{float(fixed)}]: no half-plane witness at "
                    f"[{float(a)},{float(b)}] depth {depth}")
            m = (a + b) / 2
            stack.append((m, b, depth + 1))
            stack.append((a, m, depth + 1))
            continue
        pieces.append((a, b, r))
    pieces.sort(key=lambda p: p[0])

    # endpoint arg intervals per piece, summed
    total_lo = Fraction(0)
    total_hi = Fraction(0)
    pcache = {}

    def pt(t):
        if t not in pcache:
            pcache[t] = point_box(t)
        return pcache[t]

    for a, b, r in pieces:
        la, ha = _piece_arg_interval(pt(a), r, prec)
        lb, hb = _piece_arg_interval(pt(b), r, prec)
        total_lo += lb - ha
        total_hi += hb - la
    return total_lo, total_hi


def enclose_band_edges(T0, T1, *, prec=192, bot_cache=None):
    """The five T5 edge enclosures for band [T0, T1].

    Returns dict with keys av2, aht, ahb, ag1, ag2 -> (L, H) Fractions, plus
    'top' raw (for caching as the next band's bottom).  `bot_cache` may supply
    the (L,H) of AH(zeta, T0, 2, -1) computed as a previous band's top."""
    T0, T1 = Fraction(T0), Fraction(T1)
    av2 = argchange_edge("zeta_vert", 2, T0, T1, prec=prec)
    # horizontals: compute along increasing sigma in [-1, 2], then negate
    # (argChangeHoriz f T 2 (-1) integrates 2 -> -1).
    if bot_cache is not None:
        ahb = bot_cache
    else:
        raw = argchange_edge("zeta_horiz", T0, Fraction(-1), Fraction(2), prec=prec)
        ahb = (-raw[1], -raw[0])
    raw_top = argchange_edge("zeta_horiz", T1, Fraction(-1), Fraction(2), prec=prec)
    aht = (-raw_top[1], -raw_top[0])
    ag1 = argchange_edge("gammaR_vert", -1, T0, T1, prec=prec)
    ag2 = argchange_edge("gammaR_vert", 2, T0, T1, prec=prec)
    return {"av2": av2, "aht": aht, "ahb": ahb, "ag1": ag1, "ag2": ag2}
