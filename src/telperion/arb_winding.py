"""Rigorous argument-principle winding numbers on rational rectangles (segment enclosure).

conjecture1_proved = False.  This module counts zeros of an analytic function in a box.  It says nothing
about RH.

WHY THIS EXISTS (2026-10-14).  The first DH winding routine, ``arb_dh.winding_number`` (now
``arb_dh.winding_number_sampled_heuristic``), evaluated f in Arb balls only at boundary NODES and summed
quadrant advances between consecutive nodes.  The ball values were rigorous, but the count was not.  Two
nodes in the same or adjacent quadrants say nothing about the path between them: a pair of zeros close to an
edge, between two nodes, adds 2 pi to the true argument change without changing any sampled quadrant.  An
independent AI audit (2026-10-14) built such a case: a zero pair at x = 1/7, about 1e-9 above the bottom edge of [0,1]^2.  Node sampling returns 1 at
every dyadic density (1/7 is never a node), and the true count is 2.  Doubling the density does not help.

THE METHOD here encloses f on every boundary SEGMENT, not just at its endpoints.  For an axis-aligned segment
with midpoint m and half-length r:

  1. B is an Arb ball covering the segment.  sup_B |f'| comes from a derivative jet (f, f') on B.
  2. rho = r * sup_B |f'| + (the half-widths of the ball for f(m)).  By the mean-value bound,
     |f(z) - c| <= rho on the whole segment, where c is the exact rational centre of the ball for f(m).
  3. The routine requires 4 rho^2 < |c|^2, checked in exact Fractions.  Every image point w then satisfies
     |w/c - 1| < 1/2, so w/c stays in a disc inside the right half-plane and Arg(w/c) is continuous and
     lies in (-pi/6, pi/6) along the segment.
  4. The continuous argument change over the segment is then exactly Arg(f(q)/c) - Arg(f(p)/c), with the
     endpoint values enclosed in Arb.
  5. A segment that fails step 3 is bisected, up to ``max_depth`` levels.  Past that the routine REFUSES
     (RuntimeError): a zero may lie on or extremely near the contour.
  6. The total, divided by 2 pi, is an Arb ball.  It is accepted only if it lies within 1/4 of a unique
     integer.

A wide endpoint ball can only widen the total and lead to a refusal, never to a wrong integer.  The winding
number of f is (zeros - poles) inside the box, so a function with poles must declare them.  The routine
refuses any box whose closed rectangle contains a declared pole (for example s = 1 for zeta).

POLES MUST BE DECLARED.  The guard only knows the poles it is told about.  A bare acb_series function passed
to ``rigorous_winding`` is wrapped as ENTIRE (``poles=()``): if it has a pole inside the box, the result is
silently zeros minus poles (one zero and one pole give 0).  For any count that will be certified, wrap the
function with ``from_series(fn, poles=[...])`` (an empty list for an entire function, stated on purpose).
A pole ON or very near the contour is safe either way: its enclosures are non-finite or huge, so the segment
is bisected and finally refused.

REFUSALS ARE RuntimeError.  A segment that cannot be certified, a total that is not near an integer, and a
non-finite enclosure (``NonFiniteEnclosure``, a RuntimeError subclass, raised for an infinite or NaN ball,
e.g. near an undeclared pole or on overflow) all raise RuntimeError, so retry loops that catch RuntimeError
see one exception type.  ValueError is kept for bad requests: an inverted box or a declared pole in the box.

TRUST CLASS: Arb interval arithmetic (python-flint), NOT a Lean kernel proof.  f and its derivative bound
come from the same FLINT evaluation, so this is not an independent cross-check of the evaluator itself.

Ported from ``arb_fakes.rigorous_winding`` on branch wall2/telperion-fakes (track T), which the audit judged
sound, and made generic over the function plus the pole guard the audit recommended.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable, Iterable

__all__ = [
    "METHOD", "ArbAnalytic", "NonFiniteEnclosure", "from_series", "rigorous_winding", "count_strips",
    "localise_zero",
]

#: The ``method`` label every certificate made with this module records.
METHOD = "segment-enclosure (centred form, |f - c| <= |c|/2 per segment)"


def _flint():
    from flint import acb, acb_series, arb, ctx, fmpq
    return acb, acb_series, arb, ctx, fmpq


def _arb_q(x: Fraction):
    """An Arb ball containing the exact rational x."""
    _, _, arb, _, fmpq = _flint()
    return arb(fmpq(x.numerator, x.denominator))


def _acb_point(re: Fraction, im: Fraction):
    acb = _flint()[0]
    return acb(_arb_q(re), _arb_q(im))


class NonFiniteEnclosure(RuntimeError):
    """An Arb enclosure came back infinite or NaN (near a pole, or on overflow).  A RuntimeError, so it is a
    refusal of the same kind as an uncertifiable segment."""


def _frac_interval(x) -> tuple[Fraction, Fraction]:
    """Exact outward Fraction interval [mid - rad, mid + rad] of an arb ball.

    Raises NonFiniteEnclosure (a RuntimeError) for an infinite or NaN ball."""
    if not x.is_finite():
        raise NonFiniteEnclosure(f"non-finite Arb enclosure {x}")
    def dyadic(a) -> Fraction:
        man, exp = a.man_exp()
        man, exp = int(man), int(exp)
        return Fraction(man) * Fraction(2) ** exp if exp >= 0 else Fraction(man, 2 ** (-exp))
    m, r = dyadic(x.mid()), dyadic(x.rad())
    return m - r, m + r


@dataclass(frozen=True)
class ArbAnalytic:
    """An analytic function given by an Arb point evaluator and an Arb derivative jet.

    ``point(z, prec) -> acb``: a ball containing f(z) for the acb point ``z``.
    ``jet(B, prec) -> (acb, acb)``: balls containing f(B) and f'(B) for EVERY point of the acb ball ``B``.
    ``poles``: every pole of f, as exact (re, im) pairs.  Boxes containing one are refused."""

    name: str
    point: Callable
    jet: Callable
    poles: tuple = field(default=())


def from_series(series_fn: Callable, name: str = "f", poles: Iterable = ()) -> ArbAnalytic:
    """Wrap ``series_fn``, a map acb_series -> acb_series (f composed with a power series), as an ArbAnalytic.

    The point value comes from a length-1 series and the jet (f, f') from a length-2 series on the ball, so
    one formula yields both, and FLINT encloses the result over the whole input ball."""
    def point(z, prec):
        _, acb_series, _, ctx, _ = _flint()
        old = (ctx.prec, ctx.cap)
        try:
            ctx.prec, ctx.cap = prec, 1
            return series_fn(acb_series([z])).coeffs()[0]
        finally:
            ctx.prec, ctx.cap = old

    def jet(ball, prec):
        _, acb_series, _, ctx, _ = _flint()
        old = (ctx.prec, ctx.cap)
        try:
            ctx.prec, ctx.cap = prec, 2
            c = series_fn(acb_series([ball, 1])).coeffs()
            return c[0], c[1]
        finally:
            ctx.prec, ctx.cap = old

    return ArbAnalytic(name=name, point=point, jet=jet,
                       poles=tuple((Fraction(a), Fraction(b)) for a, b in poles))


def _as_analytic(f) -> ArbAnalytic:
    if isinstance(f, ArbAnalytic):
        return f
    if callable(f):
        return from_series(f, name=getattr(f, "__name__", "f"))
    raise TypeError(f"rigorous_winding: expected an ArbAnalytic or an acb_series function, got {f!r}")


def _segment_arg_change(f: ArbAnalytic, p, q, prec, cache):
    """Rigorous argument change of f along the axis-aligned segment p -> q (exact Fraction pairs), as an arb
    ball, or None when the centred-form disc test fails or an enclosure is non-finite (the caller bisects)."""
    acb, _, arb, ctx, _ = _flint()
    (pr, pi_), (qr, qi) = p, q
    mr, mi = (pr + qr) / 2, (pi_ + qi) / 2
    r = max(abs(qr - pr), abs(qi - pi_)) / 2
    old = ctx.prec
    try:
        ctx.prec = prec
        fm = f.point(_acb_point(mr, mi), prec)
        # B = m + [-r, r] along the segment's direction.  arb(0, x) adds an upper bound of |x| to the
        # radius, and the ball for x contains r, so B covers the segment exactly, with no float rounding.
        rad = arb(0, _arb_q(r))
        ball = _acb_point(mr, mi) + (acb(rad) if qi == pi_ else acb(0, rad))
        _, d = f.jet(ball, prec)
        D = _frac_interval(d.abs_upper())[1]
        cr_lo, cr_hi = _frac_interval(fm.real)
        ci_lo, ci_hi = _frac_interval(fm.imag)
        cr, ci = (cr_lo + cr_hi) / 2, (ci_lo + ci_hi) / 2
        rho = r * D + (cr_hi - cr_lo) / 2 + (ci_hi - ci_lo) / 2
        if 4 * rho * rho >= cr * cr + ci * ci:  # need |c| > 2 rho strictly
            return None
        c = _acb_point(cr, ci)
        out = None
        for pt, sgn in ((q, 1), (p, -1)):
            if pt not in cache:
                cache[pt] = f.point(_acb_point(*pt), prec)
            if not cache[pt].is_finite():
                return None  # a NaN endpoint would poison the total; fail the segment (ends at max_depth)
            a = (cache[pt] / c).arg()
            out = a * sgn if out is None else out + a * sgn
        return out
    except NonFiniteEnclosure:
        return None  # like a failed disc test: bisect, and refuse past max_depth
    finally:
        ctx.prec = old


def _edges(re0, re1, im0, im1):
    c = [(re0, im0), (re1, im0), (re1, im1), (re0, im1)]
    return [(c[k], c[(k + 1) % 4]) for k in range(4)]


def rigorous_winding(f, re0, re1, im0, im1, prec: int = 96, init_per_side: int = 8,
                     max_depth: int = 40, stats: dict | None = None) -> int:
    """Rigorous winding number of f around the rectangle [re0,re1] x [im0,im1], walked counter-clockwise.

    The result is the number of zeros minus the number of poles in the open rectangle.  ``f`` is an
    ArbAnalytic or a bare acb_series function (treated as entire, no poles).

    Refuses:
      * ValueError for an inverted box, or a box whose CLOSED rectangle contains a declared pole;
      * RuntimeError if some boundary segment cannot be certified zero-free within ``max_depth``
        bisections (a zero on or extremely near the contour), or if the total is not within 1/4 of an
        integer.
    ``stats`` (optional dict) receives segments, min_segment, evals and the winding ball."""
    acb, _, arb, ctx, _ = _flint()
    f = _as_analytic(f)
    re0, re1, im0, im1 = map(Fraction, (re0, re1, im0, im1))
    if not (re0 < re1 and im0 < im1):
        raise ValueError(f"rigorous_winding({f.name}): inverted box [{re0},{re1}] x [{im0},{im1}]")
    if init_per_side < 1 or max_depth < 0:
        raise ValueError(f"rigorous_winding({f.name}): need init_per_side >= 1 and max_depth >= 0")
    for (pr, pi_) in f.poles:
        if re0 <= pr <= re1 and im0 <= pi_ <= im1:
            raise ValueError(f"rigorous_winding({f.name}): box [{re0},{re1}] x [{im0},{im1}] contains the "
                             f"declared pole {pr} + {pi_}i; the winding would count zeros minus poles -- refused")
    cache: dict = {}
    total = arb(0)
    nseg = 0
    min_len = None
    stack = []
    for (a, b) in reversed(_edges(re0, re1, im0, im1)):
        pts = [(a[0] + (b[0] - a[0]) * Fraction(k, init_per_side), a[1] + (b[1] - a[1]) * Fraction(k, init_per_side))
               for k in range(init_per_side + 1)]
        for k in reversed(range(init_per_side)):
            stack.append((pts[k], pts[k + 1], 0))
    while stack:
        p, q, depth = stack.pop()
        dlt = _segment_arg_change(f, p, q, prec, cache)
        if dlt is None:
            if depth >= max_depth:
                raise RuntimeError(f"rigorous_winding({f.name}): cannot certify segment {p}->{q} zero-free at "
                                   f"depth {depth}; a zero may lie on the contour -- move the box edge")
            m = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
            stack.append((m, q, depth + 1))
            stack.append((p, m, depth + 1))
            continue
        total += dlt
        nseg += 1
        L = max(abs(q[0] - p[0]), abs(q[1] - p[1]))
        min_len = L if min_len is None else min(min_len, L)
    old = ctx.prec
    ctx.prec = prec
    try:
        w = total / (2 * arb.pi())
    finally:
        ctx.prec = old
    lo, hi = _frac_interval(w)
    k = round((lo + hi) / 2)
    if not (k - Fraction(1, 4) < lo and hi < k + Fraction(1, 4)):
        raise RuntimeError(f"rigorous_winding({f.name}): total/2pi = [{float(lo)}, {float(hi)}] not near an integer")
    if stats is not None:
        stats.update(segments=nseg, min_segment=str(min_len), evals=len(cache), winding_ball=(str(lo), str(hi)))
    return k


def count_strips(f, re0, re1, im0, im1, cuts, prec: int = 96, log=None) -> dict:
    """Rigorous zero count of f in [re0, re1] x [im0, im1], split into horizontal strips at the heights
    ``cuts``.  Every strip is an independent rigorous winding; the total is their sum (the cut edges are
    shared, so a zero on a cut makes that strip refuse rather than be lost)."""
    f = _as_analytic(f)
    hs = [Fraction(im0)] + [Fraction(c) for c in cuts] + [Fraction(im1)]
    strips = []
    for a, b in zip(hs, hs[1:]):
        st: dict = {}
        w = rigorous_winding(f, re0, re1, a, b, prec=prec, stats=st)
        strips.append({"im0": str(a), "im1": str(b), "winding": w, "segments": st["segments"]})
        if log:
            log(f"{f.name} [{re0},{re1}] x [{float(a)},{float(b)}]: {w} ({st['segments']} segs)")
    return {"box": {"re0": str(Fraction(re0)), "re1": str(Fraction(re1)), "im0": str(hs[0]), "im1": str(hs[-1])},
            "strips": strips, "total": sum(s["winding"] for s in strips), "prec": prec, "method": METHOD}


def _cut(a: Fraction, b: Fraction, nudge: Fraction) -> Fraction:
    """A cut point near the midpoint of [a, b], nudged by ``nudge`` * (b - a) off the dyadic grid and
    rounded to a small denominator (so repeated bisection does not grow huge rationals)."""
    m = ((a + b) / 2 + nudge * (b - a)).limit_denominator(10 ** 12)
    if not a < m < b:
        raise RuntimeError(f"cut: interval [{a}, {b}] too narrow")
    return m


def localise_zero(f, re0, re1, im0, im1, width, prec: int = 96, nudge=Fraction(1, 10**7)) -> list[Fraction]:
    """Shrink a box of winding 1 to one of winding 1 with both sides at most ``width``.

    Bisects the longer side (the cut nudged off the midpoint by ``nudge`` times the side, so it does not
    land on a dyadic grid point)
    and keeps the half of winding 1.  Raises RuntimeError if neither half has winding 1 (the zero sits on
    the cut, or the start box is not winding 1)."""
    box = [Fraction(re0), Fraction(re1), Fraction(im0), Fraction(im1)]
    width = Fraction(width)
    if rigorous_winding(f, *box, prec=prec) != 1:
        raise RuntimeError(f"localise_zero: start box {box} does not have winding 1")
    while max(box[1] - box[0], box[3] - box[2]) > width:
        r0, r1, i0, i1 = box
        if r1 - r0 >= i1 - i0:
            m = _cut(r0, r1, nudge)
            halves = [[r0, m, i0, i1], [m, r1, i0, i1]]
        else:
            m = _cut(i0, i1, nudge)
            halves = [[r0, r1, i0, m], [r0, r1, m, i1]]
        for h in halves:
            try:
                w = rigorous_winding(f, *h, prec=prec)
            except RuntimeError:  # the cut passes too close to the zero for this half; try the other
                continue
            if w == 1:
                box = h
                break
        else:
            raise RuntimeError(f"localise_zero: lost the zero while bisecting {box}")
    return box
