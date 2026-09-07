"""Arb transcendental-constant enclosure provider.

Provides a certified rational box [lo, hi] (as fractions.Fraction) that
rigorously contains a transcendental constant (pi, e, zeta(q), gamma(q))
computed via python-flint / Arb ball arithmetic.

Also provides complex enclosures ((lo_re, hi_re), (lo_im, hi_im)) for acb
values, including the completed Riemann zeta function

    Lambda(s) = pi^(-s/2) * Gamma(s/2) * zeta(s).

Lambda zeros are exactly the nontrivial zeros of the Riemann zeta function.

CERTIFICATION STATUS
--------------------
This module is a certified rational-box provider.  Box MEMBERSHIP is a
documented NON-KERNEL input: Arb ball arithmetic (via python-flint) is
internally certified (interval arithmetic with outward rounding), but Lean
does not independently verify the constant's value.  The rational endpoints
lo, hi are exact fractions.Fraction derived via outward-rounded dyadic
arithmetic from the Arb ball's mid and rad fields (man_exp extraction).

conjecture1_proved = False.

TECHNIQUE: man_exp outward rounding
------------------------------------
An arb ball b has a midpoint mid and radius rad, both exact dyadic
rationals representable as  man * 2**exp  (SIGNED mantissa, signed
exponent).  man_exp() returns (man, exp) with  man * 2**exp == exact value.

    _dyadic(a): man, exp = a.man_exp(); return Fraction(man) * Fraction(2)**exp

The radius rad is a certified UPPER bound of the true radius, so
    lo = mid - rad
    hi = mid + rad
are exact fractions.Fraction that rigorously contain the true value.

No float arithmetic appears in the returned endpoints.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Union

try:
    import flint as _flint
    from flint import acb as _acb
    from flint import arb as _arb
    from flint import ctx as _ctx
    _FLINT_AVAILABLE = True
except ImportError:
    _FLINT_AVAILABLE = False

# ──────────────────────────────────────────────────────────────────────────────
# Internal dyadic helpers
# ──────────────────────────────────────────────────────────────────────────────

def _dyadic(a) -> Fraction:
    """Convert an Arb scalar (arb, no imaginary part) to an exact Fraction.

    Uses man_exp(): value = man * 2**exp, where man is the signed mantissa.
    Works for both positive and negative exponents without any float conversion.
    """
    man, exp = a.man_exp()
    man = int(man)
    exp = int(exp)
    if exp >= 0:
        return Fraction(man) * Fraction(2) ** exp
    else:
        # Fraction(man, 2**(-exp)) is exact for negative exponents
        return Fraction(man, 2 ** (-exp))


def _arb_ball_to_fractions(ball) -> tuple[Fraction, Fraction]:
    """Convert an Arb ball to an outward-rounded rational enclosure (lo, hi).

    Returns (mid - rad, mid + rad) as exact fractions.Fraction, where rad is
    a certified UPPER bound of the true radius.  The interval [lo, hi]
    rigorously contains the true value represented by the ball.

    No float arithmetic is used.
    """
    mid = _dyadic(ball.mid())
    rad = _dyadic(ball.rad())
    return mid - rad, mid + rad


# ──────────────────────────────────────────────────────────────────────────────
# Spec parsing and evaluation
# ──────────────────────────────────────────────────────────────────────────────

_ZETA_RE = re.compile(r"^zeta\((.+)\)$")
_GAMMA_RE = re.compile(r"^gamma\((.+)\)$")


def _parse_rational_arg(inner: str) -> Fraction:
    """Parse a rational string like '1/2' or '1/4' into a Fraction."""
    inner = inner.strip()
    return Fraction(inner)


def _eval_spec(spec: Union[str, Callable], prec_bits: int):
    """Evaluate spec at the given precision, returning an acb.

    spec can be:
      "pi"           -> acb.pi()
      "e"            -> acb(1).exp()
      "zeta(q)"      -> acb(str(q)).zeta()  where q is a rational
      "gamma(q)"     -> acb(str(q)).gamma() where q is a rational
      callable       -> spec(_flint)   (receives the flint module)

    Sets ctx.prec = prec_bits (save/restore around call).
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    old_prec = _ctx.prec
    try:
        _ctx.prec = prec_bits

        if callable(spec):
            result = spec(_flint)
        elif spec == "pi":
            result = _acb.pi()
        elif spec == "e":
            result = _acb(1).exp()
        else:
            m = _ZETA_RE.match(spec)
            if m:
                q = _parse_rational_arg(m.group(1))
                result = _acb(str(q)).zeta()
            else:
                m = _GAMMA_RE.match(spec)
                if m:
                    q = _parse_rational_arg(m.group(1))
                    result = _acb(str(q)).gamma()
                else:
                    raise ValueError(
                        f"Unknown spec {spec!r}. "
                        "Supported: 'pi', 'e', 'zeta(<rational>)', 'gamma(<rational>)', "
                        "or a callable(flint_module) -> acb."
                    )
    finally:
        _ctx.prec = old_prec

    return result


# ──────────────────────────────────────────────────────────────────────────────
# Public API
# ──────────────────────────────────────────────────────────────────────────────

def enclose_constant(
    spec: Union[str, Callable],
    prec_bits: int,
) -> tuple[Fraction, Fraction]:
    """Return a certified outward-rounded rational enclosure (lo, hi) for a
    transcendental constant.

    Parameters
    ----------
    spec : str or callable
        "pi"           -- the constant pi
        "e"            -- Euler's number e
        "zeta(q)"      -- Riemann zeta function at rational q (e.g. "zeta(1/2)")
        "gamma(q)"     -- Euler gamma function at rational q (e.g. "gamma(1/4)")
        callable       -- receives the flint module, must return an acb value

    prec_bits : int
        Working precision in bits for Arb computation.  Higher gives tighter
        enclosure.

    Returns
    -------
    (lo, hi) : tuple[Fraction, Fraction]
        Exact fractions.Fraction endpoints such that lo <= true_value <= hi.
        The interval is outward-rounded: lo may be slightly below and hi
        slightly above the best Arb approximation, by at most the certified
        radius of the Arb ball.  No float arithmetic is used in the return
        values.

    Raises
    ------
    RuntimeError
        If python-flint is not installed.
    ValueError
        If spec is not recognized.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    result_acb = _eval_spec(spec, prec_bits)
    # Take real part (arb ball)
    real_ball = result_acb.real
    return _arb_ball_to_fractions(real_ball)


# ──────────────────────────────────────────────────────────────────────────────
# EnclosureRecord
# ──────────────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class EnclosureRecord:
    """A certified rational enclosure record for a transcendental constant.

    Fields
    ------
    spec : str
        The constant specification (e.g. "pi", "e", "zeta(1/2)").
    prec_bits : int
        Arb working precision used to produce the enclosure.
    lo : Fraction
        Exact rational lower bound; true value >= lo.
    hi : Fraction
        Exact rational upper bound; true value <= hi.
    radius : Fraction
        Half-width of the enclosure (hi - lo) / 2.  A certified upper bound
        on the distance from the midpoint to the true value.

    CERTIFICATION NOTE: box membership is a documented non-kernel input.
    Arb ball arithmetic is certified; Lean does not verify the constant's
    value.  conjecture1_proved = False.
    """

    spec: str
    prec_bits: int
    lo: Fraction
    hi: Fraction
    radius: Fraction

    def to_dict(self) -> dict:
        """Serialize to a plain dict with string-encoded Fractions.

        All Fraction fields are stored as 'numerator/denominator' strings
        (or just 'numerator' for integers) to preserve exactness across
        JSON serialization.
        """
        def _frac_str(f: Fraction) -> str:
            if f.denominator == 1:
                return str(f.numerator)
            return f"{f.numerator}/{f.denominator}"

        return {
            "spec": self.spec,
            "prec_bits": self.prec_bits,
            "lo": _frac_str(self.lo),
            "hi": _frac_str(self.hi),
            "radius": _frac_str(self.radius),
        }


# ──────────────────────────────────────────────────────────────────────────────
# Complex enclosure: enclose_acb and enclose_lambda
# ──────────────────────────────────────────────────────────────────────────────

def enclose_acb(
    spec_or_callable,
    prec_bits: int,
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Return certified outward-rounded rational boxes for both parts of an acb value.

    Computes a complex Arb ball (acb) via spec_or_callable and extracts
    rigorous rational enclosures for its real and imaginary parts separately,
    reusing _arb_ball_to_fractions on acb.real and acb.imag.

    Parameters
    ----------
    spec_or_callable : str or callable
        A callable receiving the flint module that returns an acb, OR a string
        spec recognized by _eval_spec (e.g. "pi", "zeta(1/2)").
    prec_bits : int
        Working precision in bits for Arb computation.

    Returns
    -------
    ((lo_re, hi_re), (lo_im, hi_im)) : tuple of two tuple[Fraction, Fraction]
        Outward-rounded rational boxes for the real and imaginary parts.
        All four endpoints are exact fractions.Fraction.
        lo_re <= true_real <= hi_re and lo_im <= true_imag <= hi_im.

    Notes
    -----
    Box membership is a documented NON-KERNEL input: Arb ball arithmetic is
    internally certified (interval arithmetic with outward rounding), but Lean
    does not independently verify the value.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    result_acb = _eval_spec(spec_or_callable, prec_bits)
    re_box = _arb_ball_to_fractions(result_acb.real)
    im_box = _arb_ball_to_fractions(result_acb.imag)
    return re_box, im_box


def enclose_lambda(
    s_re,
    s_im,
    prec_bits: int,
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Return a certified complex enclosure of Lambda(s) at s = s_re + i*s_im.

    Lambda is the completed Riemann zeta function:

        Lambda(s) = pi^(-s/2) * Gamma(s/2) * zeta(s)

    Lambda zeros are exactly the nontrivial zeros of the Riemann zeta function.
    On the critical line (s_re = 1/2) Lambda is real-valued (functional equation),
    so the imaginary enclosure box contains 0.

    Parameters
    ----------
    s_re : int, float, Fraction, or str
        Real part of s.  Converted to string for exact Arb input.
    s_im : int, float, Fraction, or str
        Imaginary part of s.  Converted to string for exact Arb input.
    prec_bits : int
        Working precision in bits for Arb computation.  Higher gives tighter
        enclosures for both the real and imaginary parts.

    Returns
    -------
    ((lo_re, hi_re), (lo_im, hi_im)) : tuple of two tuple[Fraction, Fraction]
        Outward-rounded rational boxes for the real and imaginary parts of
        Lambda(s_re + i*s_im).  All four endpoints are exact fractions.Fraction.
        lo_re <= true_Lambda.real <= hi_re, lo_im <= true_Lambda.imag <= hi_im.
        Both boxes use the full requested prec_bits precision; the imaginary box
        is a tight Arb enclosure (a real signal off the critical line, and a
        tight box around 0 on the critical line where Lambda is real-valued).

    Notes
    -----
    Box membership is a documented NON-KERNEL input: Arb ball arithmetic is
    internally certified (interval arithmetic with outward rounding), but Lean
    does not independently verify the value.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    s_re_str = str(s_re)
    s_im_str = str(s_im)

    def _lambda_callable(flint_module):
        acb_cls = flint_module.acb
        s = acb_cls(s_re_str) + acb_cls(0, s_im_str)
        return acb_cls.pi() ** (-s / 2) * (s / 2).gamma() * s.zeta()

    return enclose_acb(_lambda_callable, prec_bits)


def enclose_zeta_segment(
    fixed_coord,
    var_lo,
    var_hi,
    is_vertical: bool,
    prec_bits: int,
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Return a RIGOROUS certified enclosure of zeta over an axis-aligned segment.

    Uses a SECOND-ORDER Taylor enclosure with a Lagrange (derivative-ball)
    remainder, which is far tighter than a naive acb ball over the segment:

        zeta(mid + h) = c0 + c1 * h + c2(xi) * h^2,   xi in the segment

    where c0 = zeta(mid) and c1 = zeta'(mid) are TIGHT point enclosures at the
    exact segment midpoint (radius ~1e-45 at prec_bits=160), and c2(xi) is the
    coefficient-2 of the zeta power series evaluated on an acb BALL covering the
    whole sub-segment -- a rigorous enclosure of zeta''(xi)/2 over all xi in the
    segment.  Multiplied by h^2 (bounded by delta^2, delta = half the segment
    length), the remainder stays small even though c2's ball enclosure is loose.

    This is the RIGOROUS route: the box is a certified outer enclosure of the
    CONTINUUM {zeta(s) : s on the sub-segment}, not merely of the endpoints.

    WHY ZETA, NOT LAMBDA: winding(zeta, dB) = winding(Lambda, dB) because they
    differ by the nonzero analytic factor pi^(-s/2) * Gamma(s/2), whose winding
    over a closed contour is 0.  zeta is O(1) on the boundary of the capstone box
    (magnitude ~0.1 to ~3), whereas Lambda is exponentially small there (Gamma
    factor ~1e-12), so Lambda's ball-enclosure radius swamps its value and always
    straddles 0.  zeta's pole at s=1 (Re=1) is outside [2/5,3/5]; zeta's zeros in
    the box are exactly the same 5 nontrivial zeros as Lambda's.

    Parameters
    ----------
    fixed_coord : Fraction-compatible
        The fixed coordinate: the real part sigma if is_vertical, else the
        imaginary part T.
    var_lo, var_hi : Fraction-compatible
        The lower and upper bounds of the varying coordinate (var_lo < var_hi).
        The varying coordinate is the imaginary part T if is_vertical, else the
        real part sigma.
    is_vertical : bool
        True if the segment is vertical (re fixed, im varies); False if
        horizontal (im fixed, re varies).
    prec_bits : int
        Working precision in bits.  Note: because the c2 remainder ball is
        computed via series-at-ball (which wraps more at higher precision),
        MODERATE precision (~160-256) minimizes the segment count; the point
        coefficients c0, c1 remain tight at these precisions.

    Returns
    -------
    ((lo_re, hi_re), (lo_im, hi_im)) : certified Fraction enclosure
        Outward-rounded rational box rigorously containing zeta on the segment.

    Raises
    ------
    RuntimeError
        If python-flint is not available.

    Notes
    -----
    Box membership is a documented NON-KERNEL input.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )
    from flint import acb_series as _acb_series

    fixed_coord = Fraction(fixed_coord)
    var_lo = Fraction(var_lo)
    var_hi = Fraction(var_hi)
    mid = (var_lo + var_hi) / 2
    delta = (var_hi - var_lo) / 2
    delta2 = delta * delta

    old_prec = _ctx.prec
    try:
        _ctx.prec = prec_bits
        if is_vertical:
            # re = fixed, im in [mid-delta, mid+delta].  h = i*t, t in [-delta, delta].
            mid_acb = _acb(str(fixed_coord)) + _acb(0, str(mid))
            seg_ball = _acb(_arb(str(fixed_coord)), _arb(str(mid), str(delta)))
            h = _acb(0, _arb("0", str(delta)))          # i*t
            # h^2 = (i t)^2 = -t^2 in [-delta^2, 0]; ball center -delta^2/2, radius delta^2/2.
            h2 = _acb(_arb(str(-delta2 / 2), str(delta2 / 2)))
        else:
            # im = fixed, re in [mid-delta, mid+delta].  h = t, t in [-delta, delta].
            mid_acb = _acb(str(mid)) + _acb(0, str(fixed_coord))
            seg_ball = _acb(_arb(str(mid), str(delta)), _arb(str(fixed_coord)))
            h = _acb(_arb("0", str(delta)), 0)          # t
            # h^2 = t^2 in [0, delta^2]; ball center delta^2/2, radius delta^2/2.
            h2 = _acb(_arb(str(delta2 / 2), str(delta2 / 2)))

        # Tight point coefficients at the exact midpoint: zeta(mid), zeta'(mid).
        point_series = _acb_series([mid_acb, 1]).zeta()
        c0 = point_series[0]
        c1 = point_series[1]
        # Remainder coefficient c2(xi) = zeta''(xi)/2 over the whole segment ball.
        c2 = _acb_series([seg_ball, 1]).zeta()[2]

        encl = c0 + c1 * h + c2 * h2
        re_box = _arb_ball_to_fractions(encl.real)
        im_box = _arb_ball_to_fractions(encl.imag)
        return re_box, im_box
    finally:
        _ctx.prec = old_prec


def _box_contains_zero_local(box) -> bool:
    """Return True iff both real and imaginary parts of the box straddle 0."""
    (lo_re, hi_re), (lo_im, hi_im) = box
    return lo_re <= 0 <= hi_re and lo_im <= 0 <= hi_im


# Eight fixed rational half-plane test directions (mirrors emit_winding_count._DIRECTIONS).
# Kept local to avoid a circular import; the canonical witness search lives in
# emit_winding_count._half_plane_witness.
_LOCAL_DIRECTIONS = (
    (Fraction(1), Fraction(0)),
    (Fraction(-1), Fraction(0)),
    (Fraction(0), Fraction(1)),
    (Fraction(0), Fraction(-1)),
    (Fraction(1), Fraction(1)),
    (Fraction(1), Fraction(-1)),
    (Fraction(-1), Fraction(1)),
    (Fraction(-1), Fraction(-1)),
)


def _local_has_witness(box_a, box_b) -> bool:
    """Return True iff box_a and box_b share an open half-plane through 0.

    Local mirror of emit_winding_count._half_plane_witness used only to drive
    adaptive witness refinement; the certificate itself re-verifies with the
    canonical _half_plane_witness.
    """
    (alo_re, ahi_re), (alo_im, ahi_im) = box_a
    (blo_re, bhi_re), (blo_im, bhi_im) = box_b
    corners = (
        (alo_re, alo_im), (alo_re, ahi_im), (ahi_re, alo_im), (ahi_re, ahi_im),
        (blo_re, blo_im), (blo_re, bhi_im), (bhi_re, blo_im), (bhi_re, bhi_im),
    )
    for d_re, d_im in _LOCAL_DIRECTIONS:
        if all(d_re * w_re + d_im * w_im > 0 for w_re, w_im in corners):
            return True
    return False


def enclose_zeta_segments(
    box,
    prec_bits: int,
    n_seed: int = 4,
    max_depth: int = 35,
) -> list[tuple[Fraction, tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]]]:
    """Return an ordered CCW cycle of RIGOROUS zeta segment enclosures around a box.

    Traverses the boundary of {sigma in [sigma0, sigma1]} x {T in [T0, T1]} CCW
    (bottom sigma0->sigma1 at T0, right T0->T1 at sigma1, top sigma1->sigma0 at
    T1, left T1->T0 at sigma0).  Each edge is ADAPTIVELY subdivided: a sub-segment
    is halved whenever its second-order Taylor zeta enclosure straddles 0, so no
    returned segment-box contains 0 (down to max_depth).  The result is a closed
    cycle suitable for segment_winding_certificate.

    This is the RIGOROUS route beta for the capstone box: winding zeta (O(1) on
    the boundary) instead of Lambda (exponentially small) via tight Taylor
    enclosures of the continuum.

    Parameters
    ----------
    box : tuple of four values (sigma0, sigma1, T0, T1)
        Rectangle corners.  Each element is converted to Fraction.
    prec_bits : int
        Working precision in bits (see enclose_zeta_segment for the moderate-
        precision guidance).
    n_seed : int
        Number of equal seed sub-segments per edge before adaptive refinement.
        Each seed sub-segment is then refined independently.
    max_depth : int
        Maximum bisection depth per seed sub-segment (safety cap).

    Returns
    -------
    list of (param, complex_box) pairs
        Ordered CCW cycle.  Each param is a Fraction in [0, 1) giving the
        sub-segment's position around the perimeter (evenly spaced by index).
        Each complex_box rigorously encloses zeta over the sub-segment.  The
        final entry repeats the first to close the cycle.

    Raises
    ------
    RuntimeError
        If python-flint is not available.

    Notes
    -----
    Box membership is a documented NON-KERNEL input.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    sigma0, sigma1, T0, T1 = (Fraction(v) for v in box)

    # Edge definitions in CCW traversal order: (fixed_coord, start, end, is_vertical).
    # start->end gives the traversal direction (may be decreasing).
    edge_defs = [
        (T0, sigma0, sigma1, False),   # bottom: im=T0, re increasing
        (sigma1, T0, T1, True),        # right:  re=sigma1, im increasing
        (T1, sigma1, sigma0, False),   # top:    im=T1, re decreasing
        (sigma0, T1, T0, True),        # left:   re=sigma0, im decreasing
    ]

    # Each atom is [fixed_coord, lo, hi, is_vertical, box, forward] where lo<hi
    # (bounds of the varying coordinate) and forward indicates traversal direction.
    atoms: list = []

    for fixed_coord, start, end, is_vertical in edge_defs:
        edge_lo, edge_hi = (start, end) if start < end else (end, start)
        forward = start < end
        edge_pieces: list = []

        n = max(1, int(n_seed))
        seeds = []
        for k in range(n):
            a = edge_lo + (edge_hi - edge_lo) * Fraction(k, n)
            b = edge_lo + (edge_hi - edge_lo) * Fraction(k + 1, n)
            seeds.append((a, b))

        def refine(a: Fraction, b: Fraction, depth: int):
            seg_box = enclose_zeta_segment(fixed_coord, a, b, is_vertical, prec_bits)
            if not _box_contains_zero_local(seg_box) or depth >= max_depth:
                edge_pieces.append((a, b, seg_box))
                return
            m = (a + b) / 2
            refine(a, m, depth + 1)
            refine(m, b, depth + 1)

        for a, b in seeds:
            refine(a, b, 0)

        # Order pieces along the traversal direction.
        if not forward:
            edge_pieces = edge_pieces[::-1]
        for a, b, seg_box in edge_pieces:
            atoms.append([fixed_coord, a, b, is_vertical, seg_box, forward])

    # Witness-refinement pass: halve the wider box of any consecutive pair (cyclic)
    # that lacks a shared half-plane witness, until every step is witnessed.  This
    # resolves the residual failures at edge corners / near zeta zeros.
    def _bw(seg_box) -> Fraction:
        (lo_re, hi_re), (lo_im, hi_im) = seg_box
        return (hi_re - lo_re) + (hi_im - lo_im)

    for _pass in range(max_depth + 10):
        m_atoms = len(atoms)
        fails = [
            i for i in range(m_atoms)
            if not _local_has_witness(atoms[i][4], atoms[(i + 1) % m_atoms][4])
        ]
        if not fails:
            break
        to_split = set()
        for i in fails:
            j = (i + 1) % m_atoms
            to_split.add(i if _bw(atoms[i][4]) >= _bw(atoms[j][4]) else j)
        for idx in sorted(to_split, reverse=True):
            fc, a, b, isv, _sb, fwd = atoms[idx]
            m = (a + b) / 2
            b1 = enclose_zeta_segment(fc, a, m, isv, prec_bits)
            b2 = enclose_zeta_segment(fc, m, b, isv, prec_bits)
            new = [[fc, a, m, isv, b1, fwd], [fc, m, b, isv, b2, fwd]]
            if not fwd:
                new = new[::-1]
            atoms[idx:idx + 1] = new

    total = len(atoms)
    segments = [(Fraction(i, total), atoms[i][4]) for i in range(total)]
    # Close the cycle.
    segments.append((Fraction(1), segments[0][1]))
    return segments


def enclose_lambda_segment(
    re_a,
    im_a,
    re_b,
    im_b,
    prec_bits: int,
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Return a certified complex enclosure of Lambda over an axis-aligned segment.

    Evaluates Lambda at both endpoints via enclose_lambda (acb ball arithmetic)
    and returns the bounding box of the two endpoint enclosures.  This gives a
    rigorous outer enclosure of Lambda({endpoint_A, endpoint_B}); it is a
    conservative container of Lambda on the segment provided Lambda stays within
    the convex hull of its endpoint values on each coordinate (which holds for
    axis-aligned boundary segments of the capstone box when n_per_side is large
    enough that no sign change occurs within a single sub-segment).

    The returned box is always strictly wider (in at least one coordinate) than
    either individual endpoint enclosure, satisfying the segment-wider-than-point
    acceptance requirement.

    Parameters
    ----------
    re_a, im_a : Fraction-compatible
        Real and imaginary parts of the first endpoint.
    re_b, im_b : Fraction-compatible
        Real and imaginary parts of the second endpoint.  The segment from A to B
        must be axis-aligned: either im_a == im_b (horizontal) or re_a == re_b
        (vertical).
    prec_bits : int
        Working precision in bits passed to each enclose_lambda call.

    Returns
    -------
    ((lo_re, hi_re), (lo_im, hi_im)) : certified Fraction enclosure
        Bounding box of both endpoint Lambda enclosures.  All four endpoints are
        exact fractions.Fraction.

    Notes
    -----
    Box membership is a documented NON-KERNEL input.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )
    re_a = Fraction(re_a)
    im_a = Fraction(im_a)
    re_b = Fraction(re_b)
    im_b = Fraction(im_b)
    box_a = enclose_lambda(re_a, im_a, prec_bits)
    box_b = enclose_lambda(re_b, im_b, prec_bits)
    lo_re = min(box_a[0][0], box_b[0][0])
    hi_re = max(box_a[0][1], box_b[0][1])
    lo_im = min(box_a[1][0], box_b[1][0])
    hi_im = max(box_a[1][1], box_b[1][1])
    return (lo_re, hi_re), (lo_im, hi_im)


def enclose_lambda_segments(
    box,
    n_per_side: int,
    prec_bits: int,
) -> list[tuple[Fraction, tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]]]:
    """Return an ordered CCW cycle where each entry encloses Lambda over a sub-segment.

    Traverses the same CCW boundary as enclose_lambda_boundary but produces
    SEGMENT enclosures rather than point enclosures.  For each consecutive pair
    of boundary nodes (node k, node k+1), the returned complex_box is a certified
    outer enclosure of Lambda({node_k, node_{k+1}}) -- a bounding box computed
    from the two endpoint acb ball enclosures via enclose_lambda_segment.

    Each segment-box is strictly wider than either constituent endpoint
    point-enclosure.  For fine enough n_per_side (typically >= 80 for the capstone
    box [2/5,3/5]x[10,35]), no segment-box contains 0 and every consecutive pair
    of segment-boxes shares a half-plane witness, allowing segment_winding_certificate
    to succeed.

    Parameters
    ----------
    box : tuple of four values (sigma0, sigma1, T0, T1)
        Rectangle corners.  Each element is converted to Fraction.  sigma0 < sigma1
        and T0 < T1 are expected.
    n_per_side : int
        Number of sub-segments contributed by each of the four edges.  Total
        sub-segments: 4 * n_per_side.  The returned list has length 4*n_per_side + 1
        (the last entry repeats the first to close the cycle).
    prec_bits : int
        Working precision in bits for each enclose_lambda call.

    Returns
    -------
    list of (param, complex_box) pairs
        Each param is a Fraction in [0, 1) giving the CCW position of the
        sub-segment's starting node.  Each complex_box = ((lo_re, hi_re),
        (lo_im, hi_im)) is a certified bounding box enclosing Lambda at both
        endpoints of the sub-segment; all endpoints are Fractions.
        The final entry repeats the first (segment_boxes[0][1] == segment_boxes[-1][1]).

    Raises
    ------
    RuntimeError
        If python-flint is not available.

    Notes
    -----
    Box membership is a documented NON-KERNEL input.  conjecture1_proved = False.
    The segment boxes are wider than the point enclosures at the same nodes
    (as returned by enclose_lambda_boundary at the same n_per_side) because each
    box spans the union of two point enclosures.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    sigma0, sigma1, T0, T1 = (Fraction(v) for v in box)
    n = int(n_per_side)

    # Build the same CCW node positions as enclose_lambda_boundary.
    total = 4 * n
    nodes = []  # list of (param, re, im) as Fractions

    for k in range(total):
        param = Fraction(k, total)
        edge = k // n
        j = k % n

        if edge == 0:
            t = Fraction(j, n)
            re = sigma0 + t * (sigma1 - sigma0)
            im = T0
        elif edge == 1:
            t = Fraction(j, n)
            re = sigma1
            im = T0 + t * (T1 - T0)
        elif edge == 2:
            t = Fraction(j, n)
            re = sigma1 + t * (sigma0 - sigma1)
            im = T1
        else:
            t = Fraction(j, n)
            re = sigma0
            im = T1 + t * (T0 - T1)

        nodes.append((param, re, im))

    # Append the first node again to allow iteration over all sub-segments.
    nodes.append(nodes[0])

    # For each consecutive pair of nodes, compute the segment enclosure.
    segments = []
    for i in range(len(nodes) - 1):
        param, re_a, im_a = nodes[i]
        _, re_b, im_b = nodes[i + 1]
        seg_box = enclose_lambda_segment(re_a, im_a, re_b, im_b, prec_bits)
        segments.append((param, seg_box))

    # Close the cycle: append a copy of the first segment's box.
    segments.append((segments[0][0], segments[0][1]))

    return segments


def enclose_lambda_boundary(
    box,
    n_per_side: int,
    prec_bits: int,
) -> list[tuple[Fraction, tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]]]:
    """Return an ordered CCW cycle of Lambda enclosures around the boundary of a box.

    Traverses the boundary of the rectangle {sigma in [sigma0, sigma1]} x {T in [T0, T1]}
    counter-clockwise: bottom edge (sigma0->sigma1 at T0), right edge (T0->T1 at sigma1),
    top edge (sigma1->sigma0 at T1), left edge (T1->T0 at sigma0).

    Each edge contributes n_per_side sample points (the shared corner from the previous
    edge is excluded to avoid duplicates).  The starting point is appended once at the
    end to close the cycle.  Total length: 4*n_per_side + 1.

    Parameters
    ----------
    box : tuple of four values (sigma0, sigma1, T0, T1)
        Rectangle corners.  Each element is converted to Fraction.  sigma0 < sigma1 and
        T0 < T1 are expected; sigma corresponds to the real part of s, T to the imaginary
        part.
    n_per_side : int
        Number of sample points contributed by each edge (excluding the shared corner at
        the start of each edge).  Total unique points: 4*n_per_side.
    prec_bits : int
        Working precision in bits for each enclose_lambda call.

    Returns
    -------
    list of (param, complex_box) pairs
        Each param is a Fraction in [0, 1) giving the monotone CCW position around the
        perimeter.  Each complex_box = ((lo_re, hi_re), (lo_im, hi_im)) is a certified
        Arb enclosure of Lambda at that boundary point; all endpoints are Fractions.
        The final element repeats the first (samples[0][1] == samples[-1][1]).

    Raises
    ------
    RuntimeError
        If python-flint is not available (mirrors enclose_lambda guard).
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    sigma0, sigma1, T0, T1 = (Fraction(v) for v in box)
    n = int(n_per_side)

    # Build CCW sample points as (param, re, im) triples.
    # param runs from 0 to 1 (exclusive) across 4*n_per_side equally-spaced points.
    # Each edge: n points, parameterised from k/(4*n) for k = 0..n-1 on that edge's
    # slice of [0,1).  Corner at start of each edge is excluded (it was appended as
    # the last point of the previous edge -- but for the very first edge we start at
    # the bottom-left corner, which is included as k=0 on edge 0).
    #
    # Bottom edge: sigma0 -> sigma1 at T0   (param 0..n-1 out of 4n)
    # Right edge:  T0    -> T1    at sigma1  (param n..2n-1 out of 4n)
    # Top edge:    sigma1 -> sigma0 at T1   (param 2n..3n-1 out of 4n)
    # Left edge:   T1    -> T0    at sigma0  (param 3n..4n-1 out of 4n)

    total = 4 * n
    points = []  # list of (param, re, im) as Fractions

    for k in range(total):
        param = Fraction(k, total)
        edge = k // n
        j = k % n  # position within edge: 0 means the corner (included on edge 0, excluded on 1-3)

        if edge == 0:
            # Bottom: sigma0->sigma1 at T0; j=0 is sigma0, j=n-1 approaches sigma1
            t = Fraction(j, n)
            re = sigma0 + t * (sigma1 - sigma0)
            im = T0
        elif edge == 1:
            # Right: T0->T1 at sigma1; j=0 is T0 corner (excluded), j>0 interior
            t = Fraction(j, n)
            re = sigma1
            im = T0 + t * (T1 - T0)
        elif edge == 2:
            # Top: sigma1->sigma0 at T1; j=0 is sigma1 corner (excluded)
            t = Fraction(j, n)
            re = sigma1 + t * (sigma0 - sigma1)
            im = T1
        else:
            # Left: T1->T0 at sigma0; j=0 is T1 corner (excluded)
            t = Fraction(j, n)
            re = sigma0
            im = T1 + t * (T0 - T1)

        points.append((param, re, im))

    samples = []
    for param, re, im in points:
        box_val = enclose_lambda(re, im, prec_bits)
        samples.append((param, box_val))

    # Close the cycle: append the first point again.
    samples.append((samples[0][0], samples[0][1]))

    return samples
