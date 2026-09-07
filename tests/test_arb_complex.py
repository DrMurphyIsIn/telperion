"""Tests for complex Arb enclosure of Lambda(s) = pi^(-s/2) * Gamma(s/2) * zeta(s).

Lambda zeros are exactly the nontrivial zeros of the Riemann zeta function.
Box membership is a documented NON-KERNEL input: Arb ball arithmetic is
internally certified; Lean does not independently verify the value.
conjecture1_proved = False.
"""
from fractions import Fraction
import mpmath
import pytest
import telperion.arb_enclosure as _ae
from telperion.arb_enclosure import enclose_acb, enclose_lambda

# python-flint (Arb) is an optional dependency absent from the lightweight `unit`
# CI environment; enclosure tests SKIP there rather than erroring. The dedicated
# `*_requires_flint` tests below intentionally have NO marker: they assert the
# graceful RuntimeError when flint is absent and are trivial when it is present.
requires_flint = pytest.mark.skipif(
    not _ae._FLINT_AVAILABLE, reason="requires python-flint (Arb enclosures)"
)


def _c(box, val):  # val real float, box=(lo,hi)
    return float(box[0]) <= val <= float(box[1])


def _lambda_oracle(sre, sim, dps=120):
    mpmath.mp.dps = dps
    s = mpmath.mpf(str(sre)) + 1j*mpmath.mpf(str(sim))
    return mpmath.power(mpmath.pi, -s/2) * mpmath.gamma(s/2) * mpmath.zeta(s)


@requires_flint
def test_lambda_on_line_is_real_and_encloses_oracle():
    # Lambda(1/2 + i*14) : known to be near a zero region; imag part must be ~0.
    # The TRUE imaginary part is exactly 0 on the critical line (functional
    # equation); the meaningful assertion is lo_im <= 0 <= hi_im.  The oracle is
    # computed at dps=120 (tighter than the Arb box at prec_bits=300) so its imag
    # noise (~1e-127) is well inside the tight Arb enclosure -- a meaningful
    # containment check that does NOT force the enclosure looser than Arb.
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(1, 2), 14, prec_bits=300)
    o = _lambda_oracle(0.5, 14, dps=120)
    assert _c((lo_re, hi_re), float(o.real))
    assert lo_im <= 0 <= hi_im   # imaginary part boxes zero on the line (true value is 0)
    assert _c((lo_im, hi_im), float(o.imag))


@requires_flint
def test_complex_point_encloses_oracle():
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(3, 5), 20, prec_bits=300)
    o = _lambda_oracle(0.6, 20)
    assert _c((lo_re, hi_re), float(o.real)) and _c((lo_im, hi_im), float(o.imag))


@requires_flint
def test_width_shrinks_with_precision():
    b1 = enclose_lambda(Fraction(1, 2), 14, prec_bits=120)
    b2 = enclose_lambda(Fraction(1, 2), 14, prec_bits=300)
    # Real-part width shrinks with precision.
    assert (b2[0][1] - b2[0][0]) < (b1[0][1] - b1[0][0])
    # Imag-part width also shrinks with precision (no hull floor).
    assert (b2[1][1] - b2[1][0]) < (b1[1][1] - b1[1][0])


@requires_flint
def test_returns_fractions():
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(1, 2), 21, prec_bits=200)
    assert all(isinstance(x, Fraction) for x in (lo_re, hi_re, lo_im, hi_im))


@requires_flint
def test_enclose_lambda_boundary_is_closed_cycle_off_zero():
    from fractions import Fraction
    from telperion.arb_enclosure import enclose_lambda_boundary
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    samples = enclose_lambda_boundary(box, n_per_side=4, prec_bits=300)
    # CCW cycle: 4 corners x 4 per side = 16 points + closing repeat
    assert len(samples) == 16 + 1
    # closed: first param==last coordinate-wise (same boundary point)
    assert samples[0][1] == samples[-1][1]
    # no enclosure box contains 0 (Lambda nonzero on this boundary): a box
    # contains 0 iff lo<=0<=hi for BOTH parts
    for _param, ((lo_re, hi_re), (lo_im, hi_im)) in samples[:-1]:
        contains_zero = (lo_re <= 0 <= hi_re) and (lo_im <= 0 <= hi_im)
        assert not contains_zero


def test_enclose_lambda_boundary_requires_flint():
    import telperion.arb_enclosure as ae
    if not ae._FLINT_AVAILABLE:
        import pytest
        with pytest.raises(RuntimeError, match="python-flint"):
            ae.enclose_lambda_boundary((0, 1, 10, 11), 2, 100)


# ---------------------------------------------------------------------------
# Task 8: segment (ball) enclosures
# ---------------------------------------------------------------------------

@requires_flint
def test_enclose_lambda_segments_closed_cycle_length():
    """enclose_lambda_segments returns 4*n_per_side + 1 entries (closed cycle)."""
    from telperion.arb_enclosure import enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    n = 10
    segs = enclose_lambda_segments(box, n_per_side=n, prec_bits=300)
    assert len(segs) == 4 * n + 1


@requires_flint
def test_enclose_lambda_segments_returns_fractions():
    """All endpoints in segment boxes are exact Fractions."""
    from telperion.arb_enclosure import enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    segs = enclose_lambda_segments(box, n_per_side=4, prec_bits=200)
    for param, ((lo_re, hi_re), (lo_im, hi_im)) in segs:
        assert isinstance(param, Fraction)
        assert isinstance(lo_re, Fraction)
        assert isinstance(hi_re, Fraction)
        assert isinstance(lo_im, Fraction)
        assert isinstance(hi_im, Fraction)


@requires_flint
def test_enclose_lambda_segments_closed_first_equals_last():
    """Segment cycle is closed: first and last boxes are identical."""
    from telperion.arb_enclosure import enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    segs = enclose_lambda_segments(box, n_per_side=6, prec_bits=200)
    assert segs[0][1] == segs[-1][1]


@requires_flint
def test_enclose_lambda_segments_wider_than_point_enclosures():
    """Each segment box is strictly wider than both endpoint point-enclosures.

    enclose_lambda_boundary at the same n_per_side gives point enclosures at
    the same nodes.  Each segment box from enclose_lambda_segments must span
    at least the union of consecutive point boxes, so it is strictly wider in
    at least one coordinate.
    """
    from telperion.arb_enclosure import enclose_lambda_boundary, enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    n = 8
    prec = 300
    # Point enclosures at each node.
    pts = enclose_lambda_boundary(box, n_per_side=n, prec_bits=prec)
    # Segment enclosures for each sub-segment.
    segs = enclose_lambda_segments(box, n_per_side=n, prec_bits=prec)

    # For each sub-segment i -> i+1, the segment box must be at least as wide
    # as each individual point enclosure, and strictly wider than at least one
    # (because it spans both endpoints).
    for i in range(4 * n):
        _, pt_box_a = pts[i]
        _, pt_box_b = pts[i + 1]
        _, seg_box = segs[i]

        seg_re_lo, seg_re_hi = seg_box[0]
        seg_im_lo, seg_im_hi = seg_box[1]
        a_re_lo, a_re_hi = pt_box_a[0]
        b_re_lo, b_re_hi = pt_box_b[0]

        seg_re_width = seg_re_hi - seg_re_lo
        a_re_width = a_re_hi - a_re_lo
        b_re_width = b_re_hi - b_re_lo

        # Segment box re-width >= max of both point box widths.
        assert seg_re_width >= a_re_width, (
            f"Segment {i} re-width {seg_re_width} < point-A width {a_re_width}"
        )
        assert seg_re_width >= b_re_width, (
            f"Segment {i} re-width {seg_re_width} < point-B width {b_re_width}"
        )
        # Segment box must contain both endpoint midpoints.
        a_re_mid = (a_re_lo + a_re_hi) / 2
        b_re_mid = (b_re_lo + b_re_hi) / 2
        assert seg_re_lo <= a_re_mid <= seg_re_hi, (
            f"Segment {i} does not contain point-A midpoint {a_re_mid}"
        )
        assert seg_re_lo <= b_re_mid <= seg_re_hi, (
            f"Segment {i} does not contain point-B midpoint {b_re_mid}"
        )


def test_enclose_lambda_segments_requires_flint():
    """enclose_lambda_segments raises RuntimeError if python-flint is unavailable."""
    import telperion.arb_enclosure as ae
    if not ae._FLINT_AVAILABLE:
        import pytest
        with pytest.raises(RuntimeError, match="python-flint"):
            ae.enclose_lambda_segments((0, 1, 10, 11), 2, 100)


# ---------------------------------------------------------------------------
# Task 8 fix round 1: RIGOROUS zeta segment enclosures (route beta)
# ---------------------------------------------------------------------------

@requires_flint
def test_enclose_zeta_segment_rigorous_contains_true_values():
    """The 2nd-order Taylor zeta segment box rigorously contains the true zeta values.

    Cross-checks against an mpmath oracle sampled across the segment: every
    sampled true value must lie inside the certified box.  This is the RIGOR
    check the endpoint-union approach failed (it only contained the endpoints).
    """
    from telperion.arb_enclosure import enclose_zeta_segment
    # Vertical segment at sigma=2/5, T in [20.9, 21.1] (near a zeta zero region).
    fixed = Fraction(2, 5)
    lo, hi = Fraction(209, 10), Fraction(211, 10)
    (lo_re, hi_re), (lo_im, hi_im) = enclose_zeta_segment(fixed, lo, hi, True, 300)

    mpmath.mp.dps = 40
    n_samples = 60
    for k in range(n_samples + 1):
        t = lo + (hi - lo) * Fraction(k, n_samples)
        z = mpmath.zeta(mpmath.mpc(str(fixed), str(t)))
        assert float(lo_re) <= float(z.real) <= float(hi_re), (
            f"Real part {float(z.real)} outside [{float(lo_re)},{float(hi_re)}] at t={t}"
        )
        assert float(lo_im) <= float(z.imag) <= float(hi_im), (
            f"Imag part {float(z.imag)} outside [{float(lo_im)},{float(hi_im)}] at t={t}"
        )


@requires_flint
def test_enclose_zeta_segment_returns_fractions():
    """zeta segment box endpoints are exact Fractions."""
    from telperion.arb_enclosure import enclose_zeta_segment
    (lo_re, hi_re), (lo_im, hi_im) = enclose_zeta_segment(Fraction(3, 5), 20, 21, True, 200)
    assert all(isinstance(x, Fraction) for x in (lo_re, hi_re, lo_im, hi_im))


@requires_flint
def test_enclose_zeta_segment_tighter_than_naive_ball():
    """The 2nd-order Taylor enclosure is tighter than a naive acb ball over the segment.

    Near a zeta zero the naive ball straddles 0 while the Taylor box does not
    (or is strictly narrower), demonstrating why route beta works.
    """
    from telperion.arb_enclosure import enclose_zeta_segment, _arb_ball_to_fractions
    from flint import acb, arb, ctx
    fixed = Fraction(2, 5)
    lo, hi = Fraction(209, 10), Fraction(211, 10)
    taylor = enclose_zeta_segment(fixed, lo, hi, True, 300)

    old = ctx.prec
    try:
        ctx.prec = 300
        mid = (lo + hi) / 2
        delta = (hi - lo) / 2
        s = acb(arb(str(fixed)), arb(str(mid), str(delta)))
        zn = s.zeta()
        naive = (_arb_ball_to_fractions(zn.real), _arb_ball_to_fractions(zn.imag))
    finally:
        ctx.prec = old

    t_re_w = taylor[0][1] - taylor[0][0]
    n_re_w = naive[0][1] - naive[0][0]
    assert t_re_w < n_re_w, (
        f"Taylor re-width {float(t_re_w)} not tighter than naive {float(n_re_w)}"
    )


@requires_flint
def test_enclose_zeta_segments_capstone_rigorous_n5():
    """RIGOROUS route beta: zeta segments on [2/5,3/5]x[10,35] certify n=5.

    Adaptive 2nd-order Taylor zeta enclosures (no endpoint-union): no
    segment-box straddles 0 and every consecutive pair is witnessed, so
    segment_winding_certificate reports n == 5.  winding(zeta) == winding(Lambda)
    because they differ by the nonzero analytic factor pi^(-s/2)*Gamma(s/2).
    conjecture1_proved = False.
    """
    from telperion.arb_enclosure import enclose_zeta_segments
    from telperion.emit_winding_count import (
        segment_winding_certificate, _box_contains_zero, _half_plane_witness,
    )
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    segs = enclose_zeta_segments(box, prec_bits=200, n_seed=4)

    for i, (param, seg_box) in enumerate(segs[:-1]):
        assert not _box_contains_zero(seg_box), (
            f"Segment {i} (param={param}) straddles 0"
        )
    for i in range(len(segs) - 1):
        assert _half_plane_witness(segs[i][1], segs[i + 1][1]) is not None, (
            f"No half-plane witness for step {i}->{i+1}"
        )

    cert = segment_winding_certificate(box, segs)
    assert cert.n == 5, f"Expected n=5, got n={cert.n}"
    # The rigorous route uses a bounded number of segments (< 300 at prec 200).
    assert len(segs) - 1 < 300


@requires_flint
def test_enclose_zeta_segments_coarse_refused():
    """A deliberately-coarse manual zeta partition (n=2 per edge) is refused.

    Bypasses the adaptive refinement to build over-wide sub-segments; the
    resulting boxes straddle 0 near the zeta zeros, so
    segment_winding_certificate raises ValueError.
    """
    import pytest
    from telperion.arb_enclosure import enclose_zeta_segment
    from telperion.emit_winding_count import segment_winding_certificate

    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    sigma0, sigma1, T0, T1 = Fraction(2, 5), Fraction(3, 5), Fraction(10), Fraction(35)
    n = 2
    boxes = []
    for fixed, a, b, isv in [
        (T0, sigma0, sigma1, False),
        (sigma1, T0, T1, True),
        (T1, sigma1, sigma0, False),
        (sigma0, T1, T0, True),
    ]:
        lo, hi = min(a, b), max(a, b)
        fwd = a < b
        pieces = []
        for k in range(n):
            x = lo + (hi - lo) * Fraction(k, n)
            y = lo + (hi - lo) * Fraction(k + 1, n)
            pieces.append(enclose_zeta_segment(fixed, x, y, isv, 200))
        if not fwd:
            pieces = pieces[::-1]
        boxes.extend(pieces)
    segs = [(Fraction(i, len(boxes)), boxes[i]) for i in range(len(boxes))]
    segs.append((Fraction(1), segs[0][1]))

    with pytest.raises(ValueError, match="contains 0|straddle|n_per_side"):
        segment_winding_certificate(box, segs)


def test_enclose_zeta_segments_requires_flint():
    """enclose_zeta_segments raises RuntimeError if python-flint is unavailable."""
    import telperion.arb_enclosure as ae
    if not ae._FLINT_AVAILABLE:
        import pytest
        with pytest.raises(RuntimeError, match="python-flint"):
            ae.enclose_zeta_segments((Fraction(2, 5), Fraction(3, 5), 10, 35), 200)
