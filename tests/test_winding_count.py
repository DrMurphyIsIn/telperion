"""Tests for winding_count numeric core (Task 3) + kernel emitter (Task 4, Stage 2A).

Toy polynomials with known winding numbers, plus negative-control refusals (numeric
core), and the emit-shape + drift + registration checks for ``WindingCountEmitter``
(the kernel-verified ``Bd(Lambda'/Lambda) = 2*pi*i*N`` theorem).
"""
from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))


def _poly_boundary(box, n_per_side, poly):
    """Build an exact rational boundary cycle for a polynomial on a box boundary.

    Each sample is a degenerate (point) enclosure box: lo == hi == value.
    The boundary traverses: bottom (left to right), right (bottom to top),
    top (right to left), left (top to bottom).

    Returns a closed cycle: last sample == first sample.

    Args:
        box: (lo_re, hi_re, lo_im, hi_im) as Fraction-compatible values.
        n_per_side: number of sample points per side (exclusive of corners, so
            n_per_side+1 intervals, n_per_side+2 points including both endpoints
            -- we use n_per_side+1 steps per side, endpoints included).
        poly: callable z -> complex, evaluated at rational complex z.

    Returns:
        list of (param, ((lo_re, hi_re), (lo_im, hi_im))) with Fraction values.
    """
    lo_re, hi_re, lo_im, hi_im = (Fraction(v) for v in box)
    n = n_per_side  # steps per side

    def make_box(z_val):
        re = Fraction(z_val.real).limit_denominator(10 ** 15)
        im = Fraction(z_val.imag).limit_denominator(10 ** 15)
        return (re, re), (im, im)

    samples = []
    param = Fraction(0)

    # Bottom side: left to right, y = lo_im
    for k in range(n):
        t = Fraction(k, n)
        re = lo_re + t * (hi_re - lo_re)
        z = complex(float(re), float(lo_im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Right side: bottom to top, x = hi_re
    for k in range(n):
        t = Fraction(k, n)
        im = lo_im + t * (hi_im - lo_im)
        z = complex(float(hi_re), float(im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Top side: right to left, y = hi_im
    for k in range(n):
        t = Fraction(k, n)
        re = hi_re + t * (lo_re - hi_re)
        z = complex(float(re), float(hi_im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Left side: top to bottom, x = lo_re
    for k in range(n):
        t = Fraction(k, n)
        im = hi_im + t * (lo_im - hi_im)
        z = complex(float(lo_re), float(im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Close the cycle: append copy of first point with param=1
    first = samples[0]
    samples.append((Fraction(1), first[1]))

    return samples


def test_winding_number_z_squared_is_two():
    # f(z)=z^2 on a box around 0 winds twice
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z * z)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 2


def test_winding_number_zero_free_is_zero():
    # f(z)=z-10 on a box near 0 (10 not enclosed) winds zero times
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z - 10)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 0


def test_winding_count_refuses_box_containing_zero():
    from telperion.emit_winding_count import winding_count_certificate

    box = (0, 1, 0, 1)
    bad = [(0, ((-1, 1), (-1, 1)))]  # straddles 0
    with pytest.raises(ValueError, match="contains 0|straddle"):
        winding_count_certificate(box, bad * 2)


def test_winding_number_z_is_one():
    # f(z)=z winds once around 0
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 1


def test_winding_number_z_cubed_is_three():
    # f(z)=z^3 winds three times
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 12, lambda z: z ** 3)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 3


def test_half_plane_witness_adjacent_first_quadrant():
    # Two boxes both in the first quadrant share the (1,1) witness direction
    from fractions import Fraction
    from telperion.emit_winding_count import _half_plane_witness

    box_a = ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2)))
    box_b = ((Fraction(2), Fraction(3)), (Fraction(1), Fraction(3)))
    w = _half_plane_witness(box_a, box_b)
    assert w is not None


def test_half_plane_witness_opposite_boxes_returns_none():
    # Boxes on opposite sides of 0 should have no common half-plane witness
    from fractions import Fraction
    from telperion.emit_winding_count import _half_plane_witness

    # box_a in Q1, box_b in Q3 -- no single direction has all corners positive
    box_a = ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2)))
    box_b = ((Fraction(-3), Fraction(-1)), (Fraction(-3), Fraction(-1)))
    w = _half_plane_witness(box_a, box_b)
    assert w is None


def test_winding_count_certificate_zero_free():
    # A curve that does not straddle 0 and has witnesses -> certificate produced
    from fractions import Fraction
    from telperion.emit_winding_count import winding_count_certificate

    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    # z-10 stays in the half-plane Re(w) < 0 so witnesses always exist
    samples = _poly_boundary(box, 8, lambda z: z - 10)
    cert = winding_count_certificate(box, samples)
    assert cert.n == 0


def test_winding_count_certificate_missing_witness_raises():
    # A two-step cycle where step crosses 0 should raise (no half-plane witness)
    from fractions import Fraction
    from telperion.emit_winding_count import winding_count_certificate

    box = (Fraction(1), Fraction(2), Fraction(1), Fraction(2))
    # Two boxes on opposite sides: Q1 then Q3 -> no witness
    sample_a = (Fraction(0), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))
    sample_b = (Fraction(Fraction(1, 2)), ((Fraction(-3), Fraction(-1)), (Fraction(-3), Fraction(-1))))
    sample_c = (Fraction(1), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))  # close cycle
    with pytest.raises(ValueError):
        winding_count_certificate(box, [sample_a, sample_b, sample_c])


# ---------------------------------------------------------------------------
# Task 4: WindingCountEmitter emit-shape + drift + registration
# ---------------------------------------------------------------------------

def test_winding_count_emits_boundary_integral_equals_2pi_i_N():
    """The toy z^2 -> N=2 instance emits a boundary log-derivative integral = 2*pi*i*2,
    with the monodromy proof present (clog_real / Complex.log)."""
    from telperion.emit_winding_count import (
        winding_count_family,
        WindingCountEmitter,
        certify_winding_count_point,
        _z2_samples,
    )
    from telperion.family import GridSpec
    from telperion.lean import LeanProfile

    fam = winding_count_family(
        "T", GridSpec([("case", [0])]),
        lean_name=lambda pt: "winding_z2",
        spec=lambda pt: {"box": (-1, 1, -1, 1), "samples": _z2_samples(), "mode": "toy_z2"},
    )
    inst, _ = certify_winding_count_point(fam, {"case": 0}, "winding_z2")

    class V:
        instances = [inst]

    body, nthm = WindingCountEmitter().emit_body(V(), LeanProfile(namespace=("X",)))
    # 3 theorems for the toy: winding-ONE primitive, log-deriv reduction, main.
    assert nthm == 3
    assert "2 * " in body and "π" in body and "* I" in body
    assert "clog_real" in body or "Complex.log" in body   # monodromy proof present
    assert "theorem winding_z2" in body
    # statement-match gate single-sourced.
    assert "example :" in body


def test_winding_count_lambda_emits_N_from_certificate():
    """The Lambda instance emits `= 2*pi*i*N` where N is the certified winding count,
    the per-pole interior primitive, and the argument-principle Finset linearity."""
    from telperion.emit_winding_count import (
        winding_count_family,
        WindingCountEmitter,
        certify_winding_count_point,
    )
    from telperion.family import GridSpec
    from telperion.lean import LeanProfile

    # A synthetic 5-pole boundary cycle: a curve that winds 5 times about 0
    # (arg increment 5*2*pi over the loop) with per-step half-plane witnesses.
    import cmath

    box = (Fraction(2, 5), Fraction(3, 5), Fraction(10), Fraction(35))
    n = 240
    samples = []
    for k in range(n):
        theta = 5 * 2 * cmath.pi * k / n
        w = cmath.exp(1j * theta)
        re = Fraction(w.real).limit_denominator(10 ** 12)
        im = Fraction(w.imag).limit_denominator(10 ** 12)
        samples.append((Fraction(k, n), ((re, re), (im, im))))
    samples.append((Fraction(0), samples[0][1]))

    fam = winding_count_family(
        "T", GridSpec([("case", [0])]),
        lean_name=lambda pt: "winding_lambda_five",
        spec=lambda pt: {"box": box, "samples": samples, "mode": "lambda"},
    )
    inst, _ = certify_winding_count_point(fam, {"case": 0}, "winding_lambda_five")
    cert, mode = inst.payload
    assert mode == "lambda"
    assert cert.n == 5

    class V:
        instances = [inst]

    body, nthm = WindingCountEmitter().emit_body(V(), LeanProfile(namespace=("X",)))
    # 2 theorems: interior-pole primitive + main.
    assert nthm == 2
    assert "= 2 * ↑π * I * 5" in body
    assert "rect_winding" in body                 # from-scratch per-pole winding primitive
    assert "integral_finsetSum" in body           # argument-principle Finset linearity
    assert "hin" in body                          # enclosure brackets as hypotheses


def test_winding_count_registered_in_certify():
    """The winding_count kind is registered at both dispatch points."""
    from telperion.certify import _SPECIAL_KINDS, _SPECIAL_DISPATCH, emitter_for

    assert "winding_count" in _SPECIAL_KINDS
    assert _SPECIAL_DISPATCH["winding_count"] == (
        "emit_winding_count", "certify_winding_count_point", "WindingCountEmitter",
    )
    assert type(emitter_for("winding_count")).__name__ == "WindingCountEmitter"


def test_winding_count_exported_from_package():
    """The public API is exported from the telperion package."""
    import telperion

    assert hasattr(telperion, "WindingCountEmitter")
    assert hasattr(telperion, "winding_count_certificate")
    assert hasattr(telperion, "winding_count_family")
    assert hasattr(telperion, "certify_winding_count_point")


def test_winding_count_emitter_classified():
    """WindingCountEmitter has a declared certificate-sensitivity stance."""
    from telperion.emitter_sensitivity import REGISTRY, STRUCTURALLY_NONVACUOUS

    assert "WindingCountEmitter" in REGISTRY
    assert REGISTRY["WindingCountEmitter"].stance == STRUCTURALLY_NONVACUOUS


# ---------------------------------------------------------------------------
# Task 8: segment winding certificate
# ---------------------------------------------------------------------------

def test_segment_winding_certificate_capstone_n5():
    """segment_winding_certificate on capstone box [2/5,3/5]x[10,35] gives n=5.

    RIGOROUS route beta: uses enclose_zeta_segments (adaptive 2nd-order Taylor
    zeta enclosures of the continuum, no endpoint-union).  winding(zeta) ==
    winding(Lambda) == 5 because they differ by the nonzero analytic factor
    pi^(-s/2)*Gamma(s/2).  conjecture1_proved = False.
    """
    pytest.importorskip("flint")
    from fractions import Fraction
    from telperion.arb_enclosure import enclose_zeta_segments
    from telperion.emit_winding_count import segment_winding_certificate

    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    segs = enclose_zeta_segments(box, prec_bits=200, n_seed=4)
    cert = segment_winding_certificate(box, segs)
    assert cert.n == 5


def test_segment_winding_certificate_refuses_zero_box():
    """segment_winding_certificate raises ValueError on a segment-box that contains 0."""
    from fractions import Fraction
    from telperion.emit_winding_count import segment_winding_certificate

    box = (Fraction(0), Fraction(1), Fraction(0), Fraction(1))
    # A segment-box that straddles 0 in both parts.
    bad_seg = (Fraction(0), ((-Fraction(1), Fraction(1)), (-Fraction(1), Fraction(1))))
    segs = [bad_seg, bad_seg]  # closed (same first and last for the check)
    with pytest.raises(ValueError, match="contains 0|straddle"):
        segment_winding_certificate(box, segs)


def test_segment_winding_certificate_refuses_no_witness():
    """segment_winding_certificate raises ValueError when a step has no half-plane witness."""
    from fractions import Fraction
    from telperion.emit_winding_count import segment_winding_certificate

    box = (Fraction(1), Fraction(2), Fraction(1), Fraction(2))
    # Two segment-boxes on opposite sides of 0: Q1 then Q3 -> no shared witness.
    seg_a = (Fraction(0), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))
    seg_b = (Fraction(1, 2), ((-Fraction(3), -Fraction(1)), (-Fraction(3), -Fraction(1))))
    seg_c = (Fraction(1), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))
    with pytest.raises(ValueError):
        segment_winding_certificate(box, [seg_a, seg_b, seg_c])


def test_segment_winding_certificate_returns_correct_fields():
    """SegmentWindingCertificate has the right fields and types."""
    from fractions import Fraction
    from telperion.emit_winding_count import SegmentWindingCertificate, segment_winding_certificate

    # Use the toy z^2 cycle (winding = 2) with exact Fraction boxes.
    # Build a minimal valid cycle: use boxes all in Q1 with winding 0 as a
    # degenerate positive control.
    box = (Fraction(1), Fraction(2), Fraction(1), Fraction(2))
    # All boxes in Q1: witness (1,0) works for every step.
    seg_a = (Fraction(0), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))
    seg_b = (Fraction(1, 4), ((Fraction(2), Fraction(3)), (Fraction(1), Fraction(2))))
    seg_c = (Fraction(1, 2), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))
    # Close the cycle.
    segs = [seg_a, seg_b, seg_c, seg_a]
    cert = segment_winding_certificate(box, segs)
    assert isinstance(cert, SegmentWindingCertificate)
    assert isinstance(cert.n, int)
    assert all(isinstance(f, Fraction) for f in cert.box)
    assert len(cert.step_witnesses) == len(segs) - 1
    for w in cert.step_witnesses:
        assert len(w) == 2
        assert all(isinstance(f, Fraction) for f in w)


def test_segment_winding_exported_from_package():
    """SegmentWindingCertificate and segment_winding_certificate are in the public API."""
    import telperion
    assert hasattr(telperion, "SegmentWindingCertificate")
    assert hasattr(telperion, "segment_winding_certificate")
    assert hasattr(telperion, "enclose_lambda_segments")
    assert hasattr(telperion, "enclose_lambda_segment")
    assert hasattr(telperion, "enclose_zeta_segments")
    assert hasattr(telperion, "enclose_zeta_segment")


def test_enclose_lambda_segments_wider_than_points_winding_test():
    """In the winding test context: segment boxes are wider than point boxes at same nodes."""
    pytest.importorskip("flint")
    from fractions import Fraction
    from telperion.arb_enclosure import enclose_lambda_boundary, enclose_lambda_segments

    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    n = 10
    prec = 200
    pts = enclose_lambda_boundary(box, n_per_side=n, prec_bits=prec)
    segs = enclose_lambda_segments(box, n_per_side=n, prec_bits=prec)

    # Check a sample of segments (every 5th) to keep the test fast.
    for i in range(0, 4 * n, 5):
        _, pt_a = pts[i]
        _, pt_b = pts[i + 1]
        _, seg = segs[i]

        # Segment re-width must be >= each endpoint's re-width.
        seg_w = seg[0][1] - seg[0][0]
        a_w = pt_a[0][1] - pt_a[0][0]
        b_w = pt_b[0][1] - pt_b[0][0]
        assert seg_w >= a_w
        assert seg_w >= b_w


def test_winding_count_lean_no_drift():
    """The frozen WindingCount.lean matches regeneration byte-for-byte (drift net).

    Skipped if python-flint (the Arb enclosure backend for the Lambda instance) is
    unavailable in the test environment."""
    pytest.importorskip("flint")
    import importlib.util

    gen_path = (
        Path(__file__).resolve().parents[1]
        / "examples" / "zeta_zero_localization" / "generate.py"
    )
    spec = importlib.util.spec_from_file_location("_zzl_generate", gen_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    text = mod.build_winding()
    frozen = mod._OUT_WINDING
    assert frozen.exists(), "WindingCount.lean not generated yet"
    assert frozen.read_text(encoding="utf-8") == text, "WindingCount.lean drifted from generate.py"
