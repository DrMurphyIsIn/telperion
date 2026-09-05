"""dVP-atom emitters (bc_split, jensen_zero_count, sphere_bound): self-check /
negative-control + emitted-Lean shape.  Kernel verification of the emitted Lean is in
CI (job `dvp-atoms-compiles`) + examples/dvp_atoms.  conjecture1_proved = False.
"""
from fractions import Fraction

import pytest

from telperion.emit_bc_split import BCSplitEmitter, bc_split_certificate
from telperion.emit_jensen_zero_count import (
    JensenZeroCountEmitter, jensen_zero_count_certificate,
)
from telperion.emit_sphere_bound import SphereBoundEmitter, sphere_bound_certificate


def _emitter(cls):
    e = cls(); e.__post_init__(); return e


# ---- bc_split -----------------------------------------------------------------------
def test_bc_split_tight_and_slack():
    assert bc_split_certificate().slack == 0
    assert bc_split_certificate(slack=Fraction(1, 10)).slack == Fraction(1, 10)
    lean = _emitter(BCSplitEmitter)._emit(bc_split_certificate(), "t")
    assert "theorem t (w Z E : ℂ) (B : ℝ) (hw : w = Z + E) (hE : ‖E‖ ≤ B)" in lean
    assert "(-w).re ≤ B - Z.re := by" in lean
    assert "Complex.abs_re_le_norm E" in lean


def test_bc_split_negative_control_refuses_negative_slack():
    with pytest.raises(ValueError, match="strengthen"):
        bc_split_certificate(slack=Fraction(-1, 10))


def test_bc_split_slack_appears_in_conclusion():
    lean = _emitter(BCSplitEmitter)._emit(bc_split_certificate(slack=Fraction(1, 10)), "s")
    assert "(-w).re ≤ B - Z.re + (1 / 10 : ℝ) := by" in lean


# ---- jensen_zero_count --------------------------------------------------------------
def test_jensen_certificate_and_shape():
    c = jensen_zero_count_certificate(r=Fraction(1, 2), R=1)
    assert (c.r, c.R) == (Fraction(1, 2), Fraction(1, 1))
    lean = _emitter(JensenZeroCountEmitter)._emit(c, "j")
    assert "AnalyticOnNhd ℂ f (Metric.closedBall c |(1 : ℝ)|)" in lean
    assert "MeromorphicOn.divisor f (Metric.closedBall c |(1 / 2 : ℝ)|)" in lean
    assert "hf.sum_divisor_le (by norm_num) (by norm_num) hM hfc hbound" in lean


def test_jensen_negative_control_equal_radii():
    with pytest.raises(ValueError, match="r < R"):
        jensen_zero_count_certificate(r=1, R=1)


def test_jensen_negative_control_nonpositive_inner():
    with pytest.raises(ValueError, match="≤ 0"):
        jensen_zero_count_certificate(r=Fraction(-1, 2), R=1)


# ---- sphere_bound -------------------------------------------------------------------
def test_sphere_certificate_and_shape():
    c = sphere_bound_certificate(R=Fraction(1, 2))
    assert c.R == Fraction(1, 2)
    lean = _emitter(SphereBoundEmitter)._emit(c, "s")
    assert "(hcR : (1 / 2 : ℝ) + 1 < c.re)" in lean
    assert "‖f z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re" in lean
    assert "(‖c‖ + (1 / 2 : ℝ)) / (c.re - (1 / 2 : ℝ) - 1)" in lean


def test_sphere_negative_control_nonpositive_radius():
    with pytest.raises(ValueError, match="≤ 0"):
        sphere_bound_certificate(R=0)
