"""dVP geometry/two-scale emitters (two_scale_separation, far_pole_sum, herglotz_lower):
self-check / negative-control + emitted-Lean shape. Kernel verification of the emitted Lean is in
CI (job `dvp-geom-atoms-compiles`) + examples/dvp_geom_atoms. conjecture1_proved = False.
"""
from fractions import Fraction

import pytest

from telperion.emit_far_pole_sum import (
    FarPoleSumEmitter, certify_far_pole_sum_point, far_pole_sum_certificate, far_pole_sum_family,
)
from telperion.emit_herglotz_lower import (
    HerglotzLowerEmitter, certify_herglotz_lower_point, herglotz_lower_certificate,
    herglotz_lower_family,
)
from telperion.emit_argument_principle import (
    ArgumentPrincipleEmitter, argument_principle_certificate, argument_principle_family,
    certify_argument_principle_point,
)
from telperion.emit_two_scale_separation import (
    TwoScaleSeparationEmitter, certify_two_scale_separation_point, two_scale_certificate,
    two_scale_separation_family,
)
from telperion.family import GridSpec
from telperion.lean import LeanProfile

_CERT = {
    "two_scale_separation": certify_two_scale_separation_point,
    "far_pole_sum": certify_far_pole_sum_point,
    "herglotz_lower": certify_herglotz_lower_point,
    "argument_principle": certify_argument_principle_point,
}


def _emit_one(fam_fn, emitter_cls, spec, name):
    fam = fam_fn("T", GridSpec([("case", [0])]), lambda pt: name, spec=lambda pt: spec)
    inst, nchk = _CERT[fam.special[0]](fam, {"case": 0}, name)
    assert nchk == 1

    class _V:
        instances = [inst]

    e = emitter_cls(); e.__post_init__()
    return e.emit_body(_V(), LeanProfile(namespace=("T",)))


def test_two_scale_certificate_and_shape():
    c = two_scale_certificate(Fraction(3, 2), 1)
    assert (c.R, c.R0) == (Fraction(3, 2), Fraction(1, 1))
    body, nthm = _emit_one(two_scale_separation_family, TwoScaleSeparationEmitter, {"R": "3/2", "R0": 1}, "ts")
    assert nthm == 1
    assert "open Metric" in body
    assert "norm_sub_norm_le _ _" in body
    assert "sub_sub_sub_cancel_right" in body
    assert "((3 / 2) : ℝ) - 1 ≤ ‖z - ρ‖" in body


def test_two_scale_negative_control():
    with pytest.raises(ValueError, match="R₀ < R"):
        two_scale_certificate(1, 2)


def test_far_pole_certificate_and_shape():
    c = far_pole_sum_certificate(Fraction(3, 2))
    assert c.R == Fraction(3, 2)
    body, nthm = _emit_one(far_pole_sum_family, FarPoleSumEmitter, {"R": "3/2"}, "fp")
    assert nthm == 1
    assert "norm_sub_norm_le _ _" in body
    assert "div_le_div_iff₀ hden_pos hRz" in body
    assert "Finset.sum_div" in body


def test_far_pole_negative_control():
    with pytest.raises(ValueError, match="strictly positive radius"):
        far_pole_sum_certificate(0)


def test_herglotz_certificate_and_shape():
    c = herglotz_lower_certificate(Fraction(3, 2), Fraction(1, 2), 1)
    assert (c.sigma, c.beta, c.k) == (Fraction(3, 2), Fraction(1, 2), 1)
    body, nthm = _emit_one(herglotz_lower_family, HerglotzLowerEmitter,
                           {"sigma": "3/2", "beta": "1/2", "k": 1}, "hl")
    assert nthm == 3  # 2 helpers + 1 wrapper
    assert "private theorem re_smul_inv_sub_at_equal_height" in body
    assert "private theorem re_inv_sub_nonneg_of_re_lt" in body
    assert "Finset.add_sum_erase" in body


def test_herglotz_negative_controls():
    with pytest.raises(ValueError, match="σ > β"):
        herglotz_lower_certificate(1, 2, 1)
    with pytest.raises(ValueError, match="k ≥ 1"):
        herglotz_lower_certificate(2, 1, 0)


def test_argument_principle_certificate_and_shape():
    c = argument_principle_certificate(Fraction(3, 2))
    assert c.R == Fraction(3, 2)
    body, nthm = _emit_one(argument_principle_family, ArgumentPrincipleEmitter, {"R": "3/2"}, "ap")
    assert nthm == 1
    assert "circleIntegral.integral_sub_inv_of_mem_ball" in body
    assert "circleIntegral.integral_fun_sum" in body
    assert "= 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ)" in body


def test_argument_principle_negative_control():
    with pytest.raises(ValueError, match="strictly positive contour radius"):
        argument_principle_certificate(0)
