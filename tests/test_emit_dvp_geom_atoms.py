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
from telperion.emit_full_argument_principle import (
    FullArgumentPrincipleEmitter, certify_full_argument_principle_point,
    full_argument_principle_certificate, full_argument_principle_family,
)
from telperion.emit_rect_argument_principle import (
    RectArgumentPrincipleEmitter, certify_rect_argument_principle_point,
    rect_argument_principle_certificate, rect_argument_principle_family,
)
from telperion.emit_annulus_count import (
    AnnulusCountEmitter, annulus_count_certificate, annulus_count_family,
    certify_annulus_count_point,
)
from telperion.emit_slit_loop_winding_zero import (
    SlitLoopWindingZeroEmitter, certify_slit_loop_winding_zero_point,
    slit_loop_winding_zero_certificate, slit_loop_winding_zero_family,
)
from telperion.emit_box_residue_sum import (
    BoxResidueSumEmitter, box_residue_sum_certificate, box_residue_sum_family,
    certify_box_residue_sum_point,
)
from telperion.emit_rect_winding import (
    RectWindingEmitter, certify_rect_winding_point, rect_winding_certificate,
    rect_winding_family,
)
from telperion.emit_log_product_bound import (
    LogProductBoundEmitter, certify_log_product_bound_point,
    log_product_bound_certificate, log_product_bound_family,
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
    "full_argument_principle": certify_full_argument_principle_point,
    "rect_argument_principle": certify_rect_argument_principle_point,
    "annulus_count": certify_annulus_count_point,
    "slit_loop_winding_zero": certify_slit_loop_winding_zero_point,
    "box_residue_sum": certify_box_residue_sum_point,
    "rect_winding": certify_rect_winding_point,
    "log_product_bound": certify_log_product_bound_point,
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


def test_full_argument_principle_certificate_and_shape():
    c = full_argument_principle_certificate(Fraction(3, 2))
    assert c.R == Fraction(3, 2)
    body, nthm = _emit_one(full_argument_principle_family, FullArgumentPrincipleEmitter,
                           {"R": "3/2"}, "fap")
    assert nthm == 1
    # residue side + analytic-vanishing side (Cauchy) both present
    assert "circleIntegral.integral_sub_inv_of_mem_ball" in body
    assert "hE.circleIntegral_eq_zero hR.le" in body
    assert "circleIntegral.integral_add hsum_int hEint" in body
    assert "= 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ)" in body


def test_full_argument_principle_negative_control():
    with pytest.raises(ValueError, match="strictly positive contour radius"):
        full_argument_principle_certificate(0)


def test_rect_argument_principle_certificate_and_shape():
    c = rect_argument_principle_certificate(0, 2, 0, 1)
    assert (c.x0, c.x1, c.y0, c.y1) == (0, 2, 0, 1)
    body, nthm = _emit_one(rect_argument_principle_family, RectArgumentPrincipleEmitter,
                           {"x0": "0", "x1": "2", "y0": "0", "y1": "1"}, "rap")
    assert nthm == 1
    assert "integral_boundary_rect_eq_zero_of_differentiableOn" in body
    assert "×ℂ" in body
    assert "= 0 := by" in body


def test_rect_argument_principle_negative_control():
    with pytest.raises(ValueError, match="x0 < x1"):
        rect_argument_principle_certificate(2, 0, 0, 1)
    with pytest.raises(ValueError, match="y0 < y1"):
        rect_argument_principle_certificate(0, 1, 1, 0)


def test_annulus_count_certificate_and_shape():
    c = annulus_count_certificate(1, 2)
    assert (c.r, c.R) == (1, 2)
    body, nthm = _emit_one(annulus_count_family, AnnulusCountEmitter, {"r": "1", "R": "2"}, "ann")
    assert nthm == 1
    # outer residue sum minus inner Cauchy-zero
    assert "circleIntegral.integral_sub_inv_of_mem_ball" in body
    assert "DiffContOnCl.circleIntegral_eq_zero" in body
    assert "rw [houter, hinner, sub_zero]" in body


def test_annulus_count_negative_control():
    with pytest.raises(ValueError, match="inner radius r > 0"):
        annulus_count_certificate(0, 2)
    with pytest.raises(ValueError, match="outer radius R > r"):
        annulus_count_certificate(2, 1)


def test_slit_loop_winding_zero_certificate_and_shape():
    c = slit_loop_winding_zero_certificate(Fraction(1, 2))
    assert c.r == Fraction(1, 2)
    body, nthm = _emit_one(slit_loop_winding_zero_family, SlitLoopWindingZeroEmitter,
                           {"r": "1"}, "slw")
    assert nthm == 1
    # clog_real antiderivative + FTC-2 + closed-loop cancellation
    assert "clog_real" in body
    assert "integral_eq_sub_of_hasDerivAt hd hint" in body
    assert "hclosed, sub_self" in body
    assert "Complex.mem_slitPlane_iff" in body


def test_slit_loop_winding_zero_negative_control():
    with pytest.raises(ValueError, match="positive leash radius"):
        slit_loop_winding_zero_certificate(0)
    with pytest.raises(ValueError, match=r"r ≤ 1"):
        slit_loop_winding_zero_certificate(2)


def test_box_residue_sum_certificate_and_shape():
    c = box_residue_sum_certificate(0, 2, 0, 1)
    assert (c.x0, c.x1, c.y0, c.y1) == (0, 2, 0, 1)
    body, nthm = _emit_one(box_residue_sum_family, BoxResidueSumEmitter,
                           {"x0": "0", "x1": "2", "y0": "0", "y1": "1"}, "brs")
    assert nthm == 1
    # Finset-linearity plumbing conditional on the per-pole winding hypothesis
    assert "intervalIntegral.integral_finsetSum" in body
    assert "hwind" in body
    assert "linear_combination (m ρ : ℂ) * hw" in body
    assert "= 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ)" in body


def test_box_residue_sum_negative_control():
    with pytest.raises(ValueError, match="x0 < x1"):
        box_residue_sum_certificate(2, 0, 0, 1)
    with pytest.raises(ValueError, match="y0 < y1"):
        box_residue_sum_certificate(0, 1, 1, 0)


def test_rect_winding_certificate_and_shape():
    c = rect_winding_certificate(0, 2, 0, 1)
    assert (c.x0, c.x1, c.y0, c.y1) == (0, 2, 0, 1)
    body, nthm = _emit_one(rect_winding_family, RectWindingEmitter,
                           {"x0": "0", "x1": "2", "y0": "0", "y1": "1"}, "rw")
    assert nthm == 3  # 2 monodromy helpers + 1 winding theorem
    # the branch-split proof: clog_real antiderivative, the ρ-(·) left branch, monodromy jumps
    assert "log_neg_sub_im_neg" in body
    assert "log_neg_sub_im_pos" in body
    assert "clog_real" in body
    assert "arg_neg_eq_arg_add_pi_of_im_neg" in body
    assert "= 2 * ↑π * I := by" in body


def test_rect_winding_negative_control():
    with pytest.raises(ValueError, match="x0 < x1"):
        rect_winding_certificate(2, 2, 0, 1)
    with pytest.raises(ValueError, match="y0 < y1"):
        rect_winding_certificate(0, 1, 1, 1)


def test_log_product_bound_certificate_and_shape():
    c = log_product_bound_certificate(2, 5)
    assert (c.R0, c.R) == (2, 5)
    body, nthm = _emit_one(log_product_bound_family, LogProductBoundEmitter,
                           {"R0": "2", "R": "5"}, "lpb")
    assert nthm == 1
    # two-scale separation + log-of-product + monotone log + Finset assembly
    assert "norm_sub_norm_le" in body
    assert "Real.log_prod" in body
    assert "Real.log_le_log" in body
    assert "Finset.sum_le_sum" in body


def test_log_product_bound_negative_control():
    with pytest.raises(ValueError, match="inner radius R₀ ≥ 1"):
        log_product_bound_certificate(Fraction(1, 2), 5)
    with pytest.raises(ValueError, match="outer radius R > R₀"):
        log_product_bound_certificate(3, 2)
