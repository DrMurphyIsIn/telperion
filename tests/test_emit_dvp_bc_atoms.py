"""dVP entire-part (i-b') emitters (max_modulus, bc_deriv_re, entire_part_bound):
self-check / negative-control + emitted-Lean shape.  Kernel verification of the emitted
Lean is in CI (job `dvp-bc-atoms-compiles`) + examples/dvp_bc_atoms.  conjecture1_proved = False.
"""
from fractions import Fraction

import pytest

from telperion.emit_bc_deriv_re import (
    BCDerivReEmitter, bc_deriv_re_certificate, bc_deriv_re_family, certify_bc_deriv_re_point,
)
from telperion.emit_entire_part_bound import (
    EntirePartBoundEmitter, certify_entire_part_bound_point, entire_part_bound_certificate,
    entire_part_bound_family,
)
from telperion.emit_max_modulus import (
    MaxModulusEmitter, certify_max_modulus_point, max_modulus_certificate, max_modulus_family,
)
from telperion.family import GridSpec
from telperion.lean import LeanProfile


def _emit_one(fam_fn, emitter_cls, spec, name):
    fam = fam_fn(
        "T", GridSpec([("case", [0])]), lambda pt: name, spec=lambda pt: spec
    )
    kind = fam.special[0]
    certify_fn = {
        "max_modulus": certify_max_modulus_point,
        "bc_deriv_re": certify_bc_deriv_re_point,
        "entire_part_bound": certify_entire_part_bound_point,
    }[kind]
    inst, nchk = certify_fn(fam, {"case": 0}, name)
    assert nchk == 1

    class _View:
        instances = [inst]

    e = emitter_cls()
    e.__post_init__()
    body, nthm = e.emit_body(_View(), LeanProfile(namespace=("T",)))
    return body, nthm


# ---- max_modulus --------------------------------------------------------------------
def test_max_modulus_certificate_and_shape():
    c = max_modulus_certificate(Fraction(1, 2), 12)
    assert (c.R, c.B) == (Fraction(1, 2), Fraction(12, 1))
    body, nthm = _emit_one(max_modulus_family, MaxModulusEmitter, {"R": "1/2", "B": 12}, "mm")
    assert nthm == 1
    assert "open Complex Metric" in body
    assert "Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd" in body
    assert "rw [frontier_ball c (by norm_num : ((1 / 2) : ℝ) ≠ 0)]" in body
    assert "∀ z ∈ ball c ((1 / 2) : ℝ), ‖f z‖ ≤ (12 : ℝ)" in body


def test_max_modulus_negative_control_nonpositive_radius():
    with pytest.raises(ValueError, match="strictly positive radius"):
        max_modulus_certificate(0, 12)
    with pytest.raises(ValueError, match="strictly positive radius"):
        max_modulus_certificate(-1, 12)


# ---- bc_deriv_re --------------------------------------------------------------------
def test_bc_deriv_re_certificate_and_shape():
    c = bc_deriv_re_certificate(Fraction(3, 2), Fraction(1, 2), 6)
    assert (c.R, c.r, c.Mp) == (Fraction(3, 2), Fraction(1, 2), Fraction(6, 1))
    body, nthm = _emit_one(
        bc_deriv_re_family, BCDerivReEmitter, {"R": "3/2", "r": "1/2", "Mp": 6}, "bd"
    )
    assert nthm == 1
    assert "Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hzball hf0" in body
    assert "Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsphere" in body
    assert "‖deriv h c‖ ≤ 2 * (6 : ℝ) / (((3 / 2) : ℝ) - (1 / 2))" in body


def test_bc_deriv_re_negative_controls():
    with pytest.raises(ValueError, match="r < R"):
        bc_deriv_re_certificate(1, 2, 6)
    with pytest.raises(ValueError, match="M' > 0"):
        bc_deriv_re_certificate(2, 1, 0)
    with pytest.raises(ValueError, match="r > 0"):
        bc_deriv_re_certificate(2, 0, 6)


# ---- entire_part_bound --------------------------------------------------------------
def test_entire_part_bound_certificate_and_shape():
    c = entire_part_bound_certificate(Fraction(3, 2), Fraction(1, 2), 6)
    assert (c.R, c.r, c.Mp) == (Fraction(3, 2), Fraction(1, 2), Fraction(6, 1))
    body, nthm = _emit_one(
        entire_part_bound_family, EntirePartBoundEmitter, {"R": "3/2", "r": "1/2", "Mp": 6}, "ep"
    )
    # 3 preamble helper lemmas + 1 wrapper
    assert nthm == 4
    assert "private theorem log_branch_of_analytic_nonvanishing" in body
    assert "private theorem norm_deriv_le_of_re_le" in body
    assert "private theorem norm_logDeriv_le_of_log_norm_le" in body
    assert (
        "norm_logDeriv_le_of_log_norm_le (by norm_num) (by norm_num) (by norm_num) hg hne hbound"
        in body
    )


def test_entire_part_bound_negative_controls():
    with pytest.raises(ValueError, match="r < R"):
        entire_part_bound_certificate(1, 2, 6)
    with pytest.raises(ValueError, match="M' > 0"):
        entire_part_bound_certificate(2, 1, 0)
