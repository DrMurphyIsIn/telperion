"""GevreyMajorant emitter (NS/Euler Gevrey-2 factorial-majorant calculus):
certify → emit → lint, with budget / polynomial-radius positive controls and
violated-budget refusals as negative controls.  The Lean kernel is the arbiter
(local `lake build` / CI)."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    gevrey_majorant_certificate,
    gevrey_majorant_family,
)
from telperion.emit_gevrey_majorant import GevreyMajorantEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(spec):
    return gevrey_majorant_family(
        name="GevreyChk",
        grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "gevrey_instance",
        spec=lambda pt: spec,
    )


def _emit(fam):
    return emit(
        certify(fam),
        LeanProfile(namespace=("NS", "Gevrey")),
        [GevreyMajorantEmitter()],
        ValidationReport(checks=(("spot", True),)),
    )


def test_kind():
    assert _family(("calculus",)).kind == "gevrey_majorant"


def test_budget_certifies_exactly():
    # A=2, Rc=1, R=8: 2*2*(1+1) = 8 <= 8 (tight budget)
    cert = certify(_family(("budget", 2, 1, 8))).instances[0].payload
    assert cert.mode == "budget"
    assert (cert.A, cert.Rc, cert.R) == (2, 1, 8)


def test_polynomial_radius_certifies():
    cert = certify(_family(("polynomial_radius", 2, 1))).instances[0].payload
    assert cert.mode == "polynomial_radius"
    assert (cert.P, cert.c) == (2, 1)


def test_calculus_emits_full_chain():
    text = _emit(_family(("calculus",))).files["GevreyChk.lean"]
    for nm in (
        "le_choose_of_interior", "choose_le_shifted", "sum_inv_choose_le_three",
        "shifted_factorial_kernel_le", "majorant_shift_le", "majorant_convolution",
        "geometric_tail_le_two_mul", "majorant_coefficient_term",
        "triangular_inverse_majorant", "triangular_inverse_polynomial_radius",
    ):
        assert nm in text, f"missing {nm}"
    assert "github.com/openai/NavierStokesAndEuler" in text  # attribution


def test_budget_emits_specialization():
    text = _emit(_family(("budget", 2, 1, 8))).files["GevreyChk.lean"]
    assert "theorem gevrey_instance" in text
    assert "triangular_inverse_majorant (2) (1) (8)" in text
    assert "norm_num" in text
    # trust seam documented
    assert "HYPOTHESES" in text


def test_polynomial_radius_emits_specialization():
    text = _emit(_family(("polynomial_radius", 3, 2))).files["GevreyChk.lean"]
    assert "triangular_inverse_polynomial_radius (3)" in text
    assert "2 * 2 + 2" in text


def test_lean_text_clean():
    check_lean_text(_emit(_family(("budget", 2, 1, 8))).files["GevreyChk.lean"])
    check_lean_text(_emit(_family(("calculus",))).files["GevreyChk.lean"])


def test_byte_stability():
    a = _emit(_family(("budget", 3, sp.Rational(1, 2), 9))).files["GevreyChk.lean"]
    b = _emit(_family(("budget", 3, sp.Rational(1, 2), 9))).files["GevreyChk.lean"]
    assert a == b


def test_negative_control_budget_violated():
    # 2*2*(1+1) = 8 > 7 — refuse
    with pytest.raises(ValueError, match="radius budget"):
        gevrey_majorant_certificate("budget", A=2, Rc=1, R=7)


def test_negative_control_A_below_one():
    with pytest.raises(ValueError, match="1 ≤ A"):
        gevrey_majorant_certificate("budget", A=sp.Rational(1, 2), Rc=0, R=10)


def test_negative_control_negative_Rc():
    with pytest.raises(ValueError, match="0 ≤ Rc"):
        gevrey_majorant_certificate("budget", A=1, Rc=-1, R=10)


def test_negative_control_P_below_two():
    with pytest.raises(ValueError, match="2 ≤ P"):
        gevrey_majorant_certificate("polynomial_radius", P=sp.Rational(3, 2), c=1)


def test_negative_control_bad_mode():
    with pytest.raises(ValueError, match="mode"):
        gevrey_majorant_certificate("nonsense")
