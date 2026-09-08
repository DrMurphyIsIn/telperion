"""CoefficientMass emitter: certify → emit → lint + mass exactness + refusals."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    coefficient_mass_certificate, coefficient_mass_family,
)
from telperion.emit_coefficient_mass import CoefficientMassEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(spec):
    return coefficient_mass_family(
        name="MassChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "mass_instance", spec=lambda pt: spec)


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "Mass")),
                [CoefficientMassEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family(("generic",)).kind == "coefficient_mass"


def test_scalar_mass_exact():
    # p = 1 - (3/2)x + 2x^2, T = 2: M = 1 + 3/2 + 2 = 9/2
    cert = certify(_family(("scalar", (1, sp.Rational(-3, 2), 2), 2))).instances[0].payload
    assert cert.M == sp.Rational(9, 2)


def test_generic_emits_polynomial_atom():
    text = _emit(_family(("generic",))).files["MassChk.lean"]
    assert "theorem polynomial_eval_bound" in text
    assert "coefficientMass" in text
    assert "github.com/openai/NavierStokesAndEuler" in text


def test_scalar_emits_sign_aware_discharge():
    text = _emit(_family(("scalar", (1, sp.Rational(-3, 2), 2), 2))).files["MassChk.lean"]
    assert "theorem mass_instance" in text
    assert "abs_of_nonpos" in text  # the negative coefficient
    assert "abs_of_nonneg" in text  # the positive ones
    assert "linarith" in text
    assert "((9 / 2)) * (2) ^ 2" in text
    assert ", hA1" in text  # linarith hints are comma-separated (not application)


def test_lean_text_clean():
    check_lean_text(
        _emit(_family(("scalar", (1, sp.Rational(-3, 2), 2), 2))).files["MassChk.lean"])
    check_lean_text(_emit(_family(("scalar", (0, 1), 1))).files["MassChk.lean"])  # x itself


def test_byte_stability():
    s = ("scalar", (2, -1, 0, sp.Rational(1, 3)), sp.Rational(3, 2))
    assert _emit(_family(s)).files["MassChk.lean"] == _emit(_family(s)).files["MassChk.lean"]


def test_negative_control_T_below_one():
    with pytest.raises(ValueError, match="1 ≤ T"):
        coefficient_mass_certificate("scalar", coeffs=(1, 1), T=sp.Rational(1, 2))


def test_negative_control_zero_leading():
    with pytest.raises(ValueError, match="leading"):
        coefficient_mass_certificate("scalar", coeffs=(1, 2, 0), T=2)


def test_negative_control_constant_refused():
    with pytest.raises(ValueError, match="degree"):
        coefficient_mass_certificate("scalar", coeffs=(5,), T=2)
