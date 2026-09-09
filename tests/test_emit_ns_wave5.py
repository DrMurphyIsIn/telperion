"""NS/Euler wave-5 emitters (comparability_envelope, discrete_moment,
poly_exp_absorption): certify → emit → lint + refusal negative controls."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    comparability_envelope_family,
    discrete_moment_family,
    poly_exp_absorption_certificate, poly_exp_absorption_family,
)
from telperion.emit_comparability_envelope import ComparabilityEnvelopeEmitter  # noqa: E402
from telperion.emit_discrete_moment import DiscreteMomentEmitter  # noqa: E402
from telperion.emit_poly_exp_absorption import PolyExpAbsorptionEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text

_VR = ValidationReport(checks=(("s", True),))
_G = GridSpec([("k", [0])])


def _emit(fam, em, ns):
    return emit(certify(fam), LeanProfile(namespace=("NS", ns)), [em], _VR)


def test_comparability_envelope_atoms():
    fam = comparability_envelope_family(name="CmpChk", grid=_G, lean_name=lambda pt: "c")
    assert fam.kind == "comparability_envelope"
    res = _emit(fam, ComparabilityEnvelopeEmitter(), "Cmp")
    text = res.files["CmpChk.lean"]
    for nm in ("comparable_rpow", "sqrt_shift_lipschitz",
               "reciprocal_quadratic_difference", "abs_div_le_of_one_le"):
        assert f"theorem {nm}" in text
    assert res.n_theorems == 4
    assert "github.com/openai/NavierStokesAndEuler" in text
    check_lean_text(text)


def test_discrete_moment_atoms():
    fam = discrete_moment_family(name="DMChk", grid=_G, lean_name=lambda pt: "d")
    assert fam.kind == "discrete_moment"
    res = _emit(fam, DiscreteMomentEmitter(), "DM")
    text = res.files["DMChk.lean"]
    for nm in ("simplex_second_moment", "reciprocal_square_telescope",
               "sum_squareDecay_le_two", "squareDecay_convolution_le"):
        assert nm in text
    assert res.n_theorems == 8
    check_lean_text(text)


def test_poly_exp_absorption_source_constant():
    # m = 2 reproduces the source's 64
    cert = poly_exp_absorption_certificate(2)
    assert cert.K == 64
    assert poly_exp_absorption_certificate(3).K == 12 ** 3


def test_poly_exp_absorption_emits():
    fam = poly_exp_absorption_family(
        name="PEChk", grid=GridSpec([("k", [0, 1])]),
        lean_name=lambda pt: f"absorb_{pt['k']}",
        spec=lambda pt: [2, 3][pt["k"]])
    text = _emit(fam, PolyExpAbsorptionEmitter(), "PE").files["PEChk.lean"]
    assert "theorem absorb_0" in text and "theorem absorb_1" in text
    assert "(64)" in text and "(1728)" in text
    assert "Real.add_one_le_exp" in text
    check_lean_text(text)


def test_poly_exp_absorption_refusal():
    with pytest.raises(ValueError, match="m ≥ 1"):
        poly_exp_absorption_certificate(0)


def test_byte_stability():
    fam = poly_exp_absorption_family(
        name="PEChk", grid=_G, lean_name=lambda pt: "a", spec=lambda pt: 2)
    a = _emit(fam, PolyExpAbsorptionEmitter(), "PE").files["PEChk.lean"]
    b = _emit(fam, PolyExpAbsorptionEmitter(), "PE").files["PEChk.lean"]
    assert a == b
