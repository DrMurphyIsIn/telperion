"""MultilinearPerturbation emitter: certify → emit → lint + refusals."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    multilinear_perturbation_certificate, multilinear_perturbation_family,
)
from telperion.emit_multilinear_perturbation import (  # noqa: E402
    MultilinearPerturbationEmitter,
)
from telperion.lean_lint import check_lean_text


def _family(bounds):
    return multilinear_perturbation_family(
        name="MultiChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "prod_perturb", spec=lambda pt: bounds)


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "Multi")),
                [MultilinearPerturbationEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family((1, 2)).kind == "multilinear_perturbation"


def test_envelope_exact_arity2_matches_source():
    # source shape: |N| ≤ 1, |F0| ≤ M → C = 1 + M; here M=(M1,M2)=(3,1): C = 1 + 3 = 4
    cert = multilinear_perturbation_certificate((3, 1))
    assert cert.C == 4


def test_envelope_exact_arity3():
    # M = (2, 3, 1/2): C = 3·(1/2) + 2·(1/2) + 2·3 = 3/2 + 1 + 6 = 17/2
    cert = multilinear_perturbation_certificate((2, 3, sp.Rational(1, 2)))
    assert cert.C == sp.Rational(17, 2)


def test_emits_telescoping_and_chain():
    text = _emit(_family((2, 3))).files["MultiChk.lean"]
    assert "theorem prod_perturb" in text
    assert "congr 1" in text and "ring" in text  # the telescoping identity
    assert "mul_le_mul" in text
    assert "abs_add_le" in text
    assert "linarith" in text
    assert "HYPOTHESES" in text


def test_arity3_emits():
    text = _emit(_family((1, 1, 1))).files["MultiChk.lean"]
    assert "F3" in text and "G3" in text
    assert "(3) * η" in text  # C = 3 for all-ones arity 3


def test_lean_text_clean():
    check_lean_text(_emit(_family((2, 3))).files["MultiChk.lean"])
    check_lean_text(_emit(_family((1, 2, sp.Rational(1, 2), 1))).files["MultiChk.lean"])


def test_byte_stability():
    assert _emit(_family((2, 1))).files["MultiChk.lean"] == \
        _emit(_family((2, 1))).files["MultiChk.lean"]


def test_negative_control_arity_out_of_range():
    with pytest.raises(ValueError, match="arity"):
        multilinear_perturbation_certificate((1,))
    with pytest.raises(ValueError, match="arity"):
        multilinear_perturbation_certificate((1,) * 7)


def test_negative_control_negative_bound():
    with pytest.raises(ValueError, match="Mᵢ ≥ 0"):
        multilinear_perturbation_certificate((2, -1))
