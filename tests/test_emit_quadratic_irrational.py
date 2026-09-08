"""QuadraticIrrational emitter (NS/Euler DiophantineGraph shape): certify → emit
→ lint.  Positive control d=2 is the manuscript's ℤ[√2]; negative controls are
d ≤ 0 and perfect squares.  The Lean kernel is the arbiter (CI `lake build`)."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    quadratic_irrational_certificate,
    quadratic_irrational_family,
)
from telperion.emit_quadratic_irrational import QuadraticIrrationalEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(d=2):
    return quadratic_irrational_family(
        name="DioGraph",
        grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "sqrt_two_separation",
        spec=lambda pt: d,
    )


def _emit(fam):
    return emit(
        certify(fam),
        LeanProfile(namespace=("NS", "Diophantine")),
        [QuadraticIrrationalEmitter()],
        ValidationReport(checks=(("spot", True),)),
    )


def test_kind():
    assert _family().kind == "quadratic_irrational"


def test_certifies_sqrt_two():
    cf = certify(_family(2))
    assert cf.instances[0].payload.d == 2


def test_certifies_nonsquare():
    for d in (2, 3, 5, 6, 7, 10):
        assert quadratic_irrational_certificate(d).d == d


def test_emits_identity_and_norm_lower():
    text = _emit(_family(2)).files["DioGraph.lean"]
    assert "theorem sqrt_two_separation_id" in text
    assert "theorem sqrt_two_separation_norm_lower" in text
    assert "Real.sqrt 2" in text
    assert "Real.sq_sqrt" in text
    assert "Int.one_le_abs" in text
    assert "p^2 - 2 * q^2" in text
    assert text.count("theorem sqrt_two_separation") == 2


def test_honesty_seam_norm_nonzero_is_hypothesis():
    text = _emit(_family(3)).files["DioGraph.lean"]
    # the non-vanishing of the norm is a HYPOTHESIS, not proved here
    assert "(hnz : p^2 - 3 * q^2 ≠ 0)" in text


def test_lean_text_clean():
    check_lean_text(_emit(_family(2)).files["DioGraph.lean"])
    check_lean_text(_emit(_family(7)).files["DioGraph.lean"])


def test_byte_stability():
    assert _emit(_family(5)).files["DioGraph.lean"] == _emit(_family(5)).files["DioGraph.lean"]


def test_negative_control_perfect_square_refused():
    for d in (1, 4, 9, 16, 25):
        with pytest.raises(ValueError, match="perfect square"):
            quadratic_irrational_certificate(d)


def test_negative_control_nonpositive_refused():
    for d in (0, -2):
        with pytest.raises(ValueError, match="d > 0"):
            quadratic_irrational_certificate(d)
