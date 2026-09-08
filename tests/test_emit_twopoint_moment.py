"""TwoPointMoment emitter: certify → emit → lint + margin refusals."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    twopoint_moment_certificate, twopoint_moment_family,
)
from telperion.emit_twopoint_moment import TwoPointMomentEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(spec):
    return twopoint_moment_family(
        name="TwoPtChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "twopt_instance", spec=lambda pt: spec)


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "TwoPt")),
                [TwoPointMomentEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family(("calculus",)).kind == "twopoint_moment"


def test_instance_margin_exact():
    # p1=1, p2=2, m=1: margin = 1 + 2 - 2 = 1 > 0
    cert = certify(_family(("instance", 1, 2, 1, sp.Rational(1, 4)))).instances[0].payload
    assert cert.margin == 1


def test_calculus_emits_full_chain():
    text = _emit(_family(("calculus",))).files["TwoPtChk.lean"]
    for nm in ("structure TwoPoint", "symmetricPair_variance", "oneSidedPair_probability",
               "exists_projected_twoPoint"):
        assert nm in text
    assert "github.com/openai/NavierStokesAndEuler" in text


def test_instance_emits_specialization():
    text = _emit(_family(("instance", 1, 2, 1, sp.Rational(1, 4)))).files["TwoPtChk.lean"]
    assert "theorem twopt_instance" in text
    assert "exists_projected_twoPoint (1) (2) (1) ((1 / 4))" in text
    assert "Feasibility only" in text  # the honesty caveat


def test_p2_zero_instance_allowed():
    # symmetric-witness branch: p2=0, needs 2 < p1
    cert = twopoint_moment_certificate("instance", p1=3, p2=0, m=5, V=2)
    assert cert.margin == 1


def test_lean_text_clean():
    check_lean_text(
        _emit(_family(("instance", 1, 2, 1, sp.Rational(1, 4)))).files["TwoPtChk.lean"])


def test_byte_stability():
    s = ("instance", 3, sp.Rational(-1, 2), -3, 1)  # 3 + 3/2 - 2 = 5/2 > 0
    assert _emit(_family(s)).files["TwoPtChk.lean"] == _emit(_family(s)).files["TwoPtChk.lean"]


def test_negative_control_margin_violated():
    with pytest.raises(ValueError, match="margin"):
        twopoint_moment_certificate("instance", p1=1, p2=1, m=1, V=0)  # 1+1 = 2, not > 2


def test_negative_control_negative_variance():
    with pytest.raises(ValueError, match="0 ≤ V"):
        twopoint_moment_certificate("instance", p1=5, p2=0, m=0, V=-1)
