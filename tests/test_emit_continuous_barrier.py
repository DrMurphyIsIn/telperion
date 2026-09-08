"""ContinuousBarrier emitter: certify → emit → lint + budget refusals."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    continuous_barrier_certificate, continuous_barrier_family,
)
from telperion.emit_continuous_barrier import ContinuousBarrierEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(spec):
    return continuous_barrier_family(
        name="BarrierChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "barrier_instance", spec=lambda pt: spec)


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "Barrier")),
                [ContinuousBarrierEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family(("generic",)).kind == "continuous_barrier"


def test_budget_certifies():
    cert = certify(_family(("budget", 2, 1, 3))).instances[0].payload  # 1*2 < 3
    assert (cert.T, cert.B, cert.a) == (2, 1, 3)


def test_generic_emits_atom():
    text = _emit(_family(("generic",))).files["BarrierChk.lean"]
    assert "theorem continuous_barrier" in text
    assert "IsCompact" in text and "intermediate_value_Icc" in text
    assert "github.com/openai/NavierStokesAndEuler" in text


def test_budget_emits_specialization():
    text = _emit(_family(("budget", 2, 1, 3))).files["BarrierChk.lean"]
    assert "theorem barrier_instance" in text
    assert "continuous_barrier f (2) (1) (3)" in text
    assert "HYPOTHESES" in text


def test_lean_text_clean():
    check_lean_text(_emit(_family(("budget", 2, 1, 3))).files["BarrierChk.lean"])


def test_byte_stability():
    a = _emit(_family(("budget", 1, sp.Rational(1, 2), 1))).files["BarrierChk.lean"]
    b = _emit(_family(("budget", 1, sp.Rational(1, 2), 1))).files["BarrierChk.lean"]
    assert a == b


def test_negative_control_budget_violated():
    with pytest.raises(ValueError, match="barrier budget"):
        continuous_barrier_certificate("budget", T=3, B=1, a=3)  # 1*3 = 3, not < 3


def test_negative_control_nonpositive_barrier():
    with pytest.raises(ValueError, match="0 < a"):
        continuous_barrier_certificate("budget", T=1, B=0, a=0)


def test_negative_control_negative_T():
    with pytest.raises(ValueError, match="0 ≤ T"):
        continuous_barrier_certificate("budget", T=-1, B=0, a=1)
