"""LogEpsOptimize emitter: certify → emit → lint + exponent-range refusals."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    log_eps_optimize_certificate, log_eps_optimize_family,
)
from telperion.emit_log_eps_optimize import LogEpsOptimizeEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(theta):
    return log_eps_optimize_family(
        name="LogEpsChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "cutoff_optimize", spec=lambda pt: theta)


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "LogEps")),
                [LogEpsOptimizeEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family(sp.Rational(1, 4)).kind == "log_eps_optimize"


def test_certifies_quarter_and_general():
    cert = certify(_family(sp.Rational(1, 4))).instances[0].payload
    assert (cert.theta, cert.m) == (sp.Rational(1, 4), 4)
    cert2 = log_eps_optimize_certificate(sp.Rational(2, 7))
    assert cert2.m == sp.Rational(7, 2)
    assert cert2.m * cert2.theta == 1


def test_emits_source_shape_at_quarter():
    text = _emit(_family(sp.Rational(1, 4))).files["LogEpsChk.lean"]
    assert "theorem cutoff_optimize" in text
    assert "Real.log (Real.exp 1 + H)" in text
    assert "Real.rpow_def_of_pos" in text
    assert "HYPOTHESIS" in text


def test_emits_general_theta():
    text = _emit(_family(sp.Rational(2, 7))).files["LogEpsChk.lean"]
    assert "(7 / 2)" in text  # m
    assert "(2 / 7)" in text  # theta


def test_lean_text_clean():
    check_lean_text(_emit(_family(sp.Rational(1, 4))).files["LogEpsChk.lean"])
    check_lean_text(_emit(_family(sp.Rational(1, 2))).files["LogEpsChk.lean"])


def test_byte_stability():
    assert _emit(_family(sp.Rational(1, 3))).files["LogEpsChk.lean"] == \
        _emit(_family(sp.Rational(1, 3))).files["LogEpsChk.lean"]


def test_negative_control_theta_out_of_range():
    for bad in (0, -1, sp.Rational(3, 2)):
        with pytest.raises(ValueError, match="0 < θ ≤ 1"):
            log_eps_optimize_certificate(bad)
