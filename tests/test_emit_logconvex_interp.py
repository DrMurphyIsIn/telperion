"""LogConvexInterp emitter: certify → emit → lint + ordering refusals."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, certify, emit,
    logconvex_interp_certificate, logconvex_interp_family,
)
from telperion.emit_logconvex_interp import LogConvexInterpEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text


def _family(spec):
    return logconvex_interp_family(
        name="LogCvxChk", grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "between_instance", spec=lambda pt: spec)


def _emit(fam):
    return emit(certify(fam), LeanProfile(namespace=("NS", "LogCvx")),
                [LogConvexInterpEmitter()], ValidationReport(checks=(("s", True),)))


def test_kind():
    assert _family(("calculus",)).kind == "logconvex_interp"


def test_calculus_emits_chain():
    text = _emit(_family(("calculus",))).files["LogCvxChk.lean"]
    for nm in ("logconvex_cross", "logconvex_pair", "logconvex_between"):
        assert f"theorem {nm}" in text
    assert "github.com/openai/NavierStokesAndEuler" in text


def test_between_certifies_and_emits():
    cert = certify(_family(("between", 2, 3, 7))).instances[0].payload
    assert (cert.s, cert.a, cert.b) == (2, 3, 7)
    text = _emit(_family(("between", 2, 3, 7))).files["LogCvxChk.lean"]
    assert "theorem between_instance" in text
    assert "x 3 * x 7 ≤ x 2 * x 8" in text  # a+b-s = 8
    assert "logconvex_between x hx hc 2 3 7" in text


def test_lean_text_clean():
    check_lean_text(_emit(_family(("between", 0, 1, 4))).files["LogCvxChk.lean"])


def test_byte_stability():
    assert _emit(_family(("between", 1, 2, 5))).files["LogCvxChk.lean"] == \
        _emit(_family(("between", 1, 2, 5))).files["LogCvxChk.lean"]


def test_negative_control_bad_ordering():
    with pytest.raises(ValueError, match="s ≤ a ≤ b"):
        logconvex_interp_certificate("between", s=3, a=2, b=5)  # s > a
    with pytest.raises(ValueError, match="s ≤ a ≤ b"):
        logconvex_interp_certificate("between", s=1, a=5, b=2)  # a > b
