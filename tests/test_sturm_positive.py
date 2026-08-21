"""Sturm strict-interval-positivity emitter: 0 < p(x) on [a,b].

Sturm sequence = exact root-exclusion oracle; strict positivity proven via a
Bernstein certificate for p - gamma >= 0 plus 0 < gamma.  A polynomial with a
root in the interval (or negative there) is refused.  sympy-only (no SDP).
"""
import sys
from pathlib import Path
import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, SturmPositiveEmitter, ValidationReport,
    certify, check_lean_text, check_nonvacuous, emit, sturm_positive_family,
)

GREEN = ValidationReport(checks=(("spot", True),))
x = sp.Symbol("x")


def _emit(fam):
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [SturmPositiveEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    check_nonvacuous(body)
    return res, body


def test_sturm_positive_strict():
    fam = sturm_positive_family("S", (x,), GridSpec([("j", [0])]), lambda pt: "s",
                                lambda pt: (x ** 2 + 1, -2, 2))
    res, body = _emit(fam)
    assert res.n_theorems == 1
    # STRICT positivity (0 < p), and the Sturm/Bernstein tactics
    assert "(0:ℝ) < 1 + x ^ 2" in body
    assert all(t in body for t in ("mul_nonneg", "pow_nonneg", "ring", "linarith", "norm_num"))


def test_sturm_refuses_root_in_interval():
    # (x-3)^2 has a root at 3 in [2,4] -> not strictly positive -> refused
    with pytest.raises(CertificationError):
        certify(sturm_positive_family("B", (x,), GridSpec([("j", [0])]), lambda pt: "b",
                                      lambda pt: ((x - 3) ** 2, 2, 4)))


def test_sturm_refuses_negative():
    # x - 5 < 0 on [0,3]
    with pytest.raises(CertificationError):
        certify(sturm_positive_family("N", (x,), GridSpec([("j", [0])]), lambda pt: "n",
                                      lambda pt: (x - 5, 0, 3)))


def test_sturm_byte_stability():
    def build():
        fam = sturm_positive_family("S", (x,), GridSpec([("j", [0])]), lambda pt: "s",
                                    lambda pt: (x ** 2 - 3 * x + 3, 0, 3))
        return emit(certify(fam), LeanProfile(namespace=("T",)), [SturmPositiveEmitter()], GREEN)
    assert build().input_hash == build().input_hash
