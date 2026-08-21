"""Runway batch A: Bernstein interval positivity + Real-Nullstellensatz finder.

Bernstein needs no SDP (exact linear solve + degree elevation, sympy-only); the
Real-Nullstellensatz finder is SDP-backed (cvxpy-guarded).  Both feed
kernel-checkable emitters; the finders are untrusted (the certifier re-verifies),
so a miss is a refusal, never a wrong theorem.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BernsteinEmitter, CertificationError, GridSpec, LeanProfile, ValidationReport,
    bernstein_family, certify, check_lean_text, check_nonvacuous, emit,
    find_bernstein_certificate,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _emit_clean(fam, emitter):
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [emitter], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    check_nonvacuous(body)
    return res, body


# --- Bernstein --------------------------------------------------------------

def test_bernstein_positive_and_refusal():
    x = sp.Symbol("x")
    fam = bernstein_family("B", (x,), GridSpec([("j", [0])]), lambda pt: "b",
                           lambda pt: (1 - x ** 2, -1, 1))
    res, body = _emit_clean(fam, BernsteinEmitter())
    assert res.n_theorems == 1
    assert all(t in body for t in ("mul_nonneg", "pow_nonneg", "ring", "linarith"))
    # x on [-1, 1] takes negative values -> refused
    bad = bernstein_family("Bad", (x,), GridSpec([("j", [0])]), lambda pt: "bad",
                           lambda pt: (x, -1, 1))
    with pytest.raises(CertificationError):
        certify(bad)


def test_bernstein_degree_elevation():
    x = sp.Symbol("x")
    # x^2 - x + 1 is strictly positive on [0,1]; needs an elevated degree
    found = find_bernstein_certificate(x ** 2 - x + 1, 0, 1, x, n_max=8)
    assert found is not None
    n, betas = found
    assert n >= 2 and all(b >= 0 for b in betas)


def test_bernstein_touching_zero_refused():
    x = sp.Symbol("x")
    # (x-1/2)^2 touches zero at an interior point -> not strictly positive ->
    # Bernstein coefficients never all nonneg -> None
    assert find_bernstein_certificate((x - sp.Rational(1, 2)) ** 2, 0, 1, x,
                                      n_max=6) is None


def test_bernstein_byte_stability():
    x = sp.Symbol("x")

    def build():
        fam = bernstein_family("B", (x,), GridSpec([("j", [0])]), lambda pt: "b",
                               lambda pt: (2 - x, 0, 1))
        return emit(certify(fam), LeanProfile(namespace=("T",)),
                    [BernsteinEmitter()], GREEN)
    assert build().input_hash == build().input_hash


# --- Real-Nullstellensatz finder (SDP) --------------------------------------

def test_real_nullstellensatz_finder():
    pytest.importorskip("cvxpy")
    from telperion import find_real_nullstellensatz
    x, y = sp.symbols("x y")
    # x = 0 and y = 0 on the real variety of x^2 + y^2 (the origin)
    for p, expect in [(x, "y"), (y, "x")]:
        r = find_real_nullstellensatz(p, [x ** 2 + y ** 2], (x, y))
        assert r is not None
        m, sos = r
        s = sum(c * b ** 2 for c, b in sos)
        _, rem = sp.reduced(sp.expand(p ** (2 * m) + s), [x ** 2 + y ** 2], x, y)
        assert sp.expand(rem) == 0


def test_real_nullstellensatz_finder_mode_emits():
    pytest.importorskip("cvxpy")
    from telperion import RealNullstellensatzEmitter, real_nullstellensatz_family
    x, y = sp.symbols("x y")
    fam = real_nullstellensatz_family("RF", (x, y), GridSpec([("j", [0])]),
                                      lambda pt: "rf",
                                      lambda pt: (x, None, None, [x ** 2 + y ** 2]))
    res = emit(certify(fam), LeanProfile(namespace=("T",)),
               [RealNullstellensatzEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1 and "pow_eq_zero_iff" in body
