"""Infeasibility / Nullstellensatz-refutation emitter — pipeline + controls.

Proves a polynomial system has NO solution (a certificate of non-existence) from
a computed refutation `1 = Σ λ_j g_j`.  A positive family certifies and emits
non-vacuous Lean concluding `False`; a satisfiable system, and one infeasible
only over ℝ (needs SOS), are both REFUSED.  Kernel verdict is CI-only.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, InfeasibilityEmitter, LeanProfile,
    ValidationReport, certify, check_lean_text, emit, find_refutation,
    infeasible_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _emit_clean(fam):
    res = emit(certify(fam), LeanProfile(namespace=("T",)),
               [InfeasibilityEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    return res, body


def test_infeasible_positive_and_controls():
    x, y = sp.symbols("x y")
    # {x = 0, x - 1 = 0} is inconsistent -> refuted by 1 = 1*x + (-1)*(x-1)
    fam = infeasible_family("Inf", (x, y), GridSpec([("j", [0])]), lambda pt: "inf",
                            lambda pt: [x, x - 1])
    res, body = _emit_clean(fam)
    assert res.n_theorems == 1
    assert all(t in body for t in ("linear_combination", "absurd", "norm_num"))
    assert "False" in body  # a refutation: concludes False, not an (in)equality
    # satisfiable system -> no refutation -> refused
    sat = infeasible_family("Sat", (x, y), GridSpec([("j", [0])]), lambda pt: "sat",
                            lambda pt: [x - y])
    with pytest.raises(CertificationError):
        certify(sat)


def test_infeasible_real_only_is_refused():
    x, y = sp.symbols("x y")
    # x^2 + 1 = 0 is infeasible over R but has complex roots -> NOT ideal-trivial;
    # the ideal-theoretic refutation must decline (that is the SOS case).
    real_only = infeasible_family("R", (x, y), GridSpec([("j", [0])]),
                                  lambda pt: "r", lambda pt: [x ** 2 + 1])
    with pytest.raises(CertificationError):
        certify(real_only)


def test_infeasible_rational_cofactors():
    x, y = sp.symbols("x y")
    # {x^2 - 1 = 0, x - 2 = 0}: no common root; cofactors are rational (deg 1)
    fam = infeasible_family("Q", (x, y), GridSpec([("j", [0])]), lambda pt: "q",
                            lambda pt: [x ** 2 - 1, x - 2])
    res, body = _emit_clean(fam)
    assert res.n_theorems == 1 and "linear_combination" in body


def test_find_refutation_direct():
    x, y = sp.symbols("x y")
    lam, deg = find_refutation([x, x - 1], [x, y])
    assert lam is not None
    assert sp.expand(sum(l * g for l, g in zip(lam, [x, x - 1])) - 1) == 0
    # satisfiable -> None
    lam2, _ = find_refutation([x - y], [x, y])
    assert lam2 is None


def test_infeasible_byte_stability():
    x, y = sp.symbols("x y")

    def build():
        fam = infeasible_family("Inf", (x, y), GridSpec([("j", [0])]),
                                lambda pt: "inf", lambda pt: [x, x - 1])
        return emit(certify(fam), LeanProfile(namespace=("T",)),
                    [InfeasibilityEmitter()], GREEN)
    assert build().input_hash == build().input_hash
