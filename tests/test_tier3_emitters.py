"""Tier-3 literature-derived emitters (2026-08-20): pipeline + negative controls.

Two more certificate families flowing through the single certify->emit->freeze
API:

  * Handelman         — `0 ≤ p` on a polytope `{ℓ_i ≥ 0}` via a nonnegative
                        combination of PRODUCTS of the constraints.
  * Nullstellensatz   — `p = 0` on a variety `V(g_1,…,g_m)` via ideal-membership
                        cofactors `p = Σ h_i g_i` (an EQUALITY, a new class).

For each: a positive family certifies and emits soundness-lint-clean, non-vacuous
Lean, and an out-of-class family is REFUSED at certification.  Kernel verdict is
CI-only.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, HandelmanEmitter, LeanProfile,
    NullstellensatzEmitter, ValidationReport, certify, check_lean_text, emit,
    handelman_family, nullstellensatz_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _emit_clean(fam, emitter):
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [emitter], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    return res, body


# --- Handelman --------------------------------------------------------------

def test_handelman_positive_and_refusal():
    x = sp.Symbol("x")
    # 0 <= 1 - x^2 on {1-x >= 0, 1+x >= 0} via the product (1-x)(1+x)
    fam = handelman_family("H", (x,), GridSpec([("j", [0])]), lambda pt: "h",
                           lambda pt: (1 - x ** 2,
                                       [(1 - x, "h1"), (1 + x, "h2")],
                                       [(1, (1, 1))]))
    res, body = _emit_clean(fam, HandelmanEmitter())
    assert res.n_theorems == 1
    assert all(t in body for t in ("mul_nonneg", "pow_nonneg", "ring", "linarith"))
    # a combination that does not reconstruct p is refused
    bad = handelman_family("Bad", (x,), GridSpec([("j", [0])]), lambda pt: "bad",
                           lambda pt: (1 - x ** 2, [(1 - x, "h1")], [(1, (1,))]))
    with pytest.raises(CertificationError):
        certify(bad)


def test_handelman_negative_coefficient_refused():
    x = sp.Symbol("x")
    bad = handelman_family("Neg", (x,), GridSpec([("j", [0])]), lambda pt: "neg",
                           lambda pt: (-(x ** 2), [(x, "hx")], [(-1, (2,))]))
    with pytest.raises(CertificationError):
        certify(bad)


# --- Nullstellensatz --------------------------------------------------------

def test_nullstellensatz_positive_and_refusal():
    x, y = sp.symbols("x y")
    # x^3 - y^3 = 0 on V(x - y); cofactor x^2 + xy + y^2 computed by reduction
    fam = nullstellensatz_family("N", (x, y), GridSpec([("j", [0])]),
                                 lambda pt: "nss",
                                 lambda pt: (x ** 3 - y ** 3, [x - y]))
    res, body = _emit_clean(fam, NullstellensatzEmitter())
    assert res.n_theorems == 1 and "linear_combination" in body
    assert "= 0" in body  # an equality on the variety, not an inequality
    # x^2 + 1 is not in <x - y> -> refused
    bad = nullstellensatz_family("Bad", (x, y), GridSpec([("j", [0])]),
                                 lambda pt: "bad",
                                 lambda pt: (x ** 2 + 1, [x - y]))
    with pytest.raises(CertificationError):
        certify(bad)


def test_nullstellensatz_multi_generator():
    x, y = sp.symbols("x y")
    fam = nullstellensatz_family("M", (x, y), GridSpec([("j", [0])]),
                                 lambda pt: "mss",
                                 lambda pt: (x * y, [x, y]))
    res, body = _emit_clean(fam, NullstellensatzEmitter())
    assert res.n_theorems == 1 and body.count("hg") >= 2  # two hypotheses used


# --- byte-stability ---------------------------------------------------------

def test_tier3_byte_stability():
    x, y = sp.symbols("x y")

    def build():
        fam = nullstellensatz_family("N", (x, y), GridSpec([("j", [0])]),
                                     lambda pt: "nss",
                                     lambda pt: (x ** 3 - y ** 3, [x - y]))
        return emit(certify(fam), LeanProfile(namespace=("T",)),
                    [NullstellensatzEmitter()], GREEN)
    assert build().input_hash == build().input_hash
