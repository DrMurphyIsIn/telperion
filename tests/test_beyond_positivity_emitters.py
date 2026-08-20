"""Beyond-positivity emitters (2026-08-20): equational consequence, SOS
Positivstellensatz refutation, and the Real Nullstellensatz.

Together with Nullstellensatz + Infeasibility, these move Telperion decisively
past 'certify 0 ≤ p': proving equalities-from-equalities, ℝ-unsatisfiability
(closing the real-only gap the ideal refutation leaves open), and real-variety
vanishing.  Each: a positive family certifies + emits non-vacuous lint-clean
Lean; an out-of-class family is refused.  Kernel verdict is CI-only.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, ConsequenceEmitter, GridSpec, LeanProfile,
    RealNullstellensatzEmitter, SOSRefutationEmitter, ValidationReport, certify,
    check_lean_text, consequence_family, emit, real_nullstellensatz_family,
    sos_refutation_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _emit_clean(fam, emitter):
    res = emit(certify(fam), LeanProfile(namespace=("T",)), [emitter], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    return res, body


# --- equational consequence -------------------------------------------------

def test_consequence_positive_and_refusal():
    x, y = sp.symbols("x y")
    fam = consequence_family("C", (x, y), GridSpec([("j", [0])]), lambda pt: "cube",
                             lambda pt: (x ** 3, y ** 3, [(x, y, "h")]))
    res, body = _emit_clean(fam, ConsequenceEmitter())
    assert res.n_theorems == 1 and "linear_combination" in body
    assert "x ^ 3 = y ^ 3" in body  # the consequence, not a hypothesis
    bad = consequence_family("Bad", (x, y), GridSpec([("j", [0])]), lambda pt: "bad",
                             lambda pt: (x ** 2, 2 * y, [(x, y, "h")]))
    with pytest.raises(CertificationError):
        certify(bad)


# --- SOS Positivstellensatz refutation (closes the ℝ-only gap) --------------

def test_sos_refutation_real_only_infeasible():
    x = sp.Symbol("x")
    # x^2 + 1 = 0 is infeasible only over ℝ (complex roots) -> needs SOS, not
    # the ideal refutation.  σ₀ = x², λ = -1.
    fam = sos_refutation_family("S", (x,), GridSpec([("j", [0])]), lambda pt: "s",
                                lambda pt: ([(1, x)], [], [(x ** 2 + 1, -1, "he1")]))
    res, body = _emit_clean(fam, SOSRefutationEmitter())
    assert res.n_theorems == 1
    assert all(t in body for t in ("positivity", "linear_combination", "linarith"))
    assert "False" in body
    # a certificate that does not equal -1 is refused
    bad = sos_refutation_family("Bad", (x,), GridSpec([("j", [0])]), lambda pt: "bad",
                                lambda pt: ([(1, x)], [], [(x ** 2 + 1, 1, "he1")]))
    with pytest.raises(CertificationError):
        certify(bad)


def test_sos_refutation_with_inequality():
    x = sp.Symbol("x")
    # {x >= 0, x + 1 = 0}: unsat.  -1 = 1*x + (-1)*(x+1).
    fam = sos_refutation_family(
        "I", (x,), GridSpec([("j", [0])]), lambda pt: "i",
        lambda pt: ([], [(x, [(1, sp.Integer(1))], "hg1")], [(x + 1, -1, "he1")]))
    res, body = _emit_clean(fam, SOSRefutationEmitter())
    assert res.n_theorems == 1 and "mul_nonneg" in body


# --- Real Nullstellensatz ---------------------------------------------------

def test_real_nullstellensatz_positive_and_refusal():
    x, y = sp.symbols("x y")
    # x = 0 on the real variety of x^2 + y^2 (the origin), via s = y^2
    fam = real_nullstellensatz_family(
        "R", (x, y), GridSpec([("j", [0])]), lambda pt: "r",
        lambda pt: (x, 1, [(1, y)], [x ** 2 + y ** 2]))
    res, body = _emit_clean(fam, RealNullstellensatzEmitter())
    assert res.n_theorems == 1
    assert "pow_eq_zero_iff" in body and "x = 0" in body
    # without the SOS s, x^2 is not in <x^2+y^2> -> refused
    bad = real_nullstellensatz_family(
        "Bad", (x, y), GridSpec([("j", [0])]), lambda pt: "bad",
        lambda pt: (x, 1, [], [x ** 2 + y ** 2]))
    with pytest.raises(CertificationError):
        certify(bad)


def test_beyond_positivity_byte_stability():
    x, y = sp.symbols("x y")

    def build():
        fam = consequence_family("C", (x, y), GridSpec([("j", [0])]),
                                 lambda pt: "cube",
                                 lambda pt: (x ** 3, y ** 3, [(x, y, "h")]))
        return emit(certify(fam), LeanProfile(namespace=("T",)),
                    [ConsequenceEmitter()], GREEN)
    assert build().input_hash == build().input_hash
