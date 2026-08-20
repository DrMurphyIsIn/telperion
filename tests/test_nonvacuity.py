"""Non-vacuity gate — Telperion pointed at its own emitted output.

The kernel guarantees no FALSE theorem; it cannot catch a TRUE-but-vacuous one
(`X = X`, `0 ≤ 0`) — the defect lives in the statement, not the proof.  These
tests cover both layers: the structural reflexive-statement lint wired into
`emit()`, and the semantic certificate-sensitivity check wired into the identity
emitters.  The headline is `test_sensitivity_catches_the_wz_collapse`: the exact
bug class that shipped a vacuous `X = X` WZ theorem, now caught mechanically.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CustomAssemblyEmitter, GridSpec, InequalityFamily, LeanProfile,
    NonVacuityError, ValidationReport, assert_certificate_sensitive,
    certify, check_nonvacuous, emit,
)

GREEN = ValidationReport(checks=(("spot", True),))


# --- Layer 1: structural reflexive-statement lint ---------------------------

@pytest.mark.parametrize("body", [
    "theorem t : ∀ n k : ℝ, (2*k - n) * (1+k) = (2*k - n) * (1+k) := by ring\n",
    "theorem t : (0:ℝ) ≤ 0 := by norm_num\n",
    "theorem t : (12:ℤ) = 12 := by norm_num\n",
    "theorem t : ∀ x : ℝ, x + 1 ≤ x + 1 := by intro x; exact le_refl _\n",
])
def test_check_nonvacuous_rejects_reflexive(body):
    with pytest.raises(NonVacuityError):
        check_nonvacuous(body)


@pytest.mark.parametrize("body", [
    "theorem t : ∀ n k : ℝ, (2*k-n)*(1+k) - 5 = 0 := by intro n k; ring\n",
    "theorem t : ∀ x y : ℝ, 0 ≤ y → 0 ≤ x + y := by intro x y hy; linarith\n",
    "theorem t : (0:ℝ) ≤ 3 * (x - y)^2 + 2 := by positivity\n",
    "theorem t : ((3:ℚ)/2)^11 < ((621:ℚ)/64)^2 := by norm_num\n",
])
def test_check_nonvacuous_passes_genuine(body):
    check_nonvacuous(body)  # must not raise


def test_mixed_body_with_tight_ingredient_passes():
    # a substantive assembly (step + ∀-bound) with a tight-but-genuine base
    # ingredient (`1 ≤ 1` at a tie) is NOT wholly vacuous — must pass.  This is
    # the monotone-tail near-star shape; per-instance rigor is the semantic gate.
    body = (
        "theorem mt_step (t : ℝ) (ht : 0 ≤ t) : 0 ≤ (1) / ((2 + t)) := by positivity\n"
        "theorem mt_base : (1 : ℝ) ≤ 1 := by norm_num\n"
        "theorem mt_tail (b : ℕ → ℝ) (B : ℝ) (hbase : b 0 ≤ B) : "
        "∀ s, 0 ≤ s → b s ≤ B := by intro s hs; exact hbase\n"
    )
    check_nonvacuous(body)  # mixed body — not flagged


# --- Layer 1 wired into emit() ---------------------------------------------

def _vacuous_emitter():
    return CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": "theorem vac : (1:ℝ) = 1 := by norm_num\n"},
        branch_fills=lambda i: {}, theorems=1)


def _trivial_family():
    return InequalityFamily(
        name="V", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "v", target=lambda pt: sp.Integer(0))


def test_emit_refuses_vacuous_theorem():
    with pytest.raises(NonVacuityError):
        emit(certify(_trivial_family()), LeanProfile(namespace=("T",)),
             [_vacuous_emitter()], GREEN)


def test_emit_allow_reflexive_opts_out():
    # a family that INTENTIONALLY emits a reference identity declares it
    res = emit(certify(_trivial_family()),
               LeanProfile(namespace=("T",), allow_reflexive=True),
               [_vacuous_emitter()], GREEN)
    assert res.n_theorems == 1


# --- Layer 2: certificate sensitivity ---------------------------------------

def test_sensitivity_passes_load_bearing():
    x = sp.Symbol("x")
    # claim(c) = (c-2)*x : vanishes at the true c=2, broken by a perturbation
    idx = assert_certificate_sensitive(
        lambda c: (c - 2) * x, 2, [lambda c: c + 1], label="demo")
    assert idx == 0


def test_sensitivity_catches_the_wz_collapse():
    x = sp.Symbol("x")
    # The X=X class: a claim that IGNORES the certificate — 0 for every input,
    # so the kernel would verify a tautology.  This is exactly the WZ bug.
    with pytest.raises(NonVacuityError):
        assert_certificate_sensitive(
            lambda c: x - x, 2, [lambda c: c + 1, lambda c: c + 2], label="collapse")


def test_sensitivity_base_must_vanish():
    x = sp.Symbol("x")
    # a certifier bug: the "true" certificate does not close the identity
    with pytest.raises(ValueError):
        assert_certificate_sensitive(lambda c: c * x, 2, [lambda c: c + 1], label="bad")


# --- corpus drift-net: only the known-intentional families are reflexive ----

def test_frozen_corpus_has_no_wholly_vacuous_emission():
    """No frozen example is a wholly-vacuous body (every theorem reflexive).
    Some contain tight/reference ingredients, but none proves *nothing*; a NEW
    collapsed emission (the WZ X=X class) would fail this net."""
    root = Path(__file__).resolve().parents[1] / "examples"
    flagged = set()
    for f in root.glob("*/frozen/*.lean"):
        try:
            check_nonvacuous(f.read_text())
        except NonVacuityError:
            flagged.add(f.parent.parent.name)
    assert flagged == set(), flagged
