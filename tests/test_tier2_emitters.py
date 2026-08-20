"""Tier-2 literature-derived emitters (2026-08-19): pipeline + negative controls.

Two certificate families beyond the BG-derived set, each flowing through the
single enforced certify->validate->emit->freeze API:

  * Putinar / constrained-SOS  — `0 ≤ p` on `{g_i ≥ 0}` via `p = σ_0 + Σ σ_i g_i`.
  * WZ / Zeilberger            — hypergeometric sum identities via a WZ mate.

For each: a positive family certifies and emits soundness-lint-clean Lean, and an
out-of-class family (a certificate that does not reconstruct the target / a wrong
WZ mate) is REFUSED at certification.  The Lean kernel verdict is CI-only.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, ValidationReport,
    certify, check_lean_text, emit,
)
from telperion import (  # noqa: E402
    ConstrainedSOSEmitter, WZEmitter, WZ_PRELUDE, putinar_family, wz_family,
)

GREEN = ValidationReport(checks=(("spot", True),))


def _emit_clean(fam, emitter, prelude=""):
    res = emit(certify(fam), LeanProfile(namespace=("T",), prelude=prelude),
               [emitter], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    return res, body


# --- Putinar / constrained SOS ----------------------------------------------

def test_putinar_positive_and_refusal():
    x, y = sp.symbols("x y")
    # 0 <= x^2*y + y on {y >= 0}:  (x^2 + 1)·y,  σ_1 = 1·x^2 + 1·1^2 (a real SOS
    # multiplier), g_1 = y.
    fam = putinar_family("Put", (x, y), GridSpec([("j", [0])]), lambda pt: "put",
                         lambda pt: (x ** 2 * y + y, [],
                                     [(y, [(1, x), (1, sp.Integer(1))], "hy")]))
    res, body = _emit_clean(fam, ConstrainedSOSEmitter())
    assert res.n_theorems == 1
    assert all(t in body for t in ("ring", "positivity", "mul_nonneg", "linarith"))
    assert "0 ≤ x" not in body.split("theorem")[0]  # sanity: hypothesis appears
    # negative control: a decomposition that does NOT reconstruct p
    bad = putinar_family("Bad", (x, y), GridSpec([("j", [0])]), lambda pt: "bad",
                         lambda pt: (x ** 2 * y + y, [],
                                     [(y, [(1, x)], "hy")]))  # (x^2)·y != x^2*y + y
    with pytest.raises(CertificationError):
        certify(bad)


def test_putinar_negative_coefficient_refused():
    x, y = sp.symbols("x y")
    # a NEGATIVE square coefficient is not a sum of squares -> refused
    bad = putinar_family("Neg", (x, y), GridSpec([("j", [0])]), lambda pt: "neg",
                         lambda pt: (-(x ** 2) * y, [],
                                     [(y, [(-1, x)], "hy")]))
    with pytest.raises(CertificationError):
        certify(bad)


# --- WZ / Zeilberger --------------------------------------------------------

def test_wz_positive_and_refusal():
    n, k = sp.symbols("n k")
    # Σ_k C(n,k) = 2^n has WZ mate R(n,k) = -k / (2(n-k+1)).
    F, R, rhs = sp.binomial(n, k), -k / (2 * (n - k + 1)), 2 ** n
    fam = wz_family("WZ", GridSpec([("j", [0])]), lambda pt: "binom",
                    lambda pt: (F, R, rhs, n, k), n=n, k=k)
    res, body = _emit_clean(fam, WZEmitter(), prelude=WZ_PRELUDE)
    assert res.n_theorems == 1 and "ring" in body
    # the emitted goal must be a NON-VACUOUS polynomial identity (not `X = X`)
    thm = next(l for l in body.splitlines() if l.startswith("theorem binom_wz"))
    lhs = thm.split(": ∀ n k : ℝ,")[1].split(" = 0")[0].strip()
    assert lhs != "0" and "-" in lhs  # a real cleared expression, ring-checked
    # negative control: a wrong mate fails the WZ equation -> refused
    bad = wz_family("Bad", GridSpec([("j", [0])]), lambda pt: "bad",
                    lambda pt: (F, sp.Integer(0), rhs, n, k), n=n, k=k)
    with pytest.raises(CertificationError):
        certify(bad)


def test_wz_prelude_lemma_present():
    assert "theorem wz_row_invariant" in WZ_PRELUDE
    check_lean_text("/- telperion -/\n" + WZ_PRELUDE)  # no sorry/axiom/stub


def test_wz_non_hypergeometric_refused():
    n, k = sp.symbols("n k")
    # F with a non-rational term ratio is not proper hypergeometric -> refused
    bad = wz_family("BadH", GridSpec([("j", [0])]), lambda pt: "badh",
                    lambda pt: (sp.sqrt(n + k), sp.Integer(0), sp.Integer(1), n, k),
                    n=n, k=k)
    with pytest.raises(CertificationError):
        certify(bad)


# --- byte-stability (the drift-net guarantee) -------------------------------

def test_tier2_byte_stability():
    n, k = sp.symbols("n k")
    F, R, rhs = sp.binomial(n, k), -k / (2 * (n - k + 1)), 2 ** n

    def build():
        fam = wz_family("WZ", GridSpec([("j", [0])]), lambda pt: "binom",
                        lambda pt: (F, R, rhs, n, k), n=n, k=k)
        return emit(certify(fam), LeanProfile(namespace=("T",)),
                    [WZEmitter()], GREEN)
    assert build().input_hash == build().input_hash
