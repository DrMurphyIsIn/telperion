"""AffineLedger emitter (NS/Euler ExponentLedger shape): certify → emit → lint,
with the real ExponentLedger.lean facts as positive controls and false-margin /
unbounded-form refusals as negative controls.  The Lean kernel is the arbiter
(CI `lake build`); these are the pre-CI self-checks."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    ValidationReport,
    affine_ledger_certificate,
    affine_ledger_family,
    certify,
    emit,
)
from telperion.emit_ns_ledger import AffineLedgerEmitter  # noqa: E402
from telperion.lean_lint import check_lean_text

sigma = sp.Symbol("σ")
kappa = sp.Symbol("κ")

# Region of ExponentLedger.lean: σ ≥ 1/5, 0 ≤ κ ≤ 1e-5.
_BOX = (("σ", sp.Rational(1, 5), None), ("κ", 0, sp.Rational(1, 100000)))


def _margin_family():
    """wave_at_least_seven_tenths: 7/10 ≤ 1/2 + σ on σ ≥ 1/5 (tight at σ=1/5)."""
    return affine_ledger_family(
        name="LedgerMargin",
        grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "wave_at_least_seven_tenths",
        spec=lambda pt: (
            (sigma,), (("σ", sp.Rational(1, 5), None),),
            "margin", sp.Rational(7, 10), (sp.Rational(1, 2) + sigma,), False,
        ),
    )


def _min_lower_family():
    """signed_bar_gain_exceeds_seventeen_hundredths: 17/100 < min of the five
    signed-bar gains on σ ≥ 1/5, 0 ≤ κ ≤ 1e-5."""
    forms = (
        sp.Rational(9, 50) - 2 * kappa,
        sp.Rational(1, 2) - 3 * kappa,
        sigma - 3 * kappa,
        1 - kappa,
        1 - 2 * kappa,
    )
    return affine_ledger_family(
        name="LedgerMinLower",
        grid=GridSpec([("k", [0])]),
        lean_name=lambda pt: "signed_bar_gain_exceeds_seventeen_hundredths",
        spec=lambda pt: ((sigma, kappa), _BOX, "min_lower", sp.Rational(17, 100), forms, True),
    )


def _emit(fam):
    return emit(
        certify(fam),
        LeanProfile(namespace=("NS", "Ledger")),
        [AffineLedgerEmitter()],
        ValidationReport(checks=(("spot", True),)),
    )


def test_kind():
    assert _margin_family().kind == "affine_ledger"
    assert _min_lower_family().kind == "affine_ledger"


def test_margin_certifies_and_worst_corner_is_tight():
    cf = certify(_margin_family())
    cert = cf.instances[0].payload
    assert cert.mode == "margin"
    assert cert.worst == (sp.Rational(7, 10),)  # tight at σ = 1/5


def test_min_lower_certifies_all_forms_above_threshold():
    cf = certify(_min_lower_family())
    cert = cf.instances[0].payload
    assert cert.mode == "min_lower"
    assert len(cert.worst) == 5
    assert all(w > sp.Rational(17, 100) for w in cert.worst)


def test_margin_emits_linarith_theorem():
    text = _emit(_margin_family()).files["LedgerMargin.lean"]
    assert "theorem wave_at_least_seven_tenths" in text
    assert "(7 / 10) ≤" in text
    assert "linarith" in text
    assert "(1 / 5) ≤ σ" in text


def test_min_lower_emits_min_and_iff():
    text = _emit(_min_lower_family()).files["LedgerMinLower.lean"]
    assert "theorem signed_bar_gain_exceeds_seventeen_hundredths" in text
    assert "(17 / 100) <" in text
    assert "min (" in text
    assert "lt_min_iff" in text


def test_lean_text_clean():
    check_lean_text(_emit(_margin_family()).files["LedgerMargin.lean"])
    check_lean_text(_emit(_min_lower_family()).files["LedgerMinLower.lean"])


def test_byte_stability():
    assert _emit(_min_lower_family()).files["LedgerMinLower.lean"] == \
        _emit(_min_lower_family()).files["LedgerMinLower.lean"]


def test_negative_control_false_margin_refused():
    # 8/10 ≤ 1/2 + σ FAILS at σ = 1/5 (LHS 0.8 > 0.7 = worst corner).
    with pytest.raises(ValueError, match="overclaim|violates"):
        affine_ledger_certificate(
            (sigma,), (("σ", sp.Rational(1, 5), None),),
            "margin", sp.Rational(8, 10), (sp.Rational(1, 2) + sigma,), False,
        )


def test_negative_control_unbounded_form_refused():
    # threshold ≤ σ with σ unbounded ABOVE but no floor ⟹ min = -∞ ⟹ refuse.
    with pytest.raises(ValueError, match="unbounded below"):
        affine_ledger_certificate(
            (sigma,), (("σ", None, None),),
            "margin", sp.Rational(0), (sigma,), False,
        )


def test_negative_control_nonaffine_refused():
    with pytest.raises(ValueError, match="not affine"):
        affine_ledger_certificate(
            (sigma,), (("σ", sp.Rational(1, 5), None),),
            "margin", sp.Rational(0), (sigma ** 2,), False,
        )
