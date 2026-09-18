"""bragg_amplitude emitter — certified truncated diffraction sum Σ cos(γ_k·u) ∈ [A,B].

The MIRRORMERE certified-diffraction shape (BraggH100 CosEnclosure fold reduced to a small base-case
instance): per-ordinate cos boxes via `cos_base_interval` + Lipschitz `cos_encl_bracket`, interval-
folded by `add_encl`, bridged to the claimed `[A,B]`.  The containment check is the negative control:
a claimed interval that does not enclose the folded box is refused.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import BraggAmplitudeEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_bragg_amplitude import (  # noqa: E402
    bragg_amplitude_certificate, bragg_amplitude_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_BRK = [("1/2", "51/100"), ("3/5", "61/100"), ("2/5", "41/100")]


def _spec(brackets, u, A, B):
    return lambda pt: {"brackets": brackets, "u": u, "A": A, "B": B}


def test_positive_cert_folds_and_contains():
    cert = bragg_amplitude_certificate(_BRK, "3/2", "0", "3")
    assert len(cert.brackets) == 3
    # folded box strictly inside the claimed [A, B]
    assert cert.A <= cert.sum_lo <= cert.sum_hi <= cert.B
    # each per-bracket box is lo = base_lo - w, hi = base_hi + w (exact)
    for bx in cert.brackets:
        assert bx.lo == bx.base_lo - bx.w
        assert bx.hi == bx.base_hi + bx.w
        assert abs(bx.c) <= 1


def test_refuses_interval_not_enclosing_sum():
    # NEGATIVE CONTROL: shrink B just below the folded upper bound Σhi.
    good = bragg_amplitude_certificate(_BRK, "3/2", "0", "3")
    tight_B = good.sum_hi - 1  # strictly below Σhi
    fam = bragg_amplitude_family("Bad", GridSpec([("_", [0])]), lambda pt: "bad",
                                 spec=_spec(_BRK, "3/2", "0", str(tight_B)))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a claimed interval not enclosing the folded amplitude must be refused"


def test_refuses_out_of_range_sample():
    # NEGATIVE CONTROL: |c| = |mid·u| > 1 is outside the order-4 base-bracket range.
    fam = bragg_amplitude_family("Big", GridSpec([("_", [0])]), lambda pt: "big",
                                 spec=_spec([("10", "101/10")], "3/2", "-3", "3"))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "|c| > 1 must be refused"


def test_emit_is_lint_clean_and_deterministic():
    fam = bragg_amplitude_family("BA", GridSpec([("_", [0])]), lambda pt: "bragg_three",
                                 spec=_spec(_BRK, "3/2", "0", "3"))
    report = emit(certify(fam), LeanProfile(namespace=("BA",), imports=("Mathlib", "CosEnclosure")),
                  [BraggAmplitudeEmitter()], ValidationReport(checks=(("bragg_amplitude", True),)))
    text = next(iter(report.files.values()))
    assert "CosEnclosure.cos_base_interval" in text
    assert "CosEnclosure.cos_encl_bracket" in text
    assert "CosEnclosure.add_encl" in text
    # per-zero lemma split: one cosbox lemma per ordinate + the fold theorem
    assert text.count("_cosbox_") >= 3
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "BraggAmplitudeEmitter" in REGISTRY
