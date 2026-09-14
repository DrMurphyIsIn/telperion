"""selfinversive_rigidity emitter — equal-modulus real-rootedness (MIRRORMERE R3, n=2).

|c₁|² = |c₂|² EXACTLY ⟹ the two-frequency sum is real-rooted (via `twoFreq_realRooted_iff`).  Unequal
modulus is the negative control: it does NOT force real-rootedness and is refused.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    SelfInversiveRigidityEmitter, ValidationReport, certify, emit,
)
from telperion.emit_selfinversive_rigidity import (  # noqa: E402
    selfinversive_rigidity_certificate, selfinversive_rigidity_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _spec(c1, c2, lam1, lam2):
    return lambda pt: {"c1": c1, "c2": c2, "lam1": lam1, "lam2": lam2}


def test_positive_cert_equal_modulus():
    cert = selfinversive_rigidity_certificate(("3/5", "4/5"), ("1", "0"), "1", "2")
    assert cert.normsq == 1
    # a conjugate pair, |c|² = 2
    cert2 = selfinversive_rigidity_certificate(("1", "1"), ("1", "-1"), "0", "3")
    assert cert2.normsq == 2


def test_refuses_unequal_modulus():
    # NEGATIVE CONTROL: |c₁|² = 1 ≠ |c₂|² = 4.
    fam = selfinversive_rigidity_family("Bad", GridSpec([("_", [0])]), lambda pt: "bad",
                                        spec=_spec(("3/5", "4/5"), ("2", "0"), "1", "2"))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "unequal modulus must be refused (does not force real-rootedness)"


def test_refuses_equal_frequencies():
    # NEGATIVE CONTROL: λ₁ = λ₂ (no two-frequency structure).
    fam = selfinversive_rigidity_family("Bad2", GridSpec([("_", [0])]), lambda pt: "bad2",
                                        spec=_spec(("1", "0"), ("1", "0"), "2", "2"))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "equal frequencies must be refused"


def test_emit_is_lint_clean_and_deterministic():
    fam = selfinversive_rigidity_family("SR", GridSpec([("_", [0])]), lambda pt: "rigidity_unit",
                                        spec=_spec(("3/5", "4/5"), ("1", "0"), "1", "2"))
    report = emit(certify(fam),
                  LeanProfile(namespace=("SR",), imports=("Mathlib", "TwoFreqRigidity")),
                  [SelfInversiveRigidityEmitter()],
                  ValidationReport(checks=(("selfinversive_rigidity", True),)))
    text = next(iter(report.files.values()))
    assert "Quasicrystal.twoFreq_realRooted_iff" in text
    assert "Complex.norm_def" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "SelfInversiveRigidityEmitter" in REGISTRY
