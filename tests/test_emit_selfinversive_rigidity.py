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
    selfinversive_offline_certificate, selfinversive_rigidity_certificate,
    selfinversive_rigidity_family,
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


# ---------------------------------------------------------------------------------------------
# OFFLINE mode (2026-09-18): the refutation-shaped mirror — unequal modulus ⟹ NOT real-rooted.
# ---------------------------------------------------------------------------------------------


def _euler_spec(p):
    """The p-th Euler-factor section twoFreq(1, −(1/√p); 0, −log p); −(1/√p) = (−1/p)·√p."""
    return {"mode": "offline", "c1": "1", "c2": {"rat": f"-1/{p}", "sqrt": p},
            "lam1": "0", "lam2": {"rat": "-1", "log": p}}


def test_offline_positive_cert_euler_factor():
    import sympy as sp

    spec = _euler_spec(2)
    cert = selfinversive_offline_certificate(spec["c1"], spec["c2"], spec["lam1"], spec["lam2"])
    # |c₁|² = 1, |c₂|² = (1/2)²·2 = 1/2 — EXACT rational arithmetic on r·√q coefficients.
    assert cert.normsq1 == 1 and cert.normsq2 == sp.Rational(1, 2)
    assert cert.euler_p == 2


def test_offline_refuses_equal_modulus():
    # NEGATIVE CONTROL of the offline mode: equal modulus FORCES real-rootedness, so there is
    # no off-line zero to certify — the mirror of the default mode's refusal.
    try:
        selfinversive_offline_certificate({"rat": "1/2", "sqrt": 2}, {"rat": "-1/2", "sqrt": 2},
                                          "0", {"rat": "-1", "log": 2})
        raised = False
    except ValueError:
        raised = True
    assert raised, "equal modulus must be refused in offline mode"


def test_offline_refuses_zero_coefficient_and_bad_radicand():
    for c2 in ({"rat": "0", "sqrt": 2}, {"rat": "-1", "sqrt": "-2"}):
        try:
            selfinversive_offline_certificate("1", c2, "0", {"rat": "-1", "log": 2})
            raised = False
        except ValueError:
            raised = True
        assert raised, f"must refuse coefficient {c2}"


def test_offline_refuses_uncertifiable_frequency_pair():
    # A NONZERO rational against r·log q would need transcendence of log to separate — refused,
    # not faked.  Equal frequencies and equal-base logs with equal rational factor too.
    for lam1, lam2 in (("1", {"rat": "-1", "log": 2}),
                       ({"rat": "1", "log": 2}, {"rat": "1", "log": 2}),
                       ({"rat": "1", "log": 2}, {"rat": "1", "log": 3}),
                       ("0", "0")):
        try:
            selfinversive_offline_certificate("1", {"rat": "-1/2", "sqrt": 2}, lam1, lam2)
            raised = False
        except ValueError:
            raised = True
        assert raised, f"must refuse frequency pair {lam1!r}, {lam2!r}"


def test_offline_accepts_zero_against_log_and_same_base_logs():
    # The kernel-certifiable distinctness cases: 0 vs r·log q, and r₁·log q vs r₂·log q.
    selfinversive_offline_certificate("1", {"rat": "-1/2", "sqrt": 2}, "0", {"rat": "-1", "log": 2})
    selfinversive_offline_certificate("1", {"rat": "-1/2", "sqrt": 2},
                                      {"rat": "1", "log": 2}, {"rat": "3", "log": 2})


def test_offline_emit_carries_refutation_witness_and_node_form():
    fam = selfinversive_rigidity_family("OFF", GridSpec([("_", [0])]),
                                        lambda pt: "euler_factor_p2_offline",
                                        spec=lambda pt: _euler_spec(2))
    report = emit(certify(fam),
                  LeanProfile(namespace=("OFF",), imports=("Mathlib", "TwoFreqRigidity")),
                  [SelfInversiveRigidityEmitter()],
                  ValidationReport(checks=(("selfinversive_rigidity_offline", True),)))
    text = next(iter(report.files.values()))
    # the refutation, via the .mp direction and the EXACT normSq inequality
    assert "¬ (∀ x : ℂ" in text
    assert ".mp hall" in text
    assert "‖euler_factor_p2_offline_c1‖ ^ 2 ≠ ‖euler_factor_p2_offline_c2‖ ^ 2" in text
    # the explicit witness x = i/2 and the second, witness-route refutation
    assert "euler_factor_p2_offline_witness :" in text
    assert "Complex.I / 2" in text
    assert "euler_factor_p2_offline_of_witness :" in text
    # the mission-registry-verbatim restatement
    assert "twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2))" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_offline_non_euler_instance_ships_no_witness():
    # An unequal-modulus instance that is NOT the Euler-factor shape still refutes, but there is
    # no closed-form witness to ship — exactly one theorem.
    fam = selfinversive_rigidity_family("OFF2", GridSpec([("_", [0])]), lambda pt: "generic_offline",
                                        spec=lambda pt: {"mode": "offline", "c1": "2", "c2": "3",
                                                         "lam1": "0", "lam2": {"rat": "-1", "log": 2}})
    report = emit(certify(fam),
                  LeanProfile(namespace=("OFF2",), imports=("Mathlib", "TwoFreqRigidity")),
                  [SelfInversiveRigidityEmitter()],
                  ValidationReport(checks=(("selfinversive_rigidity_offline", True),)))
    text = next(iter(report.files.values()))
    assert "generic_offline_witness" not in text
    assert "¬ (∀ x : ℂ" in text


def test_unknown_mode_is_refused():
    fam = selfinversive_rigidity_family("OFF3", GridSpec([("_", [0])]), lambda pt: "bogus",
                                        spec=lambda pt: {"mode": "bogus", "c1": "1", "c2": "2",
                                                         "lam1": "0", "lam2": "1"})
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "an unknown mode must be refused"


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "SelfInversiveRigidityEmitter" in REGISTRY
