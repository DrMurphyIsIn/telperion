"""Li positivity-ladder emitter (RH-roadmap Track 2).

Certifies the n-th Li-criterion rung `0 ≤ (taylorCoeff riemannXi n).re` from a
certified positive rational lower bound (the Arb enclosure = trust-seam hypothesis
`hlo`), feeding the upstream `LiCriterion.li_criterion_rh_iff`. Finite prefix, NOT RH.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    LiPositivityLadderEmitter,
    ValidationReport,
    certify,
    emit,
    li_positivity_family,
    li_rung_certificate,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


# The emitted rungs cite riemannXi / taylorCoeff, so the profile imports the
# upstream LiCriterion library (which supplies them) — the honest real config.
_PROFILE = LeanProfile(namespace=("Li",),
                       imports=("Mathlib", "Lc.LiCriterion.XiOrderBridge"))


def _emit(fam):
    report = emit(certify(fam), _PROFILE,
                  [LiPositivityLadderEmitter()], ValidationReport(checks=(("li", True),)))
    return next(iter(report.files.values()))


def test_certificate_requires_positive_lower_bound():
    assert li_rung_certificate(3, sp.Rational(1, 1000)).n == 3
    for bad in (0, sp.Rational(-1, 10)):
        try:
            li_rung_certificate(3, bad)
            raised = False
        except ValueError:
            raised = True
        assert raised, f"lo={bad} (non-positive) must be refused"
    # negative rung refused
    try:
        li_rung_certificate(-1, sp.Rational(1, 2))
        raised = False
    except ValueError:
        raised = True
    assert raised


def test_certify_refuses_nonpositive_bound_family():
    fam = li_positivity_family("Bad", GridSpec([("_", [0])]), lambda pt: "li_bad",
                               spec=lambda pt: (2, sp.Rational(-1, 5)))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised


def test_emit_cites_xi_coefficient_and_is_load_bearing():
    fam = li_positivity_family("L", GridSpec([("n", [0, 1, 2])]),
                               lambda pt: f"li_rung_{pt['n']}",
                               spec=lambda pt: (pt["n"], sp.Rational(1, 100)))
    text = _emit(fam)
    # references the ACTUAL xi Taylor coefficient (non-vacuous), not an abstract real
    assert "taylorCoeff riemannXi 0" in text
    assert "taylorCoeff riemannXi 2" in text
    assert "theorem li_rung_1" in text
    # the trust seam is explicit and the kernel step is the trivial le_trans
    assert "hlo" in text and "le_trans" in text and "norm_num" in text
    # ties to the upstream reduction in the provenance comment
    assert "li_criterion_rh_iff" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    # deterministic
    assert _emit(fam) == text


def test_emitter_is_classified():
    from telperion.emitter_sensitivity import REGISTRY, unclassified_emitters
    assert "LiPositivityLadderEmitter" in REGISTRY
    assert "LiPositivityLadderEmitter" not in set(unclassified_emitters())
