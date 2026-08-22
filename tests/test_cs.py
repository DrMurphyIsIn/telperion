"""Phase 4 combinatorics emitter — Cauchy–Schwarz / QM–AM as pairwise-difference SOS.

A second, distinct symmetric-inequality family (constraint-free, unlike the
tangent-line trick's sum constraint): for positive weights wᵢ,

    (Σ wᵢ·xᵢ)² ≤ (Σ wᵢ)·(Σ wᵢ·xᵢ²),

certified by the exact identity

    (Σwᵢ)(Σwᵢxᵢ²) − (Σwᵢxᵢ)² = Σ_{i<j} wᵢwⱼ·(xᵢ − xⱼ)²  ≥ 0,

so the emitted Lean is the deterministic `ring` (identity) + `positivity`
(nonnegative pairwise-difference squares) + `linarith`.  Unweighted (all wᵢ = 1)
is the classic `(Σxᵢ)² ≤ n·Σxᵢ²`.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import CauchySchwarzEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_cs import cauchy_schwarz_family, cs_certificate  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _spec(weights):
    return lambda pt: weights


def test_unweighted_identity_holds():
    cert = cs_certificate([sp.Integer(1)] * 4)
    assert cert.n == 4 and cert.W == 4
    xs = sp.symbols("x1 x2 x3 x4")
    lhs = cert.W * sum(x**2 for x in xs) - sum(xs) ** 2
    rhs = sum(c * (xs[i - 1] - xs[j - 1]) ** 2 for c, (i, j) in cert.sos_terms)
    assert sp.expand(lhs - rhs) == 0


def test_weighted_identity_holds():
    w = [sp.Integer(1), sp.Integer(2), sp.Integer(3)]
    cert = cs_certificate(w)
    xs = sp.symbols("x1 x2 x3")
    lhs = cert.W * sum(w[i] * xs[i] ** 2 for i in range(3)) - (sum(w[i] * xs[i] for i in range(3))) ** 2
    rhs = sum(c * (xs[i - 1] - xs[j - 1]) ** 2 for c, (i, j) in cert.sos_terms)
    assert sp.expand(lhs - rhs) == 0
    assert all(c > 0 for c, _ in cert.sos_terms)


def test_refuses_non_positive_weight():
    fam = cauchy_schwarz_family("Bad", GridSpec([("_", [0])]), lambda pt: "bad",
                                spec=_spec([sp.Integer(1), sp.Integer(-1)]))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a non-positive weight must be refused"


def test_emit_is_lint_clean_and_deterministic():
    fam = cauchy_schwarz_family("CS", GridSpec([("_", [0])]), lambda pt: "cs_three",
                                spec=_spec([sp.Integer(1)] * 3))
    report = emit(certify(fam), LeanProfile(namespace=("CS",)),
                  [CauchySchwarzEmitter()], ValidationReport(checks=(("cs", True),)))
    text = next(iter(report.files.values()))
    assert "ring" in text and "positivity" in text and "linarith" in text
    assert "nlinarith" not in text  # deterministic, no search
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "CauchySchwarzEmitter" in REGISTRY
