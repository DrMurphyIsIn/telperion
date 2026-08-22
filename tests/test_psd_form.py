"""Positive-definite quadratic-form emitter — the deterministic, cvxpy-free PSD
primitive the moment-matrix / Gram-bridge work recurs on (P=NP SoS ladder + BG).

For an explicit rational symmetric positive-definite matrix M, the exact LDLᵀ
congruence gives `xᵀMx = Σ Dᵢ·(Lᵀx)ᵢ²` with every `Dᵢ > 0`, so the emitted Lean is
the robust `ring` (identity) + `positivity`.  A non-PD matrix is refused (negative
control) — no SDP solver, all exact rational arithmetic.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import PSDFormEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_psd_form import psd_certificate, psd_form_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _spec(M):
    return lambda pt: M


def test_ldlt_sos_identity_holds_for_pd_matrix():
    M = [[2, 1], [1, 2]]
    cert = psd_certificate(M)
    assert cert.n == 2
    xs = sp.symbols("x1 x2")
    quad = sum(sp.Integer(M[i][j]) * xs[i] * xs[j] for i in range(2) for j in range(2))
    sos = sum(w * base**2 for w, base in cert.sos_terms)
    assert sp.expand(quad - sos) == 0
    assert all(w > 0 for w, _ in cert.sos_terms)


def test_singular_psd_is_supported():
    # rank-1 PSD (M = v vᵀ): completing-the-square yields a single square, no LDLᵀ
    # positive-definite requirement.
    M = [[1, 1], [1, 1]]
    cert = psd_certificate(M)
    assert len(cert.sos_terms) == 1
    xs = sp.symbols("x1 x2")
    quad = sum(sp.Integer(M[i][j]) * xs[i] * xs[j] for i in range(2) for j in range(2))
    assert sp.expand(quad - sum(w * b**2 for w, b in cert.sos_terms)) == 0
    assert all(w > 0 for w, _ in cert.sos_terms)


def test_refuses_non_psd_matrix():
    fam = psd_form_family("BadIndef", GridSpec([("_", [0])]), lambda pt: "bad",
                          spec=_spec([[1, 2], [2, 1]]))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "an indefinite matrix must be refused (negative control)"


def test_emit_is_lint_clean_and_deterministic():
    fam = psd_form_family("PSD3", GridSpec([("_", [0])]), lambda pt: "psd_three",
                          spec=_spec([[4, 2, 0], [2, 3, 1], [0, 1, 5]]))
    report = emit(certify(fam), LeanProfile(namespace=("PSD",)),
                  [PSDFormEmitter()], ValidationReport(checks=(("psd", True),)))
    text = next(iter(report.files.values()))
    assert "ring" in text and "positivity" in text
    assert "nlinarith" not in text  # deterministic, no search
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "PSDFormEmitter" in REGISTRY
