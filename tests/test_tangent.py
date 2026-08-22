"""Phase 4 combinatorics emitter — the tangent-line trick for symmetric sums.

For a convex polynomial f (degree 2 or 4) and reals x_1..x_n with Σx_i = S, the
tangent line at a = S/n gives Σf(x_i) ≥ n·f(a) = B.  The surplus f(x)−L(x) has a
double root at a and an exact rational sum-of-squares form, so the emitted Lean
is the robust per-term `ring`+`positivity` plus a `linarith` assembly — a
genuinely combinatorial (n-ary symmetric) inequality reduced to deterministic
Mathlib tactics.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    TangentSumEmitter,
    ValidationReport,
    certify,
    emit,
)
from telperion.emit_tangent import tangent_sum_family, tangent_certificate  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_x = sp.Symbol("x")


def _spec(f, n, S):
    return lambda pt: ((f, _x), n, S)


def test_quadratic_certificate_verifies_the_exact_identity():
    cert = tangent_certificate(f=_x**2, x=_x, n=3, S=sp.Integer(3))
    assert cert.a == 1 and cert.B == 3
    # the SOS reproduces f−L exactly at the tangent point
    surplus = sum(c * base**2 for c, base in cert.sos_terms)
    fL = sp.expand(_x**2 - (cert.intercept + cert.slope * _x))
    assert sp.expand(fL - surplus) == 0
    assert all(c >= 0 for c, _ in cert.sos_terms)


def test_convex_quartic_is_supported_via_exact_sos():
    # f = x^4, n=2, S=2 -> a=1; f−L = (x-1)^2 * (x^2+2x+3), an exact 2-square SOS.
    cert = tangent_certificate(f=_x**4, x=_x, n=2, S=sp.Integer(2))
    assert cert.degree == 4
    surplus = sum(c * base**2 for c, base in cert.sos_terms)
    fL = sp.expand(_x**4 - (cert.intercept + cert.slope * _x))
    assert sp.expand(fL - surplus) == 0
    assert all(c >= 0 for c, _ in cert.sos_terms)
    assert len(cert.sos_terms) >= 2  # genuinely higher-degree (not a single square)


def test_convex_sextic_is_supported_when_surplus_factors():
    # f = x^6 + 3x^4 + 2x^2, n=2, S=0 -> a=0; surplus = x^2(x^2+1)(x^2+2), a
    # rational SOS via factorization — no artificial degree cap.
    f = _x**6 + 3 * _x**4 + 2 * _x**2
    cert = tangent_certificate(f=f, x=_x, n=2, S=sp.Integer(0))
    assert cert.degree == 6
    surplus = sum(c * base**2 for c, base in cert.sos_terms)
    fL = sp.expand(f - (cert.intercept + cert.slope * _x))
    assert sp.expand(fL - surplus) == 0
    assert all(c >= 0 for c, _ in cert.sos_terms)


def test_irreducible_high_degree_surplus_is_refused():
    # f = x^6 : the surplus cofactor is an irreducible quartic over Q, so this
    # factorization method has no rational SOS — refuse honestly (named-open).
    try:
        tangent_certificate(f=_x**6, x=_x, n=2, S=sp.Integer(2))
        raised = False
    except Exception:
        raised = True
    assert raised, "an irreducible-high-degree surplus must be refused (named-open)"


def test_certify_refuses_non_convex_quadratic():
    fam = tangent_sum_family("BadConcave", GridSpec([("_", [0])]), lambda pt: "bad",
                             spec=_spec(-_x**2, 3, sp.Integer(3)))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a non-convex f (surplus not SOS) must be refused"


def test_emit_produces_lint_clean_robust_proof():
    fam = tangent_sum_family("Quartic", GridSpec([("_", [0])]), lambda pt: "quartic_two",
                             spec=_spec(_x**4, 2, sp.Integer(2)))
    certified = certify(fam)
    report = emit(certified, LeanProfile(namespace=("Tangent",)),
                  [TangentSumEmitter()], ValidationReport(checks=(("t", True),)))
    text = next(iter(report.files.values()))
    assert "positivity" in text          # per-term SOS nonnegativity
    assert "linarith" in text            # the assembly using hsum
    assert "hsum" in text
    assert "ring" in text                # the exact SOS identity
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "TangentSumEmitter" in REGISTRY
