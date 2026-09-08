"""HermitianMomentInertia emitter family (ported from anthropics/zeta-23-lean,
arXiv:2608.13637).  Two self-contained ℝ certificates:

* ``TwoMomentCountEmitter`` — the §6 scalar count certificate ``(2−κ)N − err ≤
  count`` (c=2, H(λ)) / ``(3/2−κ/2)N − err ≤ count`` (c=3, H_d(λ)), κ = 1/λ + λ/3.
* ``RankTraceScalarEmitter`` — the integrality atom ``2c·x − c² ≤ x²``.

Honesty: the two moment bounds are theorem HYPOTHESES (analytic trust seam); the
emitter proves only the arithmetic implication.  Not a step toward RH.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    RankTraceScalarEmitter,
    TwoMomentCountEmitter,
    ValidationReport,
    certify,
    emit,
    rank_trace_scalar_certificate,
    rank_trace_scalar_family,
    two_moment_count_certificate,
    two_moment_count_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


def _emit_text(fam, emitter):
    report = emit(certify(fam), LeanProfile(namespace=("HM",)), [emitter],
                  ValidationReport(checks=(("hm", True),)))
    return next(iter(report.files.values()))


# --------------------------------------------------------------------------- #
# TwoMomentCount — the H(λ) / H_d(λ) constants                                 #
# --------------------------------------------------------------------------- #


def test_headline_constants_lambda_one():
    # λ = 1: κ = 4/3, H(1) = 2/3 (Theorem A), H_d(1) = 5/6 (Theorem C).
    c2 = two_moment_count_certificate(1, c=2)
    assert c2.kappa == sp.Rational(4, 3) and c2.H == sp.Rational(2, 3)
    c3 = two_moment_count_certificate(1, c=3)
    assert c3.kappa == sp.Rational(4, 3) and c3.H == sp.Rational(5, 6)


def test_kappa_identity_exact():
    # κ = 1/λ + λ/3 exactly, at several rational band-limits.
    for lam in (sp.Rational(1, 2), sp.Rational(3, 4), sp.Rational(9, 10), 1):
        cert = two_moment_count_certificate(lam, c=2)
        L = sp.Rational(sp.nsimplify(lam))
        assert cert.kappa == 1 / L + L / 3
        assert cert.H == 2 - cert.kappa


def test_H_d_is_average_of_one_and_H():
    # H_d(λ) = (1 + H(λ))/2 for the distinct-zeros route.
    for lam in (sp.Rational(1, 2), sp.Rational(3, 4), 1):
        h = two_moment_count_certificate(lam, c=2).H
        hd = two_moment_count_certificate(lam, c=3).H
        assert hd == (1 + h) / 2


def test_refuses_bandwidth_over_one_and_bad_route():
    # λ > 1 is the bandwidth-one ceiling (needs Hardy–Littlewood-strength input).
    for bad in (sp.Rational(3, 2), 2, 0, -1):
        try:
            two_moment_count_certificate(bad, c=2)
            raised = False
        except ValueError:
            raised = True
        assert raised, f"λ={bad} must be refused"
    try:
        two_moment_count_certificate(1, c=4)
        raised = False
    except ValueError:
        raised = True
    assert raised, "route c=4 must be refused"


def test_certify_refuses_out_of_range_family():
    fam = two_moment_count_family("Bad", GridSpec([("_", [0])]), lambda pt: "bad",
                                  spec=lambda pt: (sp.Rational(3, 2), 2))
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "certify must refuse a λ > 1 family"


def test_two_moment_count_emit_lint_clean_and_deterministic():
    fam = two_moment_count_family("A", GridSpec([("_", [0])]), lambda pt: "thmA_two_thirds",
                                  spec=lambda pt: (1, 2))
    text = _emit_text(fam, TwoMomentCountEmitter())
    assert "theorem thmA_two_thirds" in text
    assert "Real.sqrt_le_sqrt hfr" in text
    assert "nlinarith" in text
    # the trust seam is explicit: moment bounds arrive as hypotheses htr/hfr
    assert "htr" in text and "hfr" in text and "count" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    # deterministic: same bytes on re-emit
    assert _emit_text(fam, TwoMomentCountEmitter()) == text


def test_c3_route_emits_halved_algebra():
    fam = two_moment_count_family("C", GridSpec([("_", [0])]), lambda pt: "thmC_five_sixths",
                                  spec=lambda pt: (1, 3))
    text = _emit_text(fam, TwoMomentCountEmitter())
    assert "2 * count" in text          # the c=3 lemma's doubled RHS
    assert "3/2 -" in text              # the (3/2 − κ/2) constant
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


# --------------------------------------------------------------------------- #
# RankTraceScalar — the integrality atom                                       #
# --------------------------------------------------------------------------- #


def test_rank_trace_scalar_emit():
    fam = rank_trace_scalar_family("R", GridSpec([("c", [2, 3])]),
                                   lambda pt: f"integrality_c{pt['c']}",
                                   spec=lambda pt: pt["c"])
    text = _emit_text(fam, RankTraceScalarEmitter())
    assert "theorem integrality_c2" in text and "theorem integrality_c3" in text
    assert "sq_nonneg" in text and "nlinarith" in text
    assert "x^2" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_rank_trace_scalar_identity_holds():
    # the emitted claim is a true real inequality: 2c·x − c² ≤ x² for all x.
    x, c = sp.symbols("x c", real=True)
    assert sp.expand(x**2 - (2 * c * x - c**2)) == sp.expand((x - c) ** 2)


# --------------------------------------------------------------------------- #
# classification gate                                                          #
# --------------------------------------------------------------------------- #


def test_emitters_are_classified():
    from telperion.emitter_sensitivity import REGISTRY, unclassified_emitters
    assert "TwoMomentCountEmitter" in REGISTRY
    assert "RankTraceScalarEmitter" in REGISTRY
    # our two must not be among the unclassified; the only pre-existing gap on
    # origin/main is EndpointGeomCapEmitter (a parallel session's emitter), which
    # this change does not introduce and does not own.
    unclassified = set(unclassified_emitters())
    assert "TwoMomentCountEmitter" not in unclassified
    assert "RankTraceScalarEmitter" not in unclassified
    assert unclassified <= {"EndpointGeomCapEmitter"}, unclassified
