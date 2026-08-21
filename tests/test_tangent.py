"""Phase 4 combinatorics emitter — the tangent-line trick for symmetric sums.

For a convex quadratic f and reals x_1..x_n with Σx_i = S, the tangent line at
a = S/n gives Σf(x_i) ≥ n·f(a) = B.  The certificate is the exact ring identity

    Σf(x_i) − B = c₂·Σ(x_i − a)² + f'(a)·(Σx_i − S),

so under the sum constraint the bound is a sum of squares — a genuinely
combinatorial (n-ary symmetric) inequality that reduces to `nlinarith` over
`sq_nonneg` hints.  This is the frontier-weak class (symmetric/combinatorial
inequalities) done deterministically.
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


def _f(c2, c1, c0):
    x = sp.Symbol("x")
    return c2 * x**2 + c1 * x + c0, x


def test_tangent_certificate_verifies_the_exact_identity():
    # f(x) = x^2 (c2=1), n=3, S=3 -> a=1, B=3. Identity must hold exactly.
    cert = tangent_certificate(c2=sp.Integer(1), c1=sp.Integer(0), c0=sp.Integer(0),
                               n=3, S=sp.Integer(3))
    assert cert.a == 1
    assert cert.B == 3          # 3 * f(1) = 3
    # the square-decomposition reproduces Σf - B modulo the constraint
    xs = sp.symbols("x1 x2 x3")
    lhs = sum(x**2 for x in xs) - cert.B
    rhs = cert.c2 * sum((x - cert.a) ** 2 for x in xs) + cert.slope * (sum(xs) - cert.S)
    assert sp.expand(lhs - rhs) == 0


def test_certify_refuses_non_convex_quadratic():
    fam = tangent_sum_family(
        "BadConcave", GridSpec([("_", [0])]), lambda pt: "bad",
        spec=lambda pt: (_f(sp.Integer(-1), sp.Integer(0), sp.Integer(0)), 3, sp.Integer(3)),
    )
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a non-convex (c2<=0) quadratic must be refused"


def test_emit_produces_lint_clean_tangent_theorem():
    fam = tangent_sum_family(
        "Jensen", GridSpec([("_", [0])]), lambda pt: "jensen_sq",
        spec=lambda pt: (_f(sp.Integer(1), sp.Integer(0), sp.Integer(0)), 3, sp.Integer(3)),
    )
    certified = certify(fam)
    report = emit(certified, LeanProfile(namespace=("Tangent",)),
                  [TangentSumEmitter()], ValidationReport(checks=(("t", True),)))
    text = next(iter(report.files.values()))
    assert "nlinarith" in text
    assert "sq_nonneg" in text
    assert "hsum" in text
    assert text.count("sq_nonneg") == 3   # one per term
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY, unclassified_emitters
    assert "TangentSumEmitter" in REGISTRY
    assert unclassified_emitters() == []
