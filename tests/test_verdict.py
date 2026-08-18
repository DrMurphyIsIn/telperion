"""The honest-verdict record (#8): taxonomy, no-float-at-decision-point guard,
structural invariants, ledger bridge."""
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.ledger import RouteLedger  # noqa: E402
from telperion.verdict import (  # noqa: E402
    FloatAtDecisionPoint,
    ProbeVerdict,
    Verdict,
    decide,
    null,
    obstructed,
    probe,
    re_derivation,
    require_exact,
    validated,
)


# --- no floats at decision points ---

def test_require_exact_accepts_exact_types():
    assert require_exact(3) == Fraction(3)
    assert require_exact(Fraction(3, 23)) == Fraction(3, 23)
    assert require_exact(sp.Rational(3, 23)) == Fraction(3, 23)
    assert require_exact(sp.Integer(5)) == Fraction(5)


def test_require_exact_refuses_python_float():
    with pytest.raises(FloatAtDecisionPoint):
        require_exact(0.3333333)


def test_require_exact_refuses_sympy_float():
    with pytest.raises(FloatAtDecisionPoint):
        require_exact(sp.Float("0.13043478"))


def test_decide_is_exact():
    # 3/23 vs 0.13043... — exact says they differ; a float decision would blur it
    assert decide(Fraction(3, 23), ">", Fraction(13, 100)) is True
    assert decide(sp.Rational(64 * 243 * 23), "==", sp.Rational(621 * 576)) is True
    assert decide(Fraction(5), "<=", Fraction(5)) is True


def test_decide_refuses_float_operand():
    with pytest.raises(FloatAtDecisionPoint):
        decide(0.13, "<", Fraction(3, 23))


# --- structural invariants: a verdict cannot be malformed ---

def test_validated_requires_evidence():
    with pytest.raises(ValueError):
        ProbeVerdict("phi <= 1 on N(c,k)", Verdict.VALIDATED)
    ok = validated("phi <= 1 on N(c,k)", "R(5)=1 exactly: 64*243*23 == 621*576")
    assert ok.verdict is Verdict.VALIDATED


def test_obstructed_requires_located_obstruction():
    with pytest.raises(ValueError):
        ProbeVerdict("smooth P closes the crux", Verdict.OBSTRUCTED_AND_LOCATED)
    ok = obstructed("smooth P closes the crux",
                    "continuous relaxation phi(c*=3.82)=1.00004>1 (arithmetic, not smooth)")
    assert ok.obstruction is not None


def test_re_derivation_requires_prior_claim():
    with pytest.raises(ValueError):
        ProbeVerdict("rho vs Phi are distinct quantities", Verdict.RE_DERIVATION)
    ok = re_derivation("BG is about rooted Phi, max over roots",
                       corrected_from="raw-rho competitor extremality (near-star maximal)")
    assert ok.corrected_from is not None


def test_null_is_clean_negative():
    v = null("weekend funding edge", "t=2.06 < 2.63 Bonferroni; mechanism gate fails")
    assert v.verdict is Verdict.NULL


# --- @probe enforces closing with a verdict ---

def test_probe_decorator_requires_verdict():
    @probe
    def good():
        return validated("x", "exact: 1==1")

    @probe
    def bad():
        return "looks fine"

    assert good().verdict is Verdict.VALIDATED
    with pytest.raises(TypeError):
        bad()


# --- ledger bridge speaks the canonical vocabulary ---

def test_to_route_entry_records(tmp_path):
    led = RouteLedger(tmp_path / "routes.json")
    v = obstructed("finite polytope closes Phi<=1",
                   "polytope ACCUMULATES (not finite) at the marginal tie")
    assert v.to_route_entry(led, route="finite_polytope") is True
    assert v.to_route_entry(led, route="finite_polytope") is False  # dedup
    md = led.render_md()
    assert "OBSTRUCTED_AND_LOCATED" in md


def test_render_reads_as_its_verdict():
    v = validated("R(5)=1", "64*243*23 == 621*576 (exact)")
    assert v.render().startswith("VALIDATED: R(5)=1")
