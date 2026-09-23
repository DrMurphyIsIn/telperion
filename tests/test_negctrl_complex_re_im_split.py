"""Negative control for ComplexReImSplitEmitter -- the forged (hence FALSE) real-part split.

The emitted proof rewrites the left-hand side into a real polynomial with the frozen
`simp only [Complex.*_re, ..., pow_succ, pow_zero, one_mul]` set and closes the identity with
`ring`.  Corrupt the claimed polynomial so the identity is false and `ring` cannot close it:
the TRUSTED Lean kernel is the arbiter.  The forgery here is not merely unprovable, it is
FALSE -- `Re ((a + b i)^2) = a^2 + b^2` fails at `a = 0, b = 1` (`-1 = 1`).

These tests are OFFLINE (string/arithmetic level): they pin the adapter registration, the
byte-level relationship between the twins, and the registry declaration.  The kernel run
happens through the generic harness in `test_certificate_sensitivity` / CI (lean-gated).

conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_complex_re_im_split import (  # noqa: E402
    complex_re_im_split_certificate,
    eval_complex_exact,
)
from telperion.emitter_sensitivity import (  # noqa: E402
    NEG_CONTROL_ADAPTER,
    REGISTRY,
)
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("ComplexReImSplitEmitter")
    assert ad is not None, "no adapter registered for ComplexReImSplitEmitter"
    return ad


def test_adapter_is_registered():
    _adapter()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["ComplexReImSplitEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    """Layer 1 would never mint the forgery: the adapter hand-builds the frozen dataclass."""
    cert = _adapter().make_false_cert()
    with pytest.raises(ValueError, match="REFUSED.*disagrees"):
        complex_re_im_split_certificate(cert.p, mode=cert.mode, params=cert.params,
                                        claim=cert.claim)


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """Pin the arithmetic: at a = 0, b = 1 the true real part is -1 and the forged claim
    says 1, so the forgery can never rot into a hard-but-true claim."""
    cert = _adapter().make_false_cert()
    a, b = cert.params
    env = {a: (Fraction(0), Fraction(0)), b: (Fraction(1), Fraction(0))}
    true_re, _true_im = eval_complex_exact(cert.p, env)
    forged = cert.claim.subs({a: 0, b: 1})
    assert true_re == Fraction(-1) and forged == 1
    assert sp.expand(cert.claim - cert.p_re) != 0
    # and the true twin's claim is the exact real part
    true_cert = _adapter().make_true_cert()
    assert sp.expand(true_cert.claim - true_cert.p_re) == 0


def test_true_twin_is_accepted_by_layer_one():
    cert = _adapter().make_true_cert()
    ok, _n = complex_re_im_split_certificate(cert.p, mode=cert.mode, params=cert.params,
                                             claim=cert.claim)
    assert ok.claim == cert.claim and ok.p_re == cert.p_re and ok.mode == "re"


def test_twins_differ_only_in_the_claimed_polynomial():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "split_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "split_twin")
    # Same expression, same binders, same frozen tactic script -- only the claim moves.
    assert "theorem split_twin (a b : ℝ) :" in false_txt and "theorem split_twin (a b : ℝ) :" in true_txt
    script = ("simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, "
              "Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, "
              "pow_zero, one_mul] all_goals ring")
    assert script in " ".join(false_txt.split()) and script in " ".join(true_txt.split())
    assert "= a ^ 2 + b ^ 2 := by" in false_txt and "= a ^ 2 + b ^ 2 := by" not in true_txt
    assert "= a ^ 2 - b ^ 2 := by" in true_txt and "= a ^ 2 - b ^ 2 := by" not in false_txt
    assert "sorry" not in false_txt and "sorry" not in true_txt
    # both are plain Mathlib statements: no island identifiers, no prelude needed
    assert ad.prelude == "" and ad.imports_line == "import Mathlib"
    assert "RvMBridge" not in false_txt and "RvMBridge" not in true_txt


# --- the cast face's twins (B D7), pinned offline --------------------------------------

def test_cast_forgery_is_refused_by_layer_one_and_is_false():
    from telperion.negctrl_adapters.adapter_complex_re_im_split import (
        make_false_cast_cert, make_true_cast_cert)
    bad, good = make_false_cast_cert(), make_true_cast_cert()
    with pytest.raises(ValueError, match="REFUSED.*disagrees"):
        complex_re_im_split_certificate(bad.p, mode=bad.mode, params=bad.params,
                                        nat_params=bad.nat_params, claim=bad.claim)
    ok, _n = complex_re_im_split_certificate(good.p, mode=good.mode, params=good.params,
                                             nat_params=good.nat_params, claim=good.claim)
    assert ok.claim == good.claim and ok.mode == "cast"
    # FALSE, not merely unproved: off by exactly 1 at every point
    assert sp.expand(bad.claim - bad.p_re) == 1


def test_cast_twins_differ_only_in_the_claimed_polynomial():
    from telperion.negctrl_adapters.adapter_complex_re_im_split import (
        make_false_cast_cert, make_true_cast_cert)
    ad = _adapter()
    false_txt = ad.emit_call(make_false_cast_cert(), "cast_twin")
    true_txt = ad.emit_call(make_true_cast_cert(), "cast_twin")
    head = "theorem cast_twin (m : ℕ) (u : ℝ) :\n    ((m : ℂ) * (u : ℂ) ^ 2 : ℂ) = "
    assert head in false_txt and head in true_txt
    assert "(((m : ℝ) * u ^ 2 + 1 : ℝ) : ℂ) := by\n  push_cast\n  all_goals ring\n" in false_txt
    assert "(((m : ℝ) * u ^ 2 : ℝ) : ℂ) := by\n  push_cast\n  all_goals ring\n" in true_txt
    assert "simp only" not in false_txt and "simp only" not in true_txt
    assert "sorry" not in false_txt and "sorry" not in true_txt
