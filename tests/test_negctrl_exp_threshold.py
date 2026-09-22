"""Negative control for ExpThresholdEmitter -- the non-positive `a` (hence FALSE) threshold step.

The emitted linear proof needs `0 < s * a` (discharged by `positivity`) to turn the threshold
hypothesis `Q / (s * a) <= lam` into `Q <= s * lam * a`, then closes by `Real.add_one_le_exp` and
`linarith`.  Corrupt the sign of `a` and the statement is not merely unproved, it is FALSE: with
`Q = 3`, `a = -1`, `s = 2` the implication `3 / (2 * (-1)) <= lam -> 3 <= exp (2 * lam * (-1))`
fails at `lam = 0` (hypothesis `-3/2 <= 0` holds, conclusion `3 <= 1` does not).  The TRUSTED
Lean kernel is the arbiter: `positivity` cannot prove `(0 : R) < 2 * (-1)`.

These tests are OFFLINE (string/arithmetic level): they pin the adapter registration, the exact
falsity of the forgery, the byte-level relationship between the twins, and the registry
declaration.  The kernel run happens through the generic harness in
`test_certificate_sensitivity` / CI (lean-gated).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_exp_threshold import exp_threshold_certificate  # noqa: E402
from telperion.emitter_sensitivity import (  # noqa: E402
    NEG_CONTROL_ADAPTER,
    REGISTRY,
)
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("ExpThresholdEmitter")
    assert ad is not None, "no adapter registered for ExpThresholdEmitter"
    return ad


def _kwargs(cert):
    (st,) = cert.steps
    return dict(mode=st.mode, Q=st.Q, a=st.a, K=st.K, scale=st.scale, strict=st.strict,
                threshold=st.threshold)


def test_adapter_is_registered():
    _adapter()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["ExpThresholdEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    """Layer 1 would never mint the forgery (a <= 0): the adapter hand-builds the dataclasses."""
    cert = _adapter().make_false_cert()
    assert cert.steps[0].a == -1
    with pytest.raises(ValueError, match="REFUSED"):
        exp_threshold_certificate(**_kwargs(cert))


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """Pin the arithmetic at lam = 0, exactly: the hypothesis holds and the conclusion fails, so
    the forgery can never rot into a hard-but-true claim."""
    (st,) = _adapter().make_false_cert().steps
    lam = sp.Integer(0)
    hyp = st.Q / (st.scale * st.a) <= lam            # -3/2 <= 0
    concl = st.Q <= sp.exp(st.scale * lam * st.a)    # 3 <= exp 0 = 1
    assert hyp is sp.true
    assert concl is sp.false
    # and the true twin's conclusion holds wherever its hypothesis does (checked at the threshold)
    (tt,) = _adapter().make_true_cert().steps
    lam_t = tt.Q / (tt.scale * tt.a)                  # 3/2
    assert lam_t == sp.Rational(3, 2)
    assert (tt.Q <= sp.exp(tt.scale * lam_t * tt.a)) is sp.true   # 3 <= e^3


def test_true_twin_is_accepted_by_layer_one():
    cert = _adapter().make_true_cert()
    ok = exp_threshold_certificate(**_kwargs(cert))
    assert ok.steps[0].a == 1 and ok.steps[0].threshold == sp.Rational(3, 2)


def test_twins_differ_only_in_the_sign_literal():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "exp_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "exp_twin")
    # same tactic script -- only the literal for `a` moves
    for line in ("have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ",
                 ":= Real.add_one_le_exp _",
                 "  linarith"):
        assert line in false_txt and line in true_txt
    assert "((-1) : ℝ)" in false_txt and "((-1) : ℝ)" not in true_txt
    assert "(1 : ℝ)" in true_txt and "(1 : ℝ)" not in false_txt
    assert false_txt.replace("((-1) : ℝ)", "(1 : ℝ)").replace("threshold -3/2", "threshold 3/2") \
        .replace("a = -1", "a = 1") == true_txt
    assert "sorry" not in false_txt and "sorry" not in true_txt


def test_false_twin_states_the_false_theorem_verbatim():
    ad = _adapter()
    txt = ad.emit_call(ad.make_false_cert(), "negctrl_forged_false")
    assert "theorem negctrl_forged_false (lam : ℝ)" in txt
    assert "(h : (3 : ℝ) / (2 * ((-1) : ℝ)) ≤ lam) :" in txt
    assert "(3 : ℝ) ≤ Real.exp (2 * lam * ((-1) : ℝ)) := by" in txt
    # the load-bearing step the kernel cannot discharge
    assert "(by positivity : (0 : ℝ) < 2 * ((-1) : ℝ))" in txt
