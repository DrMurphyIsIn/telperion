"""Negative controls for FactoredEndpointEnclosureEmitter -- a box claim false by ~1/1000, in
one and in two variables.

(1) The registered adapter's instance is the sharp log companion
``l - log(1 + l) >= c l^2`` on the closed box [0, 1/10] (endpoint l = 0 included), with
``k = 2`` and the order-5 Taylor upper bound.  The true minimum of ``(l - log(1+l))/l^2`` there
is 0.468982... at l = 1/10.  The forgery ``c = 47/100`` is FALSE by ~1/1000; Layer 1 refuses
it with a located violation, and the adapter mints it with the sign checks skipped, so the
forged Lean differs from the true twin (``c = 117/250``) only in the constant -- and the box
lemma ``0 <= H`` cannot close (``H(1/10) < 0``).

(2) The two-variable control: ``l (x - l)^2 + l^2 x - m l >= 0`` on [0, 1/2] x [1/4, 1], whose
cofactor ``H = (x - l)^2 + l x - m`` has minimum ``3/64 - m`` at (1/8, 1/4).  The forgery
``m = 3/64 + 1/1000`` is FALSE by 1/1000; the true twin ``m = 3/64 - 1/1000`` compiles.

Offline tests: registration, the exact falsity of both forged claims, and the shared skeleton.
Lean-gated tests (skipped unless ``examples/factored_endpoint_enclosure/lean`` is built): both
controls through ``generic_negative_control`` (FALSE rejected, TRUE twin clean).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import mpmath as mp  # noqa: E402
import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_factored_endpoint_enclosure import (  # noqa: E402
    L_SYM,
    LOG_SHARP_FALSE_SPEC,
    SYNTH2_MARGIN_FALSE_SPEC,
    X_SYM,
    FactoredEndpointRefusal,
    factored_endpoint_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)
from telperion.negctrl_adapters.adapter_factored_endpoint_enclosure import (  # noqa: E402
    TWO_VAR_ADAPTER,
)

_ENV = Path(__file__).resolve().parents[1] / "examples" / "factored_endpoint_enclosure" / "lean"
mp.mp.dps = 40


def _adapter():
    ad = registered_adapters().get("FactoredEndpointEnclosureEmitter")
    assert ad is not None, "no adapter registered for FactoredEndpointEnclosureEmitter"
    return ad


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["FactoredEndpointEnclosureEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_log_claim_is_refused_and_genuinely_false_by_a_thousandth():
    with pytest.raises(FactoredEndpointRefusal, match="FALSE"):
        factored_endpoint_certificate(**LOG_SHARP_FALSE_SPEC)
    cert = _adapter().make_false_cert()
    assert not cert.checked and len(cert.boxes) == 1 and not cert.boxes[0].ok()
    tenth = mp.mpf(1) / 10
    F = tenth - mp.log(1 + tenth) - mp.mpf(47) / 100 * tenth ** 2
    assert F < 0                                            # the claim is FALSE
    deficit = mp.mpf(47) / 100 - (tenth - mp.log(1 + tenth)) / tenth ** 2
    assert mp.mpf(1) / 1000 < deficit < mp.mpf(11) / 10000  # by ~1/1000
    assert cert.H.subs(L_SYM, sp.Rational(1, 10)) < 0       # the forged box lemma is false
    true = _adapter().make_true_cert()
    assert true.checked and true.boxes[0].ok()


def test_false_two_variable_claim_is_refused_and_genuinely_false():
    with pytest.raises(FactoredEndpointRefusal, match="FALSE"):
        factored_endpoint_certificate(**SYNTH2_MARGIN_FALSE_SPEC)
    cert = TWO_VAR_ADAPTER.make_false_cert()
    pt = {L_SYM: sp.Rational(1, 8), X_SYM: sp.Rational(1, 4)}
    assert cert.H.subs(pt) == sp.Rational(-1, 1000)        # false by exactly 1/1000
    assert not all(b.ok() for b in cert.boxes)
    assert TWO_VAR_ADAPTER.make_true_cert().H.subs(pt) == sp.Rational(1, 1000)


def test_twins_share_the_skeleton():
    ad = _adapter()
    f = ad.emit_call(ad.make_false_cert(), "fee_twin")
    t = ad.emit_call(ad.make_true_cert(), "fee_twin")
    for line in ("theorem factored_endpoint_core", "theorem fee_twin :",
                 "theorem fee_twin_b0_H", "upper_5",
                 "theorem fee_twin_fac"):
        assert line in f and line in t, line
    assert "(-47 / 100 : ℝ)" in f and "(-117 / 250 : ℝ)" in t
    assert "sorry" not in f and "sorry" not in t


def _ready() -> bool:
    from lean_env import lean_env_ready
    return lean_env_ready(_ENV)


@pytest.mark.skipif(not _ready(), reason="factored_endpoint_enclosure Lean env not built")
@pytest.mark.parametrize("which", ["one_variable", "two_variable"])
def test_kernel_rejects_forgery_and_accepts_twin(which):
    ad = _adapter() if which == "one_variable" else TWO_VAR_ADAPTER
    res = generic_negative_control(ad, env_dir=str(_ENV))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay is True
