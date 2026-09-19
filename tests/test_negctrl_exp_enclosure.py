"""Negative control for ExpEnclosureEmitter -- the too-tight (hence FALSE) exp bracket.

The emitted proof reaches its claimed bracket from `Real.exp_bound`'s exact rational Taylor
box by `linarith`.  Corrupt the claim so the box no longer implies it and the proof cannot
close: the TRUSTED Lean kernel is the arbiter.  The forgery here is not merely unprovable, it
is FALSE -- at `x = 1/10` the claimed `hi = 1105/1000` sits strictly BELOW `e^(1/10)` itself.

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
from telperion.emit_exp_enclosure import (  # noqa: E402
    exp_enclosure_certificate,
    taylor_box,
)
from telperion.emitter_sensitivity import (  # noqa: E402
    NEG_CONTROL_ADAPTER,
    REGISTRY,
)
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("ExpEnclosureEmitter")
    assert ad is not None, "no adapter registered for ExpEnclosureEmitter"
    return ad


def test_adapter_is_registered():
    _adapter()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["ExpEnclosureEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    """Layer 1 would never mint the forgery: the adapter hand-builds the frozen dataclass."""
    cert = _adapter().make_false_cert()
    with pytest.raises(ValueError, match="REFUSED"):
        exp_enclosure_certificate(cert.x, cert.lo, cert.hi, mode=cert.mode, n=cert.n)


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """Pin the arithmetic: the forged hi is BELOW the order-6 Taylor lower endpoint, so
    `exp (1/10) <= hi` is false -- the forgery can never rot into a hard-but-true claim."""
    cert = _adapter().make_false_cert()
    box_lo, box_hi = taylor_box(cert.x, cert.n)
    assert cert.hi < box_lo, (cert.hi, box_lo)
    # and the true twin does contain the same box
    true_cert = _adapter().make_true_cert()
    assert true_cert.lo <= box_lo and box_hi <= true_cert.hi


def test_true_twin_is_accepted_by_layer_one():
    cert = _adapter().make_true_cert()
    ok = exp_enclosure_certificate(cert.x, cert.lo, cert.hi, mode=cert.mode, n=cert.n)
    assert ok.n == cert.n and ok.lo == cert.lo and ok.hi == cert.hi


def test_twins_differ_only_in_the_claimed_bracket():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "exp_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "exp_twin")
    # Same point, same order, same tactic script -- only the two literals move.
    for line in ("have hb := Real.exp_bound hx (n := 6)",
                 "simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb",
                 "norm_num [Nat.factorial] at h1 ⊢; linarith"):
        assert line in false_txt and line in true_txt
    # 1105/1000 renders in lowest terms as 221/200 (rat_lean canonicalizes).
    assert "(221 / 200)" in false_txt and "(221 / 200)" not in true_txt
    assert "(110517 / 100000)" in true_txt and "(110517 / 100000)" not in false_txt
    assert "sorry" not in false_txt and "sorry" not in true_txt


def test_true_twin_bracket_is_a_real_decimal_enclosure_of_e_tenth():
    """Sanity: 1.10517 <= e^(1/10) <= 1.10518 (the honest twin's claim)."""
    import math

    lo, hi = Fraction(110517, 100000), Fraction(110518, 100000)
    assert float(lo) <= math.exp(0.1) <= float(hi)
    assert sp.Rational(1105, 1000) < sp.Rational(110517, 100000)
