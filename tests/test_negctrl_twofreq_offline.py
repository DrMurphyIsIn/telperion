"""Negative control for TwoFreqOfflineEmitter -- the equal-modulus forgery.

The emitted theorem NEGATES real-rootedness, and the only load-bearing arithmetic is
the EXACT inequality |c1|^2 != |c2|^2.  Forge a cert whose two moduli are EQUAL (the
selfinversive_rigidity TRUE instance c1 = 3/5 + 4/5 i, c2 = 1) and the final norm_num
is asked to derive False from (1 : R) = 1: it cannot, and the kernel rejects.

The twins are rendered in BRIDGE-HYPOTHESIS mode (the island iff carried as an explicit
hypothesis, twoFreq copied verbatim into the prelude) because the harness elaborates
against plain Mathlib -- same discipline as adapter_bragg_floor, which likewise tests
only the emitter's own arithmetic.  The hypothesis-free island theorem is what the
`twofreq-offline-compiles` CI job builds.

These tests are OFFLINE (string level); the kernel run itself is driven by the generic
harness in test_certificate_sensitivity / CI.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion.negctrl_adapters  # noqa: F401, E402  (registers adapters)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("TwoFreqOfflineEmitter")
    assert ad is not None, "no adapter registered for TwoFreqOfflineEmitter"
    return ad


def test_adapter_is_registered():
    _adapter()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["TwoFreqOfflineEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_prelude_carries_twofreq_verbatim():
    ad = _adapter()
    assert "def twoFreq (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) : ℂ :=" in ad.prelude
    assert "open Quasicrystal" in ad.prelude
    assert ad.imports_line == "import Mathlib"


def test_true_twin_is_the_p2_euler_factor_and_carries_the_bridge_hypothesis():
    ad = _adapter()
    txt = ad.emit_call(ad.make_true_cert(), "tfo_twin")
    assert "hiff :" in txt, "bridge-hypothesis mode required (plain-Mathlib elaboration)"
    assert "rw [hiff _ _ _ _ hc1 hc2 hlam]" in txt
    assert "((-(1 / Real.sqrt 2) : ℝ) : ℂ)" in txt
    assert "(-(Real.log 2))" in txt
    # normSq 1 vs 1/2 -- the genuinely unequal moduli.
    assert "= (1 : ℝ) := by" in txt and "= ((1 / 2) : ℝ) := by" in txt
    assert "sorry" not in txt


def test_false_twin_differs_only_in_the_coefficient_and_frequency_literals():
    ad = _adapter()
    true_txt = ad.emit_call(ad.make_true_cert(), "tfo_twin")
    false_txt = ad.emit_call(ad.make_false_cert(), "tfo_twin")
    assert true_txt != false_txt
    # Same skeleton: identical theorem shape, identical bridge hypothesis, identical
    # closing move.  Only the literals move.
    for line in ("theorem tfo_twin", "hiff :", "rw [hiff _ _ _ _ hc1 hc2 hlam]",
                 "intro h", "rw [hns1, hns2] at h2", "norm_num at h2"):
        assert line in true_txt and line in false_txt, line
    # The forged cert is the selfinversive_rigidity TRUE instance: EQUAL moduli.
    assert "(3 / 5) + (4 / 5) * Complex.I" in false_txt
    assert "(3 / 5) + (4 / 5) * Complex.I" not in true_txt


def test_false_twin_statement_is_genuinely_false():
    """Pin the arithmetic so the forgery can never rot into a merely-hard-for-norm_num
    truth: |3/5 + 4/5 i|^2 = 1 = |1|^2 exactly, so by twoFreq_realRooted_iff the sum IS
    real-rooted and the emitted negation is FALSE."""
    from fractions import Fraction as Fr
    assert Fr(3, 5) ** 2 + Fr(4, 5) ** 2 == Fr(1) == Fr(1) ** 2 + Fr(0) ** 2
    # And the emitter's own Layer-1 self-check refuses to build it.
    import pytest

    from telperion.emit_twofreq_offline import gauss, rat, twofreq_offline_certificate
    with pytest.raises(ValueError, match="equal modulus"):
        twofreq_offline_certificate(c1=gauss("3/5", "4/5"), c2=gauss(1, 0),
                                    lam1=rat(1), lam2=rat(2))


def test_false_twin_final_step_has_nothing_to_close_with():
    """The forged proof reaches `h2 : (1 : R) = 1` and must derive False from it."""
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "tfo_twin")
    assert "= (1 : ℝ) := by" in false_txt
    assert "((1 / 2) : ℝ)" not in false_txt
