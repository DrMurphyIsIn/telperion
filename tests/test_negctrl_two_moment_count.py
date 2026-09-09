"""Davenport–Heilbronn negative control for the HermitianMomentInertia family.

The zeta-23 two-moment method is *blind to RH by construction*: the
Davenport–Heilbronn function satisfies the same functional-equation/moment
structure as ζ yet has off-critical-line zeros, so the method can never certify
more than its two moments support.  The honest kernel-backed control for
``TwoMomentCountEmitter`` is therefore the **over-claim forgery**: keep the
emitter's own rendering (hypotheses untouched, κ = 4/3 at λ = 1) and inflate
ONLY the concluded on-line proportion constant from ``2 − κ = 2/3`` to ``1``
("all zeros counted") — the exact claim DH refutes.  The forged implication is
genuinely false (N = 3, trGh = 3, frGh = 4, R1 = R2 = NII = B = 0 gives
``count = 2`` satisfying the hypotheses while ``1·3 ≤ 2`` fails), so the kernel
must reject it; the untouched twin must compile.

These tests are OFFLINE (string-level): they pin the adapter's registration,
the byte-level relationship between the twins, and the registry declaration.
The kernel run itself happens through the generic harness in
``test_certificate_sensitivity`` / CI (lean-gated).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion.negctrl_adapters  # noqa: F401, E402  (registers adapters)
from telperion.negative_control_harness import registered_adapters  # noqa: E402
from telperion.emitter_sensitivity import (  # noqa: E402
    NEG_CONTROL_ADAPTER,
    REGISTRY,
)


def _adapter():
    ad = registered_adapters().get("TwoMomentCountEmitter")
    assert ad is not None, "no adapter registered for TwoMomentCountEmitter"
    return ad


def test_adapter_is_registered():
    _adapter()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["TwoMomentCountEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_true_twin_is_the_emitters_own_rendering():
    ad = _adapter()
    txt = ad.emit_call(ad.make_true_cert(), "dh_true_twin")
    # The honest λ = 1, c = 2 certificate: κ = 4/3, proportion constant 2 − κ.
    assert "theorem dh_true_twin" in txt
    assert "(2 - (4 / 3)) * N" in txt
    assert "nlinarith" in txt
    # Hypothesis side must carry the same κ (the moments the analytic side supplies).
    assert "(4 / 3) * N + R2" in txt


def test_false_twin_differs_only_in_the_concluded_constant():
    ad = _adapter()
    true_txt = ad.emit_call(ad.make_true_cert(), "dh_twin")
    false_txt = ad.emit_call(ad.make_false_cert(), "dh_twin")
    # The forged claim: proportion constant inflated 2 − κ → 1; nothing else moves.
    assert "(2 - (4 / 3)) * N" in true_txt and "(2 - (4 / 3)) * N" not in false_txt
    assert "1 * N" in false_txt
    assert false_txt == true_txt.replace("(2 - (4 / 3)) * N", "1 * N")
    # Hypotheses byte-identical: the DH story is same moments, bigger claim.
    for line in ("htr : N - R1", "hfr : frGh", "h0 :"):
        t = [ln for ln in true_txt.splitlines() if line in ln]
        f = [ln for ln in false_txt.splitlines() if line in ln]
        assert t == f, f"hypothesis line drifted: {line}"


def test_false_twin_statement_is_genuinely_false():
    """Pin the arithmetic counterexample so the forgery can never rot into a
    merely-hard-for-nlinarith truth: N=3, trGh=3, frGh=4, errors=0 satisfies the
    hypotheses with count=2, and the inflated conclusion demands 3 <= 2."""
    from fractions import Fraction as Fr

    N, trGh, frGh, count = Fr(3), Fr(3), Fr(4), Fr(2)
    R1 = R2 = NII = B = Fr(0)
    kappa = Fr(4, 3)
    # Hypotheses (with sqrt-term zeroed by B = 0):
    assert 4 * trGh - frGh - 2 * N - 3 * NII - 0 <= count          # h0
    assert N - R1 <= trGh                                          # htr
    assert frGh <= kappa * N + R2                                  # hfr
    # Honest conclusion holds:
    assert (2 - kappa) * N - (4 * R1 + R2 + 3 * NII) <= count
    # Forged conclusion fails:
    assert not (1 * N - (4 * R1 + R2 + 3 * NII) <= count)
