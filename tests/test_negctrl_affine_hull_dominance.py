"""Negative control for AffineHullDominanceEmitter -- a wrong maximum behind a bad witness.

The adapter's instance is the Randic-weighted matching sum on trees with at most 6 vertices
(true M_6 = 29/8).  Its forgery removes every maximizing root bundle from the kept lists,
gives the candidates that produced them a convex-combination witness that does NOT dominate
them, and claims the second-best value as M_6.  The claim is then FALSE (the true maximizer
beats it), Layer 1 refuses it, the forged value is still attained by a tree (so the listed-
maximizer check passes), and the ONLY wrong objects are the forged witnesses, which the
kernel-decided checker `Cert.Valid` evaluates to false.  The TRUSTED Lean kernel is the
arbiter.

These tests are OFFLINE: registration, the exact falsity of the forged claim, the exact reason
the forged Lean cannot compile (a failing witness and nothing else), and the shared skeleton.
The kernel run is `test_certificate_sensitivity::test_generic_negative_control_holds`
(lean-gated; it uses `examples/affine_hull_dominance/lean`); the lane ran it by hand (FALSE
twin rejected at `decide` on `Cert.Valid`, TRUE twin clean, standard axioms).

conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_affine_hull_dominance import (  # noqa: E402
    cand_bundle,
    eval_pi,
    verify_certificate,
    witness_ok,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import registered_adapters  # noqa: E402
from telperion.negctrl_adapters.adapter_affine_hull_dominance import rooted_trees  # noqa: E402


def _adapter():
    ad = registered_adapters().get("AffineHullDominanceEmitter")
    assert ad is not None, "no adapter registered for AffineHullDominanceEmitter"
    return ad


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["AffineHullDominanceEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    cert = _adapter().make_false_cert()
    assert not cert.checked
    with pytest.raises(ValueError, match="REFUSED"):
        verify_certificate(cert)


def test_false_claim_is_genuinely_false_not_merely_unproved():
    ad = _adapter()
    false, true = ad.make_false_cert(), ad.make_true_cert()
    N = false.N
    forged, honest = false.value(N), true.value(N)
    assert honest == Fraction(29, 8) and forged < honest
    best = max(eval_pi(true.rec, t) for t in rooted_trees(N))
    assert best == honest                    # brute force: some tree beats the forged claim
    # ... and the forged value is attained, so the listed-maximizer check is not what fails
    assert all(eval_pi(false.rec, t) == forged for t in dict(false.maximizers)[N])


def test_only_the_forged_witnesses_fail():
    false = _adapter().make_false_cert()
    true = _adapter().make_true_cert()
    rec, N = false.rec, false.N
    KB, KH = false.kb(), false.kh()
    failing = []
    for (s, c), wits in false.WB:
        cands = [x for x, _ in cand_bundle(rec, KB, KH, s, c)]
        for x, w in zip(cands, wits):
            if not witness_ok(KB.get((s, c), ()), x, w):
                failing.append((s, c))
    assert failing and all(s == N - 1 for s, _ in failing)
    # every value/root-bound check still passes for the forged claim
    for k in range(1, N):
        for p in KB.get((N - 1, k), ()):
            assert rec.root(k, p) <= false.value(N)
    verify_certificate(true)


def test_twins_share_the_skeleton():
    ad = _adapter()
    f = ad.emit_call(ad.make_false_cert(), "ahd_twin")
    t = ad.emit_call(ad.make_true_cert(), "ahd_twin")
    for line in ("theorem ahd_twin_valid : ahd_twin_C.Valid ahd_twin_R 6 (0 : Fin 2) := by "
                 "decide +kernel", "theorem kept_of_pi_eq", "theorem isGreatest_pi",
                 "theorem ahd_twin :"):
        assert line in f and line in t, line
    assert "(29 / 8 : ℚ)" in t and "(29 / 8 : ℚ)" not in f
    assert "sorry" not in f and "sorry" not in t
