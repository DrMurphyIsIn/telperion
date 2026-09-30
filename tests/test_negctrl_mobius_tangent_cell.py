"""Negative control for MobiusTangentCellEmitter -- the log-mean cell with its constant raised.

The TRUE twin states `-2 + 0 x + log(0 + 1 x) + 4/(1 + 1 x) <= 0` on [1/4, 1/2] (the
logarithmic-mean bound `log x <= 2 (x - 1)/(x + 1)`), one convex cell at t = 7/16.  The
FALSE twin moves the constant to -19/10: `F(1/2) = log(1/2) - 2/3 + 1/10 = 0.0735... > 0`,
so the statement is FALSE, not merely unproved.  The TRUSTED Lean kernel is the arbiter: the
cell's closing `linarith` is off by exactly 1/10.

These tests are OFFLINE (string/arithmetic level): they pin the adapter registration, the
exact falsity of the forgery (decided with an exact rational upper bound for log 2 against
Mathlib's own `Real.log_two_gt_d9`), the byte-level relationship between the twins, and the
registry declaration.  The kernel run happens through the generic harness in
`test_certificate_sensitivity` / CI (lean-gated); the lane ran it by hand on the dogfood
project (FALSE twin rejected at the cell `linarith`, TRUE twin clean with
[propext, Classical.choice, Quot.sound]).

conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_mobius_tangent_cell import (  # noqa: E402
    LOG2_LO,
    MobiusTangentRefusal,
    check_cell,
    mobius_tangent_cell_certificate,
    verify_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("MobiusTangentCellEmitter")
    assert ad is not None, "no adapter registered for MobiusTangentCellEmitter"
    return ad


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["MobiusTangentCellEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    cert = _adapter().make_false_cert()
    assert cert.problem.a == Fr(-19, 10)
    with pytest.raises(MobiusTangentRefusal):
        verify_certificate(cert)
    with pytest.raises(MobiusTangentRefusal):
        check_cell(cert.problem, cert.cells[0])
    with pytest.raises(MobiusTangentRefusal, match="FALSE"):
        mobius_tangent_cell_certificate(cert.problem, max_depth=6)


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """At x = 1/2: F = -19/10 - log 2 + 4/(3/2).  With Mathlib's log 2 < 0.6931471808
    and > 0.6931471803, F > -19/10 - 0.6931471808 + 8/3 > 0 exactly."""
    lo_F = Fr(-19, 10) - Fr(6931471808, 10 ** 10) + Fr(8, 3)
    assert lo_F > 0
    assert LOG2_LO < Fr(6931471808, 10 ** 10)
    # and the TRUE twin at the same point is negative with room to spare
    assert Fr(-2) - Fr(6931471803, 10 ** 10) + Fr(8, 3) < 0


def test_true_twin_is_accepted_by_layer_one():
    true = _adapter().make_true_cert()
    verify_certificate(true)
    assert len(true.cells) == 1
    c = true.cells[0]
    assert c.mode == "convex" and c.t == Fr(7, 16) and c.bounds[0].n < 0


def test_twins_differ_only_in_the_forged_constant():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "mt_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "mt_twin")
    assert "(-19 / 10) + (0) * x" in false_txt and "(-2) + (0) * x" in true_txt
    assert false_txt.replace("(-19 / 10) + (0) * x", "(-2) + (0) * x") == true_txt
    for txt in (false_txt, true_txt):
        assert "sorry" not in txt and "native_decide" not in txt
        assert "theorem mt_twin (x : ℝ)" in txt
