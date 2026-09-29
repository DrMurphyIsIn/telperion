"""Negative control for GapBudgetMultiplicityEmitter -- a forged gap bound in the max-product
N = 3t + 2 budget.

The honest certificate proves, for parts with sum 3t + 2 and product at least 2 * 3^t, that there
is at most one 2.  The forgery raises the certified lower bound on gamma(2) = 2/3 log 3 - log 2
(= 0.03926...) to 1/20, above theta_hi, so the derived cap at 2 is 0 and the main theorem claims
`count 2 = 0`.  That is FALSE, not merely unproved: the benchmark {2} + 3^t satisfies every
hypothesis and has one 2.  The TRUSTED Lean kernel is the arbiter: the forged enclosure
`1/20 < 2/3 log 3 - log 2` cannot be reached by its linarith.

These tests are OFFLINE (string/arithmetic level).  The kernel run happens through the generic
harness in `test_certificate_sensitivity` (lean-gated; it uses
`examples/gap_budget_multiplicity/lean`); the lane ran it by hand: FALSE twin rejected at the
forged enclosure, TRUE twin clean.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import mpmath as mp  # noqa: E402
import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_gap_budget_multiplicity import (  # noqa: E402
    GapBudgetRefusal,
    gap_budget_multiplicity_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import registered_adapters  # noqa: E402
from telperion.negctrl_adapters.adapter_gap_budget_multiplicity import (  # noqa: E402
    FORGED_G2,
    make_false_cert_cap,
    spec,
)
from telperion.negative_control import assert_kernel_rejects  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_env import lean_env_ready  # noqa: E402

_ENV = Path(__file__).resolve().parents[1] / "examples" / "gap_budget_multiplicity" / "lean"


def _adapter():
    ad = registered_adapters().get("GapBudgetMultiplicityEmitter")
    assert ad is not None, "no adapter registered for GapBudgetMultiplicityEmitter"
    return ad


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["GapBudgetMultiplicityEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    with pytest.raises(GapBudgetRefusal, match="REFUSED"):
        gap_budget_multiplicity_certificate(**spec(), gap_lo={2: FORGED_G2})
    cert = _adapter().make_false_cert()
    assert dict(cert.caps)[2] == 0 and cert.atoms[1].g == FORGED_G2


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """The benchmark {2} + 3^t meets every hypothesis (sum 3t + 2, value log 2 + t log 3) and
    has one 2, so `count 2 = 0` fails at every t; and gamma(2) < 1/20 at 50 digits."""
    mp.mp.dps = 50
    assert 2 * mp.log(3) / 3 - mp.log(2) < mp.mpf(1) / 20
    true = _adapter().make_true_cert()
    assert dict(true.caps)[2] == 1
    assert dict(true.bench)[2] == 1                           # the benchmark's own 2
    assert true.theta_hi < FORGED_G2                           # so the forged cap is 0


def test_twins_differ_only_in_the_forged_literals():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "gb_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "gb_twin")
    assert "sorry" not in false_txt and "sorry" not in true_txt
    assert "(1 / 20 : ℝ) < 2 / 3 * Real.log 3 - Real.log 2" in false_txt
    assert "(39261 / 1000000 : ℝ) < 2 / 3 * Real.log 3 - Real.log 2" in true_txt
    assert "m.count 2 = 0" in false_txt and "m.count 2 ≤ 1" in true_txt
    # In the true twin the theta enclosure IS the gap-2 enclosure (same expression, same
    # bracket: theta = gamma(2)) and is shared; the forgery breaks the sharing, so the false twin
    # carries one extra theta theorem.  Undo exactly that and the forged literals:
    import re
    back = re.sub(r"/-- `gb_twin_theta_enc`.*?\n\n", "", false_txt, flags=re.S)
    back = (back.replace("gb_twin_theta_enc", "gb_twin_gap_2_enc")
            .replace("(1 / 20 : ℝ)", "(39261 / 1000000 : ℝ)")
            .replace("at least 1/20", "at least 39261/1000000")
            .replace("m.count 2 = 0", "m.count 2 ≤ 1")
            .replace("Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 2 _ gb_twin_gap_2) "
                     "(by norm_num))",
                     "gapBudget_nat_cap 1 (by norm_num) (hc 2 _ gb_twin_gap_2) (by norm_num)"))

    def strip(txt):      # the fold-slack comment quotes the (forged) claim
        return [ln for ln in txt.splitlines() if not ln.startswith("    Exact fold")]
    assert strip(back) == strip(true_txt)


def test_true_twin_is_the_dogfood_instance():
    true = _adapter().make_true_cert()
    assert true.theta == sp.expand(true.theta)
    assert dict(true.caps) == {1: 0, 2: 1, 4: 0} and true.tail_cap == 0


def test_cap_forgery_keeps_every_bound_honest():
    """The second forgery moves ONLY the derived cap: the gap bounds and theta_hi are honest,
    and floor(theta_hi / g_2) = 1, not the forged 0."""
    true = _adapter().make_true_cert()
    forged = make_false_cert_cap()
    assert forged.atoms == true.atoms and forged.theta_hi == true.theta_hi
    g2 = true.atoms[1].g
    assert dict(forged.caps)[2] == 0 and not (true.theta_hi < 1 * g2)
    txt = _adapter().emit_call(forged, "gb_cap")
    assert "Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 2 _ gb_cap_gap_2)" in txt


@pytest.mark.skipif(not lean_env_ready(_ENV), reason="no built Lean env for the dogfood")
def test_cap_forgery_is_kernel_rejected():
    txt = "import Mathlib\n" + _adapter().emit_call(make_false_cert_cap(), "gb_cap") + "\n"
    assert assert_kernel_rejects(txt, "gb_cap", env_dir=str(_ENV))
