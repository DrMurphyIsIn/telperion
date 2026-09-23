"""Negative control for EnclosureTreeEmitter -- the pi-face rate instance one past the truth.

The emitted root theorem for `LiLadderHeight`'s side condition is proved by `linarith` from the
pi atom `6283 / 2000 < Real.pi` (`Real.pi_gt_d4`), so its stated lower bound is the load-bearing
content.  Move it (and the cap it licenses) one past the truth and the statement is not merely
unproved, it is FALSE: `6000 pi = 18849.5559...`, so `18850 < 3 * pi * 4000 / 2` fails, and the
rate statement fails at `n = 18849`.  The TRUSTED Lean kernel is the arbiter: the root `linarith`
cannot reach `18850`.

These tests are OFFLINE (string/arithmetic level): they pin the adapter registration, the exact
falsity of the forgery (decided in exact rationals against Mathlib's own d20 upper bound), the
byte-level relationship between the twins, and the registry declaration.  The kernel run happens
through the generic harness in `test_certificate_sensitivity` / CI (lean-gated); the lane ran it
by hand on the li_positivity island (FALSE twin rejected, TRUE twin clean).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_enclosure_tree import (  # noqa: E402
    PI_LADDER,
    enclosure_tree_certificate,
    lean_expr,
)
from telperion.emitter_sensitivity import (  # noqa: E402
    NEG_CONTROL_ADAPTER,
    REGISTRY,
)
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("EnclosureTreeEmitter")
    assert ad is not None, "no adapter registered for EnclosureTreeEmitter"
    return ad


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["EnclosureTreeEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    """Layer 1 would never mint the forgery, at any rung of the ladder: the adapter hand-builds it."""
    cert = _adapter().make_false_cert()
    assert cert.root.lo == 18850 and cert.rate_cap == 18849
    tree_root = cert.root
    assert lean_expr(tree_root) == "3 * Real.pi * 4000 / 2"
    from telperion.emit_enclosure_tree import (
        node_div, node_mul, node_pi, node_rat,
    )
    tree = node_div(node_mul(node_mul(node_rat(3), node_pi()), node_rat(4000)), node_rat(2))
    with pytest.raises(ValueError, match="REFUSED"):
        enclosure_tree_certificate(tree, rate_cap=18849)
    with pytest.raises(ValueError, match="REFUSED"):
        enclosure_tree_certificate(tree, lo=18850)


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """Decide the falsity EXACTLY: Mathlib's own `pi < 3.14159265358979323847` gives
    `3 * pi * 4000 / 2 < 18849.5559...`, strictly below the forged 18850 -- so no proof of the
    forged statement exists, whatever the tactic."""
    pi_hi = PI_LADDER[20][1]
    assert 3 * pi_hi * 4000 / 2 < 18850
    assert 3 * pi_hi * 4000 / 2 < sp.Rational(18849556, 1000)      # 6000 pi < 18849.556
    # the forged rate statement at n = 18849 needs 18850 <= 6000 pi: false for the same reason
    cert = _adapter().make_false_cert()
    assert cert.rate_cap + 1 == 18850
    # and the TRUE twin's lower bound is Mathlib's d4 rung, exactly tight at the cap
    true = _adapter().make_true_cert()
    assert true.root.lo == 3 * PI_LADDER[4][0] * 4000 / 2 == true.rate_cap + 1 == 18849


def test_true_twin_is_accepted_by_layer_one_and_is_the_dogfood_instance():
    true = _adapter().make_true_cert()
    assert true.pi_digits == 4 and true.rate_cap == 18848
    assert true.root.lo_strict and true.root.hi_strict


def test_twins_differ_only_in_the_forged_literals():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "enc_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "enc_twin")
    # same tactic script
    for line in ("  constructor <;> linarith [Real.pi_gt_d4, Real.pi_lt_d4]\n",
                 "  obtain ⟨h0lo, h0hi⟩ := enc_twin_n0\n",
                 "  constructor <;> linarith\n",
                 "  obtain ⟨hlo, _hhi⟩ := enc_twin\n",
                 "  have hn' : (n : ℝ) ≤ ("):
        assert line in false_txt and line in true_txt, line
    # only the root lower bound, the cap, and the header text that quotes them move
    assert "(18850 : ℝ) < 3 * Real.pi * 4000 / 2" in false_txt
    assert "(18849 : ℝ) < 3 * Real.pi * 4000 / 2" in true_txt
    back = (false_txt
            .replace("(18850 : ℝ) <", "(18849 : ℝ) <")
            .replace("n ≤ 18849", "n ≤ 18848")
            .replace("(18849 : ℝ) := by exact_mod_cast", "(18848 : ℝ) := by exact_mod_cast")
            .replace("slack (-1, 0)", "slack (0, 0)")
            .replace("18850 is at least 18849 + 1 = 18850", "18849 is at least 18848 + 1 = 18849")
            .replace("every `n <= 18849`", "every `n <= 18848`"))
    assert back == true_txt
    assert "sorry" not in false_txt and "sorry" not in true_txt


def test_false_twin_states_the_false_theorems_verbatim():
    ad = _adapter()
    txt = ad.emit_call(ad.make_false_cert(), "negctrl_forged_false")
    assert ("theorem negctrl_forged_false :\n"
            "    (18850 : ℝ) < 3 * Real.pi * 4000 / 2 ∧ 3 * Real.pi * 4000 / 2 < (94248 / 5 : ℝ)"
            " := by\n") in txt
    assert ("theorem negctrl_forged_false_rate (n : ℕ) (hn : n ≤ 18849) :\n"
            "    (n + 1 : ℝ) ≤ 3 * Real.pi * 4000 / 2 := by\n") in txt
