"""Negative control for PreorderingMultiplierEmitter -- the negative-coefficient (hence FALSE)
preordering certificate.

The emitted `M = 1` proof checks the identity `p = sum c_alpha prod g^alpha` by `ring` and closes
`0 <= p` by folding the cone with `positivity`, which succeeds ONLY because every `c_alpha >= 0`.
Corrupt one sign and the statement is not merely unproved, it is FALSE: `p = x - x^2 - 2 y^2 =
d - B` on the disk `x^2 + y^2 <= x` (the Li generators `d = x - x^2 - y^2`, `B = y^2`) is negative
at `(1/2, 1/2)`, a point of the disk.  The TRUSTED Lean kernel is the arbiter: `positivity` cannot
prove `0 <= d - B`.

The offline tests pin the adapter registration, the exact falsity of the forgery, the byte-level
relationship between the twins and the registry declaration.  The kernel run happens through the
generic harness (`test_certificate_sensitivity`, when its env is built) and, opt-in here, against
the built li_positivity island: `TELPERION_PM_KERNEL=1` (run under the machine's Lean slot lock).

conjecture1_proved = False.
"""
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_preordering_multiplier import (  # noqa: E402
    PreorderingObstruction,
    PreorderingRefusal,
    preordering_multiplier_certificate,
)
from telperion.emitter_sensitivity import (  # noqa: E402
    NEG_CONTROL_ADAPTER,
    REGISTRY,
)
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)
from lean_env import lean_env_ready  # noqa: E402

_LI = Path(__file__).resolve().parents[1] / "examples" / "li_positivity" / "lean"


def _adapter():
    ad = registered_adapters().get("PreorderingMultiplierEmitter")
    assert ad is not None, "no adapter registered for PreorderingMultiplierEmitter"
    return ad


def _layer_one(cert, **kw):
    """Re-submit a hand-minted cert's data to the certifier (Layer 1)."""
    return preordering_multiplier_certificate(
        symbols=cert.symbols, target=cert.target, generators=cert.generators,
        multiplier=(cert.mult_coeff, None, 0), terms=list(cert.terms), **kw)


def test_adapter_is_registered():
    _adapter()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["PreorderingMultiplierEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_cert_is_refused_by_layer_one():
    """Layer 1 would never mint the forgery (a negative coefficient): the adapter hand-builds
    the frozen dataclass."""
    cert = _adapter().make_false_cert()
    assert [c for c, _a in cert.terms] == [1, -1]
    assert cert.identity_residual == 0                     # the identity itself is EXACT
    with pytest.raises(PreorderingRefusal, match="NEGATIVE coefficient"):
        _layer_one(cert)


def test_false_claim_is_located_false_by_layer_one_scan():
    """With a scan box, Layer 1 refuses the forged claim as OBSTRUCTED_AND_LOCATED -- before it
    ever looks at the certificate."""
    cert = _adapter().make_false_cert()
    with pytest.raises(PreorderingObstruction) as ei:
        _layer_one(cert, scan_box={"x": (0, 1), "y": ("-1/2", "1/2")}, scan_steps=20)
    w = ei.value.witness
    assert w["x"] ** 2 + w["y"] ** 2 <= w["x"] and ei.value.value < 0


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """Pin the arithmetic at (1/2, 1/2), exactly: the disk hypothesis holds and p < 0, so the
    forgery can never rot into a hard-but-true claim."""
    cert = _adapter().make_false_cert()
    x, y = cert.symbols
    pt = {x: sp.Rational(1, 2), y: sp.Rational(1, 2)}
    assert (x ** 2 + y ** 2).subs(pt) <= x.subs(pt)        # 1/2 <= 1/2: a point of the disk
    assert cert.target.subs(pt) == sp.Rational(-1, 4)       # p = -1/4 < 0
    # and the true twin's target is d + B, a sum of two nonnegatives on the disk
    tt = _adapter().make_true_cert()
    d, B = (g.expr for g in tt.generators)
    assert sp.expand(tt.target - (d + B)) == 0


def test_true_twin_is_accepted_by_layer_one():
    ok = _layer_one(_adapter().make_true_cert(),
                    scan_box={"x": (0, 1), "y": ("-1/2", "1/2")}, scan_steps=20)
    assert [c for c, _a in ok.terms] == [1, 1] and ok.identity_residual == 0


def test_twins_share_the_tactic_script():
    ad = _adapter()
    false_txt = ad.emit_call(ad.make_false_cert(), "pm_twin")
    true_txt = ad.emit_call(ad.make_true_cert(), "pm_twin")
    for line in ("theorem pm_twin (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :",
                 "  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=",
                 "  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = y ^ 2 :=",
                 "    rw [hde, hBe]\n    ring\n  rw [key]\n  positivity\n"):
        assert line in false_txt and line in true_txt
    # only the target's y^2 coefficient and the cone's sign on B move in the proof
    f_code = false_txt.split("-/\n", 1)[1]
    t_code = true_txt.split("-/\n", 1)[1]
    assert f_code.replace(" - 2 * y ^ 2", "").replace("d - B", "d + B") == t_code
    assert "sorry" not in false_txt and "sorry" not in true_txt


def test_false_twin_states_the_false_theorem_verbatim():
    ad = _adapter()
    txt = ad.emit_call(ad.make_false_cert(), "negctrl_forged_false")
    assert "theorem negctrl_forged_false (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :" in txt
    assert "    0 ≤ x - x ^ 2 - 2 * y ^ 2 := by" in txt
    # the load-bearing step the kernel cannot discharge
    assert "  have key : x - x ^ 2 - 2 * y ^ 2 = d - B := by" in txt
    assert txt.rstrip().endswith("rw [key]\n  positivity")


_KERNEL = os.environ.get("TELPERION_PM_KERNEL") == "1" and lean_env_ready(_LI)


@pytest.mark.skipif(not _KERNEL, reason="opt-in kernel check (TELPERION_PM_KERNEL=1 and a built "
                                        "li_positivity island)")
def test_generic_negative_control_holds_on_the_li_island():
    """The two-sided kernel control: forged FALSE rejected AND the TRUE twin compiles clean."""
    res = generic_negative_control(_adapter(), env_dir=str(_LI))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay is True, res.detail
