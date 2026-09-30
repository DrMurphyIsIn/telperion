"""Negative controls for SingleCrossingLadderEmitter -- a wrong breakpoint bracket and a double
crossing.

(1) The registered adapter's instance is one pair of the arm ladder (A_3 against A_4).  Its
forgery shifts the bracket of lambda_3 = 0.4305018... two grid steps right, to
(0.43052, 0.43053): the claim `D(lo) > 0` is then FALSE, Layer 1 refuses it, and the adapter
mints the certificate with the sign checks skipped, so the forged Lean differs from the true
twin only in the bracket -- and the value theorem's `linarith` over the (honest) log-atom
brackets cannot reach the false sign.

(2) The double-crossing control: the synthetic family whose difference crosses zero near 0.971
AND near 4.315, claimed single on [0, oo).  Layer 1 refuses (N has two sign changes); the forged
certificate's tail cell asserts `N < 0` on `[3/8, oo)`, false past N's second root, and its
`linarith` cannot close.  The true twin is the same family on [0, 2], where the crossing is
single.

Offline tests: registration, the exact falsity of both forged claims, and the shared skeleton.
Lean-gated tests (skipped unless `examples/single_crossing_ladder/lean` is built): both controls
through `generic_negative_control` (FALSE rejected, TRUE twin clean).

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
from telperion.emit_single_crossing_ladder import (  # noqa: E402
    ARM_PAIR3_WRONG_BRACKET_SPEC,
    DOUBLE_DIP_UNBOUNDED_SPEC,
    SingleCrossingRefusal,
    single_crossing_ladder_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)
from telperion.negctrl_adapters.adapter_single_crossing_ladder import (  # noqa: E402
    DOUBLE_DIP_ADAPTER,
)

_ENV = Path(__file__).resolve().parents[1] / "examples" / "single_crossing_ladder" / "lean"
mp.mp.dps = 40


def _adapter():
    ad = registered_adapters().get("SingleCrossingLadderEmitter")
    assert ad is not None, "no adapter registered for SingleCrossingLadderEmitter"
    return ad


def _D(cert, x):
    p = cert.pairs[0]
    return sum(mp.mpf(k.p) / k.q * mp.log(1 + mp.mpf(b.p) / b.q * x) for k, b in p.dterms)


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["SingleCrossingLadderEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_false_bracket_is_refused_by_layer_one_and_genuinely_false():
    with pytest.raises(SingleCrossingRefusal):
        single_crossing_ladder_certificate(**ARM_PAIR3_WRONG_BRACKET_SPEC)
    cert = _adapter().make_false_cert()
    assert not cert.checked
    lo = cert.pairs[0].lo
    assert lo == sp.Rational(43052, 100000)
    assert _D(cert, mp.mpf(lo.p) / lo.q) < 0            # the forged D(lo) > 0 is FALSE
    true = _adapter().make_true_cert()
    tlo = true.pairs[0].lo
    assert _D(true, mp.mpf(tlo.p) / tlo.q) > 0


def test_double_crossing_is_refused_and_genuinely_double():
    with pytest.raises(SingleCrossingRefusal, match="2 sign changes"):
        single_crossing_ladder_certificate(**DOUBLE_DIP_UNBOUNDED_SPEC)
    cert = DOUBLE_DIP_ADAPTER.make_false_cert()
    D = lambda x: _D(cert, x)  # noqa: E731
    z1, z2 = mp.findroot(D, 0.97), mp.findroot(D, 4.3)
    assert 0.97 < z1 < 0.98 and 4.3 < z2 < 4.33          # two zeros on (0, oo)
    assert D(mp.mpf(10)) > 0                              # positive again after the second
    tail = cert.pairs[0].right[-1].pc
    assert tail.t is None and not tail.ok()               # the forged tail cell is false


def test_twins_share_the_skeleton():
    ad = _adapter()
    f = ad.emit_call(ad.make_false_cert(), "scl_twin")
    t = ad.emit_call(ad.make_true_cert(), "scl_twin")
    for line in ("theorem scl_twin : ∃ Λ : ℕ → ℝ,", "theorem single_crossing_core",
                 "theorem scl_twin_p3_vlo", "theorem ladder_core"):
        assert line in f and line in t, line
    assert "(10763 / 25000 : ℝ)" in f and "(861 / 2000 : ℝ)" in t
    assert "sorry" not in f and "sorry" not in t


def _ready() -> bool:
    from lean_env import lean_env_ready
    return lean_env_ready(_ENV)


@pytest.mark.skipif(not _ready(), reason="single_crossing_ladder Lean env not built")
@pytest.mark.parametrize("which", ["wrong_bracket", "double_crossing"])
def test_kernel_rejects_forgery_and_accepts_twin(which):
    ad = _adapter() if which == "wrong_bracket" else DOUBLE_DIP_ADAPTER
    res = generic_negative_control(ad, env_dir=str(_ENV))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay is True
