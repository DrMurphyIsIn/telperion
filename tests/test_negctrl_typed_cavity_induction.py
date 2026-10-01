"""Negative control for TypedCavityInductionEmitter -- the Balister-Bollobas-Gerke
maximum-degree-3 table with beta lowered below the published beta_3 = 7/27.

The registered adapter's instance is the BBG half-tree recursion (J. Graph Theory 56 (2007)
270-286, recursion (2) at alpha = gamma = 1) with types by root degree and the table c_d of
their (4)-(5).  The forgery lowers beta to 7/27 - 1/1000 and recomputes the table: the claim
`c_T <= c_{d(T)}` is then FALSE (joining two copies of a half-tree at a new root doubles the
excess of c_T over beta - 2/9, which is positive for [3, 2, 1] below beta_3), Layer 1 refuses
it, and the adapter mints the certificate with the sign checks skipped, so the forged Lean
differs from the true twin only in beta and the table -- and the degree-3 point cell's
`norm_num` cannot prove the false rational inequality.

Offline tests: registration, the exact falsity of the forged claim (an explicit half-tree family
whose R_{-1} - beta n passes c_3), and the shared skeleton.  Lean-gated test (skipped unless
`examples/typed_cavity_induction/lean` is built): the control through
`generic_negative_control` (FALSE rejected, TRUE twin clean).

conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_typed_cavity_induction import (  # noqa: E402
    BBG3_LOWERED_SPEC,
    TypedCavityRefusal,
    bbg_c_table,
    typed_cavity_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)

_ENV = Path(__file__).resolve().parents[1] / "examples" / "typed_cavity_induction" / "lean"
Q = Fraction


def _adapter():
    ad = registered_adapters().get("TypedCavityInductionEmitter")
    assert ad is not None, "no adapter registered for TypedCavityInductionEmitter"
    return ad


def _randic_half(t) -> Q:
    d = len(t) + 1
    return sum((_randic_half(c) + Q(1, d * (len(c) + 1)) for c in t), Q(0))


def _size(t) -> int:
    return 1 + sum(_size(c) for c in t)


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["TypedCavityInductionEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_forgery_is_refused_by_layer_one_and_genuinely_false():
    with pytest.raises(TypedCavityRefusal, match="FALSE at k = 2"):
        typed_cavity_certificate(**BBG3_LOWERED_SPEC)
    cert = _adapter().make_false_cert()
    assert not cert.checked
    beta = Q(7, 27) - Q(1, 1000)
    c3 = Q(int(cert.types[2].B.p), int(cert.types[2].B.q))
    assert c3 == Q(4, 3) - 5 * beta
    # [3, 2, 1] attains c_3; joining two copies at a new root doubles the excess over
    # beta - 2/9, so some half-tree of maximum degree 3 has c_T > c_3: the claim is FALSE
    t = (((),), ((),))
    assert _randic_half(t) - beta * _size(t) == c3
    for _ in range(12):
        t = (t, t)
        if _randic_half(t) - beta * _size(t) > c3:
            break
    assert _randic_half(t) - beta * _size(t) > c3
    # the true twin's table holds on the same family
    true = _adapter().make_true_cert()
    c3t = Q(int(true.types[2].B.p), int(true.types[2].B.q))
    assert c3t == Q(1, 27)
    assert _randic_half(t) - Q(7, 27) * _size(t) <= c3t


def test_forged_table_is_the_recursion_at_the_lowered_beta():
    cert = _adapter().make_false_cert()
    beta = sp.Rational(7, 27) - sp.Rational(1, 1000)
    assert [t.B for t in cert.types] == bbg_c_table(3, beta)


def test_twins_share_the_skeleton():
    ad = _adapter()
    f = ad.emit_call(ad.make_false_cert(), "tci_twin")
    t = ad.emit_call(ad.make_true_cert(), "tci_twin")
    for line in ("theorem tci_twin (b : PTree)", "theorem typed_induction_core",
                 "theorem tci_twin_cnt2", "theorem tci_twin_e2_0_0_2_b0_val",
                 "theorem tci_twin_join"):
        assert line in f and line in t, line
    assert "(-7 / 27 : ℝ)" in t and "(-6973 / 27000 : ℝ)" in f
    assert "sorry" not in f and "sorry" not in t


def _ready() -> bool:
    from lean_env import lean_env_ready
    return lean_env_ready(_ENV)


@pytest.mark.skipif(not _ready(), reason="typed_cavity_induction Lean env not built")
def test_kernel_rejects_forgery_and_accepts_twin():
    res = generic_negative_control(_adapter(), env_dir=str(_ENV))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay is True
