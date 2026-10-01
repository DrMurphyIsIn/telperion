"""Negative control for AnchoredMonotoneExtensionEmitter -- a too-small normalizer.

The registered adapter's instance is the hard-core (independent-set) recursion on rooted trees.
Its forgery replaces the normalizer (1 + lam)^n by (1 + 3 lam/4)^n, which is genuinely FALSE (a
single vertex has Z = 1 + lam).  Layer 1 refuses it at the row-0 residual of the inductive step
(a located exact violation); the adapter mints the certificate with every check skipped, so the
forged Lean differs from the true twin only in the normalizer data and the obligations that
depend on it -- and the residual cell's `linarith` cannot close (a negative product-basis
coefficient).

Offline tests: registration, the exact falsity of the forged claim, and the shared skeleton.
Lean-gated test (skipped unless `examples/anchored_monotone_extension/lean` is built): the control
through `generic_negative_control` (FALSE rejected, TRUE twin clean).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_anchored_monotone_extension import (  # noqa: E402
    HARDCORE_TOO_SMALL_SPEC,
    AnchoredMonotoneRefusal,
    anchored_monotone_extension_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)

_ENV = Path(__file__).resolve().parents[1] / "examples" / "anchored_monotone_extension" / "lean"


def _adapter():
    ad = registered_adapters().get("AnchoredMonotoneExtensionEmitter")
    assert ad is not None, "no adapter registered for AnchoredMonotoneExtensionEmitter"
    return ad


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["AnchoredMonotoneExtensionEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER


def test_forgery_is_refused_by_layer_one_and_genuinely_false():
    spec = dict(HARDCORE_TOO_SMALL_SPEC)
    spec.pop("sanity")
    with pytest.raises(AnchoredMonotoneRefusal, match="obligation res0.*FALSE at"):
        anchored_monotone_extension_certificate(**spec)
    cert = _adapter().make_false_cert()
    assert not cert.checked
    # the residual at the leaf point (A = 1, k = 0) is -x(3x + 4)(x + 1)/4 < 0
    x, a, k = sp.symbols("x a k")
    r0 = cert.obligation("res0").cert.polynomial().as_expr()
    assert sp.expand(r0.subs({a: 1, k: 0}) + x * (3 * x + 4) * (x + 1) / 4) == 0
    assert not cert.obligation("res0").cert.ok()
    # a single vertex: Z = 1 + x exceeds the forged normalizer 1 + 3x/4 for every x > 0
    assert sp.simplify((1 + x) - (1 + sp.Rational(3, 4) * x)) == x / 4
    assert _adapter().make_true_cert().checked


def test_twins_share_the_skeleton():
    ad = _adapter()
    f = ad.emit_call(ad.make_false_cert(), "ame_twin")
    t = ad.emit_call(ad.make_true_cert(), "ame_twin")
    for line in ("theorem invariant", "theorem anchored_extension", "theorem ame_twin_res0",
                 "theorem ame_twin_checks", "theorem ame_twin :"):
        assert line in f and line in t, line
    assert "pN := [(0, 0, (1 : ℝ)), (1, 0, (3 / 4 : ℝ))]" in f
    assert "pN := [(0, 0, (1 : ℝ)), (1, 0, (1 : ℝ))]" in t
    assert "sorry" not in f and "sorry" not in t


def _ready() -> bool:
    from lean_env import lean_env_ready
    return lean_env_ready(_ENV)


@pytest.mark.skipif(not _ready(), reason="anchored_monotone_extension Lean env not built")
def test_kernel_rejects_forgery_and_accepts_twin():
    res = generic_negative_control(_adapter(), env_dir=str(_ENV))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay is True
