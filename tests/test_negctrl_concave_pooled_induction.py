"""Negative control for ConcavePooledInductionEmitter -- the path-density bound past 1/phi.

The adapter's instance is the dogfood's bounded-degree case (the matching message on PATHS).
Its forgery raises the deficit to `alpha = 13/20 > 1/phi = 0.618...`: the claim
`sum_u y_u >= (13/20) n` is then FALSE on long paths, Layer 1 refuses it, and the adapter mints
the certificate algebra with the sign checks skipped, so the forged Lean differs from the true
twin only in what depends on `alpha` -- and some cell polynomial acquires a NEGATIVE Bernstein
coefficient that the emitted `linarith` cannot absorb.  The TRUSTED Lean kernel is the arbiter.

These tests are OFFLINE: registration, the exact falsity of the forged claim, the exact reason
the forged Lean cannot compile (a negative coefficient), and the shared tactic skeleton.  The
kernel run is `test_certificate_sensitivity::test_generic_negative_control_holds` (lean-gated;
it uses `examples/concave_pooled_induction/lean`); the lane ran it by hand (FALSE twin rejected
with "linarith failed" at the forged cells, TRUE twin clean).

conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from telperion.emit_concave_pooled_induction import (  # noqa: E402
    PATH_DENSITY_SPEC,
    concave_pooled_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.negative_control_harness import registered_adapters  # noqa: E402


def _adapter():
    ad = registered_adapters().get("ConcavePooledInductionEmitter")
    assert ad is not None, "no adapter registered for ConcavePooledInductionEmitter"
    return ad


def test_adapter_is_registered_over_mathlib_alone():
    ad = _adapter()
    assert ad.imports_line == "import Mathlib"
    assert ad.prelude == "" and ad.allow_axioms == ()


def test_registry_declares_wired_adapter():
    stance = REGISTRY["ConcavePooledInductionEmitter"]
    assert stance.neg_control is not None
    assert stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "communicated privately" in stance.reason


def test_false_cert_is_refused_by_layer_one():
    cert = _adapter().make_false_cert()
    assert cert.alpha == sp.Rational(13, 20) and not cert.checked
    with pytest.raises(ValueError, match="REFUSED"):
        concave_pooled_certificate(**dict(PATH_DENSITY_SPEC, alpha=sp.Rational(13, 20)))


def test_false_claim_is_genuinely_false_not_merely_unproved():
    """On the path with n vertices, sum_u y_u = sum_k F_k / F_{k+1} (Fibonacci ratios), whose
    density tends to 1/phi < 13/20; at n = 100 the forged `ell + (13/20) n <= U(y) <= 0` fails."""
    ys = [Fraction(1)]
    for _ in range(99):
        ys.append(1 / (1 + ys[-1]))
    ell, n = -sum(ys), len(ys)
    assert ell + Fraction(13, 20) * n > 0          # the forged conclusion is violated ...
    cert = _adapter().make_false_cert()
    assert max(cert.vs) == 0                         # ... and U <= max v_j = 0 on I
    assert ell + Fraction(3, 5) * n <= 0             # while the honest alpha = 3/5 holds


def test_forged_cells_carry_a_negative_coefficient_and_true_twin_none():
    false = _adapter().make_false_cert()
    true = _adapter().make_true_cert()
    neg = [(c.s, c.t, o.side, o.k) for c in false.cells for o in c.obligations
           if not o.num.ok()]
    assert neg, "forged certificate has no negative coefficient: control would be vacuous"
    assert all(o.num.ok() for c in true.cells for o in c.obligations)


def test_twins_share_the_tactic_skeleton():
    ad = _adapter()
    f = ad.emit_call(ad.make_false_cert(), "cpi_twin")
    t = ad.emit_call(ad.make_true_cert(), "cpi_twin")
    for line in ("theorem cpi_twin (b : PTree) (hb : b.AllDeg (fun m => m ≤ 1)) :\n",
                 "  pooled_induction_core (fun m => m ≤ 1) cpi_twin_h cpi_twin_g",
                 "theorem pooled_induction_core", "theorem minPieces_jensen"):
        assert line in f and line in t, line
    assert "(13 / 20 : ℝ) * b.size" in f and "(3 / 5 : ℝ) * b.size" in t
    assert "sorry" not in f and "sorry" not in t
