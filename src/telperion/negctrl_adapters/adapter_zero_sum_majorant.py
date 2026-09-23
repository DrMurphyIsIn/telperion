"""Negative-control adapter for ZeroSumMajorantEmitter (the zero-sum majorant strip certificate).

The load-bearing kernel content of a `zero_window` instance is its strip theorem

    theorem nm {rho : C} (hz : Zeta23.IsNontrivialZero rho) (him : (1 : R) <= |rho.im|) :
        1 / Complex.normSq rho <= C / (1 + Complex.normSq (Zeta23.gammaOf rho))

proved by clearing denominators and stating the certificate identity
`C * (x^2 + w^2) - 1 * (1 + (w^2 + (1/2 - x)^2)) = sum c_alpha * P_alpha` as `key`, closed by `ring`,
then `linarith only` over the explicit nonnegative summands.  (The majorant / summable faces are
a fixed composition with the island atom `RvMBridgeXi.zeroBoundAt`; they add no numeric content.)

FALSE forgery: the far constant `C = 1` carrying the certificate terms of the honest `C = 9/4`
instance.  The statement `1/|rho|^2 <= 1/(1 + |gamma_rho|^2)` for `|Im rho| >= 1` is FALSE, not
merely unproved: cleared it reads `x^2 + w^2 >= 1 + w^2 + (1/2 - x)^2`, i.e. `x >= 5/4`, which fails
at EVERY point of the open strip (at rho = 1/2 + i: 4/5 > 1/2) -- in particular at every nontrivial
zero, on the critical line or off it.  Layer 1 (`zero_sum_majorant_certificate`) refuses it with a
located witness; the adapter mints the frozen dataclass BY HAND (`dataclasses.replace` of the true
certificate), bypassing that guard exactly as `adapter_exp_threshold` does, so the kernel is the
arbiter: the emitted `key` identity is false and `ring` cannot close it.

TRUE twin: the same instance with `C = 9/4` (the E6Bridge19 / E6Bridge15 / RvMBridgeXi strip
inequality, sharp at `Re rho -> 0`, `|Im rho| = 1`); compiles clean and axiom-clean.

Both twins share every tactic line; only the `C` literal moves.  They elaborate against
`import Mathlib` with the zero vocabulary supplied as stand-ins in the adapter prelude: the strip
proof reads a zero ONLY through `hz.2.1 : 0 < rho.re` and `hz.2.2 : rho.re < 1`, so the stand-in
`IsNontrivialZero` keeps exactly those two conjuncts (the zeta conjunct becomes `True`), and
`gammaOf` is Zeta23's `(rho - 1/2)/I` written by its components `(rho.im, 1/2 - rho.re)` so the two
projection lemmas are `rfl` on any Mathlib.  The control therefore tests the EMITTER's certificate
arithmetic; the real island vocabulary is exercised by
`examples/rvm_bridge/lean/Probes/Dogfood_zero_sum_majorant.lean`.

conjecture1_proved = False.
"""
from __future__ import annotations

import dataclasses

import sympy as sp

from telperion.emit_zero_sum_majorant import (
    ZeroSumMajorantCert,
    ZeroSumMajorantEmitter,
    zero_sum_majorant_certificate,
)
from telperion.negative_control_harness import NegativeControlAdapter, register

_PRELUDE = (
    "namespace Zeta23\n"
    "/-- Stand-in: the emitted strip proof reads a zero only through the two strip conjuncts\n"
    "    `0 < rho.re` and `rho.re < 1` (`hz.2.1`, `hz.2.2`); the zeta conjunct is replaced by\n"
    "    `True`, so the certificate is checked at exactly the generality it covers. -/\n"
    "def IsNontrivialZero (ρ : ℂ) : Prop := True ∧ 0 < ρ.re ∧ ρ.re < 1\n"
    "/-- Zeta23's `gammaOf ρ = (ρ - 1/2) / I`, written by its components. -/\n"
    "noncomputable def gammaOf (ρ : ℂ) : ℂ := ⟨ρ.im, 1 / 2 - ρ.re⟩\n"
    "namespace WeilEF\n"
    "theorem gammaOf_re (ρ : ℂ) : (gammaOf ρ).re = ρ.im := rfl\n"
    "theorem gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := rfl\n"
    "end WeilEF\n"
    "end Zeta23\n"
)

#: the honest instance (the 9/4 strip inequality, strip face only)
_TRUE_SPEC = dict(centre=0, h=1, c_far="9/4", num=1, den_kind="normSq", faces=("strip",))


def make_true_cert() -> ZeroSumMajorantCert:
    """Paired TRUE twin: C = 9/4 with its exact certificate (Layer 1 accepts it)."""
    return zero_sum_majorant_certificate(**_TRUE_SPEC)


def make_false_cert() -> ZeroSumMajorantCert:
    """Hand-forged FALSE cert: C = 1 with the C = 9/4 certificate terms (Layer 1 would refuse;
    the claim fails at every point of the open strip)."""
    return dataclasses.replace(make_true_cert(), c_far=sp.Integer(1))


def _emit(cert: ZeroSumMajorantCert, name: str) -> str:
    # the private per-instance route: the strip face under EXACTLY `name`
    return ZeroSumMajorantEmitter()._emit_strip(cert, name)


register(
    NegativeControlAdapter(
        emitter_name="ZeroSumMajorantEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=_PRELUDE,
        allow_axioms=(),
        label=(
            "forged strip certificate with far constant C = 1 (the C = 9/4 terms): the claim "
            "1/|rho|^2 <= 1/(1 + |gamma_rho|^2) on |Im rho| >= 1 reduces to Re rho >= 5/4 and is "
            "FALSE at every point of the strip (rho = 1/2 + i: 4/5 > 1/2); the emitted `ring` "
            "identity fails and the kernel rejects; the true twin C = 9/4 compiles"
        ),
        imports_line="import Mathlib",
    )
)
