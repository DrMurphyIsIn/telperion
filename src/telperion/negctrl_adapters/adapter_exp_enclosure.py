"""Negative-control adapter for ExpEnclosureEmitter (rational `Real.exp` brackets).

The emitted theorem is `lo <= Real.exp x /\\ Real.exp x <= hi`, proved from Mathlib's
`Real.exp_bound` at the certified Taylor order: the tactic derives `S - r <= exp x <= S + r`
for the EXACT rational partial sum `S` and remainder `r`, then closes the claimed bracket by
`linarith`.  The load-bearing content is therefore exactly the pair `(lo, hi)`: a claim the
Taylor box does not imply cannot be reached by that `linarith`, and the TRUSTED Lean kernel
rejects the proof.

FALSE forgery: `x = 1/10`, `n = 6`, `lo = 1`, `hi = 1105/1000`.  Now `e^(1/10) = 1.1051709...`
and the order-6 box is `[1.1051709150..., 1.1051709182...]`, so the claimed `hi` sits BELOW the
box's lower endpoint -- the claim is not merely unproved, it is FALSE.  Layer 1
(`exp_enclosure_certificate`) refuses it (no order up to the cap fits, and this one is
explicitly pinned at `n = 6`); the adapter mints the frozen dataclass BY HAND, bypassing that
guard exactly as `adapter_bragg_floor` does, so the kernel is the arbiter: the final
`linarith` cannot get `exp (1/10) <= 1105/1000` out of `h2 : exp (1/10) <= S_6 + r_6`.

TRUE twin: the same point and order with an honest bracket, `lo = 110517/100000`,
`hi = 110518/100000` (which does contain the order-6 box) -- compiles clean and axiom-clean.

Both twins are plain `(· : ℝ)` statements over Mathlib alone (imports_line `import Mathlib`,
empty prelude), so the control needs no island definitions.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_exp_enclosure import (
    ExpEnclosureCert,
    ExpEnclosureEmitter,
    taylor_parts,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_X = sp.Rational(1, 10)
_N = 6
_S, _R = taylor_parts(_X, _N)


def make_false_cert():
    """Hand-forged FALSE cert: hi = 1105/1000 is BELOW the order-6 Taylor lower endpoint
    S_6 - r_6 = 1.10517091..., so `exp (1/10) <= hi` is false and unreachable by linarith."""
    return ExpEnclosureCert(
        x=_X, n=_N, partial_sum=_S, remainder=_R,
        lo=sp.Rational(1), hi=sp.Rational(1105, 1000), mode="exp",
        partial_sum_neg=taylor_parts(-_X, _N)[0],
    )


def make_true_cert():
    """Paired TRUE twin: an honest bracket at the same point and order (it contains the box)."""
    return ExpEnclosureCert(
        x=_X, n=_N, partial_sum=_S, remainder=_R,
        lo=sp.Rational(110517, 100000), hi=sp.Rational(110518, 100000), mode="exp",
        partial_sum_neg=taylor_parts(-_X, _N)[0],
    )


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        ExpEnclosureEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="ExpEnclosureEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged exp bracket [1, 1105/1000] at x = 1/10 whose upper endpoint lies BELOW the "
            "order-6 Real.exp_bound box (e^(1/10) = 1.1051709...): the final linarith cannot "
            "reach the claim and the kernel rejects it; the true twin [110517/100000, "
            "110518/100000] at the same point and order compiles"
        ),
        imports_line="import Mathlib",
    )
)
