"""Negative-control adapter for OrderBalanceEmitter (emit_order_balance.py).

CERTIFICATE_SENSITIVE: the emitter bakes the supplied nonnegative-cosine weights
(a0, a1, ...) and integer zero-orders (k1, ...) into a `... : False := by linarith`
proof.  From `0 ≤ Σ a_j·P_j`, the pole `P0 = 1`, and the polar bounds
`P_j ≤ -(k_j : ℝ)`, `linarith` can derive `False` ONLY when the order balance is
STRICTLY violated, i.e. a0 < Σ_{j≥1} a_j·k_j.  The weights/orders are the
corruptible witness.

FALSE forge: weights=(5,4,1), orders=(1,1) -> a0=5, Σ a_j·k_j = 4+1 = 5, a TIE
(deficit 0).  The emitted `linarith` cannot derive False from
0 ≤ 5·P0 + 4·P1 + 1·P2 with P0=1, P1 ≤ -1, P2 ≤ -1 (best case 0 ≤ 5-4-1 = 0, no
strict contradiction), so the Lean fails to close `False`.
order_balance_certificate REFUSES this (balance not violated), so the cert is
hand-built to bypass Layer 1.

TRUE twin: weights=(3,4,1), orders=(1,1) -> a0=3 < 5 = Σ a_j·k_j (deficit 2 > 0),
the classical dVP 3-4-1 hinge; `linarith` closes `False` and it compiles clean.

The emitted theorem is named exactly `{base}` (= name) and binds all its reals /
integers in its own signature, so no rename and no family symbols are needed.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_order_balance import (
    OrderBalanceCertificate,
    OrderBalanceEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_false_cert() -> OrderBalanceCertificate:
    # a0 = 5, Σ_{j≥1} a_j·k_j = 4·1 + 1·1 = 5 -> deficit 0 (a TIE, NOT strict).
    # linarith cannot derive False; order_balance_certificate would REFUSE this
    # (balance not violated), so the cert is minted by hand.
    return OrderBalanceCertificate(
        weights=(sp.Rational(5), sp.Rational(4), sp.Rational(1)),
        orders=(sp.Integer(1), sp.Integer(1)),
        balance_deficit=sp.Rational(0),   # forged: not > 0
    )


def make_true_cert() -> OrderBalanceCertificate:
    # Classical dVP 3-4-1: a0 = 3 < 4·1 + 1·1 = 5 -> deficit 2 > 0 (strict
    # violation); linarith closes False.
    return OrderBalanceCertificate(
        weights=(sp.Rational(3), sp.Rational(4), sp.Rational(1)),
        orders=(sp.Integer(1), sp.Integer(1)),
        balance_deficit=sp.Rational(2),
    )


def _emit(cert: OrderBalanceCertificate, name: str) -> str:
    # OrderBalanceEmitter exposes only public emit_body(fam, profile), reading the
    # OrderBalanceCertificate off inst.payload.  It names the single theorem
    # exactly `{base}` (= name) and binds P0.. and k1.. in the theorem signature,
    # so no rename and no family symbols are needed.
    return emit_via_single_instance_family(
        OrderBalanceEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="OrderBalanceEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged order-balance cert with weights (5,4,1), orders (1,1): a0=5 = "
            "Σ a_j·k_j = 5 (a TIE, deficit 0), so `linarith` cannot derive False "
            "and the emitted proof fails.  True twin (3,4,1) has a0=3 < 5 (deficit "
            "2), the dVP hinge, and closes False."
        ),
        imports_line="import Mathlib",
    )
)
