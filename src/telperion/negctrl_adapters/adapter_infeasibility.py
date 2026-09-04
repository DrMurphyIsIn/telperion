"""Negative-control adapter for InfeasibilityEmitter.

Certificate under test: the Nullstellensatz refutation ``1 = Sum_j lam_j * g_j``
of an infeasible polynomial system ``{g_j = 0}``.  The multipliers ``lam_j`` are
the certificate of non-existence.  The emitted Lean closes ``(1:R) = 0`` with
``linear_combination lam_1*e_1 + ... + lam_m*e_m``; that step succeeds iff the
combination is EXACTLY 1 as a ring identity.

FALSE twin: a genuinely infeasible system ``{x = 0, x - 1 = 0}`` but with ONE
multiplier corrupted (``-1`` -> ``-2``).  Then ``Sum lam_j g_j = 2 - x != 1``,
so ``linear_combination`` leaves the nonzero residual ``x - 1 = 0`` that its
closing ``ring1`` cannot discharge: the kernel rejects.  (The theorem statement
is still true; only the supplied certificate is wrong -- exactly what
certificate-sensitivity means.)  certify() would REFUSE this cert at line 104
of emit_infeasible.py (``Sum lam g - 1 = 1 - x != 0``); the hand-forged cert
bypasses that guard.

TRUE twin: the same system with the correct multipliers ``[1, -1]`` so
``1*x + (-1)*(x-1) = 1`` exactly; the emitted proof compiles (this is the
positive control in tests/test_infeasible_emitter.py).
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_infeasible import InfeasibilityEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Shared infeasible system: {x = 0, x - 1 = 0} has no common zero.
_x = sp.Symbol("x")
_CONSTRAINTS = [sp.expand(_x), sp.expand(_x - sp.Integer(1))]


def make_true_cert():
    """Correct refutation 1 = 1*x + (-1)*(x - 1)."""
    cofactors = [sp.Integer(1), sp.Integer(-1)]
    # positive control: Sum lam_j g_j - 1 == 0
    assert sp.expand(
        sum(l * g for l, g in zip(cofactors, _CONSTRAINTS)) - 1
    ) == 0
    return (list(_CONSTRAINTS), cofactors)


def make_false_cert():
    """Corrupt the second multiplier (-1 -> -2): Sum lam_j g_j = 2 - x != 1.

    linear_combination (1)*e1 + (-2)*e2 leaves the residual x - 1 = 0, which
    ring1 cannot close -> kernel rejects.  Same infeasible system, so the only
    defect is the certificate itself.
    """
    cofactors = [sp.Integer(1), sp.Integer(-2)]
    # self-check DISAGREES (nonzero) -> a genuine forgery certify() would refuse
    assert sp.expand(
        sum(l * g for l, g in zip(cofactors, _CONSTRAINTS)) - 1
    ) != 0
    return (list(_CONSTRAINTS), cofactors)


def _emit_call(cert, name: str) -> str:
    return emit_via_single_instance_family(
        InfeasibilityEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ fam.family.symbols : ℝ`; declare x so the emitted
        # `∀ x : ℝ, x = 0 -> x - 1 = 0 -> False` binder is bound.
        family_kwargs={"symbols": (_x,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="InfeasibilityEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        label=(
            "InfeasibilityEmitter: a corrupted Nullstellensatz multiplier "
            "(lam_2 = -1 -> -2) claims 1 = 1*x + (-2)*(x-1) for the infeasible "
            "system {x = 0, x - 1 = 0}; the combination is 2 - x != 1 so "
            "linear_combination cannot close 1 = 0 and the kernel rejects."
        ),
    )
)
