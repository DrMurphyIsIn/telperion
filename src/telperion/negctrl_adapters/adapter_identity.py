"""Negative-control adapter for IdentityEmitter (emit_facts.py).

IdentityEmitter emits `lhs = rhs := by field_simp; try ring` per equation
instance.  The load-bearing fact is that the two sides are the same rational
number.  We forge a cert whose RHS is corrupted (1/6 + 1/3 = 7/5, true value
1/2); field_simp + ring cannot close the resulting false numeric goal, so the
kernel rejects the forged theorem.  The true twin restores the RHS to 1/2.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_facts import IdentityEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Symbol-free rational identity.  LHS = 1/6 + 1/3 = 1/2 (exact).
_LHS = sp.Rational(1, 6) + sp.Rational(1, 3)   # == 1/2


def make_false_cert():
    """Hand-forged FALSE cert: RHS corrupted from 1/2 to 7/5.

    sympy self-check sp.simplify(lhs - rhs) == 0 returns False
    (1/2 - 7/5 = -9/10 != 0), so certify() would refuse this; the harness
    mints it directly, bypassing Layer 1.
    """
    return (_LHS, sp.Rational(7, 5))


def make_true_cert():
    """Paired TRUE twin: correct RHS = 1/2 (minimal difference)."""
    return (_LHS, sp.Rational(1, 2))


def _emit(cert, name: str) -> str:
    lhs, rhs = cert
    return emit_via_single_instance_family(
        IdentityEmitter(),
        lean_name=name,
        instance_kwargs={"equation": (lhs, rhs)},
    )


register(
    NegativeControlAdapter(
        emitter_name="IdentityEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        label="forged rational identity 1/6 + 1/3 = 7/5 (true value 1/2); "
        "field_simp + ring leaves a false numeric goal the kernel rejects",
    )
)
