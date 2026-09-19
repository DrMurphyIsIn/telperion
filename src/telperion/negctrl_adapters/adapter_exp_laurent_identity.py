"""Negative-control adapter for ExpLaurentIdentityEmitter.

The forged twin is the mistake QC_RECURRENCE section 6 caught in ITSELF and
corrected: the two one-sided clearances of an off-line pair are `e^d - 1` and
`1 - e^(-d)`, and it is their PRODUCT -- not their SUM -- that equals the Bragg
amplification excess `e^d + e^(-d) - 2`.  The sum is `2d + O(d^3)`; the claim

    (e^d - 1) + (1 - e^(-d)) = e^d + e^(-d) - 2                      [FALSE]

leaves the residue `2 - 2*e^(-d)`, which no cofactor multiple of the relation
`e^d * e^(-d) = 1` can absorb.  `certify` REFUSES it at Layer 1; this adapter
bypasses that refusal, hands the emitter a hand-built certificate carrying the
TRUE row's cofactor `-1`, and checks that the Lean KERNEL rejects the emitted
theorem anyway -- `linear_combination (-1) * hrel` faces a goal `ring` cannot
close.

The TRUE twin is the same row with the product restored, cofactor `-1`, which
compiles clean: the rejection is for falsity, not for a malformed spine.
conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_exp_laurent_identity import (
    Y,
    Z,
    ExpLaurentCert,
    ExpLaurentIdentityEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_G_PLUS = Y - 1        # outer mirror clearance   e^d - 1
_G_MINUS = 1 - Z       # inner clearance          1 - e^(-d)
_EXCESS = Y + Z - 2    # Bragg amplification excess
_COFACTOR = sp.Integer(-1)  # the TRUE row's certificate: lhs - rhs = -(y*z - 1)


def make_true_cert() -> ExpLaurentCert:
    """The genuine row: the PRODUCT of the clearances is the excess, cofactor -1."""
    return ExpLaurentCert(lhs=_G_PLUS * _G_MINUS, rhs=_EXCESS,
                          cofactor=_COFACTOR, var="d")


def make_false_cert() -> ExpLaurentCert:
    """Forged twin: product -> SUM, with the true row's cofactor kept.

    `exp_laurent_certificate` would REFUSE this (remainder 2 - 2*expNeg != 0);
    the certificate is assembled BY HAND so Layer 2 -- the kernel -- decides.
    """
    return ExpLaurentCert(lhs=_G_PLUS + _G_MINUS, rhs=_EXCESS,
                          cofactor=_COFACTOR, var="d")


def _emit_call(cert: ExpLaurentCert, name: str) -> str:
    return emit_via_single_instance_family(
        ExpLaurentIdentityEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        family_kwargs={"symbols": (Y, Z)},
    )


register(
    NegativeControlAdapter(
        emitter_name="ExpLaurentIdentityEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "FALSE exp-Laurent row (e^d - 1) + (1 - e^(-d)) = e^d + e^(-d) - 2 "
            "(the clearances' SUM substituted for their PRODUCT, QC_RECURRENCE "
            "section 6's own corrected mistake); linear_combination (-1) * hrel "
            "cannot close the residue 2 - 2*e^(-d)."
        ),
        imports_line="import Mathlib",
    )
)
