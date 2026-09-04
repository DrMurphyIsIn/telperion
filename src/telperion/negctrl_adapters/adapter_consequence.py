"""Negative-control adapter for ConsequenceEmitter.

CERTIFICATE_SENSITIVE: the emitted proof is a single Mathlib `linear_combination
Sum c_i * h_i`, load-bearing on the exact cofactor identity
`lhs - rhs = Sum c_i * (a_i - b_i)`.  Corrupt one cofactor and the residual is a
nonzero polynomial that `ring` (inside linear_combination) cannot close, so the
Lean kernel rejects the term.

FALSE instance: hypothesis `x = 2`, consequence `x ^ 2 = 4`, cofactor forged to
`(x + 3)` instead of the correct `(x + 2)`.  Residual (x^2-4)-(x+3)(x-2)=2-x != 0.
TRUE twin: same statement, honest cofactor `(x + 2)`, residual 0 -> compiles.

The payload matches CertifiedInstance.payload as read by
ConsequenceEmitter.emit_body: the 4-tuple (lhs, rhs, hypotheses, cofactors) with
hypotheses = [(a_i, b_i, hyp_name)].  No prelude / extra axioms are needed.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_consequence import ConsequenceEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Single real variable shared by both twins.
_X = sp.Symbol("x")

# Consequence statement (identical in both twins): x = 2  =>  x^2 = 4.
_LHS = _X ** 2
_RHS = sp.Integer(4)
# hypotheses: list of (a_i, b_i, hyp_name); here the single hyp `x = 2`.
_HYPS = [(_X, sp.Integer(2), "h_1")]


def _make_cert(cofactor: sp.Expr):
    """Build a ConsequenceEmitter payload 4-tuple with the given single cofactor.

    Shape mirrors certify_consequence_point's CertifiedInstance.payload:
        (lhs, rhs, hypotheses, cofactors)
    which emit_body unpacks verbatim.
    """
    return (
        sp.expand(_LHS),
        sp.expand(_RHS),
        list(_HYPS),
        [sp.expand(cofactor)],
    )


def make_false_cert():
    # Corrupted cofactor (x + 3): (x^2 - 4) - (x + 3)(x - 2) = 2 - x != 0.
    # certify_consequence_point would REFUSE this at its self-check (line 65);
    # the harness bypasses certify via _construction_guard.
    return _make_cert(_X + 3)


def make_true_cert():
    # Honest cofactor (x + 2) = sp.reduced(x^2 - 4, [x - 2], x)[0]:
    # (x^2 - 4) - (x + 2)(x - 2) = 0.  linear_combination closes by ring.
    return _make_cert(_X + 2)


def emit_call(cert, name: str) -> str:
    # Route (A): ConsequenceEmitter exposes only public emit_body(fam, profile).
    # instance_kwargs={"payload": cert} lands on CertifiedInstance.payload, the
    # exact field emit_body reads.
    return emit_via_single_instance_family(
        ConsequenceEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ fam.family.symbols : ℝ`; declare x so the emitted
        # theorem's free variable is bound (else both twins fail to compile).
        family_kwargs={"symbols": (_X,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="ConsequenceEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=emit_call,
        label=(
            "forged cofactor: claims x^2 = 4 follows from x = 2 via "
            "linear_combination (x + 3) * h_1, but (x^2-4)-(x+3)(x-2) = 2-x != 0, "
            "so ring cannot close it (true cofactor is x + 2)"
        ),
    )
)
