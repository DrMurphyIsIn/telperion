"""Negative-control adapter for SOSRefutationEmitter.

The emitter's load-bearing fact is the Positivstellensatz identity
    -1 = sigma0 + Sum sigma_i * g_i + Sum lambda_j * h_j,
rendered as `have key : (-1:R) = <rhs> := by linear_combination <combo>`.
The lambda_j (equality multipliers) and sigma_i (SOS multipliers) are the
corruptible refutation certificate.

FALSE twin: take the real-only-infeasible system x^2 + 1 = 0 and corrupt the
single equality multiplier lambda_1 from the true value -1 to +1.  The
reconstruction becomes 2*x^2 + 1 != -1, so certify_sos_refutation_point's sympy
self-check refuses it -- a genuinely false instance.  Emitted as
`linear_combination (1) * he1`, the `have key` ring residual is -2*x^2 - 2 != 0,
so the Lean kernel rejects the proof.

TRUE twin: the same system with the correct lambda_1 = -1, i.e.
-1 = x^2 + (-1)*(x^2+1), whose emitted proof compiles clean.

The cert passed through instance_kwargs={"payload": cert} is the raw
(sigma0, ineqs, eqs) tuple emit_body destructures from CertifiedInstance.payload.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_sos_refutation import SOSRefutationEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_X = sp.Symbol("x")


def _payload(lam):
    """(sigma0, ineqs, eqs) for the system {x^2 + 1 = 0} with sigma0 = x^2 and
    equality multiplier lambda_1 = ``lam``.  lam = -1 refutes (-1 = x^2 - (x^2+1));
    any other lam breaks the identity."""
    sigma0 = [(1, _X)]                        # sigma0 = 1 * x^2
    ineqs = []                                # no inequality constraints
    eqs = [(_X ** 2 + 1, lam, "he1")]         # h_1 = x^2 + 1, multiplier lam
    return (sigma0, ineqs, eqs)


def make_false_cert():
    # Corrupt the single equality multiplier: -1 (true) -> +1 (false).
    return _payload(sp.Integer(1))


def make_true_cert():
    # Genuine SOS-Positivstellensatz refutation of x^2 + 1 = 0.
    return _payload(sp.Integer(-1))


def _emit_call(cert, name: str) -> str:
    return emit_via_single_instance_family(
        SOSRefutationEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ fam.family.symbols : ℝ`; declare x so the emitted
        # `∀ x : ℝ, x^2 + 1 = 0 -> False` binder is bound.
        family_kwargs={"symbols": (_X,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="SOSRefutationEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged SOS-Positivstellensatz refutation of x^2 + 1 = 0 with the "
            "equality multiplier lambda_1 corrupted from -1 to +1: the identity "
            "-1 = sigma0 + Sum lambda_j*h_j no longer holds (reconstruction = "
            "2*x^2 + 1), so the emitted `linear_combination` ring step is false "
            "and the kernel rejects it."
        ),
        imports_line="import Mathlib",
    )
)
