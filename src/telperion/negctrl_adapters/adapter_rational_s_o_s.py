"""Negative-control adapter for RationalSOSEmitter (Artin-denominator SOS).

CERTIFICATE_SENSITIVE. The emitter proves 0 <= p for a nonneg-but-not-SOS p via
an Artin identity q*p = Sum d_i * l_i^2 with q > 0, discharged by a load-bearing
`ring` step. We forge a FALSE cert by corrupting a single SOS coefficient of the
exact Motzkin certificate (1 -> 2); emit_body renders the ring identity with LHS =
expand(q*p) (true product) and RHS = the corrupted Sum, so `by ring` asserts a
false polynomial identity and the kernel rejects. The TRUE twin restores the
coefficient to 1 (an exact, cvxpy-independent Motzkin Artin decomposition) and
compiles.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_rational_sos import RationalSOSEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_x, _y = sp.symbols("x y")

# Motzkin: nonnegative everywhere, NOT a sum of squares (Hilbert's minimal example).
_MOTZKIN = _x ** 4 * _y ** 2 + _x ** 2 * _y ** 4 - 3 * _x ** 2 * _y ** 2 + 1
# Strictly-positive Artin multiplier q = 1 + x^2 + y^2 + x^2 y^2 (positivity-clean).
_Q = _x ** 2 * _y ** 2 + _x ** 2 + _y ** 2 + 1
# Exact SOS of q*Motzkin (closed form; independent of the SDP/cvxpy finder):
#   q*Motzkin = (1 - x^2 y^2)^2 + (x - x^3 y^2)^2 + (y - x^2 y^3)^2 + (x^3 y - x y^3)^2.
_SOS_BASES = (
    -_x ** 2 * _y ** 2 + 1,
    -_x ** 3 * _y ** 2 + _x,
    -_x ** 2 * _y ** 3 + _y,
    _x ** 3 * _y - _x * _y ** 3,
)


def make_true_cert():
    """Positive control: the exact Motzkin Artin certificate (all coeffs = 1)."""
    sos = [(sp.Integer(1), sp.expand(b)) for b in _SOS_BASES]
    return (sp.expand(_MOTZKIN), sp.expand(_Q), sos)


def make_false_cert():
    """Forged FALSE cert: bump the first SOS coefficient 1 -> 2. This breaks the
    identity by exactly -(x^2 y^2 - 1)^2, so the emitted `by ring` step is a false
    polynomial equality the kernel rejects. certify_rational_sos_point's exact
    re-check (q*p - Sum != 0) would REFUSE this; the single-instance-family route
    bypasses certify()."""
    bases = list(_SOS_BASES)
    sos = [(sp.Integer(2), sp.expand(bases[0]))] + [
        (sp.Integer(1), sp.expand(b)) for b in bases[1:]
    ]
    return (sp.expand(_MOTZKIN), sp.expand(_Q), sos)


def _emit_call(cert, name: str) -> str:
    return emit_via_single_instance_family(
        RationalSOSEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ fam.family.symbols : ℝ`; declare x, y so the emitted
        # `∀ x y : ℝ, 0 <= p` binder is bound (else both twins fail to compile).
        family_kwargs={"symbols": (_x, _y)},
    )


register(
    NegativeControlAdapter(
        emitter_name="RationalSOSEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "Artin denominator: forged q*p = Sum d_i*l_i^2 with one SOS coefficient "
            "corrupted (1 -> 2) for the Motzkin polynomial; the load-bearing `ring` "
            "identity is false (off by -(x^2 y^2 - 1)^2), so 0 <= p does not follow."
        ),
    )
)
