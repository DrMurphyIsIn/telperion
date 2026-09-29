"""Negative-control adapter for EventualThresholdEmitter, quadratic-sign-race face.

The arity face has no corruptible data (the arity IS the statement); the
quadratic-sign-race face does: the switch point ``r`` and the Taylor literals at
the anchor ``k = r + 1`` are baked into the emitted ``norm_num`` endpoint facts and
``ring`` identity.

FALSE forgery: ``P(m) = m² − 10m − 7`` with the switch moved one step late,
``r = 11``.  The statement claims ``P(11) < 0``, but ``P(11) = 4``, so it is FALSE,
not merely unproved.  The Layer-1 self-check refuses ``r = 11``
(``P(11) = 4`` is not ``< 0``).  The adapter mints the dataclass BY HAND, with
anchor 12, slope ``P'(12) = 14`` and value ``P(12) = 17``, so the ``ring`` identity
is consistent.  Only the ``norm_num`` fact ``P(11) < 0`` is false, and the kernel
rejects it.

TRUE twin: the same quadratic with ``r = 10`` (``P(10) = −7 < 0 < 4 = P(11)``).

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_eventual_threshold import (
    EventualThresholdEmitter,
    QuadraticSignRaceCert,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_A, _B, _C = sp.Integer(1), sp.Integer(-10), sp.Integer(-7)


def _P(m):
    return _A * m * m + _B * m + _C


def _cert(r: int) -> QuadraticSignRaceCert:
    k = r + 1
    return QuadraticSignRaceCert(
        mode="switch", a=_A, b=_B, c=_C, m0=5, r=r, anchor=k,
        slope=2 * _A * k + _B, value=_P(k), head_value=_P(r))


def make_false_cert() -> QuadraticSignRaceCert:
    """Switch forged one step late: claims P(11) < 0, but P(11) = 4."""
    return _cert(11)


def make_true_cert() -> QuadraticSignRaceCert:
    """The genuine switch between 10 and 11."""
    return _cert(10)


def _emit(cert: QuadraticSignRaceCert, name: str) -> str:
    return emit_via_single_instance_family(
        EventualThresholdEmitter(), lean_name=name, instance_kwargs={"payload": cert})


register(
    NegativeControlAdapter(
        emitter_name="EventualThresholdEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        label=("quadratic sign race m^2 - 10m - 7 forged to switch after 11: claims "
               "P(11) < 0 but P(11) = 4, so the emitted norm_num endpoint fact fails; "
               "the true switch r = 10 compiles"),
    )
)
