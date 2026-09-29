"""Negative-control adapter for MonotoneRatioTailEmitter, piecewise-linear node face.

The ratio face has no separately-supplied corruptible witness. The piecewise-linear
node-condition face does: the tail threshold ``M`` and the node values are baked
into the per-segment ``linarith`` node facts ``h(a), h(b) <= 0``.

FALSE forgery: nodes ``(1/4, 0), (1/2, -1/20), (3/4, -1/8), (1, -1/5)``,
``y_dag = 1/2``, ``L(y) = log(1+y) - log(3/2)``, ``s = 2/3``, with the threshold
lowered to ``M = 0`` (claims every ``m >= 1``).  This is FALSE, not merely
unproved.  At ``m = 1``, ``y = 1``, ``U = min(0, segment lines)`` gives
``-1/5 + log(4/3) ~ 0.088 > 0``, and those ``U``, ``L`` satisfy every hypothesis of
the core theorem, so the core theorem is false too.  Layer 1 refuses ``M = 0``
(the node condition at ``y = 1`` fails, ``1/5 < 1/3``).  The adapter mints the
payload BY HAND, and the kernel rejects the node fact.

TRUE twin: the same data with ``M = 1``.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_monotone_tail import MonotoneRatioTailEmitter, PLNodeTailPayload
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_R = sp.Rational
_NODES = ((_R(1, 4), _R(0)), (_R(1, 2), _R(-1, 20)), (_R(3, 4), _R(-1, 8)), (_R(1), _R(-1, 5)))


def _cert(M: int) -> PLNodeTailPayload:
    slopes = tuple((u1 - u0) / (y1 - y0) for (y0, u0), (y1, u1) in zip(_NODES, _NODES[1:]))
    return PLNodeTailPayload(M=M, nodes=_NODES, slopes=slopes, y_dag=_R(1, 2),
                             s=_R(2, 3), L="log_tangent")


def make_false_cert() -> PLNodeTailPayload:
    """Threshold forged down to M = 0: false at m = 1, y = 1."""
    return _cert(0)


def make_true_cert() -> PLNodeTailPayload:
    """The certified threshold M = 1."""
    return _cert(1)


def _emit(cert: PLNodeTailPayload, name: str) -> str:
    return emit_via_single_instance_family(
        MonotoneRatioTailEmitter(), lean_name=name, instance_kwargs={"payload": cert})


register(
    NegativeControlAdapter(
        emitter_name="MonotoneRatioTailEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        label=("piecewise-linear node tail forged to M = 0: at m = 1, y = 1 the value is "
               "-1/5 + log(4/3) > 0, so the node fact at y = 1 fails; the true twin "
               "M = 1 compiles"),
    )
)
