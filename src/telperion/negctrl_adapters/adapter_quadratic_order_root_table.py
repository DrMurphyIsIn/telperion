"""Negative-control adapter for QuadraticOrderRootTableEmitter (kernel-decided root faces).

The split face ``IsRootMod t c p y`` and the witness face ``IsWitness t c p y`` carry the residue
``y`` as literal witness data, closed by ``decide``.  The load-bearing content is therefore ``y``.

FALSE forgery: the order ``X^2 + 5`` (``t = 0``, ``c = 5``, ``d = 20``, the field ``Q(sqrt -5)``
with ``h = 2``) at ``p = 3``.  The honest root is ``y = 1`` (``1 + 5 = 6``, divisible by 3) and it is
a class-number witness (``4 * 3 = 12 <= 20``, ``3 != 5``).  The forgery keeps everything and sets
``y = 0``: ``0 + 5 = 5`` is NOT divisible by 3, so ``decide`` on ``IsRootMod 0 5 3 0`` and on the
third conjunct of ``IsWitness 0 5 3 0`` is false and the kernel rejects both.  Layer 1 would never
mint it (``root_mod`` computes ``y``; ``verify_certificate`` rejects the forged face), so the
adapter edits the frozen dataclass BY HAND and calls ``_render_instance`` directly, bypassing the
emitter's own re-check -- exactly as ``adapter_scaled_interval_eval`` does, so the kernel is the
arbiter.

TRUE twin: the same certificate unmodified -- compiles clean and axiom-clean.  The two emitted
texts differ exactly in the lines carrying the literal ``y``.

Both twins elaborate over Mathlib alone: the ``QuadraticOrderRoot`` prelude is spliced in as the
adapter ``prelude`` (its body without the import line), so no island module is needed.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace

from telperion.emit_quadratic_order_root_table import (
    PrimeFace,
    QuadraticOrderRootTableEmitter,
    _render_instance,
    quadratic_order_root_prelude_body,
    quadratic_order_root_table_certificate,
)
from telperion.negative_control_harness import NegativeControlAdapter, register

_T, _C, _P = 0, 5, 3


def make_true_cert():
    """The honest certificate: ``X^2 + 5`` at ``p = 3`` (split, root ``y = 1``, a witness)."""
    return quadratic_order_root_table_certificate(_T, _C, [_P])


def make_false_cert():
    """The honest certificate with the root forged to ``y = 0`` (``3`` does not divide ``5``)."""
    cert = make_true_cert()
    (face,) = cert.faces
    assert face.face == "split" and face.y == 1 and face.witness
    return replace(cert, faces=(PrimeFace(face.p, face.face, 0, face.witness),))


def _emit(cert, name: str) -> str:
    # Direct render: the emitter's emit_body re-checks the certificate and would REFUSE the
    # forgery (Layer 1); the control must reach the kernel (Layer 2).
    body = "open QuadraticOrderRoot NumberField Ideal\n\n"
    lines, _n = _render_instance(cert, name)
    return body + "\n".join(lines) + "\n"


# The emitter class is named here so the registry pairs the adapter with its stance.
_EMITTER = QuadraticOrderRootTableEmitter

register(
    NegativeControlAdapter(
        emitter_name=_EMITTER.__name__,
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=quadratic_order_root_prelude_body(),
        allow_axioms=(),
        label=(
            "X^2 + 5 at p = 3 with the root forged from y = 1 to y = 0: 3 does not divide "
            "0^2 + 5, so decide on IsRootMod 0 5 3 0 (and on IsWitness 0 5 3 0) is false and the "
            "kernel rejects; the unmodified twin compiles"
        ),
        imports_line="import Mathlib",
    )
)
