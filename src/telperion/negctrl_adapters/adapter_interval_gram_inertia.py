"""Negative-control adapter for IntervalGramInertiaEmitter (the interval-inertia certificate).

WHAT IS LOAD-BEARING.  The inertia theorem `posIndex hG = p AND defect hG = q` is only as true as
one arithmetic fact: on every witness direction the compressed midpoint form (the diagonal `cx`)
must STRICTLY dominate the interval slack `w * S_X`.  If it does not, the box straddles an
eigenvalue sign and the signature is NOT constant on the box.  The emitter exposes exactly that
fact as its private pure-real route ``_emit_compress_margin``:

    theorem <name> (v0 ... : R) (hv : 0 < sum v_k^2) :
        0 < (sum cx_k * v_k^2) - (w * S_X) * (sum v_k^2)

Corrupt a pivot `cx_k`, the half-width `w`, or the column constant `S_X` and this becomes FALSE:
`nlinarith` cannot close it and the TRUSTED Lean kernel rejects the proof.  Layer 1
(`interval_gram_inertia_certificate`) refuses such a box outright ("the box is WIDER than the pivot
margin"); the adapter mints the frozen dataclass BY HAND to bypass that guard, so Layer 2 -- the
kernel -- is the arbiter.

FALSE forgery: a 2x2 box whose positive-side pivot is `cx = 1/10` while the slack is
`w * S_X = (1/2) * 1 = 1/2`.  The claim `0 < (1/10) v0^2 - (1/2) v0^2` is false for every `v0 != 0`
(the box straddles the eigenvalue sign), so the kernel rejects it.

TRUE twin: the same shape with a separated box -- `cx = 1`, `w = 1/10`, `S_X = 1`, so
`0 < 1*v0^2 - (1/10) v0^2` holds and compiles clean.

Both twins are pure `(. : R)` polynomial inequalities: the control elaborates against plain Mathlib
with no RHLinalg import.  It tests the EMITTER's certificate arithmetic; the RHLinalg-pinned
Sylvester assembly is CI-compiled in the gram_inertia example island itself.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_interval_gram_inertia import (
    IntervalGramInertiaCert,
    IntervalGramInertiaEmitter,
)
from telperion.negative_control_harness import NegativeControlAdapter, register

_EMITTER = IntervalGramInertiaEmitter()


def _cert(cx: sp.Rational, w: sp.Rational) -> IntervalGramInertiaCert:
    """A 2x2 (p, q) = (1, 1) certificate shell with positive-side pivot ``cx`` and half-width ``w``.

    Only ``cx``, ``w`` and ``p`` (= S_X) reach ``_emit_compress_margin``; the box/basis fields are
    filled with the consistent 2x2 data (`M = diag(1, -2)`, `X = e0`, `Y = e1`) so the record stays
    readable, but they are not what the control tests.
    """
    return IntervalGramInertiaCert(
        n=2,
        lo=((sp.Integer(1) - w, sp.Integer(0) - w), (sp.Integer(0) - w, sp.Integer(-2) - w)),
        hi=((sp.Integer(1) + w, sp.Integer(0) + w), (sp.Integer(0) + w, sp.Integer(-2) + w)),
        mid=((sp.Integer(1), sp.Integer(0)), (sp.Integer(0), sp.Integer(-2))),
        w=sp.Rational(w), p=1, q=1,
        x_basis=((sp.Integer(1),), (sp.Integer(0),)),
        y_basis=((sp.Integer(0),), (sp.Integer(1),)),
        cx=(sp.Rational(cx),), cy=(sp.Integer(2),),
        delta_x=sp.Rational(cx), delta_y=sp.Integer(2),
    )


def make_false_cert() -> IntervalGramInertiaCert:
    """Hand-forged FALSE cert: pivot 1/10 BELOW the slack w*S_X = 1/2 (margin -2/5 < 0;
    ``interval_gram_inertia_certificate`` would refuse this box)."""
    return _cert(sp.Rational(1, 10), sp.Rational(1, 2))


def make_true_cert() -> IntervalGramInertiaCert:
    """Paired TRUE twin: pivot 1 ABOVE the slack w*S_X = 1/10 (margin +9/10 > 0), a genuinely
    separated box."""
    return _cert(sp.Integer(1), sp.Rational(1, 10))


def _emit(cert: IntervalGramInertiaCert, name: str) -> str:
    """The emitter's private per-instance route for the certificate's arithmetic core."""
    return _EMITTER._emit_compress_margin(cert, name)


register(
    NegativeControlAdapter(
        emitter_name="IntervalGramInertiaEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged interval-inertia cert whose positive pivot cx=1/10 sits BELOW the interval "
            "slack w*S_X=1/2 (the box straddles an eigenvalue sign): the margin inequality "
            "0 < (1/10)v0^2 - (1/2)v0^2 is false and the kernel rejects it; true twin "
            "(cx=1, w=1/10, S_X=1, margin +9/10) compiles clean"
        ),
        imports_line="import Mathlib",
    )
)
