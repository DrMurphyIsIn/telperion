"""Negative-control adapter for ScaledIntervalEvalEmitter (kernel-recomputed integer boxes).

Every DAG node carries a literal box ``b_k`` and a check ``RI.subset (op <children>) b_k = true``
closed by ``decide +kernel``: the kernel re-runs the integer operation and compares.  The
load-bearing content is therefore the literal boxes themselves.

FALSE forgery: the honest certificate of ``exp(1/3) * (1/7) + 2/9`` at scale ``10^30`` with the
ROOT box's upper end shrunk by ONE ulp.  The kernel recomputes ``RI.add`` of the two child boxes,
gets an upper end one larger than the forged literal, so the Bool equation
``RI.subset (...) b_root = true`` is FALSE and ``decide +kernel`` fails.  Layer 1 would never mint
it (the box is computed, not supplied); the adapter edits the frozen dataclass BY HAND, bypassing
that, exactly as ``adapter_exp_enclosure`` does, so the kernel is the arbiter.

TRUE twin: the same certificate unmodified -- compiles clean and axiom-clean.  The two emitted
texts differ in exactly one line (the root box literal).

Both twins elaborate over Mathlib alone: the ``ScaledInterval`` prelude is spliced in as the
adapter ``prelude`` (its body without the import line), so no island module is needed.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import replace

import sympy as sp

from telperion.emit_scaled_interval_eval import (
    ScaledIntervalEvalEmitter,
    scaled_interval_eval_certificate,
    scaled_interval_prelude_body,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_EXPR = sp.exp(sp.Rational(1, 3)) * sp.Rational(1, 7) + sp.Rational(2, 9)
_SCALE = 10 ** 30


def make_true_cert():
    """The honest certificate (claim = the computed root box over the scale)."""
    return scaled_interval_eval_certificate(_EXPR, scale=_SCALE)


def make_false_cert():
    """The honest certificate with the root box's upper end shrunk by one ulp."""
    cert = make_true_cert()
    nodes = list(cert.nodes)
    root = nodes[cert.root]
    nodes[cert.root] = replace(root, box=(root.box[0], root.box[1] - 1))
    return replace(cert, nodes=tuple(nodes))


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        ScaledIntervalEvalEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="ScaledIntervalEvalEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=scaled_interval_prelude_body(),
        allow_axioms=(),
        label=(
            "root box of exp(1/3)*(1/7) + 2/9 at scale 10^30 shrunk by one ulp: the kernel "
            "recomputes RI.add of the child boxes and the _calc subset decide is false; the "
            "unmodified twin compiles"
        ),
        imports_line="import Mathlib",
    )
)
