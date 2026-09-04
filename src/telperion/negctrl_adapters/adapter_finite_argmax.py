"""Negative-control adapter for FiniteArgmaxMarginEmitter (emit_finite_argmax.py).

CERTIFICATE_SENSITIVE: per competitor the emitter ships the cross-multiplied
INTEGER strict inequality

    theorem {base}_beats_{i} : ({p_i} * {q_w} : ℤ) < {p_w} * {q_i} := by norm_num

where the winner/competitor integers come off the supplied FiniteArgmaxCertificate
payload.  `norm_num` is the load-bearing step consuming those literals.

FALSE forge: winner (p_w,q_w)=(1,2), a single competitor (p_i,q_i)=(2,3).  The
competitor value 2/3 actually BEATS the winner 1/2, but the forged cert claims
`p_i*q_w < p_w*q_i`, i.e. `2*2 < 1*3` -> `4 < 3`, which `norm_num` rejects.
finite_argmax_certificate REFUSES this (competitor is not strictly below the
winner), so the cert is hand-built to bypass Layer 1.

TRUE twin: winner (3,4) with competitor (1,2) -> `1*4 < 3*2` -> `4 < 6`, true,
compiles clean.

check_lt_one is left False so the ONLY emitted theorem is `_beats_0` (renamed to
bare `name` for the axiom-check), keeping the twins differing solely in the
load-bearing cross-multiplied claim.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_finite_argmax import (
    FiniteArgmaxCertificate,
    FiniteArgmaxMarginEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_false_cert() -> FiniteArgmaxCertificate:
    # winner 1/2, competitor 2/3 (which actually EXCEEDS the winner): the
    # emitted _beats_0 claims 2*2 < 1*3 -> 4 < 3 (FALSE); norm_num rejects.
    return FiniteArgmaxCertificate(
        p_w=sp.Integer(1), q_w=sp.Integer(2),
        competitors=((sp.Integer(2), sp.Integer(3)),),
        check_lt_one=False,
    )


def make_true_cert() -> FiniteArgmaxCertificate:
    # winner 3/4, competitor 1/2 (genuinely below the winner): _beats_0 claims
    # 1*4 < 3*2 -> 4 < 6 (TRUE); compiles clean.
    return FiniteArgmaxCertificate(
        p_w=sp.Integer(3), q_w=sp.Integer(4),
        competitors=((sp.Integer(1), sp.Integer(2)),),
        check_lt_one=False,
    )


def _emit(cert: FiniteArgmaxCertificate, name: str) -> str:
    # FiniteArgmaxMarginEmitter exposes only public emit_body(fam, profile),
    # reading the FiniteArgmaxCertificate off inst.payload.  With a single
    # competitor and check_lt_one=False the emitter writes exactly one theorem
    # `{name}_beats_0`; the generic engine axiom-checks the decl named `name`, so
    # rename it to bare `name`.  All facts are ℤ literals, so no family symbols.
    body = emit_via_single_instance_family(
        FiniteArgmaxMarginEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )
    return body.replace(f"{name}_beats_0", name)


register(
    NegativeControlAdapter(
        emitter_name="FiniteArgmaxMarginEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged finite-argmax cert whose competitor 2/3 actually BEATS the "
            "winner 1/2 but claims p_i*q_w < p_w*q_i (2*2 < 1*3, i.e. 4 < 3): "
            "`norm_num` rejects it.  True twin (winner 3/4 beats 1/2) emits "
            "4 < 6 and compiles."
        ),
        imports_line="import Mathlib",
    )
)
