"""Negative-control adapter for RecursiveDominationRatioEmitter
(emit_domination_ratio.py).

CERTIFICATE_SENSITIVE: the emitter bakes the certificate's per-corner D-values
(D = P - Q) into the load-bearing convex-combination identity

    have hid : (D) * (prod(u_i - l_i)) = Σ_corner (wnum_corner) * (D_value_corner)
            := by ring

Corrupting a single corner D-value makes this a FALSE polynomial identity, so
`ring` cannot close it and the kernel rejects.

Instance: the 1-parameter linear ratio P = 2*x, Q = x on box [1,2] (D = x).
True corners: lo (x=1) -> D=1, hi (x=2) -> D=2; the identity
`x*(2-1) = (2-x)*1 + (x-1)*2 = x` holds by `ring`.

FALSE forge: corrupt the lo corner value from 1 to 5.  The emitted `hid` becomes
`x*(2-1) = (2-x)*5 + (x-1)*2`, i.e. `x = 8 - 3x`, a FALSE identity that `ring`
rejects.  (The nonneg witness `hq0 : 0 ≤ (2-x)*5` still closes by norm_num since
5 > 0, so the rejection is due to the false identity, not malformed Lean.)
domination_ratio_certificate re-checks the convex-combination identity exactly and
would REFUSE the corrupted corner, so the cert is hand-built to bypass Layer 1.

TRUE twin: the genuine certificate (lo -> 1); `hid` holds and it compiles clean.

The emitted theorem is named exactly `{lean_name}` (= name) and binds `(x : ℝ)`
in its own signature, so no rename and no family symbols are needed.
"""
from __future__ import annotations

import dataclasses

import sympy as sp

from telperion.emit_domination_ratio import (
    RecursiveDominationRatioEmitter,
    domination_ratio_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_X = sp.Symbol("x")


def make_true_cert():
    # Genuine 1-param linear ratio: P=2x, Q=x on [1,2] -> D=x, corners (1, 2).
    return domination_ratio_certificate(2 * _X, _X, (_X,), ((1, 2),))


def make_false_cert():
    # Start from the genuine cert, then corrupt the lo corner's D-value 1 -> 5.
    # The convex-combination identity D*(u-l) = Σ wnum*D_corner no longer holds:
    # x*(2-1) = (2-x)*5 + (x-1)*2 = 8 - 3x != x, so `ring` in hid fails.
    true = make_true_cert()
    forged_corners = tuple(
        (key, sp.Integer(5) if key == ("lo",) else dv)
        for key, dv in true.corners
    )
    return dataclasses.replace(true, corners=forged_corners)


def _emit(cert, name: str) -> str:
    # RecursiveDominationRatioEmitter exposes only public emit_body(fam, profile),
    # reading the DominationRatioCertificate off inst.payload.  It names the single
    # theorem exactly `{lean_name}` (= name) and binds `(x : ℝ)` in the signature,
    # so no rename and no family symbols are needed.
    return emit_via_single_instance_family(
        RecursiveDominationRatioEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="RecursiveDominationRatioEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged domination-ratio cert corrupting the lo-corner D-value 1 -> 5 "
            "(P=2x, Q=x on [1,2]): the convex-combination identity hid "
            "`x*(2-1) = (2-x)*5 + (x-1)*2` (= 8-3x != x) is a FALSE polynomial "
            "identity `ring` rejects.  True twin keeps D=1 and compiles."
        ),
        imports_line="import Mathlib",
    )
)
