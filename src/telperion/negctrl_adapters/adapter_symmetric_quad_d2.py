"""Negative-control adapter for SymmetricQuadD2Emitter (emit_symmetric_quad_d2.py).

CERTIFICATE_SENSITIVE: the load-bearing step is the exact three-piece
completing-the-square congruence (symbolic in N)

    have hid : Q2(f0..f4) = piece1 + pcoef*(T2 - s1^2/N) + a*N2 := by
      subst hT2; subst hN2def; field_simp; ring

with T2 substituted by cert.t2_expr and N2 by cert.n2_expr.  Corrupting t2_expr
(or n2_expr / pcoef / a / a moment) so the three pieces no longer reassemble to
Q2 leaves a nonzero residual, so `ring` fails to close hid and the kernel rejects.

FALSE forge: start from the genuine knapsack-moment certificate, then add the
constant 1 to t2_expr.  The emitted hid RHS then carries an extra pcoef*1 term
(pcoef = N/(4(N-1))), so Q2 - RHS = -pcoef != 0 and `field_simp; ring` cannot
close the identity.  The additive constant does not introduce a new denominator
atom, so field_simp's denominator handling is unchanged -- the rejection is due
to the false symbolic identity, not malformed Lean.  symmetric_quad_d2_certificate
re-verifies the assembly over Q(N) and would REFUSE a broken t2_expr, so the cert
is hand-built to bypass Layer 1.

TRUE twin: the genuine certificate; hid closes by field_simp; ring and the whole
theorem compiles clean.

The emitted theorem is named exactly `{name}` and binds N and all coordinates in
its own signature, so no rename and no family symbols are needed.
"""
from __future__ import annotations

import dataclasses

import sympy as sp

from telperion.emit_symmetric_quad_d2 import (
    SymmetricQuadD2Emitter,
    _knapsack_f,
    symmetric_quad_d2_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_true_cert():
    # Genuine level-2 PSD certificate for the knapsack harmonic moments f(N,0..4).
    return symmetric_quad_d2_certificate(
        _knapsack_f(0), _knapsack_f(1), _knapsack_f(2), _knapsack_f(3), _knapsack_f(4),
        n_min=4,
    )


def make_false_cert():
    # Corrupt the T2 defining expression by +1: the three-piece assembly
    # Q2 = piece1 + pcoef*(T2 - s1^2/N) + a*N2 gains a spurious pcoef*1 term, so
    # `field_simp; ring` in hid fails on the nonzero residual (-pcoef).
    true = make_true_cert()
    return dataclasses.replace(true, t2_expr=sp.expand(true.t2_expr + 1))


def _emit(cert, name: str) -> str:
    # SymmetricQuadD2Emitter exposes only public emit_body(fam, profile), reading
    # the SymmetricQuadD2Certificate off inst.payload.  It names the single theorem
    # exactly `{name}` and binds N + all collective coordinates in the signature,
    # so no rename and no family symbols are needed.
    return emit_via_single_instance_family(
        SymmetricQuadD2Emitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="SymmetricQuadD2Emitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged d=2 moment cert adding +1 to the T2 defining expression: the "
            "three-piece completing-the-square identity hid gains a spurious "
            "pcoef*1 term, so `field_simp; ring` fails on the nonzero residual "
            "(-pcoef = -N/(4(N-1))).  True twin uses the genuine T2 and compiles."
        ),
        imports_line="import Mathlib",
    )
)
