"""Negative-control adapter for HandelmanEmitter.

Handelman emits `0 <= p` on a polytope {l_i >= 0} from a certificate
`p = sum c_alpha * prod l_i^{alpha_i}` with every c_alpha >= 0.  The load-bearing
fact is the EXACT reconstruction identity, rendered as `have hid : p = rhs := by
ring`.  We forge a FALSE cert by corrupting one nonnegative coefficient: the sign
guard still passes (the coefficient stays >= 0), but the ring identity becomes
false, so the kernel rejects the forged proof.  The TRUE twin restores the honest
coefficient and compiles clean.

READ-ONLY generator output: registered at import so the gate test discovers it.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_handelman import HandelmanEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Polytope [0, 1] on a single variable x: constraints L = x >= 0, U = 1 - x >= 0.
_X = sp.Symbol("x")
_CONSTRAINTS = [(_X, "hL"), (1 - _X, "hU")]

# Target p = x + 2  (== 3*x + 2*(1 - x) expanded), positive on [0, 1].
_P = _X + 2


def make_true_cert():
    """Genuine Handelman certificate: p = 3*L^1 + 2*U^1 = x + 2 (exact)."""
    terms = [(sp.Integer(3), (1, 0)), (sp.Integer(2), (0, 1))]
    return (sp.expand(_P), list(_CONSTRAINTS), terms)


def make_false_cert():
    """Forged cert: first coefficient corrupted 3 -> 5 (still nonnegative, so the
    sign guard passes) so the claimed identity x + 2 = 5*L + 2*U = 3*x + 2 is
    FALSE (LHS - RHS = -2*x).  emit_body renders `by ring` on this false identity;
    the kernel rejects it.  Layer 1's sp.expand(p - recon) = -2*x != 0 also refuses."""
    terms = [(sp.Integer(5), (1, 0)), (sp.Integer(2), (0, 1))]
    return (sp.expand(_P), list(_CONSTRAINTS), terms)


def _emit_call(cert, name):
    # Single-instance-family route: the forged (p, constraints, terms) tuple is
    # carried as CertifiedInstance.payload, exactly what HandelmanEmitter.emit_body
    # reads.  build_single_instance_family mints the family without going through
    # certify(), bypassing the Layer-1 self-check (the negative-control point).
    return emit_via_single_instance_family(
        HandelmanEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ fam.family.symbols : ℝ`; declare x so the emitted
        # `∀ x : ℝ, 0 <= x -> 0 <= 1-x -> 0 <= p` binder is bound.
        family_kwargs={"symbols": (_X,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="HandelmanEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        label=(
            "Forged Handelman cert: p = x + 2 on [0,1] with first coefficient "
            "corrupted 3 -> 5, claiming x + 2 = 5*x + 2*(1 - x) = 3*x + 2 "
            "(false by -2*x); the `ring` reconstruction identity fails."
        ),
    )
)
