"""Negative-control adapter for NullstellensatzEmitter.

CERTIFICATE_SENSITIVE emitter: the finite witness is the ideal-membership
cofactor tuple `(h_1, ..., h_m)` with `p = Sum_i h_i * g_i`.  The emitted Lean
is `linear_combination Sum_i (h_i) * hg_i`, whose sole correctness obligation is
that `p - Sum_i h_i * g_i` ring-reduces to zero.  Corrupting one cofactor makes
that residual a nonzero polynomial, so `linear_combination`'s trailing `ring`
fails and the Lean kernel rejects the forged proof.

The emitter's `emit_body` reads `inst.payload = (p, gens, cofactors)` and splices
the cofactors straight into the tactic with NO re-verification, so the forged
payload (minted through `build_single_instance_family`, which opens
`certify._construction_guard`) never passes Layer-1 `certify_nullstellensatz_point`.
"""
from __future__ import annotations

from typing import Any, List, Tuple

import sympy as sp

from telperion.emit_nullstellensatz import NullstellensatzEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# One real symbol; a single ideal generator g = x - 1 and target p = x^2 - 1.
# p lies in <x - 1> with the genuine cofactor h = x + 1, since (x+1)(x-1)=x^2-1.
_X = sp.Symbol("x")


def _payload(cofactor: sp.Expr) -> Tuple[sp.Expr, List[sp.Expr], List[sp.Expr]]:
    """Assemble the (p, gens, cofactors) payload tuple the emitter reads.

    `p` and `gens` are held fixed (a genuinely true ideal-membership instance);
    only the single cofactor varies between the true twin and the forgery.
    """
    p = sp.expand(_X ** 2 - 1)
    gens: List[sp.Expr] = [sp.expand(_X - 1)]
    cofactors: List[sp.Expr] = [sp.expand(cofactor)]
    return (p, gens, cofactors)


def make_true_cert() -> Any:
    """Genuine ideal-membership cert: cofactor h = x + 1, so p - h*g = 0."""
    return _payload(_X + 1)


def make_false_cert() -> Any:
    """Hand-forged FALSE cert: corrupt the sole cofactor to h = x + 2.

    Then p - h*g = (x^2-1) - (x+2)(x-1) = 1 - x, a NONZERO polynomial, so the
    emitted `linear_combination (x + 2) * hg1` cannot close `x^2 - 1 = 0` under
    `x - 1 = 0`; `ring` leaves the residual `1 - x = 0` and the kernel rejects.

    `certify_nullstellensatz_point` would REFUSE this (it recomputes cofactors
    via sympy.reduced and checks p - Sum h*g == 0); building the payload by hand
    bypasses that Layer-1 guard entirely.
    """
    return _payload(_X + 2)


def _emit_call(cert: Any, name: str) -> str:
    """(cert, name) -> Lean `theorem <name> : ... := by ...` proof ATTEMPT.

    Route (A): NullstellensatzEmitter exposes only public emit_body(fam, profile)
    reading inst.payload, so we mint a single-instance CertifiedFamily whose sole
    instance carries `payload=cert` and render it.
    """
    return emit_via_single_instance_family(
        NullstellensatzEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ fam.family.symbols : ℝ`; declare x so the emitted
        # `∀ x : ℝ, x - 1 = 0 -> x^2 - 1 = 0` binder is bound.
        family_kwargs={"symbols": (_X,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="NullstellensatzEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "FALSE ideal-membership: forged cofactor h = x + 2 for "
            "p = x^2 - 1, g = x - 1 (genuine h = x + 1); residual "
            "p - h*g = 1 - x != 0 so linear_combination's ring fails."
        ),
        imports_line="import Mathlib",
    )
)
