"""Negative-control adapter for ConeFarkasEmitter (emit_cone.py).

CERTIFICATE_SENSITIVE emitter: the emitted proof is
    theorem N : (0:R) <= <target> := by
      have hid : <target> = <Sum w_i * b_i> := by ring
      rw [hid]; positivity
where <target> = ConeCombination.as_expr() = Sum w_i * b_i.  The `ring` step is
trivially satisfiable (target IS the combo); the load-bearing fact is
`positivity`, which succeeds only when every Farkas weight w_i is nonnegative.

FALSE forge: flip one multiplier sign (lambda_0: +1 -> -1) on a genuinely
nonneg basis element x^2.  Emits `0 <= -x^2` with hid `-x^2 = -1 * x^2`;
`ring` closes hid, but `positivity` cannot prove `0 <= -1 * x^2` and the goal
`0 <= -x^2` is false, so the kernel rejects.  certify_cone_point would refuse
this (it solves with nonnegative weights and re-checks exactly), so the cert is
hand-built to bypass Layer 1.

TRUE twin: weights=(+1,), same basis -> `0 <= x^2`, compiles clean.

The basis is the SYMBOLIC nonneg element x^2, not a bare numeral: with a
constant target the emitter's `rw [hid]` (hid : 4 = 1 * 4) cannot locate the
`OfNat` literal 4 inside `0 <= 4`, so the TRUE twin would fail to compile for a
reason unrelated to falsity.  A symbolic square makes `rw` match cleanly, leaving
the load-bearing multiplier sign the sole difference between the twins.  The free
symbol x is declared via family_kwargs so the emitted `∀ x : ℝ` binder is bound.
"""
from __future__ import annotations

import sympy as sp

from telperion.cone import ConeCombination
from telperion.emit_cone import ConeFarkasEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Symbolic nonneg basis element (positivity-provable square) so the emitted
# `rw [hid]` has a real subterm x^2 to rewrite (a bare numeral defeats rw).  The
# free symbol x is declared to the family so the `∀ x : ℝ` binder is bound.
_X = sp.Symbol("x")
_BASIS = (_X ** 2,)


def make_false_cert() -> ConeCombination:
    # Corrupted Farkas multiplier: lambda_0 = -1 (< 0) on a nonneg basis.
    # as_expr() = -x^2 -> theorem claims 0 <= -x^2 (FALSE); positivity rejects.
    return ConeCombination(weights=(sp.Integer(-1),), basis=_BASIS)


def make_true_cert() -> ConeCombination:
    # Minimal repair: lambda_0 = +1 (>= 0).  as_expr() = x^2 -> 0 <= x^2 compiles.
    return ConeCombination(weights=(sp.Integer(1),), basis=_BASIS)


def _emit_call(cert: ConeCombination, name: str) -> str:
    # ConeFarkasEmitter exposes only public emit_body(fam, profile); it reads
    # inst.payload as the ConeCombination and binds `∀ fam.family.symbols`.
    # Route (A): single-instance family, declaring the free symbol x.
    return emit_via_single_instance_family(
        ConeFarkasEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        family_kwargs={"symbols": (_X,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="ConeFarkasEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged cone/Farkas cert with a NEGATIVE multiplier (lambda_0 = -1) "
            "on a nonneg basis element x^2: claims 0 <= -x^2.  `ring` closes the "
            "identity hid (-x^2 = -1*x^2) but `positivity` cannot prove "
            "0 <= -1*x^2 and the goal is false, so the kernel rejects.  True twin "
            "flips the weight to +1 (0 <= x^2) and compiles."
        ),
        imports_line="import Mathlib",
    )
)
