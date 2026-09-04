"""Negative-control adapter for CGRoundEmitter (Chvatal-Gomory integer rounding).

The emitted theorem is `forall x : Int, (facts) -> goal`, closed by `omega`.
Because `omega` is a complete LIA decision procedure that performs CG rounding
itself, the kernel only checks whether the GOAL follows from the FACTS over the
integers -- corrupting an internal multiplier or a cg_round step is invisible to
the kernel (omega re-derives any true implication). The single meaningful
falsification is therefore to forge a payload whose emitted STATEMENT is a false
integer implication.

FALSE forgery: keep the genuine fact `3*x >= 2` but corrupt the goal bound from
`x >= 1` to `x >= 2`. Over Int, `3x >= 2` only yields `x >= 1` (x = 1 satisfies
3 >= 2 yet 1 >= 2 is false), so `omega` cannot close `x >= 2` and the kernel
rejects. Layer 1 (certify_cg_round_point._dominates) would also refuse this, but
build_single_instance_family bypasses certify()'s guard so the TRUSTED Lean
kernel is the arbiter.

TRUE twin: the canonical single-cut certificate with goal `x >= 1` (one scalar
different: goal rhs 1 vs 2), which omega closes and which compiles clean.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from telperion.emit_cg_round import CGRoundEmitter, _norm_fact
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Single integer variable x; a CG-round payload is the 4-tuple the emitter's
# emit_body reads directly: (symbols, facts0, deriv, goal), with facts0/goal
# normalized to (dict[sym -> sympy.Rational], sympy.Rational) as _norm_fact
# produces (matching what certify_cg_round_point stores in inst.payload).
_X = sp.Symbol("x")


def _payload(goal_rhs: int):
    """CG payload with fact 3*x >= 2, single-cut derivation, and goal x >= goal_rhs."""
    facts0 = [_norm_fact(({"x": 3}, Fr(2)))]                     # 3x >= 2
    deriv = [
        {"rule": "lincomb", "combo": {0: Fr(1, 3)}, "const": Fr(0)},  # x >= 2/3
        {"rule": "cg_round", "src": 1},                              # x >= ceil(2/3)=1
    ]
    goal = _norm_fact(({"x": 1}, Fr(goal_rhs)))
    return (tuple([_X]), facts0, deriv, goal)


def make_false_cert():
    # Corrupt ONLY the goal bound: x >= 2, which 3x >= 2 does NOT imply over Int
    # (x = 1 is a counterexample) -> omega fails -> kernel rejects.
    return _payload(2)


def make_true_cert():
    # The genuine single-cut certificate: 3x >= 2 forces x >= 1 over Int.
    return _payload(1)


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        CGRoundEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="CGRoundEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged CG-round goal x >= 2 from fact 3*x >= 2 (only x >= 1 is "
            "implied over Int; x = 1 is a counterexample, so omega fails)"
        ),
        imports_line="import Mathlib",
    )
)
