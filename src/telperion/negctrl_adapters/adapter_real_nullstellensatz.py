"""Negative-control adapter for RealNullstellensatzEmitter.

Registers a hand-forged FALSE Real-Nullstellensatz certificate (a corrupted
cofactor) and its minimal TRUE twin, so the kernel-gated negative-control test
can confirm Layer 2 (the Lean kernel) rejects the forged proof while the honest
twin compiles clean.

Canonical instance: p = x vanishes on the REAL variety of x^2 + y^2 (the
origin), certified by p^{2*1} + y^2 = 1*(x^2 + y^2).  The FALSE twin corrupts
the load-bearing cofactor 1 -> 3, breaking the emitted `linear_combination`
step's `ring` closure.  No emoji anywhere (Lean/QuantConnect constraint).

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_real_nullstellensatz import RealNullstellensatzEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Shared, canonical ingredients (all sympy, in the two real symbols x, y).
_X, _Y = sp.symbols("x y")
_P = _X                       # target polynomial p
_M = 1                        # multiplicity -> even power 2m = 2
_SOS = [(sp.Integer(1), _Y)]  # s = 1 * y^2  (nonnegative-rational-coeff SOS)
_GENS = [_X**2 + _Y**2]       # ideal generator; real variety = {origin}


def _make_cert(cofactor):
    """Build the raw 5-tuple payload emit_body reads off inst.payload:
    (p, m, sos, gens, cofactors).  `cofactor` is the single load-bearing
    multiplier of the generator in p^{2m} + s = h * (x^2 + y^2)."""
    return (_P, _M, list(_SOS), list(_GENS), [sp.sympify(cofactor)])


def make_true_cert():
    """Positive control: the HONEST cofactor 1, so p^2 + y^2 = 1*(x^2 + y^2)
    is a true ring identity and the emitted proof compiles clean."""
    return _make_cert(1)


def make_false_cert():
    """Forged FALSE control: cofactor corrupted 1 -> 3.  The emitted
    `linear_combination 3*e1` step reduces to the FALSE ring identity
    -2*x^2 - 2*y^2 = 0, so `ring` fails and the kernel rejects the proof.
    Everything else (statement, SOS, generators) is identical to the twin,
    isolating the cofactor as the corruptible certificate element."""
    return _make_cert(3)


def _emit(cert, name: str) -> str:
    # RealNullstellensatzEmitter has only public emit_body(fam, profile); route
    # through a single-instance CertifiedFamily whose lone instance carries the
    # (possibly forged) payload.  The emitter binds `∀ fam.family.symbols : ℝ`,
    # so declare x, y via family_kwargs (else the emitted `∀ x y : ℝ, x^2+y^2 = 0
    # -> x = 0` references unbound identifiers and both twins fail to compile).
    return emit_via_single_instance_family(
        RealNullstellensatzEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        family_kwargs={"symbols": (_X, _Y)},
    )


register(
    NegativeControlAdapter(
        emitter_name="RealNullstellensatzEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Real-Nullstellensatz cofactor forgery: p=x on V(x^2+y^2); "
            "corrupt the load-bearing cofactor 1 -> 3 so linear_combination's "
            "ring step (-2*x^2 - 2*y^2 = 0) is false and the kernel rejects."
        ),
        imports_line="import Mathlib",
    )
)
