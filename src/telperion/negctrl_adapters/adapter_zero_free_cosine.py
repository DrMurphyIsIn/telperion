"""Negative-control adapter for ZeroFreeCosineEmitter (CERTIFICATE_SENSITIVE).

Fejer-Riesz/Handelman witness p = Sum c_a prod l^a. The load-bearing emitted
step is `have hid : (p : R) = Sum c_a * prod l^a := by ring`. Corrupting one
Handelman coefficient makes rhs != p as polynomials, so `ring` fails and the
Lean kernel rejects the forged proof -- while the theorem statement (p >= 0)
stays true. This is the Layer-2 property: the generator cannot forge a
COMPILING proof, even of a statement that happens to be true.

The de la Vallee-Poussin d=2 instance is the twin base:
  n=2, a=[3/2,2,1/2], p = 2 + 4x + 2x^2 = 2*(1+x)^2,
  constraints=[(1+x,'hx1'),(1-x,'hx2')], scale_used=2, F=f_functional(a).
TRUE terms = [(2,(2,0))]   ->  hid : p = 2*(1+x)^2   (ring closes; compiles)
FALSE terms = [(3,(2,0))]  ->  hid : p = 3*(1+x)^2   (ring fails; rejected)
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_zero_free_cosine import (
    ZeroFreeCosineEmitter,
    cosine_to_chebyshev,
    f_functional,
    vallee_poussin_coeffs,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# de la Vallee-Poussin degree for the twin (smallest with a nontrivial box term).
_N = 2


def _base_payload():
    """Common (certified) d=2 data shared by both twins, minus the `terms`.

    Returns (n, a, p, constraints, scale_used, F). p is the integer-cleared
    Chebyshev reduction 2*(1+x)^2; constraints are the box {1+x, 1-x}.
    """
    x = sp.Symbol("x")
    a = vallee_poussin_coeffs(_N)                       # [3/2, 2, 1/2]
    scale_used = sp.Integer(2)                          # lcm of denominators
    p = sp.expand(scale_used * cosine_to_chebyshev(a, x))   # 2 + 4x + 2x^2
    constraints = [(1 + x, "hx1"), (1 - x, "hx2")]
    F = f_functional(a)
    return _N, a, p, constraints, scale_used, F


def make_true_cert():
    """Genuinely TRUE twin: correct Handelman coefficient 2 for the (1+x)^2 term.

    payload matches exactly what certify_zero_free_cosine_point would produce for
    n=2: p = 2*(1+x)^2 with the single term (2, (2,0)). Emitted proof compiles.
    """
    n, a, p, constraints, scale_used, F = _base_payload()
    terms = [(sp.Rational(2), (2, 0))]                  # 2 * (1+x)^2 * (1-x)^0
    return (n, a, p, constraints, terms, scale_used, F)


def make_false_cert():
    """Hand-forged FALSE cert: corrupt the Handelman coefficient 2 -> 3.

    certify's step-4 re-verification (p - Sum c_a prod l^a == 0) would REFUSE
    this (residual -x^2 - 2x - 1 != 0), so it is built BY HAND and reaches the
    emitter through the single-instance-family construction guard. emit_body then
    writes `have hid : (2 + 4*x + 2*x^2 : R) = 3*(1+x)^2 := by ring`, a false
    polynomial identity, so `ring` fails and the kernel rejects the proof.
    """
    n, a, p, constraints, scale_used, F = _base_payload()
    terms = [(sp.Rational(3), (2, 0))]                  # corrupted: 3 instead of 2
    return (n, a, p, constraints, terms, scale_used, F)


def _emit_call(cert, name):
    """emit_body only reads inst.payload, so drive it via a single-instance family.

    build_single_instance_family fills point={}/lean_name and flips the
    construction guard so the forged payload is minted without going through
    certify() (which would refuse the corrupted coefficient).
    """
    return emit_via_single_instance_family(
        ZeroFreeCosineEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="ZeroFreeCosineEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",                       # no FSTAR / no extra defs needed
        allow_axioms=(),                  # standard [propext, Classical.choice, Quot.sound]
        label=(
            "Forged Fejer-Riesz/Handelman witness for the d=2 de la "
            "Vallee-Poussin polynomial: the box-term coefficient is corrupted "
            "2 -> 3, so the emitted `p = Sum c_a prod l^a` identity closed by "
            "`ring` is false (3*(1+x)^2 != 2*(1+x)^2) and the kernel rejects."
        ),
        imports_line="import Mathlib",
    )
)
