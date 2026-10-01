"""Negative-control adapter for RationalIdentityEmitter.

Forges a CERTIFICATE_SENSITIVE rational-function identity whose rhs numerator
cofactor is corrupted (n+1 -> n+2): `(n^2 - 1)/(n-1) = n + 2` on the ray `1 < n`.
The emitted `rw [div_eq_iff hL0]; ring` spine faces the false polynomial goal
`n^2 - 1 = (n+2)*(n-1)`, which `ring` cannot close, so the kernel rejects the
forged theorem.  The paired true twin `(n^2 - 1)/(n-1) = n + 1` compiles clean.

Both sides are kept in the shape the emitter provably discharges: a SINGLE
fraction on the left and a polynomial on the right (so the spine is the
one-sided `div_eq_iff`).  The earlier `1 + 1/(n-1)` right-hand side is a SUM of a
polynomial and a fraction, which `_split_frac` does not see as one quotient, so
the emitter clears only the LHS denominator and `ring` is left an uncleared
`1/(n-1)` it cannot close -- the TRUE twin would then fail to compile for a
reason unrelated to falsity.  The single-fraction form isolates the numerator
cofactor as the sole load-bearing difference between the twins.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_rational_identity import (
    RationalIdentityEmitter,
    _denominator_roots,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_N = sp.Symbol("n")
_C0 = sp.Rational(1)  # ray bound: 1 < n keeps the (n - 1) denominator nonzero


def _payload(lhs, rhs):
    """Assemble the exact (lhs, rhs, c0, roots) 4-tuple emit_body unpacks."""
    roots = sorted(
        set(_denominator_roots(lhs, _N) + _denominator_roots(rhs, _N))
    )
    return (lhs, rhs, _C0, roots)


def make_true_cert():
    """Genuine identity (n^2 - 1)/(n-1) = n + 1; sp.cancel(lhs - rhs) == 0.

    Single fraction on the left, polynomial on the right, so the emitter's
    one-sided `div_eq_iff` spine reduces to n^2 - 1 = (n+1)(n-1), closed by ring.
    """
    lhs = (_N ** 2 - 1) / (_N - 1)
    rhs = _N + 1
    return _payload(lhs, rhs)


def make_false_cert():
    """Forged twin: rhs numerator cofactor corrupted n+1 -> n+2, so
    lhs - rhs = -1 != 0.  certify_rational_identity_point would REFUSE this
    ('does not cancel to 0'); the emitted `ring` step hits the false goal
    n^2 - 1 = (n+2)*(n-1)."""
    lhs = (_N ** 2 - 1) / (_N - 1)
    rhs = _N + 2  # corrupted numerator cofactor
    return _payload(lhs, rhs)


def _emit_call(cert, name):
    return emit_via_single_instance_family(
        RationalIdentityEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ tuple(fam.family.symbols)[0] : ℚ`; declare n so the
        # emitted `∀ n : ℚ, 1 < n -> lhs = rhs` binder is bound (else IndexError
        # / an unbound identifier -> both twins fail to compile).
        family_kwargs={"symbols": (_N,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="RationalIdentityEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "FALSE rational identity (n^2 - 1)/(n-1) = n + 2 on 1 < n "
            "(rhs numerator cofactor corrupted n+1 -> n+2); ring cannot close "
            "n^2 - 1 = (n+2)*(n-1)."
        ),
        imports_line="import Mathlib",
    )
)


# ---------------------------------------------------------------------------
# Extension controls (2026-10-01): multivariate and minimal-polynomial modes.  NOT
# registered (one adapter per emitter); the kernel runs are in
# tests/test_negctrl_rational_identity_ext.py against examples/rational_identity/lean.
# ---------------------------------------------------------------------------

from telperion.emit_rational_identity import extended_identity_certificate  # noqa: E402

_X, _Y, _T = sp.symbols("x y t")


def make_multivariate_true_cert():
    """1/((x+y)(x+2y)) = (1/(x+y) - 1/(x+2y))/y on x, y > 0 (a two-variable partial fraction)."""
    return extended_identity_certificate(
        symbols=(_X, _Y), lhs=1 / ((_X + _Y) * (_X + 2 * _Y)),
        rhs=(1 / (_X + _Y) - 1 / (_X + 2 * _Y)) / _Y, domain={"x": 0, "y": 0})


def make_multivariate_false_cert():
    """FALSE by 1/1000: the same right side plus 1/1000 (Layer 1 refuses: lhs - rhs = -1/1000);
    `field_simp; ring` is left a goal that is off by a nonzero polynomial."""
    return extended_identity_certificate(
        symbols=(_X, _Y), lhs=1 / ((_X + _Y) * (_X + 2 * _Y)),
        rhs=(1 / (_X + _Y) - 1 / (_X + 2 * _Y)) / _Y + sp.Rational(1, 1000),
        domain={"x": 0, "y": 0}, check=False)


def _emit_ext(cert, name):
    return emit_via_single_instance_family(
        RationalIdentityEmitter(), lean_name=name, instance_kwargs={"payload": cert},
        family_kwargs={"symbols": tuple(cert.symbols)})


MULTIVARIATE_ADAPTER = NegativeControlAdapter(
    emitter_name="RationalIdentityEmitter",
    make_false_cert=make_multivariate_false_cert,
    make_true_cert=make_multivariate_true_cert,
    emit_call=_emit_ext,
    label=("multivariate: 1/((x+y)(x+2y)) = (1/(x+y) - 1/(x+2y))/y + 1/1000 (false): ring "
           "fails after field_simp; the true partial fraction compiles"),
    imports_line="import Mathlib",
)


def make_modular_true_cert():
    """t^5 = 5 t + 3 modulo t^2 - t - 1 (Fibonacci: F_5 = 5, F_4 = 3)."""
    return extended_identity_certificate(symbols=(_T,), lhs=_T ** 5, rhs=5 * _T + 3,
                                         modulus=_T ** 2 - _T - 1)


def make_modular_false_cert():
    """WRONG identity: t^5 = 5 t + 4 modulo t^2 - t - 1 (remainder -1, refused by Layer 1);
    `linear_combination q * h` leaves the nonzero remainder and `ring1` fails."""
    return extended_identity_certificate(symbols=(_T,), lhs=_T ** 5, rhs=5 * _T + 4,
                                         modulus=_T ** 2 - _T - 1, check=False)


MODULAR_ADAPTER = NegativeControlAdapter(
    emitter_name="RationalIdentityEmitter",
    make_false_cert=make_modular_false_cert,
    make_true_cert=make_modular_true_cert,
    emit_call=_emit_ext,
    label=("modulo t^2 - t - 1: t^5 = 5t + 4 (wrong, the remainder is -1): linear_combination "
           "fails; t^5 = 5t + 3 compiles (and its instance at (1 + sqrt 5)/2)"),
    imports_line="import Mathlib",
)
