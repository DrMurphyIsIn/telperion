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
