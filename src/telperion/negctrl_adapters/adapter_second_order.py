"""Negative-control adapter for SecondOrderRecurrenceEmitter (emit_second_order.py).

CERTIFICATE_SENSITIVE: the emitter ships the recurrence-satisfaction (star)
identity for the supplied closed form g,

    have hgid : (A_m)*g(m+2) + (B_m)*g(m+1) + (C_m)*g m = 0 := by
      simp only [g]; push_cast; ring

which is load-bearing for the induction step (`linear_combination hrecm - hgid`).
The recurrence coefficients (A,B,C) and the closed form (g, g_lean) are the
supplied witness.

Recurrence A=1, B=-5, C=6 (characteristic (x-2)(x-3)); the genuine closed form is
g(q) = 2^q + 3^q.

FALSE forge: keep the coefficients (1,-5,6) but ship g = 2^q + 5^q (5 is NOT a
root of (x-2)(x-3)).  The base values are recomputed from this g so
`{name}_base0`/`{name}_base1` still pass (they are norm_num facts about g itself),
but `hgid`'s `ring` fails: (2^(m+2)+5^(m+2)) - 5*(2^(m+1)+5^(m+1)) + 6*(2^m+5^m)
= 5^m*(25-25+6) = 6*5^m != 0.  second_order_certificate REFUSES this (g does not
satisfy the recurrence), so the cert is hand-built to bypass Layer 1.

TRUE twin: coefficients (1,-5,6) with the genuine g = 2^q + 3^q; `hgid` closes by
ring (5^m -> 3^m gives 3^m*(9-15+6)=0) and the whole theorem compiles clean.

The main theorem is named exactly `{name}`, which is the decl the engine
axiom-checks, so no rename is needed.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_second_order import (
    SecondOrderCertificate,
    SecondOrderRecurrenceEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_Q = sp.Symbol("q")
# Recurrence f(q+2) - 5 f(q+1) + 6 f(q) = 0, characteristic (x-2)(x-3).
_A = sp.Integer(1)
_B = sp.Integer(-5)
_C = sp.Integer(6)


def _cert(g: sp.Expr, g_lean: str) -> SecondOrderCertificate:
    # Base values recomputed from THIS g so the base0/base1 norm_num facts always
    # hold; only the (star) recurrence identity distinguishes the twins.
    base0 = sp.Rational(sp.nsimplify(g.subs(_Q, 0)))
    base1 = sp.Rational(sp.nsimplify(g.subs(_Q, 1)))
    return SecondOrderCertificate(
        q0=0, A=_A, B=_B, C=_C, g=g, g_lean=g_lean, base0=base0, base1=base1,
    )


def make_false_cert() -> SecondOrderCertificate:
    # g = 2^q + 5^q does NOT satisfy the (2,3)-recurrence: residual 6*5^q != 0.
    return _cert(2 ** _Q + 5 ** _Q, "(2 : ℝ) ^ q + (5 : ℝ) ^ q")


def make_true_cert() -> SecondOrderCertificate:
    # Genuine solution g = 2^q + 3^q of f(q+2) - 5 f(q+1) + 6 f(q) = 0.
    return _cert(2 ** _Q + 3 ** _Q, "(2 : ℝ) ^ q + (3 : ℝ) ^ q")


def _emit(cert: SecondOrderCertificate, name: str) -> str:
    # SecondOrderRecurrenceEmitter exposes only public emit_body(fam, profile),
    # reading the SecondOrderCertificate off inst.payload.  It names the main
    # theorem exactly `{name}` (plus `{name}_base0/base1` and a `{name}_g` def),
    # so the engine's axiom-check of `name` lands on the main closed-form theorem;
    # no rename, and no family symbols (f/q are bound in the theorem signature).
    return emit_via_single_instance_family(
        SecondOrderRecurrenceEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="SecondOrderRecurrenceEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged second-order cert: coefficients (1,-5,6) [(x-2)(x-3)] with the "
            "non-solution g = 2^q + 5^q; the (star) recurrence identity hgid leaves "
            "residual 6*5^m != 0 so `ring` fails.  True twin uses g = 2^q + 3^q and "
            "compiles."
        ),
        imports_line="import Mathlib",
    )
)
