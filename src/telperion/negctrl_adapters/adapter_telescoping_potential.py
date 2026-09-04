"""Negative-control adapter for TelescopingPotentialEmitter.

The telescoping emitter closes a tree bound by a per-node super-solution:
each certified node-class ships one kernel fact

    theorem <name>_c0 : (0:R) <= <margin> := by positivity

where <margin> = P(v) - sum P(children) - local(v) is guaranteed NONNEGATIVE by
polya_certify (all-nonneg-coefficient numerator over a positive denominator).
That nonnegativity is the load-bearing fact `positivity` discharges.

FALSE forge: hand-build a PolyaCertificate (bypassing polya_certify's Layer-1
self-check) whose margin is  -x^2 - 1 , negative for every real x.  The emitted
`0 <= 0 - 1 - x ^ 2 := by positivity` is a genuinely false nonnegativity claim;
`positivity` cannot close it and the Lean KERNEL rejects the proof (Layer 2).

TRUE twin: the minimal sign-flip  x^2 + 1 , a legitimate nonnegative margin;
`0 <= 1 + x ^ 2 := by positivity` compiles clean.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.certify import CertifiedInstance, PolyaCertificate
from telperion.emit_telescope import TelescopingPotentialEmitter
from telperion.lean import LeanProfile
from telperion.negative_control_harness import NegativeControlAdapter, register

# Single free real symbol; the margin is a univariate polynomial in it.
_X = sp.Symbol("x")
_SYMS: tuple[sp.Symbol, ...] = (_X,)


def _telescope_payload(numerator: sp.Expr) -> tuple:
    """Hand-forge the emitter payload (certs, syms) with denominator 1.

    Bypasses polya_certify entirely: PolyaCertificate.numerator is stored as-is,
    so a numerator with a negative floor is emitted verbatim (Layer 1 bypassed).
    """
    cert = PolyaCertificate(
        expr=numerator,
        numerator=sp.expand(numerator),
        denominator=sp.Integer(1),
        lift_n=0,
    )
    return ((cert,), _SYMS)


def make_false_cert() -> tuple:
    # margin = -x^2 - 1 : strictly negative for all real x (max = -1 at x=0).
    return _telescope_payload(-_X**2 - 1)


def make_true_cert() -> tuple:
    # margin = x^2 + 1 : nonnegative everywhere (minimal sign-flip twin).
    return _telescope_payload(_X**2 + 1)


class _SingleInstanceFamily:
    """Minimal fam shim: emit_body only reads `.instances`."""

    def __init__(self, inst: CertifiedInstance) -> None:
        self.instances: tuple[CertifiedInstance, ...] = (inst,)


def emit_call(cert: tuple, name: str) -> str:
    """(payload, name) -> the single super-solution theorem, decl-named `name`.

    Builds a one-instance family by hand and runs the REAL emit_body, then strips
    the emitter's `_c0` node-class suffix so the kernel-checked declaration is
    exactly `name` (what generic_negative_control verifies).
    """
    inst = CertifiedInstance(point={}, lean_name=name, corners=(), payload=cert)
    fam = _SingleInstanceFamily(inst)
    body, _n = TelescopingPotentialEmitter().emit_body(fam, LeanProfile())
    return body.replace(f"{name}_c0", name)


register(
    NegativeControlAdapter(
        emitter_name="TelescopingPotentialEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "forged telescoping super-solution margin -x^2-1 (negative for all "
            "real x): claims 0 <= -1 - x^2 via positivity; kernel must reject"
        ),
        imports_line="import Mathlib",
    )
)
