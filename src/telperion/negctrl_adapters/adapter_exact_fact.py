"""Negative-control adapter for ExactFactEmitter (CERTIFICATE_SENSITIVE).

The emitted, load-bearing Lean fact is a single symbol-free numeric relation
`lhs rel rhs` closed by `decide`.  We forge the origin crux with the inequality
REVERSED (23^129 <= 3^317*2^81, FALSE) and supply a matching corrupted (negative)
target so the emitter's internal diff==target re-check passes; the kernel then
rejects the false `decide` proof.  The TRUE twin is the genuine crux
3^317*2^81 <= 23^129 with a consistent positive target.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from telperion.certify import PolyaCertificate
from telperion.emit_facts import ExactFactEmitter, fact_pow
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


@dataclass(frozen=True)
class _FactCert:
    """Hand-forged ExactFactEmitter cert: the target corner plus the spelling
    the emitter closure must return.  Carries everything emit_call needs to
    rebuild the emitter and its single-instance family."""

    polya: PolyaCertificate           # -> instance_kwargs["corners"] = (polya,)
    lhs: sp.Expr                       # spelling left operand (unevaluated power)
    rel: str                           # spelling relation
    rhs: sp.Expr                       # spelling right operand (unevaluated power)


def _crux_false() -> _FactCert:
    # REVERSED crux: claim 23^129 <= 3^317 * 2^81  (FALSE: 3^317*2^81 < 23^129).
    lhs = fact_pow(23, 129)
    rhs = sp.Mul(fact_pow(3, 317), fact_pow(2, 81), evaluate=False)
    diff = sp.expand(rhs.doit() - lhs.doit())          # rel is "≤": target = rhs - lhs (NEGATIVE)
    polya = PolyaCertificate(expr=sp.Integer(0), numerator=diff, denominator=sp.Integer(1))
    return _FactCert(polya=polya, lhs=lhs, rel="≤", rhs=rhs)


def _crux_true() -> _FactCert:
    # Genuine crux: 3^317 * 2^81 <= 23^129  (TRUE).
    lhs = sp.Mul(fact_pow(3, 317), fact_pow(2, 81), evaluate=False)
    rhs = fact_pow(23, 129)
    diff = sp.expand(rhs.doit() - lhs.doit())          # target = rhs - lhs (POSITIVE)
    polya = PolyaCertificate(expr=sp.Integer(0), numerator=diff, denominator=sp.Integer(1))
    return _FactCert(polya=polya, lhs=lhs, rel="≤", rhs=rhs)


def _emit(cert: _FactCert, name: str) -> str:
    emitter = ExactFactEmitter(
        spelling=lambda _pt, c=cert: (c.lhs, c.rel, c.rhs),
        tactic="decide",
        type_ascription="ℤ",
    )
    return emit_via_single_instance_family(
        emitter,
        lean_name=name,
        instance_kwargs={"corners": (cert.polya,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="ExactFactEmitter",
        make_false_cert=_crux_false,
        make_true_cert=_crux_true,
        emit_call=_emit,
        label="forged reversed integer crux 23^129 <= 3^317*2^81 (FALSE; decide rejects)",
    )
)
