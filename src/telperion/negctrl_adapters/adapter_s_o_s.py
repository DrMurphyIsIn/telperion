"""Negative-control adapter for SOSEmitter (src/telperion/emit_sos.py).

CERTIFICATE_SENSITIVE: the emitted `have hsos : p = SUM d_i * base_i^2 := by ring`
is a polynomial ring identity.  Corrupting a single multiplier d_i (a Gram / LDL
diagonal entry) breaks the identity, so `ring` -- and hence the kernel -- rejects.

The false cert is minted BY HAND (Layer-1 bypass): certify_sos_point would refuse
it at emit_sos.py:91 (`cert.as_expr() - p != 0`).  emit_body reads p from
`fam.family.target(inst.point)` and the squares from `inst.sos.terms`, so the
single-instance-family helper carries the polynomial via family_kwargs={"target":
..., "symbols": (x,)} and the SOSCertificate via instance_kwargs={"sos": ...}.
That helper opens certify._construction_guard itself, so the forged (uncertified)
family is minted without passing through certify() (which would refuse the false
cert) -- no hand-managed guard flip in this adapter.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_sos import SOSEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)
from telperion.sos import SOSCertificate

# One real symbol; the claim is 0 <= x^2 + 1 over all reals.
_X = sp.Symbol("x")
_TARGET = lambda pt: _X**2 + 1  # noqa: E731 -- match the family's target signature


def make_true_cert() -> SOSCertificate:
    """TRUE twin: x^2 + 1 = 1*(x)^2 + 1*(1)^2 -- an exact SOS identity."""
    return SOSCertificate(terms=((sp.Integer(1), _X), (sp.Integer(1), sp.Integer(1))))


def make_false_cert() -> SOSCertificate:
    """FALSE twin: ONE multiplier corrupted 1 -> 2 on the constant square, so the
    cert CLAIMS x^2 + 1 = 1*(x)^2 + 2*(1)^2 = x^2 + 2.  cert.as_expr() - p = 1 != 0
    (sympy self-check refuses); emitted `ring` must prove 1 = 2 (kernel rejects)."""
    return SOSCertificate(terms=((sp.Integer(1), _X), (sp.Integer(2), sp.Integer(1))))


def _emit_sos(cert: SOSCertificate, name: str) -> str:
    """Render `cert` through SOSEmitter.emit_body via the single-instance family.

    emit_body reads the polynomial p from `fam.family.target(inst.point)` and the
    SOS squares from `inst.sos.terms`, so the family carries the target/symbols and
    the instance carries the (forged or true) SOSCertificate.  The helper opens the
    construction guard, bypassing certify()'s Layer-1 self-check by design.
    """
    return emit_via_single_instance_family(
        SOSEmitter(),
        lean_name=name,
        instance_kwargs={"sos": cert, "tight": ()},
        family_kwargs={"target": _TARGET, "symbols": (_X,)},
    )


register(
    NegativeControlAdapter(
        emitter_name="SOSEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_sos,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged SOS cert doubles one multiplier: claims x^2 + 1 = "
            "1*(x)^2 + 2*(1)^2 (= x^2 + 2). The `by ring` step must prove "
            "1 = 2, which the kernel rejects."
        ),
        imports_line="import Mathlib",
    )
)
