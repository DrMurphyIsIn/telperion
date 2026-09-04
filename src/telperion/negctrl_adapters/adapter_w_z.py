"""Negative-control adapter for WZEmitter (Wilf-Zeilberger creative telescoping).

The load-bearing fact is the denominator-cleared WZ equation, emitted as an
exact `ring` polynomial identity `termA - termB - termC + termD = 0`.  A correct
WZ mate R(n,k) makes this identically zero; a corrupted mate makes it a genuine
non-zero polynomial, so `ring` cannot close the goal and the kernel rejects it.

FALSE twin: the canonical identity Sum_k C(n,k) = 2^n with its mate corrupted
from R = -k/(2(n-k+1)) to R+1.  certify_wz_point REFUSES this (WZ-equation
rational check fails), so the payload is hand-built here to bypass Layer 1.
TRUE twin: the same identity with the genuine mate; certifies + compiles clean.
"""
from __future__ import annotations

from typing import Any

import sympy as sp

from telperion.emit_wz import WZEmitter, _hyper_ratio
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Canonical WZ instance: Sum_k binomial(n,k) = 2^n, mate R = -k/(2(n-k+1)).
_n, _k = sp.symbols("n k")
_F = sp.binomial(_n, _k)
_RHS = 2 ** _n
_R_TRUE = -_k / (2 * (_n - _k + 1))
_R_FALSE = _R_TRUE + 1          # additive corruption of the mate (breaks ring)


def _wz_payload(F: sp.Expr, R: sp.Expr, rhs: sp.Expr,
                n: sp.Symbol, k: sp.Symbol) -> tuple:
    """Build the emit_body payload (n, k, termA, termB, termC, termD).

    Replicates certify_wz_point's denominator-clearing arithmetic exactly, but
    for an ARBITRARY (possibly corrupt) mate R -- the certification WZ-equation
    check is deliberately NOT run, so a false mate yields a false payload.
    """
    ratio_n = _hyper_ratio(F.subs(n, n + 1), F, (n, k))
    ratio_k = _hyper_ratio(F.subs(k, k + 1), F, (n, k))
    rhs_ratio = sp.simplify(rhs / rhs.subs(n, n + 1))
    a = sp.together(ratio_n * rhs_ratio)      # F~(n+1,k)/F~(n,k)
    b = ratio_k                               # F~(n,k+1)/F~(n,k)
    na, da = sp.fraction(sp.together(a))
    nb, db = sp.fraction(sp.together(b))
    nR, dR = sp.fraction(sp.together(R))
    nR1, dR1 = sp.fraction(sp.together(R.subs(k, k + 1)))
    termA = (na, dR1, db, dR)                 #  a . D
    termB = (da, dR1, db, dR)                 #  1 . D
    termC = (nR1, nb, da, dR)                 #  R(n,k+1) . b . D
    termD = (nR, da, dR1, db)                 #  R . D
    return (n, k, termA, termB, termC, termD)


def make_false_cert() -> Any:
    """Payload of the forged FALSE instance (corrupted mate R+1)."""
    return _wz_payload(_F, _R_FALSE, _RHS, _n, _k)


def make_true_cert() -> Any:
    """Payload of the genuine TRUE twin (the real WZ mate)."""
    return _wz_payload(_F, _R_TRUE, _RHS, _n, _k)


def emit_call(cert: Any, name: str) -> str:
    # WZEmitter names its theorem `{lean_name}_wz` (the emitter's convention),
    # but the generic engine axiom-checks the decl named exactly `name`
    # (verify_lean(..., decls=[name])).  Rename the single emitted identifier
    # `{name}_wz` -> `name` so the engine can `#print axioms` the theorem it
    # elaborated; the statement and proof are untouched, so the negative/positive
    # controls still turn solely on the (corrupt vs genuine) WZ mate.  The WZ
    # statement binds `∀ n k : ℝ` literally with the payload's own n, k, so no
    # family symbols are needed.
    body = emit_via_single_instance_family(
        WZEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )
    return body.replace(f"{name}_wz", name)


register(NegativeControlAdapter(
    emitter_name="WZEmitter",
    make_false_cert=make_false_cert,
    make_true_cert=make_true_cert,
    emit_call=emit_call,
    label=("WZ mate for Sum_k C(n,k)=2^n corrupted R -> R+1: the "
           "denominator-cleared WZ equation is no longer the zero polynomial, "
           "so `ring` fails and the kernel rejects the forged certificate."),
))
