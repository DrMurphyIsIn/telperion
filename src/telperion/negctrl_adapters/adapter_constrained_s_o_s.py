"""Negative-control adapter for ConstrainedSOSEmitter (Putinar / constrained SOS).

CERTIFICATE_SENSITIVE emitter: the load-bearing certificate is the Putinar
decomposition  p = sigma_0 + Sum_i sigma_i * g_i  (+ Sum_j lambda_j * h_j on the
equality variety).  The SOS multipliers sigma_i are the corruptible witness.  The
emitter renders the reconstruction identity as `have hid : p = <rhs> := by ring`;
if the supplied multipliers do not reconstruct p exactly, that `ring` step is a
FALSE polynomial identity and the Lean kernel rejects the file.

FORGERY: take the genuine instance  0 <= x^2*y + y  on {y >= 0}, whose honest
certificate is sigma_1 = x^2 + 1 (so sigma_1 * y = x^2*y + y = p).  We CORRUPT
sigma_1 by dropping its `+1` square, leaving sigma_1 = x^2.  Then the emitted
identity is  y + x^2*y = (1*x^2)*y, i.e. LHS - RHS = y != 0, so `ring` cannot
close it.  (The positivity / mul_nonneg step still succeeds, isolating the
falsehood in the reconstruction identity -- the certificate itself.)  This is
exactly the check `sp.expand(p - recon) != 0` in `certify_putinar_point`, which
we bypass by hand-building the CertifiedInstance payload instead of calling
certify().

The TRUE twin restores the single dropped square (1, 1), the only difference.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_constrained_sos import ConstrainedSOSEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_x, _y = sp.symbols("x y")

# Target polynomial p and the single constraint g_1 = y >= 0.
_P = _x ** 2 * _y + _y
_G1 = _y
_HYP = "hy"


def make_false_cert():
    """Hand-forged Putinar payload with a CORRUPTED SOS multiplier.

    sigma_1 = x^2 (the honest x^2 + 1 with its +1 square dropped), so
    sigma_1 * g_1 = x^2*y != x^2*y + y = p.  The emitted `ring` identity
    `y + x^2*y = (1*x^2)*y` is FALSE and the kernel rejects it.

    payload = (p, sigma0, constraints, equalities), where each constraint is
    (g_i, sigma_i, hyp_name) and sigma_i is a list of (coef, base) SOS terms.
    """
    sigma1_bad = [(1, _x)]  # x^2 only -- the +1 square is missing
    return (_P, [], [(_G1, sigma1_bad, _HYP)], [])


def make_true_cert():
    """The paired TRUE Putinar payload (positive control).

    sigma_1 = x^2 + 1, so sigma_1 * g_1 = (x^2 + 1)*y = x^2*y + y = p exactly;
    the `ring` identity holds and the theorem compiles clean.  Minimal delta
    from the false twin: the single restored SOS square (1, 1).
    """
    sigma1_ok = [(1, _x), (1, sp.Integer(1))]  # x^2 + 1
    return (_P, [], [(_G1, sigma1_ok, _HYP)], [])


def _emit_call(cert, name: str) -> str:
    # Route (A): ConstrainedSOSEmitter exposes only public emit_body(fam,
    # profile); the single-instance-family helper mints a forged CertifiedFamily
    # (flipping the construction guard) whose sole instance carries payload=cert,
    # which emit_body reads directly.
    return emit_via_single_instance_family(
        ConstrainedSOSEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        # emit_body binds `∀ fam.family.symbols : ℝ`; declare x, y so the emitted
        # `∀ x y : ℝ, 0 <= y -> 0 <= p` binder is bound (else both twins fail).
        family_kwargs={"symbols": (_x, _y)},
    )


register(
    NegativeControlAdapter(
        emitter_name="ConstrainedSOSEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "Putinar certificate with a corrupted SOS multiplier "
            "(sigma_1 = x^2 instead of x^2 + 1): the reconstruction identity "
            "y + x^2*y = (1*x^2)*y is false, so the `ring` step fails to compile."
        ),
        imports_line="import Mathlib",
    )
)
