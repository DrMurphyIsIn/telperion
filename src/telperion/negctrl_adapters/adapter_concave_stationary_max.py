"""Negative-control adapter for ConcaveStationaryMaxEmitter
(emit_concave_stationary_max.py).

CERTIFICATE_SENSITIVE: the emitter ships a `_foc` theorem asserting the exact
rational first-order condition

    g'(f*) = wr*b/(1+f*·b) - (1-wr)/(1-f*) = 0   := by norm_num

where `f*` (=cert.fstar) is a SEPARATELY-supplied stationary point.  If f* is not
the true Kelly root, `_foc` becomes a FALSE rational identity and `by norm_num`
fails at the kernel.  (The companion `_concave` theorem reads only wr, b, so it
stays compiling regardless of f* — the twins differ ONLY in fstar.)

FALSE forge: wr=55/100, b=2 with fstar=1/2 (the true Kelly root is 325/1000).
The emitted `_foc` becomes 55/100*2/(1+1/2*2) - (1-55/100)/(1-1/2)
= 11/20 - 9/10 = -7/20 != 0, so `norm_num` rejects it.
concave_stationary_max_certificate REFUSES fstar=1/2 (non-stationary), so the
cert is hand-built to bypass Layer 1.

TRUE twin: same wr=55/100, b=2 with the real Kelly root fstar=325/1000; `_foc`
clears to 0 and both theorems compile clean.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_concave_stationary_max import (
    ConcaveStationaryMaxCertificate,
    ConcaveStationaryMaxEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Kelly parameters wr=0.55, b=2 -> true stationary point f* = (0.55*2 - 0.45)/2 = 0.325.
_WR = sp.Rational(55, 100)
_B = sp.Integer(2)
_FSTAR_TRUE = sp.Rational(325, 1000)   # the real Kelly root; g'(f*) = 0
_FSTAR_FALSE = sp.Rational(1, 2)       # non-stationary; g'(1/2) = -7/20 != 0


def make_false_cert() -> ConcaveStationaryMaxCertificate:
    # Corrupted stationary point: fstar=1/2 is NOT the Kelly root (325/1000).
    # concave_stationary_max_certificate would REFUSE this (g'(fstar) != 0); the
    # cert is minted by hand to bypass Layer 1.
    return ConcaveStationaryMaxCertificate(wr=_WR, b=_B, fstar=_FSTAR_FALSE)


def make_true_cert() -> ConcaveStationaryMaxCertificate:
    # Minimal repair: restore fstar to the true Kelly root; _foc clears to 0.
    return ConcaveStationaryMaxCertificate(wr=_WR, b=_B, fstar=_FSTAR_TRUE)


def _emit(cert: ConcaveStationaryMaxCertificate, name: str) -> str:
    # ConcaveStationaryMaxEmitter exposes only public emit_body(fam, profile),
    # reading the ConcaveStationaryMaxCertificate off inst.payload.  The theorem
    # statements carry their own f binder (`∀ f ∈ Set.Ioo ...`), so no family
    # symbols are needed.
    #
    # The emitter names its two theorems `{name}_foc` and `{name}_concave`; the
    # generic engine axiom-checks the decl named exactly `name`
    # (verify_lean(..., decls=[name])), so rename the load-bearing `_foc` theorem
    # (the one carrying the fstar-dependent identity) to bare `name`.  The
    # `_concave` theorem (reads only wr,b) is left as an extra compiling theorem;
    # both twins turn solely on the (corrupt vs true) fstar in `_foc`.
    body = emit_via_single_instance_family(
        ConcaveStationaryMaxEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )
    return body.replace(f"{name}_foc", name)


register(
    NegativeControlAdapter(
        emitter_name="ConcaveStationaryMaxEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged Kelly cert with a NON-stationary fstar=1/2 (true root 325/1000, "
            "wr=55/100, b=2): the emitted `_foc` theorem g'(f*)=0 becomes "
            "11/20 - 9/10 = -7/20 != 0, which `norm_num` rejects.  True twin "
            "restores fstar=325/1000 and both theorems compile."
        ),
        imports_line="import Mathlib",
    )
)
