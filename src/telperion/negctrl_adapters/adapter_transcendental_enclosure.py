"""Negative-control adapter for TranscendentalEnclosureEmitter
(emit_transcendental_enclosure.py).

CERTIFICATE_SENSITIVE: the log-face `_lower_box` theorem asserts the rational
LOWER bound `L ≤ Real.log (1 + x)` on the box [x0, x1].  Its proof reduces (via
Real.le_log_iff_exp_le) to the purely-rational Taylor fact

    hsum : (Σ_{m<3} L^m/m!) + L^3*(3+1)/(3!*3) ≤ 1 + x0   := by norm_num

which holds only when L is a genuine lower bound, i.e. exp(L) ≤ 1 + x0.  L is the
supplied corruptible witness.

FALSE forge: L = 1/4 on box [1/4, 1/2] (x0 = 1/4).  Then log(1+x0) = log(5/4)
≈ 0.223 < 1/4, so L is NOT a lower bound, and the emitted `hsum` must prove the
degree-3 Taylor upper bound of exp(1/4) ≈ 1.284 ≤ 1 + x0 = 5/4 = 1.25, which is
FALSE, so `norm_num`/`linarith` fails and the kernel rejects.
transcendental_enclosure_certificate REFUSES L=1/4 here (L above the transcendental
min), so the cert is hand-built to bypass Layer 1.

TRUE twin: the genuine cert L = 1/5 on [1/4, 1/2] (exp(1/5) ≈ 1.221 ≤ 5/4); the
Taylor bound holds and all three theorems compile clean.

The emitter names three theorems `{name}_upper`, `{name}_lower_box`,
`{name}_enclosure`; the load-bearing L-dependent one is `_lower_box`, renamed to
bare `name` for the engine's axiom-check (the `_enclosure` theorem's reference to
`{name}_lower_box` is renamed in lockstep, so the file stays consistent).
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_transcendental_enclosure import (
    TranscendentalEnclosureCertificate,
    TranscendentalEnclosureEmitter,
    transcendental_enclosure_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_true_cert() -> TranscendentalEnclosureCertificate:
    # Genuine log-face enclosure on [1/4, 1/2]: L=1/5, U=1/2 (defaults);
    # exp(1/5) ~ 1.221 <= 5/4, so the Taylor lower-bound route closes.
    return transcendental_enclosure_certificate(
        face="log", x0=sp.Rational(1, 4), x1=sp.Rational(1, 2),
        L=sp.Rational(1, 5), U=sp.Rational(1, 2),
    )


def make_false_cert() -> TranscendentalEnclosureCertificate:
    # Corrupt L to 1/4 on the SAME box [1/4, 1/2]: log(1+x0) = log(5/4) ~ 0.223
    # < 1/4, so L is NOT a lower bound.  The emitted Taylor `hsum` must prove
    # exp(1/4) ~ 1.284 <= 5/4 = 1.25, which is FALSE; norm_num rejects it.
    # expr_lo/expr_hi are not read by the emitter; set to the true log values.
    x0, x1 = sp.Rational(1, 4), sp.Rational(1, 2)
    return TranscendentalEnclosureCertificate(
        face="log", x0=x0, x1=x1, L=sp.Rational(1, 4), U=sp.Rational(1, 2),
        expr_lo=sp.log(1 + x0), expr_hi=sp.log(1 + x1),
    )


def _emit(cert: TranscendentalEnclosureCertificate, name: str) -> str:
    # TranscendentalEnclosureEmitter exposes only public emit_body(fam, profile),
    # reading the TranscendentalEnclosureCertificate off inst.payload.  It emits
    # `{name}_upper`, `{name}_lower_box`, `{name}_enclosure`; the L-dependent
    # load-bearing theorem is `_lower_box`, which we rename to bare `name` so the
    # generic engine axiom-checks it.  The `_enclosure` proof's `{name}_lower_box`
    # reference is renamed in lockstep by the same replace, keeping the file
    # consistent.  All bounds are rational literals, so no family symbols.
    body = emit_via_single_instance_family(
        TranscendentalEnclosureEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )
    return body.replace(f"{name}_lower_box", name)


register(
    NegativeControlAdapter(
        emitter_name="TranscendentalEnclosureEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged log-enclosure cert with L=1/4 on [1/4,1/2] (log(5/4)~0.223 < "
            "1/4): the `_lower_box` Taylor step must prove exp(1/4)~1.284 <= 5/4 = "
            "1.25, which is false, so `norm_num`/`linarith` fails.  True twin uses "
            "L=1/5 (exp(1/5)~1.221 <= 5/4) and compiles."
        ),
        imports_line="import Mathlib",
    )
)
