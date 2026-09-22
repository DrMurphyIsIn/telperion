"""Negative-control adapter for ExpThresholdEmitter (threshold-to-exponential domination).

The emitted linear-mode theorem is

    theorem nm (lam : R) (h : Q / (s * a) <= lam) : Q <= Real.exp (s * lam * a)

proved by `div_le_iff0` (which needs `0 < s * a`, discharged by `positivity`) +
`Real.add_one_le_exp` + `linarith`.  For a RATIONAL instance the load-bearing numeric content
is the sign of `a` (and of `K`, `s`): the exponent `s * lam * a` grows with `lam` only when
`a > 0`, and the kernel re-decides that sign at the `positivity` step.

FALSE forgery: `Q = 3`, `a = -1`, `s = 2`, no `K`.  The statement
`3 / (2 * (-1)) <= lam -> 3 <= exp (2 * lam * (-1))` is FALSE, not merely unproved: at
`lam = 0` the hypothesis reads `-3/2 <= 0` (true) and the conclusion `3 <= exp 0 = 1` (false).
Layer 1 (`exp_threshold_certificate`) refuses `a <= 0` outright (the audit's headline phantom);
the adapter mints the frozen dataclasses BY HAND, bypassing that guard exactly as
`adapter_exp_enclosure` does, so the kernel is the arbiter: `positivity` cannot prove
`(0 : R) < 2 * (-1)` and the proof does not elaborate.

TRUE twin: the same instance with `a = 1` -- `3 / (2 * 1) <= lam -> 3 <= exp (2 * lam * 1)`,
which the linear route proves (`3 <= 2 lam <= 2 lam + 1 <= exp (2 lam)`); compiles clean and
axiom-clean over Mathlib alone (imports_line `import Mathlib`, empty prelude).

Both twins share every tactic line; only the literal `((-1) : R)` / `(1 : R)` moves.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_exp_threshold import (
    ExpThresholdCert,
    ExpThresholdEmitter,
    ExpThresholdStep,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

_Q = sp.Integer(3)
_S = sp.Integer(2)


def _cert(a) -> ExpThresholdCert:
    a = sp.Rational(a)
    step = ExpThresholdStep(
        mode="linear", Q=_Q, a=a, K=None, scale=_S, strict=False,
        threshold=_Q / (_S * a),
    )
    return ExpThresholdCert(mode="linear", steps=(step,), guard=False, lam="lam")


def make_false_cert() -> ExpThresholdCert:
    """Hand-forged FALSE cert: a = -1, so the exponent shrinks with lam and the implication
    fails at lam = 0 (hypothesis -3/2 <= 0 holds, conclusion 3 <= exp 0 = 1 fails)."""
    return _cert(-1)


def make_true_cert() -> ExpThresholdCert:
    """Paired TRUE twin: a = 1 (the honest instance at the same Q and scale)."""
    return _cert(1)


def _emit(cert: ExpThresholdCert, name: str) -> str:
    return emit_via_single_instance_family(
        ExpThresholdEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="ExpThresholdEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged linear exp-threshold instance Q = 3, a = -1, s = 2: the statement "
            "3 / (2 * (-1)) <= lam -> 3 <= exp (2 * lam * (-1)) is FALSE at lam = 0 and the "
            "emitted positivity step cannot prove 0 < 2 * (-1), so the kernel rejects it; the "
            "true twin a = 1 compiles"
        ),
        imports_line="import Mathlib",
    )
)
