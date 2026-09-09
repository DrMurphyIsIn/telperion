"""Negative-control adapter for LiPositivityLadderEmitter (Li-criterion rungs).

The rung theorem's load-bearing certificate is the separately-supplied rational
lower bound ``lo``: the kernel decides ``0 ≤ lo`` by ``norm_num`` inside the
proof.  Corrupt the SIGN of ``lo`` and the emitted proof of the (still
true-shaped, hypothesis-conditioned) statement fails to compile — the honest
two-sided control.

FALSE forgery: the n = 0 rung with ``lo = −1/100``.  Layer 1
(``li_rung_certificate``) refuses ``lo ≤ 0``; the adapter mints the frozen
dataclass BY HAND, bypassing that guard, so the TRUSTED Lean kernel is the
arbiter: ``by norm_num : (0:ℝ) ≤ (-1/100)`` fails and the theorem is rejected.

TRUE twin: the n = 0 rung with ``lo = 1/100`` (one sign different) — a genuine
lower bound (λ₁ ≈ 0.0230957 > 1/100), compiles clean.

Both twins reference ``(taylorCoeff riemannXi 0).re``; the harness supplies a
local abbreviation so the control elaborates against plain Mathlib without the
upstream LiCriterion library (the control tests the EMITTER's certificate
arithmetic, not the upstream reduction — the real wiring is CI-compiled in the
li_positivity example itself).

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_li_positivity import LiPositivityLadderEmitter, LiRungCert
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Stand-ins so the twins elaborate against plain Mathlib: the control pins the
# certificate arithmetic (0 ≤ lo by norm_num + le_trans), not the upstream defs.
_PRELUDE = (
    "noncomputable def riemannXi (s : ℂ) : ℂ :=\n"
    "  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)\n"
    "noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=\n"
    "  (deriv^[n] (fun z => deriv (fun w => f (1 / (1 - w))) z\n"
    "      / (fun w => f (1 / (1 - w))) z)) 0 / n.factorial\n"
)


def make_false_cert():
    """Hand-forged FALSE cert: lo = -1/100 (li_rung_certificate would refuse)."""
    return LiRungCert(n=0, lo=sp.Rational(-1, 100))


def make_true_cert():
    """Paired TRUE twin: lo = 1/100 (a genuine bound; λ₁ ≈ 0.0230957)."""
    return LiRungCert(n=0, lo=sp.Rational(1, 100))


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        LiPositivityLadderEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="LiPositivityLadderEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=_PRELUDE,
        allow_axioms=(),
        label=(
            "forged Li rung with NEGATIVE lower bound lo = -1/100: the in-proof "
            "norm_num gate 0 <= lo fails, kernel rejects; true twin lo = +1/100 "
            "compiles (lambda_1 ~ 0.0230957)"
        ),
        imports_line="import Mathlib",
    )
)
