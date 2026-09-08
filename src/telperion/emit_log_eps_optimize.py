"""LogEpsilonWitnessOptimization emitter — the cutoff-parameter optimization
distilled from the OpenAI Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``,
``Euler/LogarithmicCutoffOptimization.lean`` ``optimize``, Apache-2.0).

The classical ending of an interpolation estimate: a bound holding for EVERY
cutoff ``ε ∈ (0,1)``,

    X ≤ c·(L + W·(−log ε) + ε^θ·H),

is instantiated at the exponential witness ``ε = exp(−m·log(e+H))`` (with
``m = 1/θ``) so that ``ε^θ = (e+H)⁻¹`` absorbs ``H`` and ``−log ε`` becomes a
fixed log — yielding the ε-free conclusion

    X ≤ m·c·(1 + L + W·log(e + H)).

The source proves the case ``θ = 1/4`` (m = 4); this emitter GENERALIZES to any
rational ``θ ∈ (0, 1]``, certifying ``m·θ = 1`` exactly in sympy (the constants
are the statement; ``ring``/``norm_num`` re-verify the coefficient arithmetic
in-kernel).  ``θ ∉ (0, 1]`` is REFUSED — the negative control.

HONESTY SEAM: the ∀-ε family bound is an analytic-side HYPOTHESIS; the kernel
certifies only the witness instantiation and constant bookkeeping.
``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class LogEpsOptimizeCert:
    """The rational cutoff exponent ``θ ∈ (0,1]`` and witness multiplier
    ``m = 1/θ``, with ``m·θ = 1`` re-verified exactly."""

    theta: sp.Rational
    m: sp.Rational


def log_eps_optimize_certificate(theta) -> LogEpsOptimizeCert:
    """Build and EXACTLY re-check a cutoff-optimization instance."""
    theta = sp.Rational(sp.nsimplify(theta))
    if not (0 < theta <= 1):
        raise ValueError(
            f"log_eps_optimize REFUSED: need cutoff exponent 0 < θ ≤ 1; got {theta}")
    m = sp.Rational(1) / theta
    assert m * theta == 1  # exact re-validation
    return LogEpsOptimizeCert(theta=theta, m=m)


def certify_log_eps_optimize_point(family, pt, name):
    """``spec(pt) -> θ`` (rational in (0,1]).  n_checks = 2 (range + m·θ = 1)."""
    theta = family.special[1](pt)
    cert = log_eps_optimize_certificate(theta)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


@dataclass
class LogEpsOptimizeEmitter(Emitter):
    """Emit the ε-witness optimization at exponent θ: instantiate the ∀-ε
    hypothesis at ``ε = exp(−m·log(e+H))`` and collapse to the ε-free bound.
    Self-contained over ℝ (``Real.log``/``Real.exp``/``Real.rpow``)."""

    def __post_init__(self):
        self.kind = "log_eps_optimize"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: LogEpsOptimizeCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            th = rat_lean(cert.theta)
            m = rat_lean(cert.m)
            lines.append(
                f"-- {nm}: log-ε witness optimization at θ={cert.theta} (m=1/θ={cert.m}).\n"
                f"-- Ported/generalized from NavierStokesAndEuler\n"
                f"-- Euler/LogarithmicCutoffOptimization.lean (θ=1/4 case; Apache-2.0).\n"
                f"-- Trust seam: the ∀-ε family bound hbound is an analytic-side HYPOTHESIS.\n"
                f"theorem {nm} (X c L W H : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (hH : 0 ≤ H)\n"
                f"    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →\n"
                f"      X ≤ c * (L + W * (-Real.log ε) + ε ^ ({th} : ℝ) * H)) :\n"
                f"    X ≤ ({m}) * c * (1 + L + W * Real.log (Real.exp 1 + H)) := by\n"
                f"  set A := Real.exp 1 + H with hAdef\n"
                f"  have hE : 1 < Real.exp (1 : ℝ) := by\n"
                f"    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0:ℝ) < 1)\n"
                f"  have hA1 : 1 < A := by rw [hAdef]; linarith\n"
                f"  have hA0 : 0 < A := zero_lt_one.trans hA1\n"
                f"  have hl : 0 < Real.log A := Real.log_pos hA1\n"
                f"  set ε := Real.exp (-({m}) * Real.log A) with hedef\n"
                f"  have he0 : 0 < ε := Real.exp_pos _\n"
                f"  have he1 : ε < 1 := by\n"
                f"    have hneg : -({m}) * Real.log A < 0 :=\n"
                f"      mul_neg_of_neg_of_pos (by norm_num) hl\n"
                f"    rw [hedef]\n"
                f"    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg\n"
                f"  have heLog : -Real.log ε = ({m}) * Real.log A := by\n"
                f"    rw [hedef, Real.log_exp]; ring\n"
                f"  have hePow : ε ^ ({th} : ℝ) = A⁻¹ := by\n"
                f"    rw [hedef, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,\n"
                f"      show (-({m}) * Real.log A) * ({th} : ℝ) = -Real.log A by ring,\n"
                f"      Real.exp_neg, Real.exp_log hA0]\n"
                f"  have hHA : H ≤ A := le_add_of_nonneg_left (Real.exp_pos 1).le\n"
                f"  have hsmall : A⁻¹ * H ≤ 1 := by\n"
                f"    rw [mul_comm, ← div_eq_mul_inv]\n"
                f"    exact (div_le_one hA0).mpr hHA\n"
                f"  have h := hbound ε he0 he1\n"
                f"  rw [heLog, hePow] at h\n"
                f"  have hmid : X ≤ c * (L + ({m}) * (W * Real.log A) + 1) := by\n"
                f"    apply h.trans\n"
                f"    apply mul_le_mul_of_nonneg_left _ hc\n"
                f"    nlinarith only [hsmall]\n"
                f"  have hdiff : 0 ≤ c * ((({m}) - 1) + (({m}) - 1) * L) :=\n"
                f"    mul_nonneg hc (by nlinarith only [hL])\n"
                f"  nlinarith only [hmid, hdiff]\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def log_eps_optimize_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``log_eps_optimize``; ``spec: pt -> θ`` (rational in (0,1])."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("log_eps_optimize", spec),
        constants=dict(constants or {}),
    )
