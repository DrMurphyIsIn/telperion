"""TwoPointMomentFeasibility emitter — explicit discrete-measure moment
witnesses, distilled from the OpenAI Navier--Stokes blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``NavierStokes/LoopMoments.lean``
``exists_projected_twoPoint``, Apache-2.0).

CONSTRUCTS (rather than bounds) a two-point probability measure with prescribed
mean ``m`` and centered variance ``V ≥ 0``, both support points strictly
respecting an affine constraint ``2 < p₁ + p₂·x``:

    symmetric witness (p₂ = 0):  equal masses at ``m ± √V``;
    one-sided witness (p₂ ≠ 0):  masses ``(Vp²/(d²+Vp²), d²/(d²+Vp²))`` at
        ``m − d/p``, ``m + Vp/d``  with the margin ``d = (p₁+p₂m−2)/2``.

This is a rank-2 pseudo-expectation feasibility witness — the DUAL of the
SOS/cone shapes (every other Telperion kind certifies an inequality; this one
certifies EXISTENCE by explicit rational data) — directly the object shape
needed on the SoS 3-XOR pseudo-expectation front.

Modes: ``calculus`` (the fixed TwoPoint chain + the existence capstone) and
``instance`` at concrete rationals ``(p₁, p₂, m, V)`` with ``2 < p₁+p₂·m`` and
``0 ≤ V`` certified EXACTLY (violated margin refused — the negative control).

HONESTY SEAM: this is a feasibility statement for the tilt moments, NOT the
full cone test (the source's own caveat).  ``conjecture1_proved = False``.
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

TWOPOINT_PRELUDE = r"""
-- Two-point moment-feasibility calculus, ported from OpenAI's Navier-Stokes
-- blowup formalization (github.com/openai/NavierStokesAndEuler,
-- NavierStokes/LoopMoments.lean; Apache-2.0).

structure TwoPoint where
  leftWeight : ℝ
  rightWeight : ℝ
  leftValue : ℝ
  rightValue : ℝ

def TwoPoint.mean (q : TwoPoint) : ℝ :=
  q.leftWeight * q.leftValue + q.rightWeight * q.rightValue

def TwoPoint.centeredSecond (q : TwoPoint) (m : ℝ) : ℝ :=
  q.leftWeight * (q.leftValue - m) ^ 2 + q.rightWeight * (q.rightValue - m) ^ 2

def TwoPoint.IsProbability (q : TwoPoint) : Prop :=
  0 ≤ q.leftWeight ∧ 0 ≤ q.rightWeight ∧ q.leftWeight + q.rightWeight = 1

/-- For any nonnegative variance, equal masses at `m ± √V` realize it. -/
noncomputable def symmetricPair (m V : ℝ) : TwoPoint :=
  ⟨1 / 2, 1 / 2, m - Real.sqrt V, m + Real.sqrt V⟩

theorem symmetricPair_probability (m V : ℝ) : (symmetricPair m V).IsProbability := by
  norm_num [TwoPoint.IsProbability, symmetricPair]

theorem symmetricPair_mean (m V : ℝ) : (symmetricPair m V).mean = m := by
  dsimp [TwoPoint.mean, symmetricPair]
  ring

theorem symmetricPair_variance (m V : ℝ) (hV : 0 ≤ V) :
    (symmetricPair m V).centeredSecond m = V := by
  dsimp [TwoPoint.centeredSecond, symmetricPair]
  have hsq := Real.sq_sqrt hV
  nlinarith

noncomputable def oneSidedPair (m p d V : ℝ) : TwoPoint :=
  ⟨V * p ^ 2 / (d ^ 2 + V * p ^ 2), d ^ 2 / (d ^ 2 + V * p ^ 2),
    m - d / p, m + V * p / d⟩

theorem oneSidedPair_denom_pos (p d V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    0 < d ^ 2 + V * p ^ 2 := by
  have hprod := mul_nonneg hV (sq_nonneg p)
  nlinarith

theorem oneSidedPair_probability (m p d V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).IsProbability := by
  have hden := oneSidedPair_denom_pos p d V hd hV
  dsimp [TwoPoint.IsProbability, oneSidedPair]
  refine ⟨div_nonneg (mul_nonneg hV (sq_nonneg p)) (le_of_lt hden),
    div_nonneg (sq_nonneg d) (le_of_lt hden), ?_⟩
  field_simp
  ring

theorem oneSidedPair_mean (m p d V : ℝ) (hp : p ≠ 0) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).mean = m := by
  have hden := ne_of_gt (oneSidedPair_denom_pos p d V hd hV)
  have hdne := ne_of_gt hd
  dsimp [TwoPoint.mean, oneSidedPair]
  field_simp
  ring

theorem oneSidedPair_variance (m p d V : ℝ)
    (hp : p ≠ 0) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).centeredSecond m = V := by
  have hden := ne_of_gt (oneSidedPair_denom_pos p d V hd hV)
  have hdne := ne_of_gt hd
  dsimp [TwoPoint.centeredSecond, oneSidedPair]
  field_simp
  ring

theorem oneSidedPair_lower_projection (m p d V : ℝ) (hp : p ≠ 0) :
    p * ((oneSidedPair m p d V).leftValue - m) = -d := by
  dsimp [oneSidedPair]
  field_simp
  ring

theorem oneSidedPair_upper_projection (m p d V : ℝ) :
    p * ((oneSidedPair m p d V).rightValue - m) = V * p ^ 2 / d := by
  dsimp [oneSidedPair]
  ring

/-- Every mean whose affine projection is strictly above `2` has a two-point
distribution with any prescribed nonnegative variance, both support points
still strictly above the threshold.  Feasibility only — not a cone test. -/
theorem exists_projected_twoPoint (p₁ p₂ m V : ℝ)
    (hP : 2 < p₁ + p₂ * m) (hV : 0 ≤ V) :
    ∃ q : TwoPoint, q.IsProbability ∧ q.mean = m ∧ q.centeredSecond m = V ∧
      2 < p₁ + p₂ * q.leftValue ∧ 2 < p₁ + p₂ * q.rightValue := by
  by_cases hp : p₂ = 0
  · refine ⟨symmetricPair m V, symmetricPair_probability m V,
      symmetricPair_mean m V, symmetricPair_variance m V hV, ?_, ?_⟩ <;>
      simpa only [hp, zero_mul, add_zero] using hP
  · let d := (p₁ + p₂ * m - 2) / 2
    have hd : 0 < d := by dsimp only [d]; linarith
    refine ⟨oneSidedPair m p₂ d V, oneSidedPair_probability m p₂ d V hd hV,
      oneSidedPair_mean m p₂ d V hp hd hV,
      oneSidedPair_variance m p₂ d V hp hd hV, ?_, ?_⟩
    · have hleft := oneSidedPair_lower_projection m p₂ d V hp
      dsimp only [d] at hleft
      linarith [hleft]
    · have hright := oneSidedPair_upper_projection m p₂ d V
      have hinc : 0 ≤ V * p₂ ^ 2 / d :=
        div_nonneg (mul_nonneg hV (sq_nonneg p₂)) (le_of_lt hd)
      linarith [hright, hinc]
""".strip("\n")


@dataclass(frozen=True)
class TwoPointMomentCert:
    """``calculus`` or a concrete rational instance ``(p₁, p₂, m, V)`` with the
    margin ``p₁ + p₂·m − 2 > 0`` re-verified exactly."""

    mode: str
    p1: sp.Rational | None = None
    p2: sp.Rational | None = None
    m: sp.Rational | None = None
    V: sp.Rational | None = None
    margin: sp.Rational | None = None


def twopoint_moment_certificate(mode, p1=None, p2=None, m=None, V=None
                                ) -> TwoPointMomentCert:
    """Build and EXACTLY re-check a two-point moment instance."""
    if mode == "calculus":
        return TwoPointMomentCert(mode="calculus")
    if mode != "instance":
        raise ValueError(f"twopoint_moment REFUSED: mode ∈ {{calculus, instance}}; got {mode}")
    p1, p2, m, V = (sp.Rational(sp.nsimplify(v)) for v in (p1, p2, m, V))
    if not V >= 0:
        raise ValueError(f"twopoint_moment REFUSED: need 0 ≤ V; got {V}")
    margin = p1 + p2 * m - 2
    if not margin > 0:
        raise ValueError(
            f"twopoint_moment REFUSED: affine margin 2 < p₁+p₂·m violated "
            f"({p1}+{p2}·{m} = {p1 + p2*m} ≤ 2)")
    return TwoPointMomentCert(mode="instance", p1=p1, p2=p2, m=m, V=V,
                              margin=sp.Rational(margin))


def certify_twopoint_moment_point(family, pt, name):
    """``spec(pt) -> ("calculus",) | ("instance", p₁, p₂, m, V)``."""
    spec = family.special[1](pt)
    mode, *args = spec
    if mode == "instance":
        cert = twopoint_moment_certificate("instance", *args)
        n_checks = 2
    else:
        cert = twopoint_moment_certificate("calculus")
        n_checks = 1
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


@dataclass
class TwoPointMomentEmitter(Emitter):
    """Emit the fixed TwoPoint feasibility calculus plus per-instance
    specializations of the existence capstone (side conditions by ``norm_num``)."""

    def __post_init__(self):
        self.kind = "twopoint_moment"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [TWOPOINT_PRELUDE, ""]
        n_thm = 10  # the calculus chain incl. capstone
        for inst in fam.instances:
            cert: TwoPointMomentCert = inst.payload  # type: ignore[assignment]
            if cert.mode == "calculus":
                continue
            nm = inst.lean_name
            p1, p2, m, v = (rat_lean(x) for x in (cert.p1, cert.p2, cert.m, cert.V))
            lines.append(
                f"-- {nm}: two-point moment witness at (p₁,p₂,m,V)=({cert.p1},{cert.p2},"
                f"{cert.m},{cert.V}); margin p₁+p₂·m−2 = {cert.margin} > 0 certified exactly.\n"
                f"-- Feasibility only — not a cone test (the source's own caveat).\n"
                f"theorem {nm} :\n"
                f"    ∃ q : TwoPoint, q.IsProbability ∧ q.mean = ({m}) ∧\n"
                f"      q.centeredSecond ({m}) = ({v}) ∧\n"
                f"      2 < ({p1}) + ({p2}) * q.leftValue ∧\n"
                f"      2 < ({p1}) + ({p2}) * q.rightValue :=\n"
                f"  exists_projected_twoPoint ({p1}) ({p2}) ({m}) ({v})\n"
                f"    (by norm_num) (by norm_num)\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def twopoint_moment_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``twopoint_moment``; ``spec: pt -> ("calculus",) | ("instance", p₁, p₂, m, V)``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("twopoint_moment", spec),
        constants=dict(constants or {}),
    )
