"""ContinuousBarrierBootstrap emitter — the open-closed continuity bootstrap
distilled from the OpenAI Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``Euler/GevreyFlowBootstrap.lean``
``continuous_barrier``, Apache-2.0; reused in ``LocalFlowTrap.lean``).

The classical closer of a-priori PDE estimates: a continuous path that starts
at 0 and satisfies a CONDITIONAL step bound ("as long as it has stayed ≤ a so
far, it is ≤ B·t") in fact satisfies the bound UNCONDITIONALLY on [0, T],
provided the budget ``B·T < a`` keeps the barrier strictly out of reach:

    f continuous on [0,T],  f 0 = 0,  B·T < a,
    (∀ t, (∀ s ≤ t, f s ≤ a) → f t ≤ B·t)
    ─────────────────────────────────────────
    ∀ t ∈ [0,T],  f t ≤ B·t

The proof is the compact-least-hit + intermediate-value argument: the first
time f reaches a is an exact hit, but the conditional bound caps it at
``B·T < a`` — contradiction.  This is Telperion's first TOPOLOGICAL certificate
shape (all prior kinds are discrete-index or algebraic); the topology is fixed
library material (``IsCompact.exists_isLeast`` + ``intermediate_value_Icc``),
the per-instance certificate is the rational budget.

Modes: ``generic`` (the fixed atom) and ``budget`` (concrete rationals
``(T, B, a)`` with ``0 ≤ T``, ``0 ≤ B``, ``0 < a``, ``B·T < a`` certified
EXACTLY; violated budget refused — the negative control).

HONESTY SEAM: continuity, the initial condition, and the conditional step bound
are analytic-side HYPOTHESES; the kernel certifies only the bootstrap logic.
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

BARRIER_PRELUDE = r"""
-- Open-closed continuity bootstrap, ported from OpenAI's Euler blowup
-- formalization (github.com/openai/NavierStokesAndEuler,
-- Euler/GevreyFlowBootstrap.lean continuous_barrier; Apache-2.0).
open Set

/-- A continuous path cannot first hit a barrier if its bound up to that
first hit lies strictly below the barrier. -/
theorem continuous_barrier (f : ℝ → ℝ) (T B a : ℝ)
    (_hT : 0 ≤ T) (hB : 0 ≤ B) (ha : 0 < a) (hBa : B * T < a)
    (hf : ContinuousOn f (Icc 0 T)) (hf0 : f 0 = 0)
    (hstep : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, f s ≤ a) → f t ≤ B * t) :
    ∀ t ∈ Icc 0 T, f t ≤ B * t := by
  have hstrict : ∀ t ∈ Icc 0 T, f t < a := by
    intro t ht
    by_contra hfail
    let S := Icc (0 : ℝ) T ∩ f ⁻¹' Ici a
    have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
    have hSn : S.Nonempty := ⟨t, ht, le_of_not_gt hfail⟩
    obtain ⟨m, hm⟩ := hSc.exists_isLeast hSn
    have hmI : m ∈ Icc (0 : ℝ) T := hm.1.1
    have hmhigh : a ≤ f m := hm.1.2
    have hfm : f m = a := by
      have hc : ContinuousOn f (Icc 0 m) := hf.mono (Icc_subset_Icc_right hmI.2)
      obtain ⟨r, hr, her⟩ := intermediate_value_Icc hmI.1 hc
        (show a ∈ Icc (f 0) (f m) from ⟨by rw [hf0]; exact ha.le, hmhigh⟩)
      have hmr : m ≤ r := hm.2 ⟨⟨hr.1, hr.2.trans hmI.2⟩, her.ge⟩
      have hrm : r = m := le_antisymm hr.2 hmr
      simpa only [hrm] using her
    have hbefore : ∀ s ∈ Icc 0 m, f s ≤ a := by
      intro s hs
      by_cases hsm : s = m
      · simp only [hsm, hfm, le_refl]
      · have hlt : s < m := lt_of_le_of_ne hs.2 hsm
        by_contra hhigh
        have hms : m ≤ s := hm.2 ⟨⟨hs.1, hs.2.trans hmI.2⟩, (lt_of_not_ge hhigh).le⟩
        exact (not_le_of_gt hlt) hms
    have hh := hstep m hmI hbefore
    have hmB : B * m ≤ B * T := mul_le_mul_of_nonneg_left hmI.2 hB
    rw [hfm] at hh
    linarith
  intro t ht
  exact hstep t ht (fun s hs => (hstrict s ⟨hs.1, hs.2.trans ht.2⟩).le)
""".strip("\n")


@dataclass(frozen=True)
class ContinuousBarrierCert:
    """``generic`` or a concrete rational budget ``(T, B, a)`` with
    ``B·T < a`` re-verified exactly."""

    mode: str
    T: sp.Rational | None = None
    B: sp.Rational | None = None
    a: sp.Rational | None = None


def continuous_barrier_certificate(mode, T=None, B=None, a=None) -> ContinuousBarrierCert:
    """Build and EXACTLY re-check a barrier-bootstrap instance."""
    if mode == "generic":
        return ContinuousBarrierCert(mode="generic")
    if mode != "budget":
        raise ValueError(f"continuous_barrier REFUSED: mode ∈ {{generic, budget}}; got {mode}")
    T = sp.Rational(sp.nsimplify(T))
    B = sp.Rational(sp.nsimplify(B))
    a = sp.Rational(sp.nsimplify(a))
    if not T >= 0:
        raise ValueError(f"continuous_barrier REFUSED: need 0 ≤ T; got {T}")
    if not B >= 0:
        raise ValueError(f"continuous_barrier REFUSED: need 0 ≤ B; got {B}")
    if not a > 0:
        raise ValueError(f"continuous_barrier REFUSED: need 0 < a; got {a}")
    if not B * T < a:
        raise ValueError(
            f"continuous_barrier REFUSED: barrier budget B·T < a violated "
            f"({B}·{T} = {B*T} ≥ {a})")
    return ContinuousBarrierCert(mode="budget", T=T, B=B, a=a)


def certify_continuous_barrier_point(family, pt, name):
    """``spec(pt) -> ("generic",) | ("budget", T, B, a)``."""
    spec = family.special[1](pt)
    mode, *args = spec
    if mode == "budget":
        cert = continuous_barrier_certificate("budget", *args)
        n_checks = 4
    else:
        cert = continuous_barrier_certificate("generic")
        n_checks = 1
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


@dataclass
class ContinuousBarrierEmitter(Emitter):
    """Emit the fixed open-closed bootstrap atom plus per-instance budget
    specializations (side conditions by ``norm_num``).  Continuity / initial
    condition / conditional step bound are hypotheses (the trust seam)."""

    def __post_init__(self):
        self.kind = "continuous_barrier"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [BARRIER_PRELUDE, ""]
        n_thm = 1
        for inst in fam.instances:
            cert: ContinuousBarrierCert = inst.payload  # type: ignore[assignment]
            if cert.mode == "generic":
                continue
            nm = inst.lean_name
            t, b, a = rat_lean(cert.T), rat_lean(cert.B), rat_lean(cert.a)
            lines.append(
                f"-- {nm}: barrier bootstrap at the concrete budget T={cert.T}, "
                f"B={cert.B}, a={cert.a} (B·T = {cert.B*cert.T} < {cert.a} certified exactly).\n"
                f"-- Trust seam: continuity, f 0 = 0, and the conditional step bound are\n"
                f"-- HYPOTHESES supplied by the analytic side.\n"
                f"theorem {nm} (f : ℝ → ℝ)\n"
                f"    (hf : ContinuousOn f (Set.Icc 0 ({t}))) (hf0 : f 0 = 0)\n"
                f"    (hstep : ∀ t ∈ Set.Icc (0:ℝ) ({t}),\n"
                f"      (∀ s ∈ Set.Icc (0:ℝ) t, f s ≤ ({a})) → f t ≤ ({b}) * t) :\n"
                f"    ∀ t ∈ Set.Icc (0:ℝ) ({t}), f t ≤ ({b}) * t :=\n"
                f"  continuous_barrier f ({t}) ({b}) ({a})\n"
                f"    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf hf0 hstep\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def continuous_barrier_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``continuous_barrier``; ``spec: pt -> ("generic",) | ("budget", T, B, a)``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("continuous_barrier", spec),
        constants=dict(constants or {}),
    )
