"""Annulus-count emitter — zeros in a shell via `∮_{C(c,R)} − ∮_{C(c,r)} = 2πi · Σ_shell m`.

The natural primitive for zero-DENSITY arguments: counting zeros in an annulus `r < |z−c| < R` by
subtracting two circle integrals.  For a Herglotz sum whose poles all lie in the shell (inside the
outer radius `R`, outside the inner radius `r`),

    ∮_{C(c,R)} Σ_ρ (m ρ)(z−ρ)⁻¹  −  ∮_{C(c,r)} Σ_ρ (m ρ)(z−ρ)⁻¹  =  2πi · Σ_ρ (m ρ).

The outer integral counts everything inside `R` (residue side, `integral_sub_inv_of_mem_ball`); the
inner integral is `0` because every pole is OUTSIDE the closed inner disk, making each `(z−ρ)⁻¹`
holomorphic on `ball c r` (Cauchy, `DiffContOnCl.circleIntegral_eq_zero`).  The difference isolates the
shell — the winding number counted over an annular region.

Certificate: `0 < r < R` (a genuine annulus).  NEGATIVE CONTROL: `r ≤ 0` or `R ≤ r` (empty/degenerate
annulus) is REFUSED.  conjecture1_proved = False (NOT a proof of RH).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .expr import rat_lean
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.expr import rat_lean
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


@dataclass(frozen=True)
class AnnulusCountCertificate:
    """A verified annulus certificate: inner radius `r` and outer radius `R` with `0 < r < R`."""

    r: sp.Rational
    R: sp.Rational


def annulus_count_certificate(r, R) -> AnnulusCountCertificate:
    """Build and EXACTLY self-check an annulus certificate.  Refuses `r ≤ 0` or `R ≤ r` (empty or
    degenerate annulus) — the negative control."""
    rq, Rq = sp.nsimplify(r), sp.nsimplify(R)
    if not (rq.is_rational and Rq.is_rational):
        raise ValueError(f"annulus_count radii must be rational; got r={r!r}, R={R!r}")
    if rq <= 0:
        raise ValueError(f"annulus_count needs inner radius r > 0; got r={rq}")
    if not (Rq > rq):
        raise ValueError(f"annulus_count needs outer radius R > r (genuine annulus); got r={rq}, R={Rq}")
    return AnnulusCountCertificate(r=rq, R=Rq)


def certify_annulus_count_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict with keys r, R)."""
    spec = family.special[1](pt)
    cert = annulus_count_certificate(spec["r"], spec["R"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class AnnulusCountEmitter(Emitter):
    """Emit the annulus/shell count `∮_R − ∮_r = 2πi·Σ_shell m` for a Herglotz sum in the shell."""

    def __post_init__(self):
        self.kind = "annulus_count"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex Metric Real\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: AnnulusCountCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            rr, Rr = rat_lean(cert.r), rat_lean(cert.R)
            lines.append(
                f"/-- Annulus count on the shell `{rr} < |z-c| < {Rr}`: outer circle integral minus\n"
                f"    inner circle integral isolates the poles in the shell,\n"
                f"    `∮_(C(c,{Rr})) Σ_ρ (m ρ)(z-ρ)⁻¹ - ∮_(C(c,{rr})) Σ_ρ (m ρ)(z-ρ)⁻¹ = 2πi · Σ_ρ (m ρ)`.\n"
                f"    Outer counts all inside; inner = 0 (poles outside ⟹ analytic ⟹ Cauchy). -/\n"
                f"theorem {base} {{c : ℂ}} (m : ℂ → ℤ) (s : Finset ℂ)\n"
                f"    (hin : ∀ ρ ∈ s, ρ ∈ ball c (({Rr}) : ℝ))\n"
                f"    (hout : ∀ ρ ∈ s, (({rr}) : ℝ) < dist ρ c) :\n"
                f"    (∮ z in C(c, ({Rr} : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)\n"
                f"        - (∮ z in C(c, ({rr} : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)\n"
                f"      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by\n"
                f"  have hRout : (0 : ℝ) < {Rr} := by norm_num\n"
                f"  have houter_int : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ({Rr} : ℝ) := by\n"
                f"    intro ρ hρ\n"
                f"    have hd : dist ρ c < ({Rr} : ℝ) := by rw [← mem_ball]; exact hin ρ hρ\n"
                f"    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ({Rr} : ℝ) := by\n"
                f"      rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_\n"
                f"      rw [mem_sphere, abs_of_pos hRout]; exact fun h => absurd h (by linarith)\n"
                f"    exact hbase.const_mul _\n"
                f"  have houter : (∮ z in C(c, ({Rr} : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)\n"
                f"      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by\n"
                f"    rw [circleIntegral.integral_fun_sum houter_int]\n"
                f"    have hcong : ∀ ρ ∈ s,\n"
                f"        (∮ z in C(c, ({Rr} : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by\n"
                f"      intro ρ hρ\n"
                f"      rw [circleIntegral.integral_const_mul,\n"
                f"        circleIntegral.integral_sub_inv_of_mem_ball (hin ρ hρ)]\n"
                f"    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]\n"
                f"  have hinner : (∮ z in C(c, ({rr} : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) = 0 := by\n"
                f"    have hzero : ∀ ρ ∈ s, (∮ z in C(c, ({rr} : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = 0 := by\n"
                f"      intro ρ hρ\n"
                f"      rw [circleIntegral.integral_const_mul]\n"
                f"      have hbody : (∮ z in C(c, ({rr} : ℝ)), (z - ρ)⁻¹) = 0 := by\n"
                f"        apply DiffContOnCl.circleIntegral_eq_zero (by norm_num : (0 : ℝ) ≤ {rr})\n"
                f"        apply DifferentiableOn.diffContOnCl\n"
                f"        rw [closure_ball c (by norm_num : ({rr} : ℝ) ≠ 0)]\n"
                f"        intro z hz\n"
                f"        have hzr : dist z c ≤ {rr} := by rwa [mem_closedBall] at hz\n"
                f"        have hne : z - ρ ≠ 0 := by\n"
                f"          intro h; rw [sub_eq_zero] at h\n"
                f"          have hd2 := hout ρ hρ; rw [← h] at hd2; linarith\n"
                f"        exact ((differentiableAt_id.sub_const ρ).inv hne).differentiableWithinAt\n"
                f"      rw [hbody, mul_zero]\n"
                f"    have hinner_int : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ({rr} : ℝ) := by\n"
                f"      intro ρ hρ\n"
                f"      have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ({rr} : ℝ) := by\n"
                f"        rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_\n"
                f"        rw [mem_sphere]; intro h\n"
                f"        have hd2 := hout ρ hρ; rw [h] at hd2; norm_num at hd2\n"
                f"      exact hbase.const_mul _\n"
                f"    rw [circleIntegral.integral_fun_sum hinner_int, Finset.sum_congr rfl hzero,\n"
                f"      Finset.sum_const_zero]\n"
                f"  rw [houter, hinner, sub_zero]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def annulus_count_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build an annulus-count family (kind='annulus_count').  ``spec``: ``pt -> {"r","R"}``.  Refuses
    `r ≤ 0` or `R ≤ r` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("annulus_count", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert annulus 1 < |z-c| < 2 ===")
    c = annulus_count_certificate(1, 2)
    print(f"cert OK: r={c.r} R={c.R}")
    print("\n=== NEGATIVE CONTROL: R <= r must raise ===")
    try:
        annulus_count_certificate(2, 1)
        raise SystemExit("FAIL: R<=r not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = annulus_count_family(
        "T", GridSpec([("case", [0])]), lambda pt: "annulus_a", spec=lambda pt: {"r": "1", "R": "2"}
    )
    inst, _ = certify_annulus_count_point(fam, {"case": 0}, "annulus_a")

    class _V:
        instances = [inst]

    body, nthm = AnnulusCountEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:400]}\n...[truncated]")
