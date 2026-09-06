"""Full argument-principle emitter — residue-sum PLUS analytic-vanishing in one theorem.

The completing half of the argument principle.  The `argument_principle` atom handles the residue
sum `∮ Σ m/(z−ρ) = 2πi Σ m`; this atom folds in the analytic remainder via Cauchy's theorem so the
FULL log-derivative integral collapses to the zero count in a single step:

    f = (Σ_ρ (m ρ)/(z−ρ)) + E,   E holomorphic on the closed disk   ⟹
        ∮_{C(c,R)} f = 2πi · Σ_ρ (m ρ).

The `E` term vanishes by `DiffContOnCl.circleIntegral_eq_zero` (Cauchy–Goursat); the pole terms give
`2πi` each by `circleIntegral.integral_sub_inv_of_mem_ball`.  With `f = ζ'/ζ` and `E` its entire part,
this is exactly `(2πi)⁻¹ ∮ ζ'/ζ = Σ divisor =` the winding number = the zero count — the dangling `∮ E`
term of the winding-number derivation is removed.

Certificate: `R > 0` (contour radius).  NEGATIVE CONTROL: `R ≤ 0` is REFUSED at certification.
conjecture1_proved = False (NOT a proof of RH).
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
class FullArgumentPrincipleCertificate:
    """A verified full-argument-principle certificate: contour radius `R > 0`."""

    R: sp.Rational


def full_argument_principle_certificate(R) -> FullArgumentPrincipleCertificate:
    """Build and EXACTLY self-check a certificate.  Refuses ``R ≤ 0`` (no circle)."""
    Rq = sp.nsimplify(R)
    if not Rq.is_rational:
        raise ValueError(f"full_argument_principle radius R must be rational; got {R!r}")
    if Rq <= 0:
        raise ValueError(
            f"full_argument_principle needs a strictly positive contour radius R > 0; got R={Rq}"
        )
    return FullArgumentPrincipleCertificate(R=Rq)


def certify_full_argument_principle_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict ``{"R":…}`` or scalar ``R``)."""
    spec = family.special[1](pt)
    cert = full_argument_principle_certificate(spec["R"] if isinstance(spec, dict) else spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class FullArgumentPrincipleEmitter(Emitter):
    """Emit `∮_{C(c,R)} f = 2πi·Σ m` for `f = Σ_ρ (m ρ)(z−ρ)⁻¹ + E` with `E` holomorphic on the disk."""

    def __post_init__(self):
        self.kind = "full_argument_principle"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex Metric Real\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: FullArgumentPrincipleCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr = rat_lean(cert.R)
            lines.append(
                f"/-- FULL argument principle on the circle of radius `{Rr}` about `c`.\n"
                f"    For `f = Σ_ρ (m ρ)(z-ρ)⁻¹ + E` with `E` holomorphic on the closed disk,\n"
                f"    `∮_(C(c,{Rr})) f = 2πi · Σ_ρ (m ρ)`.  The analytic part `E` vanishes (Cauchy);\n"
                f"    the pole terms give `2πi` each — the winding number = the zero count. -/\n"
                f"theorem {base} {{c : ℂ}} (m : ℂ → ℤ) (s : Finset ℂ) (E : ℂ → ℂ) (f : ℂ → ℂ)\n"
                f"    (hmem : ∀ ρ ∈ s, ρ ∈ ball c ({Rr} : ℝ))\n"
                f"    (hE : DiffContOnCl ℂ E (ball c ({Rr} : ℝ)))\n"
                f"    (hf : ∀ z, f z = (∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) + E z) :\n"
                f"    (∮ z in C(c, ({Rr} : ℝ)), f z) = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by\n"
                f"  have hR : (0 : ℝ) < {Rr} := by norm_num\n"
                f"  have hint : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ({Rr} : ℝ) := by\n"
                f"    intro ρ hρ\n"
                f"    have hd : dist ρ c < ({Rr} : ℝ) := by rw [← mem_ball]; exact hmem ρ hρ\n"
                f"    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ({Rr} : ℝ) := by\n"
                f"      rw [circleIntegrable_sub_inv_iff]; refine Or.inr ?_\n"
                f"      rw [mem_sphere, abs_of_pos hR]; exact fun h => absurd h (by linarith)\n"
                f"    exact hbase.const_mul _\n"
                f"  have hsum_int : CircleIntegrable (fun z => ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) c ({Rr} : ℝ) := by\n"
                f"    have h := CircleIntegrable.sum s hint\n"
                f"    have heq : (∑ ρ ∈ s, fun z => (m ρ : ℂ) * (z - ρ)⁻¹)\n"
                f"        = (fun z => ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹) := by\n"
                f"      funext z; exact Finset.sum_apply z s _\n"
                f"    rwa [heq] at h\n"
                f"  have hsub : sphere c ({Rr} : ℝ) ⊆ closure (ball c ({Rr} : ℝ)) := by\n"
                f"    rw [closure_ball c (by norm_num : ({Rr} : ℝ) ≠ 0)]; exact sphere_subset_closedBall\n"
                f"  have hEint : CircleIntegrable E c ({Rr} : ℝ) :=\n"
                f"    (hE.continuousOn.mono hsub).circleIntegrable hR.le\n"
                f"  simp only [hf]\n"
                f"  rw [circleIntegral.integral_add hsum_int hEint, hE.circleIntegral_eq_zero hR.le,\n"
                f"    add_zero, circleIntegral.integral_fun_sum hint]\n"
                f"  have hcong : ∀ ρ ∈ s,\n"
                f"      (∮ z in C(c, ({Rr} : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by\n"
                f"    intro ρ hρ\n"
                f"    rw [circleIntegral.integral_const_mul,\n"
                f"      circleIntegral.integral_sub_inv_of_mem_ball (hmem ρ hρ)]\n"
                f"  rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def full_argument_principle_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a full-argument-principle family (kind='full_argument_principle').  ``spec``: ``pt ->
    {"R":…}`` or ``pt -> R``.  Refuses ``R ≤ 0`` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("full_argument_principle", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert R=3/2 ===")
    c = full_argument_principle_certificate(sp.Rational(3, 2))
    print(f"cert OK: R={c.R}")
    print("\n=== NEGATIVE CONTROL: R=0 must raise ===")
    try:
        full_argument_principle_certificate(0)
        raise SystemExit("FAIL: R=0 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = full_argument_principle_family(
        "T", GridSpec([("case", [0])]), lambda pt: "full_ap_a", spec=lambda pt: {"R": "3/2"}
    )
    inst, _ = certify_full_argument_principle_point(fam, {"case": 0}, "full_ap_a")

    class _V:
        instances = [inst]

    body, nthm = FullArgumentPrincipleEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:400]}\n...[truncated]")
