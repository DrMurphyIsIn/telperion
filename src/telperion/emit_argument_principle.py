"""Argument-principle emitter — the winding/residue bridge `∮ Σ m/(z−ρ) = 2πi · Σ m`.

The shared atom between the analytic (log-derivative) and topological (winding-number) views of zero
localization: on a circle `C(c, R)`, the contour integral of a Herglotz zero-sum equals `2πi` times
the total multiplicity of the zeros inside,

    ∮_{C(c,R)} Σ_ρ (m ρ)·(z − ρ)⁻¹ dz = 2πi · Σ_ρ (m ρ)   (all ρ in `ball c R`).

Each pole `ρ` inside the disk contributes a residue `2πi` (`circleIntegral.integral_sub_inv_of_mem_ball`);
linearity (`integral_fun_sum` + `integral_const_mul`) sums them.  This is the residue side of the
argument principle: with `ζ'/ζ = Σ_ρ (divisor ρ)/(z−ρ) + E` (`DlvpBlaschkeSplitExpand`) and the analytic
part `E` integrating to `0`, `(2πi)⁻¹ ∮ ζ'/ζ = Σ divisor = ` the winding number = the zero count.
Bridges the dVP explicit-formula work to an argument-principle / winding-number localization.

Certificate: `R > 0` (the contour radius).  NEGATIVE CONTROL: `R ≤ 0` is REFUSED at certification.
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
class ArgumentPrincipleCertificate:
    """A verified argument-principle certificate: contour radius `R > 0`.  The certified fact is
    `R > 0` (a genuine circle); the Lean is a concrete-`R` copy of the residue-sum identity."""

    R: sp.Rational


def argument_principle_certificate(R) -> ArgumentPrincipleCertificate:
    """Build and EXACTLY self-check an argument-principle certificate.  Refuses ``R ≤ 0`` (the
    negative control — no circle)."""
    Rq = sp.nsimplify(R)
    if not Rq.is_rational:
        raise ValueError(f"argument_principle radius R must be rational; got {R!r}")
    if Rq <= 0:
        raise ValueError(f"argument_principle needs a strictly positive contour radius R > 0; got R={Rq}")
    return ArgumentPrincipleCertificate(R=Rq)


def certify_argument_principle_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict ``{"R":…}`` or scalar ``R``)."""
    spec = family.special[1](pt)
    cert = argument_principle_certificate(spec["R"] if isinstance(spec, dict) else spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class ArgumentPrincipleEmitter(Emitter):
    """Emit the argument-principle residue-sum identity `∮_{C(c,R)} Σ_ρ (m ρ)(z−ρ)⁻¹ = 2πi·Σ_ρ (m ρ)`
    on a circle of concrete radius `R`.  One theorem per instance."""

    def __post_init__(self):
        self.kind = "argument_principle"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex Metric Real\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: ArgumentPrincipleCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr = rat_lean(cert.R)
            lines.append(
                f"/-- Argument principle (residue-sum) on the circle of radius `{Rr}` about `c`:\n"
                f"    `∮_(C(c,{Rr})) Σ_ρ (m ρ)(z-ρ)⁻¹ = 2πi · Σ_ρ (m ρ)` for zeros `ρ` inside the disk.\n"
                f"    The winding/residue bridge — `(2πi)⁻¹ ∮ ζ'/ζ = Σ divisor` = the zero count. -/\n"
                f"theorem {base} {{c : ℂ}} (m : ℂ → ℤ) (s : Finset ℂ)\n"
                f"    (hmem : ∀ ρ ∈ s, ρ ∈ ball c ({Rr} : ℝ)) :\n"
                f"    (∮ z in C(c, ({Rr} : ℝ)), ∑ ρ ∈ s, (m ρ : ℂ) * (z - ρ)⁻¹)\n"
                f"      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by\n"
                f"  have hR : (0 : ℝ) < {Rr} := by norm_num\n"
                f"  have hint : ∀ ρ ∈ s, CircleIntegrable (fun z => (m ρ : ℂ) * (z - ρ)⁻¹) c ({Rr} : ℝ) := by\n"
                f"    intro ρ hρ\n"
                f"    have hd : dist ρ c < ({Rr} : ℝ) := by rw [← mem_ball]; exact hmem ρ hρ\n"
                f"    have hbase : CircleIntegrable (fun z => (z - ρ)⁻¹) c ({Rr} : ℝ) := by\n"
                f"      rw [circleIntegrable_sub_inv_iff]\n"
                f"      refine Or.inr ?_\n"
                f"      rw [mem_sphere, abs_of_pos hR]\n"
                f"      exact fun h => absurd h (by linarith)\n"
                f"    exact hbase.const_mul _\n"
                f"  rw [circleIntegral.integral_fun_sum hint]\n"
                f"  have hcong : ∀ ρ ∈ s,\n"
                f"      (∮ z in C(c, ({Rr} : ℝ)), (m ρ : ℂ) * (z - ρ)⁻¹) = (m ρ : ℂ) * (2 * π * I) := by\n"
                f"    intro ρ hρ\n"
                f"    rw [circleIntegral.integral_const_mul,\n"
                f"      circleIntegral.integral_sub_inv_of_mem_ball (hmem ρ hρ)]\n"
                f"  rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, mul_comm]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def argument_principle_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build an argument-principle family (kind='argument_principle').  ``spec``: ``pt -> {"R":…}`` or
    ``pt -> R``.  Refuses ``R ≤ 0`` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("argument_principle", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert R=3/2 ===")
    c = argument_principle_certificate(sp.Rational(3, 2))
    print(f"cert OK: R={c.R}")
    print("\n=== NEGATIVE CONTROL: R=0 must raise ===")
    try:
        argument_principle_certificate(0)
        raise SystemExit("FAIL: R=0 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean (R=3/2) [head] ===")
    fam = argument_principle_family(
        "T", GridSpec([("case", [0])]), lambda pt: "arg_principle_a", spec=lambda pt: {"R": "3/2"}
    )
    inst, _ = certify_argument_principle_point(fam, {"case": 0}, "arg_principle_a")

    class _V:
        instances = [inst]

    body, nthm = ArgumentPrincipleEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:800]}\n...[truncated]")
