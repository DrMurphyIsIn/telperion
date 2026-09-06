"""Box residue-sum emitter — the box analogue of full_argument_principle (conditional on winding).

The rectangle counterpart of `annulus_count` / `full_argument_principle`: the four-segment boundary
integral of a Herglotz sum over a box `[x0,x1] × [y0,y1]` equals `2πi` times the total multiplicity,

    Bd(Σ_ρ (m ρ)(z−ρ)⁻¹) = 2πi · Σ_ρ (m ρ),   where
    Bd(g) = (∫_{x0}^{x1} g(x+y0 i)) − (∫_{x0}^{x1} g(x+y1 i))
              + i(∫_{y0}^{y1} g(x1+y i)) − i(∫_{y0}^{y1} g(x0+y i)).

This atom discharges the tedious part — Finset linearity of the four segment integrals plus the constant
pull-out (`intervalIntegral.integral_finsetSum` + `integral_const_mul`) — leaving as the single explicit
hypothesis the per-pole winding primitive `Bd((z−ρ)⁻¹) = 2πi`.  That primitive is a GENUINE Mathlib gap:
Mathlib's residue lemmas are circle-based (`circleIntegral.integral_sub_inv_of_mem_ball`), and the
winding number of a non-circular contour about an interior point is not formalized.  So — exactly like
`full_argument_principle` takes the log-derivative decomposition as a hypothesis — this takes the box
winding as a hypothesis and delivers the full box argument principle by structural linearity.

Certificate: a proper box `x0 < x1`, `y0 < y1`.  NEGATIVE CONTROL: a degenerate/inverted box
(`x1 ≤ x0` or `y1 ≤ y0`) is REFUSED.  conjecture1_proved = False (NOT a proof of RH).
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
class BoxResidueSumCertificate:
    """A verified box certificate: a proper box `x0 < x1`, `y0 < y1`."""

    x0: sp.Rational
    x1: sp.Rational
    y0: sp.Rational
    y1: sp.Rational


def box_residue_sum_certificate(x0, x1, y0, y1) -> BoxResidueSumCertificate:
    """Build and EXACTLY self-check a box certificate.  Refuses a degenerate/inverted box
    (`x1 ≤ x0` or `y1 ≤ y0`) — the negative control."""
    xs = [sp.nsimplify(v) for v in (x0, x1, y0, y1)]
    for v, nm in zip(xs, ("x0", "x1", "y0", "y1")):
        if not v.is_rational:
            raise ValueError(f"box_residue_sum corner {nm} must be rational; got {v!r}")
    X0, X1, Y0, Y1 = xs
    if not (X0 < X1):
        raise ValueError(f"box_residue_sum needs x0 < x1 (proper box); got x0={X0}, x1={X1}")
    if not (Y0 < Y1):
        raise ValueError(f"box_residue_sum needs y0 < y1 (proper box); got y0={Y0}, y1={Y1}")
    return BoxResidueSumCertificate(x0=X0, x1=X1, y0=Y0, y1=Y1)


def certify_box_residue_sum_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict with keys x0,x1,y0,y1)."""
    spec = family.special[1](pt)
    cert = box_residue_sum_certificate(spec["x0"], spec["x1"], spec["y0"], spec["y1"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BoxResidueSumEmitter(Emitter):
    """Emit the box residue-sum `Bd(Σ_ρ (m ρ)(z−ρ)⁻¹) = 2πi·Σ m`, conditional on the per-pole winding."""

    def __post_init__(self):
        self.kind = "box_residue_sum"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex intervalIntegral MeasureTheory\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: BoxResidueSumCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            x0, x1 = rat_lean(cert.x0), rat_lean(cert.x1)
            y0, y1 = rat_lean(cert.y0), rat_lean(cert.y1)
            lines.append(
                f"/-- Box residue-sum on `[{x0}, {x1}] × [{y0}, {y1}]`: the four-segment boundary\n"
                f"    integral of a Herglotz sum equals `2πi·Σ m`, GIVEN the per-pole winding\n"
                f"    primitive `Bd((z-ρ)⁻¹) = 2πi` (a Mathlib gap — non-circular winding).\n"
                f"    This atom discharges the Finset-linearity plumbing over the four sides. -/\n"
                f"theorem {base} {{s : Finset ℂ}} (m : ℂ → ℤ)\n"
                f"    (hb : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + ({y0} : ℝ) * I) - ρ)⁻¹) volume ({x0}) ({x1}))\n"
                f"    (ht : ∀ ρ ∈ s, IntervalIntegrable (fun x : ℝ => ((↑x + ({y1} : ℝ) * I) - ρ)⁻¹) volume ({x0}) ({x1}))\n"
                f"    (hr : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => ((({x1} : ℝ) + ↑y * I) - ρ)⁻¹) volume ({y0}) ({y1}))\n"
                f"    (hl : ∀ ρ ∈ s, IntervalIntegrable (fun y : ℝ => ((({x0} : ℝ) + ↑y * I) - ρ)⁻¹) volume ({y0}) ({y1}))\n"
                f"    (hwind : ∀ ρ ∈ s,\n"
                f"      (∫ x in ({x0}: ℝ)..({x1}), ((↑x + ({y0} : ℝ) * I) - ρ)⁻¹)\n"
                f"        - (∫ x in ({x0}: ℝ)..({x1}), ((↑x + ({y1} : ℝ) * I) - ρ)⁻¹)\n"
                f"        + I • (∫ y in ({y0}: ℝ)..({y1}), ((({x1} : ℝ) + ↑y * I) - ρ)⁻¹)\n"
                f"        - I • (∫ y in ({y0}: ℝ)..({y1}), ((({x0} : ℝ) + ↑y * I) - ρ)⁻¹) = 2 * π * I) :\n"
                f"    (∫ x in ({x0}: ℝ)..({x1}), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ({y0} : ℝ) * I) - ρ)⁻¹)\n"
                f"        - (∫ x in ({x0}: ℝ)..({x1}), ∑ ρ ∈ s, (m ρ : ℂ) * ((↑x + ({y1} : ℝ) * I) - ρ)⁻¹)\n"
                f"        + I • (∫ y in ({y0}: ℝ)..({y1}), ∑ ρ ∈ s, (m ρ : ℂ) * ((({x1} : ℝ) + ↑y * I) - ρ)⁻¹)\n"
                f"        - I • (∫ y in ({y0}: ℝ)..({y1}), ∑ ρ ∈ s, (m ρ : ℂ) * ((({x0} : ℝ) + ↑y * I) - ρ)⁻¹)\n"
                f"      = 2 * π * I * ∑ ρ ∈ s, (m ρ : ℂ) := by\n"
                f"  rw [intervalIntegral.integral_finsetSum (fun ρ hρ => (hb ρ hρ).const_mul (m ρ : ℂ)),\n"
                f"      intervalIntegral.integral_finsetSum (fun ρ hρ => (ht ρ hρ).const_mul (m ρ : ℂ)),\n"
                f"      intervalIntegral.integral_finsetSum (fun ρ hρ => (hr ρ hρ).const_mul (m ρ : ℂ)),\n"
                f"      intervalIntegral.integral_finsetSum (fun ρ hρ => (hl ρ hρ).const_mul (m ρ : ℂ))]\n"
                f"  simp only [intervalIntegral.integral_const_mul, smul_eq_mul, Finset.mul_sum]\n"
                f"  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]\n"
                f"  apply Finset.sum_congr rfl\n"
                f"  intro ρ hρ\n"
                f"  have hw := hwind ρ hρ; simp only [smul_eq_mul] at hw\n"
                f"  linear_combination (m ρ : ℂ) * hw\n"
            )
            nthm += 1
        return "".join(lines), nthm


def box_residue_sum_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a box-residue-sum family (kind='box_residue_sum').  ``spec``: ``pt ->
    {"x0","x1","y0","y1"}``.  Refuses a degenerate/inverted box at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("box_residue_sum", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert box [0,2]x[0,1] ===")
    c = box_residue_sum_certificate(0, 2, 0, 1)
    print(f"cert OK: x0={c.x0} x1={c.x1} y0={c.y0} y1={c.y1}")
    print("\n=== NEGATIVE CONTROL: inverted box y1<=y0 must raise ===")
    try:
        box_residue_sum_certificate(0, 2, 1, 0)
        raise SystemExit("FAIL: inverted box not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = box_residue_sum_family(
        "T", GridSpec([("case", [0])]), lambda pt: "box_res_a",
        spec=lambda pt: {"x0": "0", "x1": "2", "y0": "0", "y1": "1"},
    )
    inst, _ = certify_box_residue_sum_point(fam, {"case": 0}, "box_res_a")

    class _V:
        instances = [inst]

    body, nthm = BoxResidueSumEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:500]}\n...[truncated]")
