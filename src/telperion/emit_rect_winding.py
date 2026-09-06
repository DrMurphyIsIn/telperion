"""Rectangle winding-number emitter — the winding-NONZERO primitive, from scratch.

Closes the Mathlib gap flagged as blocking both the full box residue and Rouché: for `ρ` strictly
inside the rectangle `[x0,x1] × [y0,y1]`, the four-segment boundary integral of `(z−ρ)⁻¹` equals `2πi`
(winding number ONE about the interior point),

    (∫_{x0}^{x1}(x+y0 i −ρ)⁻¹) − (∫_{x0}^{x1}(x+y1 i −ρ)⁻¹)
        + i(∫_{y0}^{y1}(x1+y i −ρ)⁻¹) − i(∫_{y0}^{y1}(x0+y i −ρ)⁻¹)  =  2πi.

Mathlib has NO winding number / non-circular residue — only the circle Cauchy formula.  The proof is the
segment/`Complex.log` computation with an explicit branch-split at the single cut-crossing: the bottom
(`Im<0`), right (`Re>0`), and top (`Im>0`) segments each stay in the slit plane, so principal `log`
(antiderivative via `HasDerivAt.clog_real` + FTC-2) applies and they telescope to `log(D−ρ) − log(A−ρ)`;
the LEFT segment (`Re<0`) would cross the cut, so it uses the branch `log(ρ − (x0+yi))` whose argument
has `Re>0` throughout, giving `log(ρ−D) − log(ρ−A)`.  Telescoping leaves
`[log(ρ−A) − log(A−ρ)] + [log(D−ρ) − log(ρ−D)]`, and the two `log(−w) − log(w) = ±iπ` monodromy jumps
(`Complex.arg_neg_eq_arg_±pi`, sign from `Im w`) sum to `iπ + iπ = 2πi`.

This DISCHARGES the `hwind` hypothesis of `box_residue_sum` — combined, they give the UNCONDITIONAL box
argument principle.  Certificate: a proper box `x0 < x1`, `y0 < y1`.  NEGATIVE CONTROL: a
degenerate/inverted box (`x1 ≤ x0` or `y1 ≤ y0`) is REFUSED.  conjecture1_proved = False (NOT RH).
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
class RectWindingCertificate:
    """A verified winding certificate: a proper box `x0 < x1`, `y0 < y1`."""

    x0: sp.Rational
    x1: sp.Rational
    y0: sp.Rational
    y1: sp.Rational


def rect_winding_certificate(x0, x1, y0, y1) -> RectWindingCertificate:
    """Build and EXACTLY self-check a winding certificate.  Refuses a degenerate/inverted box
    (`x1 ≤ x0` or `y1 ≤ y0`) — the negative control."""
    xs = [sp.nsimplify(v) for v in (x0, x1, y0, y1)]
    for v, nm in zip(xs, ("x0", "x1", "y0", "y1")):
        if not v.is_rational:
            raise ValueError(f"rect_winding corner {nm} must be rational; got {v!r}")
    X0, X1, Y0, Y1 = xs
    if not (X0 < X1):
        raise ValueError(f"rect_winding needs x0 < x1 (proper box); got x0={X0}, x1={X1}")
    if not (Y0 < Y1):
        raise ValueError(f"rect_winding needs y0 < y1 (proper box); got y0={Y0}, y1={Y1}")
    return RectWindingCertificate(x0=X0, x1=X1, y0=Y0, y1=Y1)


def certify_rect_winding_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict with keys x0,x1,y0,y1)."""
    spec = family.special[1](pt)
    cert = rect_winding_certificate(spec["x0"], spec["x1"], spec["y0"], spec["y1"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


_HELPERS = r"""open Complex intervalIntegral Real

/-- Monodromy jump: `log(-x) - log x = π i` when `Im x < 0` (principal branch). -/
theorem log_neg_sub_im_neg (x : ℂ) (hx : x.im < 0) :
    Complex.log (-x) - Complex.log x = ↑π * I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]

/-- Monodromy jump: `log(-x) - log x = -(π i)` when `Im x > 0` (principal branch). -/
theorem log_neg_sub_im_pos (x : ℂ) (hx : 0 < x.im) :
    Complex.log (-x) - Complex.log x = -(↑π * I) := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]

"""


@dataclass
class RectWindingEmitter(Emitter):
    """Emit `∮_∂rect (z-ρ)⁻¹ = 2πi` for `ρ` strictly inside a concrete rectangle."""

    def __post_init__(self):
        self.kind = "rect_winding"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [_HELPERS]
        nthm = 2  # the two monodromy helpers, emitted once per module
        for inst in fam.instances:
            cert: RectWindingCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            x0, x1 = rat_lean(cert.x0), rat_lean(cert.x1)
            y0, y1 = rat_lean(cert.y0), rat_lean(cert.y1)
            lines.append(
                f"/-- Winding number ONE: `∮_∂[{x0},{x1}]×[{y0},{y1}] (z-ρ)⁻¹ = 2πi` for `ρ` strictly\n"
                f"    inside.  Segment/log branch-split proof — the winding-NONZERO primitive. -/\n"
                f"theorem {base} (ρ : ℂ)\n"
                f"    (hre0 : ({x0} : ℝ) < ρ.re) (hre1 : ρ.re < {x1})\n"
                f"    (him0 : ({y0} : ℝ) < ρ.im) (him1 : ρ.im < {y1}) :\n"
                f"    (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y0} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
                f"        - (∫ x in ({x0} : ℝ)..{x1}, ((↑x + (({y1} : ℝ) : ℂ) * I) - ρ)⁻¹)\n"
                f"        + I • (∫ y in ({y0} : ℝ)..{y1}, (((({x1} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
                f"        - I • (∫ y in ({y0} : ℝ)..{y1}, (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
                f"      = 2 * ↑π * I := by\n"
                f"  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - ρ).im ≠ 0) →\n"
                f"      (∫ x in ({x0} : ℝ)..{x1}, ((↑x + c) - ρ)⁻¹)\n"
                f"        = Complex.log ((↑({x1} : ℝ) + c) - ρ) - Complex.log ((↑({x0} : ℝ) + c) - ρ) := by\n"
                f"    intro c hc\n"
                f"    have hderiv : ∀ x ∈ Set.uIcc ({x0} : ℝ) {x1},\n"
                f"        HasDerivAt (fun x : ℝ => Complex.log ((↑x + c) - ρ)) (((↑x + c) - ρ)⁻¹) x := by\n"
                f"      intro x _\n"
                f"      have hpath : HasDerivAt (fun x : ℝ => ((↑x : ℂ) + c) - ρ) 1 x := by\n"
                f"        have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp\n"
                f"        exact (h1.add_const c).sub_const ρ\n"
                f"      have hslit : ((↑x + c) - ρ) ∈ Complex.slitPlane := by\n"
                f"        rw [Complex.mem_slitPlane_iff]; exact Or.inr (hc x)\n"
                f"      have hd := hpath.clog_real hslit\n"
                f"      rwa [one_div] at hd\n"
                f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
                f"    apply Continuous.intervalIntegrable\n"
                f"    refine Continuous.inv₀ (by fun_prop) (fun x => ?_)\n"
                f"    rw [sub_ne_zero]; intro h\n"
                f"    exact hc x (by rw [h]; simp)\n"
                f"  have vert : ∀ c : ℂ, (∀ y : ℝ, ((c + ↑y * I) - ρ) ∈ Complex.slitPlane) →\n"
                f"      I • (∫ y in ({y0} : ℝ)..{y1}, ((c + ↑y * I) - ρ)⁻¹)\n"
                f"        = Complex.log ((c + ↑({y1} : ℝ) * I) - ρ) - Complex.log ((c + ↑({y0} : ℝ) * I) - ρ) := by\n"
                f"    intro c hslit\n"
                f"    rw [← intervalIntegral.integral_smul]\n"
                f"    have hderiv : ∀ y ∈ Set.uIcc ({y0} : ℝ) {y1},\n"
                f"        HasDerivAt (fun y : ℝ => Complex.log ((c + ↑y * I) - ρ)) (I • ((c + ↑y * I) - ρ)⁻¹) y := by\n"
                f"      intro y _\n"
                f"      have hpath : HasDerivAt (fun y : ℝ => (c + (↑y : ℂ) * I) - ρ) I y := by\n"
                f"        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp\n"
                f"        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I\n"
                f"        exact (h2.const_add c).sub_const ρ\n"
                f"      have hd := hpath.clog_real (hslit y)\n"
                f"      rwa [div_eq_mul_inv, ← smul_eq_mul] at hd\n"
                f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
                f"    apply Continuous.intervalIntegrable\n"
                f"    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I\n"
                f"    have := hslit y\n"
                f"    rw [Complex.mem_slitPlane_iff] at this\n"
                f"    intro h; rw [h] at this; simp at this\n"
                f"  have hbot := horiz ((({y0} : ℝ) : ℂ) * I) (by\n"
                f"    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
                f"      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)\n"
                f"  have htop := horiz ((({y1} : ℝ) : ℂ) * I) (by\n"
                f"    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,\n"
                f"      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)\n"
                f"  have hright := vert (({x1} : ℝ) : ℂ) (by\n"
                f"    intro y; rw [Complex.mem_slitPlane_iff]; left\n"
                f"    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,\n"
                f"      Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith)\n"
                f"  have hleftJ : I • (∫ y in ({y0} : ℝ)..{y1}, (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹)\n"
                f"      = Complex.log (ρ - ((({x0} : ℝ) : ℂ) + ↑({y1} : ℝ) * I))"
                f" - Complex.log (ρ - ((({x0} : ℝ) : ℂ) + ↑({y0} : ℝ) * I)) := by\n"
                f"    rw [← intervalIntegral.integral_smul]\n"
                f"    have hderiv : ∀ y ∈ Set.uIcc ({y0} : ℝ) {y1},\n"
                f"        HasDerivAt (fun y : ℝ => Complex.log (ρ - ((({x0} : ℝ) : ℂ) + ↑y * I)))\n"
                f"          (I • (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) y := by\n"
                f"      intro y _\n"
                f"      have hpath : HasDerivAt (fun y : ℝ => ρ - ((({x0} : ℝ) : ℂ) + (↑y : ℂ) * I)) (-I) y := by\n"
                f"        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp\n"
                f"        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I\n"
                f"        exact (h2.const_add ((({x0} : ℝ) : ℂ))).const_sub ρ\n"
                f"      have hslit : (ρ - ((({x0} : ℝ) : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by\n"
                f"        rw [Complex.mem_slitPlane_iff]; left\n"
                f"        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,\n"
                f"          Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith\n"
                f"      have hd := hpath.clog_real hslit\n"
                f"      have hval : (-I) / (ρ - ((({x0} : ℝ) : ℂ) + ↑y * I))"
                f" = I • (((({x0} : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹ := by\n"
                f"        rw [smul_eq_mul, div_eq_mul_inv,\n"
                f"          show ρ - ((({x0} : ℝ) : ℂ) + ↑y * I)"
                f" = -(((({x0} : ℝ) : ℂ) + ↑y * I) - ρ) from by ring, inv_neg]\n"
                f"        ring\n"
                f"      rwa [hval] at hd\n"
                f"    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]\n"
                f"    apply Continuous.intervalIntegrable\n"
                f"    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I\n"
                f"    rw [sub_ne_zero]; intro h\n"
                f"    have : (((({x0} : ℝ) : ℂ) + ↑y * I)).re = ρ.re := by rw [h]\n"
                f"    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,\n"
                f"      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this; linarith\n"
                f"  rw [hbot, htop, hright, hleftJ,\n"
                f"    show ρ - ((({x0} : ℝ) : ℂ) + ↑({y1} : ℝ) * I)"
                f" = -((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - ρ) from by ring,\n"
                f"    show ρ - ((({x0} : ℝ) : ℂ) + ↑({y0} : ℝ) * I)"
                f" = -((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - ρ) from by ring]\n"
                f"  have hAim : ((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - ρ).im < 0 := by\n"
                f"    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,\n"
                f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith\n"
                f"  have hDim : 0 < ((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - ρ).im := by\n"
                f"    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,\n"
                f"      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith\n"
                f"  linear_combination log_neg_sub_im_neg ((↑({x0} : ℝ) + (({y0} : ℝ) : ℂ) * I) - ρ) hAim\n"
                f"    - log_neg_sub_im_pos ((↑({x0} : ℝ) + (({y1} : ℝ) : ℂ) * I) - ρ) hDim\n"
            )
            nthm += 1
        return "".join(lines), nthm


def rect_winding_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a rect-winding family (kind='rect_winding').  ``spec``: ``pt -> {"x0","x1","y0","y1"}``.
    Refuses a degenerate/inverted box at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("rect_winding", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert box [0,2]x[0,1] ===")
    c = rect_winding_certificate(0, 2, 0, 1)
    print(f"cert OK: x0={c.x0} x1={c.x1} y0={c.y0} y1={c.y1}")
    print("\n=== NEGATIVE CONTROL: degenerate box x1<=x0 must raise ===")
    try:
        rect_winding_certificate(2, 2, 0, 1)
        raise SystemExit("FAIL: degenerate box not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = rect_winding_family(
        "T", GridSpec([("case", [0])]), lambda pt: "rect_winding_a",
        spec=lambda pt: {"x0": "0", "x1": "2", "y0": "0", "y1": "1"},
    )
    inst, _ = certify_rect_winding_point(fam, {"case": 0}, "rect_winding_a")

    class _V:
        instances = [inst]

    body, nthm = RectWindingEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:600]}\n...[truncated]")
