"""Slit-loop winding-zero emitter — the homotopy-free heart of Rouché.

A closed loop `w : [a,b] → ℂ` that stays inside the leash `‖w − 1‖ < r` (with `r ≤ 1`, so the loop
never leaves the slit plane `ℂ ∖ (−∞,0]`) has vanishing logarithmic-derivative integral:

    w a = w b,  ∀ t, ‖w t − 1‖ < r ≤ 1   ⟹   ∮ w'/w = ∫_a^b w'(t)/w(t) dt = 0.

This is winding number ZERO about the origin: `w'/w = (log∘w)'` (Mathlib `HasDerivAt.clog_real`, valid
since `‖w−1‖<1 ⟹ Re w > 0 ⟹ w ∈ slitPlane`), and FTC-2 (`integral_eq_sub_of_hasDerivAt`) collapses the
integral to `log(w b) − log(w a) = 0` on the closed loop.  It is the argument-principle-free engine of
Rouché's theorem — the "dog on a leash": if `f/g` stays in `‖·−1‖<1` on a contour, `∮ (f/g)'/(f/g) = 0`,
so `f` and `g` have the same number of zeros inside.  (Mathlib has no winding number / Rouché; the
winding-NONZERO primitive `∮_contour (z−ρ)⁻¹ = 2πi` remains a genuine gap — this is the tractable half.)

Certificate: leash radius `0 < r ≤ 1` (the loop is pinned off the branch cut).  NEGATIVE CONTROL: `r > 1`
is REFUSED — a looser leash lets `w` reach the non-positive reals, where `log` branches and the winding
number need not vanish.  conjecture1_proved = False (NOT a proof of RH).
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
class SlitLoopWindingZeroCertificate:
    """A verified winding-zero certificate: leash radius `0 < r ≤ 1`."""

    r: sp.Rational


def slit_loop_winding_zero_certificate(r) -> SlitLoopWindingZeroCertificate:
    """Build and EXACTLY self-check a certificate.  Refuses `r ≤ 0` (no leash) or `r > 1` (leash too
    loose — the loop could reach the branch cut, winding need not vanish) — the negative control."""
    rq = sp.nsimplify(r)
    if not rq.is_rational:
        raise ValueError(f"slit_loop_winding_zero leash radius r must be rational; got {r!r}")
    if rq <= 0:
        raise ValueError(f"slit_loop_winding_zero needs a positive leash radius r > 0; got r={rq}")
    if rq > 1:
        raise ValueError(
            f"slit_loop_winding_zero needs r ≤ 1 (leash inside the slit plane); got r={rq} > 1")
    return SlitLoopWindingZeroCertificate(r=rq)


def certify_slit_loop_winding_zero_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict ``{"r":…}`` or scalar ``r``)."""
    spec = family.special[1](pt)
    cert = slit_loop_winding_zero_certificate(spec["r"] if isinstance(spec, dict) else spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class SlitLoopWindingZeroEmitter(Emitter):
    """Emit `∮ w'/w = 0` for a closed loop pinned inside the leash `‖w−1‖ < r ≤ 1`."""

    def __post_init__(self):
        self.kind = "slit_loop_winding_zero"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex intervalIntegral\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: SlitLoopWindingZeroCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            rr = rat_lean(cert.r)
            lines.append(
                f"/-- Winding-zero (Rouché heart) with leash radius `{rr}`: a closed loop `w` pinned\n"
                f"    inside `‖w-1‖ < {rr} ≤ 1` (hence in the slit plane) has `∮ w'/w = 0` —\n"
                f"    winding number 0 about the origin.  The argument-principle-free engine of Rouché. -/\n"
                f"theorem {base} {{a b : ℝ}} (w w' : ℝ → ℂ)\n"
                f"    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt w (w' t) t)\n"
                f"    (hleash : ∀ t ∈ Set.uIcc a b, ‖w t - 1‖ < ({rr} : ℝ))\n"
                f"    (hint : IntervalIntegrable (fun t => w' t / w t) MeasureTheory.volume a b)\n"
                f"    (hclosed : w a = w b) :\n"
                f"    (∫ t in a..b, w' t / w t) = 0 := by\n"
                f"  have hslit : ∀ t ∈ Set.uIcc a b, w t ∈ Complex.slitPlane := by\n"
                f"    intro t ht\n"
                f"    have h1 : ‖w t - 1‖ < 1 := lt_of_lt_of_le (hleash t ht) (by norm_num : ({rr} : ℝ) ≤ 1)\n"
                f"    rw [Complex.mem_slitPlane_iff]; left\n"
                f"    have h2 : |(w t - 1).re| ≤ ‖w t - 1‖ := Complex.abs_re_le_norm _\n"
                f"    have h3 : |(w t).re - 1| < 1 := by\n"
                f"      have he : (w t - 1).re = (w t).re - 1 := by simp\n"
                f"      rw [he] at h2; linarith\n"
                f"    have := (abs_lt.mp h3).1; linarith\n"
                f"  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Complex.log (w t)) (w' t / w t) t :=\n"
                f"    fun t ht => (hderiv t ht).clog_real (hslit t ht)\n"
                f"  rw [integral_eq_sub_of_hasDerivAt hd hint, hclosed, sub_self]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def slit_loop_winding_zero_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a winding-zero family (kind='slit_loop_winding_zero').  ``spec``: ``pt -> {"r":…}`` or
    ``pt -> r``.  Refuses `r ≤ 0` or `r > 1` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("slit_loop_winding_zero", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert r=1 ===")
    c = slit_loop_winding_zero_certificate(1)
    print(f"cert OK: r={c.r}")
    print("\n=== NEGATIVE CONTROL: r=2 (>1) must raise ===")
    try:
        slit_loop_winding_zero_certificate(2)
        raise SystemExit("FAIL: r>1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = slit_loop_winding_zero_family(
        "T", GridSpec([("case", [0])]), lambda pt: "slit_loop_a", spec=lambda pt: {"r": "1"}
    )
    inst, _ = certify_slit_loop_winding_zero_point(fam, {"case": 0}, "slit_loop_a")

    class _V:
        instances = [inst]

    body, nthm = SlitLoopWindingZeroEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:400]}\n...[truncated]")
