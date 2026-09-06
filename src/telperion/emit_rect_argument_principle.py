"""Rectangle argument-principle emitter — Cauchy vanishing on a box boundary `∮_{∂rect} E = 0`.

The box analogue of the analytic-vanishing half of the argument principle.  Zero localization in the
critical strip is done on RECTANGLES (a box `[x0,x1] × [y0,y1]`), not disks — this atom gives the
four-segment boundary integral of a holomorphic `f`,

    (∫ x0..x1, f(x + y0 i)) − (∫ x0..x1, f(x + y1 i))
        + i (∫ y0..y1, f(x1 + y i)) − i (∫ y0..y1, f(x0 + y i)) = 0,

directly from `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (rectangular Cauchy–Goursat).
Combined with a box residue-sum it yields the argument principle on a strip.  Scope note: Mathlib's
residue lemmas are circle-based, so the residue-sum-on-a-rectangle half is NOT packaged here — this atom
is the analytic-vanishing (Cauchy) half, the box counterpart of `full_argument_principle`'s `E` term.

Certificate: a proper box `x0 < x1` and `y0 < y1`.  NEGATIVE CONTROL: a degenerate/inverted box
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
class RectArgumentPrincipleCertificate:
    """A verified rectangle certificate: a proper box `x0 < x1`, `y0 < y1`."""

    x0: sp.Rational
    x1: sp.Rational
    y0: sp.Rational
    y1: sp.Rational


def rect_argument_principle_certificate(x0, x1, y0, y1) -> RectArgumentPrincipleCertificate:
    """Build and EXACTLY self-check a rectangle certificate.  Refuses a degenerate/inverted box
    (`x1 ≤ x0` or `y1 ≤ y0`) — the negative control."""
    xs = [sp.nsimplify(v) for v in (x0, x1, y0, y1)]
    for v, nm in zip(xs, ("x0", "x1", "y0", "y1")):
        if not v.is_rational:
            raise ValueError(f"rect_argument_principle corner {nm} must be rational; got {v!r}")
    X0, X1, Y0, Y1 = xs
    if not (X0 < X1):
        raise ValueError(f"rect_argument_principle needs x0 < x1 (proper box); got x0={X0}, x1={X1}")
    if not (Y0 < Y1):
        raise ValueError(f"rect_argument_principle needs y0 < y1 (proper box); got y0={Y0}, y1={Y1}")
    return RectArgumentPrincipleCertificate(x0=X0, x1=X1, y0=Y0, y1=Y1)


def certify_rect_argument_principle_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict with keys x0,x1,y0,y1)."""
    spec = family.special[1](pt)
    cert = rect_argument_principle_certificate(spec["x0"], spec["x1"], spec["y0"], spec["y1"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class RectArgumentPrincipleEmitter(Emitter):
    """Emit the rectangular Cauchy vanishing `∮_{∂[x0,x1]×[y0,y1]} f = 0` for holomorphic `f`."""

    def __post_init__(self):
        self.kind = "rect_argument_principle"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex Metric Real intervalIntegral\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: RectArgumentPrincipleCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            x0, x1 = rat_lean(cert.x0), rat_lean(cert.x1)
            y0, y1 = rat_lean(cert.y0), rat_lean(cert.y1)
            lines.append(
                f"/-- Argument principle (analytic/Cauchy part) on the rectangle\n"
                f"    `[{x0}, {x1}] × [{y0}, {y1}]`: the four-segment boundary integral of a\n"
                f"    holomorphic `f` vanishes.  Box counterpart of the analytic `E`-term. -/\n"
                f"theorem {base} (f : ℂ → ℂ)\n"
                f"    (H : DifferentiableOn ℂ f (Set.Icc (({x0}) : ℝ) ({x1}) ×ℂ Set.Icc (({y0}) : ℝ) ({y1}))) :\n"
                f"    (∫ x : ℝ in (({x0}) : ℝ)..({x1}), f (↑x + ((({y0}) : ℝ) : ℂ) * I))\n"
                f"        - (∫ x : ℝ in (({x0}) : ℝ)..({x1}), f (↑x + ((({y1}) : ℝ) : ℂ) * I))\n"
                f"        + I • (∫ y : ℝ in (({y0}) : ℝ)..({y1}), f (((({x1}) : ℝ) : ℂ) + ↑y * I))\n"
                f"        - I • (∫ y : ℝ in (({y0}) : ℝ)..({y1}), f (((({x0}) : ℝ) : ℂ) + ↑y * I)) = 0 := by\n"
                f"  have key := integral_boundary_rect_eq_zero_of_differentiableOn f\n"
                f"    (((({x0}) : ℝ) : ℂ) + ((({y0}) : ℝ) : ℂ) * I) (((({x1}) : ℝ) : ℂ) + ((({y1}) : ℝ) : ℂ) * I)\n"
                f"  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,\n"
                f"    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at key\n"
                f"  norm_num at key ⊢\n"
                f"  exact key H\n"
            )
            nthm += 1
        return "".join(lines), nthm


def rect_argument_principle_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a rectangle-argument-principle family (kind='rect_argument_principle').  ``spec``: ``pt
    -> {"x0","x1","y0","y1"}``.  Refuses a degenerate/inverted box at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("rect_argument_principle", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert box [0,2]x[0,1] ===")
    c = rect_argument_principle_certificate(0, 2, 0, 1)
    print(f"cert OK: x0={c.x0} x1={c.x1} y0={c.y0} y1={c.y1}")
    print("\n=== NEGATIVE CONTROL: inverted box x1<=x0 must raise ===")
    try:
        rect_argument_principle_certificate(2, 0, 0, 1)
        raise SystemExit("FAIL: inverted box not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = rect_argument_principle_family(
        "T", GridSpec([("case", [0])]), lambda pt: "rect_ap_a",
        spec=lambda pt: {"x0": "0", "x1": "2", "y0": "0", "y1": "1"},
    )
    inst, _ = certify_rect_argument_principle_point(fam, {"case": 0}, "rect_ap_a")

    class _V:
        instances = [inst]

    body, nthm = RectArgumentPrincipleEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:500]}\n...[truncated]")
