"""Two-scale separation emitter — an inner-disk point and an outer-sphere point are separated.

The geometric crux of the two-scale (dVP / Blaschke / Jensen) argument: if `ρ` lies in the inner
disk `closedBall c R₀` and `z` lies on the outer sphere `sphere c R`, then

    R − R₀ ≤ ‖z − ρ‖ .

Reverse triangle: `‖z − ρ‖ ≥ ‖z − c‖ − ‖ρ − c‖ = R − ‖ρ − c‖ ≥ R − R₀`.  This is exactly
`examples/zero_free_bridge/lean/DlvpZeroFactor.lean:norm_sub_ge_of_inner_outer`, the fact that makes
factored (inner-disk) zeros bounded away from a point on the outer sphere.

Certificate: `(R, R₀)` with `R₀ < R` — the separation `R − R₀` must be POSITIVE to be informative
(the bound holds for any radii, but is vacuous when `R₀ ≥ R`).

NEGATIVE CONTROL: `R₀ ≥ R` is REFUSED at certification with a ``ValueError``.  conjecture1_proved = False.
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
class TwoScaleCertificate:
    """A verified two-scale separation certificate: outer radius `R`, inner radius `R₀ < R`.
    The certified fact is `0 < R − R₀` (positive separation); the Lean is a concrete-radii copy of
    `norm_sub_ge_of_inner_outer`."""

    R: sp.Rational
    R0: sp.Rational


def two_scale_certificate(R, R0) -> TwoScaleCertificate:
    """Build and EXACTLY self-check a two-scale separation certificate.

    Refuses (``ValueError``): ``R₀ ≥ R`` — the separation `R − R₀` is non-positive (the negative
    control), so the bound carries no geometric content.
    """
    Rq, R0q = sp.nsimplify(R), sp.nsimplify(R0)
    for nm, v in (("R", Rq), ("R₀", R0q)):
        if not v.is_rational:
            raise ValueError(f"two_scale radius {nm} must be rational; got {v!r}")
    if R0q >= Rq:
        raise ValueError(
            f"two_scale needs R₀ < R (positive separation R − R₀); got R₀={R0q}, R={Rq}"
        )
    return TwoScaleCertificate(R=Rq, R0=R0q)


def certify_two_scale_separation_point(family, pt, name):
    """Certify one two-scale instance from ``family.special[1](pt)`` (dict ``{"R":…, "R0":…}`` or
    tuple ``(R, R0)``)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = two_scale_certificate(spec["R"], spec["R0"])
    elif isinstance(spec, (tuple, list)):
        cert = two_scale_certificate(spec[0], spec[1])
    else:
        raise ValueError(f"two_scale spec must be a dict or (R, R0) tuple; got {spec!r}")
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class TwoScaleSeparationEmitter(Emitter):
    """Emit the two-scale separation `R − R₀ ≤ ‖z − ρ‖` for `ρ ∈ closedBall c R₀`, `z ∈ sphere c R`
    (concrete radii), a copy of `norm_sub_ge_of_inner_outer`.  One theorem per instance."""

    def __post_init__(self):
        self.kind = "two_scale_separation"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Metric\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: TwoScaleCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr, R0r = rat_lean(cert.R), rat_lean(cert.R0)
            lines.append(
                f"/-- Two-scale separation: `ρ` in the inner disk `closedBall c {R0r}` and `z` on the\n"
                f"    outer sphere `sphere c {Rr}` are separated by `{Rr} - {R0r} ≤ ‖z - ρ‖`. -/\n"
                f"theorem {base} (c z ρ : ℂ)\n"
                f"    (hz : z ∈ sphere c ({Rr} : ℝ)) (hρ : ρ ∈ closedBall c ({R0r} : ℝ)) :\n"
                f"    ({Rr} : ℝ) - {R0r} ≤ ‖z - ρ‖ := by\n"
                f"  rw [mem_sphere_iff_norm] at hz\n"
                f"  rw [mem_closedBall_iff_norm] at hρ\n"
                f"  calc ({Rr} : ℝ) - {R0r} ≤ ‖z - c‖ - ‖ρ - c‖ := by rw [hz]; linarith\n"
                f"    _ ≤ ‖(z - c) - (ρ - c)‖ := norm_sub_norm_le _ _\n"
                f"    _ = ‖z - ρ‖ := by rw [sub_sub_sub_cancel_right]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def two_scale_separation_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a two-scale separation family (kind='two_scale_separation').  ``spec``: ``pt -> {"R":…,
    "R0":…}`` or ``pt -> (R, R0)``.  Refuses ``R₀ ≥ R`` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("two_scale_separation", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert R=3/2, R0=1 ===")
    c = two_scale_certificate(sp.Rational(3, 2), 1)
    print(f"cert OK: R={c.R}, R0={c.R0}")
    print("\n=== NEGATIVE CONTROL: R0 ≥ R (R0=2, R=1) must raise ===")
    try:
        two_scale_certificate(1, 2)
        raise SystemExit("FAIL: R0 ≥ R not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean (R=3/2, R0=1) ===")
    fam = two_scale_separation_family(
        "T", GridSpec([("case", [0])]), lambda pt: "two_scale_a", spec=lambda pt: {"R": "3/2", "R0": 1}
    )
    inst, _ = certify_two_scale_separation_point(fam, {"case": 0}, "two_scale_a")

    class _V:
        instances = [inst]

    body, nthm = TwoScaleSeparationEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body}")
