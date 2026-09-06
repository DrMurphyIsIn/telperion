"""Far-pole sum emitter — a sum of rational terms whose poles lie OUTSIDE the disk is bounded.

The Blaschke/dVP correction estimate: for coefficients `n u`, zeros `u` in `ball 0 R`, and `‖z‖ < R`,
each term `(n u)·conj u/(R² − conj u·z)` has its pole `R²/conj u` OUTSIDE the disk, so
`|R² − conj u·z| ≥ R² − ‖u‖‖z‖ ≥ R(R − ‖z‖) > 0`, whence

    ‖Σ_u (n u)·conj u/(R² − conj u·z)‖ ≤ (Σ_u |n u|)/(R − ‖z‖) ,

a constant `1/(R − ‖z‖)` times the coefficient total `Σ|n u|`.  This is exactly
`examples/zero_free_bridge/lean/DlvpCorrectionBound.lean:norm_correction_sum_le`.

Certificate: `R > 0` (the disk radius).  The far-pole geometry `|R² − conj u·z| ≥ R(R − ‖z‖)` and the
whole bound are well-posed exactly when `R > 0` (and, at use, `‖z‖ < R`, a hypothesis of the theorem).

NEGATIVE CONTROL: `R ≤ 0` is REFUSED at certification with a ``ValueError``.  conjecture1_proved = False.
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
class FarPoleSumCertificate:
    """A verified far-pole sum certificate: disk radius `R > 0`.  The certified fact is `R > 0`
    (so the far-pole geometry `|R² − conj u·z| ≥ R(R − ‖z‖)` is well-posed); the Lean is a
    concrete-`R` copy of `norm_correction_sum_le`, universally quantified over the coefficients."""

    R: sp.Rational


def far_pole_sum_certificate(R) -> FarPoleSumCertificate:
    """Build and EXACTLY self-check a far-pole sum certificate.  Refuses ``R ≤ 0`` (the negative
    control — the far-pole geometry degenerates)."""
    Rq = sp.nsimplify(R)
    if not Rq.is_rational:
        raise ValueError(f"far_pole_sum radius R must be rational; got {R!r}")
    if Rq <= 0:
        raise ValueError(f"far_pole_sum needs a strictly positive radius R > 0; got R={Rq}")
    return FarPoleSumCertificate(R=Rq)


def certify_far_pole_sum_point(family, pt, name):
    """Certify one far-pole instance from ``family.special[1](pt)`` (dict ``{"R":…}`` or scalar ``R``)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = far_pole_sum_certificate(spec["R"])
    else:
        cert = far_pole_sum_certificate(spec)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class FarPoleSumEmitter(Emitter):
    """Emit the far-pole sum bound `‖Σ_u (n u)·conj u/(R² − conj u·z)‖ ≤ (Σ|n u|)/(R − ‖z‖)` on a disk
    of concrete radius `R` (a copy of `norm_correction_sum_le`).  One theorem per instance."""

    def __post_init__(self):
        self.kind = "far_pole_sum"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Metric\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: FarPoleSumCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr = rat_lean(cert.R)
            lines.append(
                f"/-- Far-pole sum bound on the disk of radius `{Rr}`: the poles `{Rr}²/conj u` lie\n"
                f"    outside the disk, so `‖Σ_u (n u)·conj u/({Rr}² - conj u·z)‖ ≤ (Σ|n u|)/({Rr} - ‖z‖)`.\n"
                f"    A concrete-radius copy of `norm_correction_sum_le`. -/\n"
                f"theorem {base} (n : ℂ → ℤ) (s : Finset ℂ)\n"
                f"    (hsupp : ∀ u ∈ s, u ∈ ball (0 : ℂ) ({Rr} : ℝ)) {{z : ℂ}} (hz : ‖z‖ < ({Rr} : ℝ)) :\n"
                f"    ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / (({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖\n"
                f"      ≤ (∑ u ∈ s, |(n u : ℝ)|) / (({Rr} : ℝ) - ‖z‖) := by\n"
                f"  have hR : (0 : ℝ) < {Rr} := by norm_num\n"
                f"  have hRz : 0 < ({Rr} : ℝ) - ‖z‖ := by linarith\n"
                f"  have hterm : ∀ u ∈ s,\n"
                f"      ‖(n u : ℂ) * (starRingEnd ℂ) u / (({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖\n"
                f"        ≤ |(n u : ℝ)| / (({Rr} : ℝ) - ‖z‖) := by\n"
                f"    intro u hu\n"
                f"    have huR : ‖u‖ < ({Rr} : ℝ) := by rw [← mem_ball_zero_iff]; exact hsupp u hu\n"
                f"    have hden_ge : ({Rr} : ℝ) * ({Rr} - ‖z‖)\n"
                f"        ≤ ‖({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by\n"
                f"      calc ({Rr} : ℝ) * ({Rr} - ‖z‖) = {Rr} ^ 2 - {Rr} * ‖z‖ := by ring\n"
                f"        _ ≤ {Rr} ^ 2 - ‖u‖ * ‖z‖ := by nlinarith [norm_nonneg z, norm_nonneg u]\n"
                f"        _ = ‖(({Rr} : ℂ) ^ 2)‖ - ‖(starRingEnd ℂ) u * z‖ := by\n"
                f"            rw [norm_mul, RCLike.norm_conj]; norm_num\n"
                f"        _ ≤ ‖({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := norm_sub_norm_le _ _\n"
                f"    have hden_pos : 0 < ‖({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=\n"
                f"      lt_of_lt_of_le (by positivity) hden_ge\n"
                f"    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_intCast]\n"
                f"    rw [div_le_div_iff₀ hden_pos hRz]\n"
                f"    calc |(n u : ℝ)| * ‖u‖ * ({Rr} - ‖z‖) ≤ |(n u : ℝ)| * {Rr} * ({Rr} - ‖z‖) := by\n"
                f"            apply mul_le_mul_of_nonneg_right _ hRz.le\n"
                f"            apply mul_le_mul_of_nonneg_left huR.le (abs_nonneg _)\n"
                f"      _ = |(n u : ℝ)| * (({Rr} : ℝ) * ({Rr} - ‖z‖)) := by ring\n"
                f"      _ ≤ |(n u : ℝ)| * ‖({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=\n"
                f"            mul_le_mul_of_nonneg_left hden_ge (abs_nonneg _)\n"
                f"  calc ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / (({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖\n"
                f"      ≤ ∑ u ∈ s, ‖(n u : ℂ) * (starRingEnd ℂ) u / (({Rr} : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ :=\n"
                f"        norm_sum_le _ _\n"
                f"    _ ≤ ∑ u ∈ s, |(n u : ℝ)| / (({Rr} : ℝ) - ‖z‖) := Finset.sum_le_sum hterm\n"
                f"    _ = (∑ u ∈ s, |(n u : ℝ)|) / (({Rr} : ℝ) - ‖z‖) := by rw [Finset.sum_div]\n"
            )
            nthm += 1
        return "".join(lines), nthm


def far_pole_sum_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a far-pole sum family (kind='far_pole_sum').  ``spec``: ``pt -> {"R":…}`` or ``pt -> R``.
    Refuses ``R ≤ 0`` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("far_pole_sum", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert R=3/2 ===")
    c = far_pole_sum_certificate(sp.Rational(3, 2))
    print(f"cert OK: R={c.R}")
    print("\n=== NEGATIVE CONTROL: R=0 must raise ===")
    try:
        far_pole_sum_certificate(0)
        raise SystemExit("FAIL: R=0 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean (R=3/2) [head] ===")
    fam = far_pole_sum_family(
        "T", GridSpec([("case", [0])]), lambda pt: "far_pole_a", spec=lambda pt: {"R": "3/2"}
    )
    inst, _ = certify_far_pole_sum_point(fam, {"case": 0}, "far_pole_a")

    class _V:
        instances = [inst]

    body, nthm = FarPoleSumEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:900]}\n...[truncated]")
