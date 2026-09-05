"""Maximum-modulus propagation emitter — a sphere norm bound propagates to the disk.

Maximum-modulus principle (norm form): for `f : ℂ → ℂ` holomorphic on the open
disk `Metric.ball c R` and continuous up to the boundary (`DiffContOnCl`), if
`‖f z‖ ≤ B` on the boundary sphere `Metric.sphere c R`, then

    ‖f z‖ ≤ B   for all z ∈ Metric.ball c R   (for R ≠ 0).

This is exactly Mathlib's `Complex.norm_le_of_forall_mem_frontier_norm_le`
(v4.32.0) specialised to a ball, whose frontier is the sphere (`frontier_ball`).
It is the reusable engine behind the de la Vallee Poussin entire-part argument:
`log‖g‖ = Re(log g)` is harmonic, so its sup over a disk is attained on the
boundary, letting a boundary-sphere growth bound propagate inward
(`examples/zero_free_bridge/lean/DlvpMaxMod.lean:norm_le_on_ball_of_sphere`).

Certificate: `(R, B)` with `R > 0` (refuse `R ≤ 0` — the ball/sphere geometry is
degenerate and `frontier_ball` needs `R ≠ 0`).

NEGATIVE CONTROL: `R ≤ 0` is REFUSED at certification with a ``ValueError``.
conjecture1_proved = False.
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
class MaxModulusCertificate:
    """A verified maximum-modulus propagation certificate.

    ``R`` is the disk radius (strictly positive) and ``B`` the boundary bound.
    The certified fact is the well-posedness ``R > 0`` (so `frontier (ball c R) =
    sphere c R` holds and the propagation is non-degenerate); the Lean is a
    concrete-radius wrapper of `Complex.norm_le_of_forall_mem_frontier_norm_le`.
    """

    R: sp.Rational
    B: sp.Rational


def max_modulus_certificate(R, B) -> MaxModulusCertificate:
    """Build and EXACTLY self-check a maximum-modulus propagation certificate.

    Refuses (``ValueError``): ``R ≤ 0`` — the negative control (degenerate
    ball/sphere; `frontier_ball` requires ``R ≠ 0``).
    """
    Rq = sp.nsimplify(R)
    Bq = sp.nsimplify(B)
    if not Rq.is_rational:
        raise ValueError(f"max-modulus radius R must be rational; got {R!r}")
    if not Bq.is_rational:
        raise ValueError(f"max-modulus boundary bound B must be rational; got {B!r}")
    if Rq <= 0:
        raise ValueError(
            f"max-modulus propagation needs strictly positive radius R > 0; got R={Rq}"
        )
    return MaxModulusCertificate(R=Rq, B=Bq)


def certify_max_modulus_point(family, pt, name):
    """Certify one maximum-modulus instance from ``family.special[1](pt)``.

    ``spec(pt)`` returns a dict ``{"R": ..., "B": ...}`` or a tuple ``(R, B)``.
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = max_modulus_certificate(spec["R"], spec["B"])
    elif isinstance(spec, (tuple, list)):
        cert = max_modulus_certificate(spec[0], spec[1])
    else:
        raise ValueError(f"max_modulus spec must be a dict or (R, B) tuple; got {spec!r}")
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class MaxModulusEmitter(Emitter):
    """Emit the maximum-modulus propagation ``(‖f‖ ≤ B on sphere) → (‖f‖ ≤ B on
    ball)`` on a disk of concrete radius ``R`` (a wrapper of
    `Complex.norm_le_of_forall_mem_frontier_norm_le`).  One theorem per instance."""

    def __post_init__(self):
        self.kind = "max_modulus"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex Metric\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: MaxModulusCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr = rat_lean(cert.R)
            Br = rat_lean(cert.B)
            lines.append(
                f"/-- Maximum-modulus propagation on the disk of radius `{Rr}` about `c`:\n"
                f"    `f` holomorphic on `ball c {Rr}` (continuous up to the boundary) with\n"
                f"    `‖f z‖ ≤ {Br}` on `sphere c {Rr}` implies `‖f z‖ ≤ {Br}` throughout `ball c {Rr}`.\n"
                f"    A concrete-radius wrapper of `Complex.norm_le_of_forall_mem_frontier_norm_le`. -/\n"
                f"theorem {base} (f : ℂ → ℂ) (c : ℂ)\n"
                f"    (hd : DiffContOnCl ℂ f (ball c ({Rr} : ℝ)))\n"
                f"    (hB : ∀ z ∈ sphere c ({Rr} : ℝ), ‖f z‖ ≤ ({Br} : ℝ)) :\n"
                f"    ∀ z ∈ ball c ({Rr} : ℝ), ‖f z‖ ≤ ({Br} : ℝ) := by\n"
                f"  intro z hz\n"
                f"  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_\n"
                f"    (subset_closure hz)\n"
                f"  rw [frontier_ball c (by norm_num : ({Rr} : ℝ) ≠ 0)]\n"
                f"  exact hB\n"
            )
            nthm += 1
        return "".join(lines), nthm


def max_modulus_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a maximum-modulus propagation family (kind='max_modulus').

    ``spec``: a callable ``pt -> {"R":…, "B":…}`` or ``pt -> (R, B)``.  Refuses
    ``R ≤ 0`` at certification (the negative control)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("max_modulus", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive certificate R=1/2, B=12 ===")
    cert = max_modulus_certificate(sp.Rational(1, 2), 12)
    print(f"cert OK: R={cert.R}, B={cert.B}")

    print("\n=== NEGATIVE CONTROL: R=0 must raise ValueError ===")
    try:
        max_modulus_certificate(0, 12)
        raise SystemExit("FAIL: R=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: R=-1 must raise ValueError ===")
    try:
        max_modulus_certificate(-1, 12)
        raise SystemExit("FAIL: R=-1 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean: R=1/2,B=12 and R=1/4,B=3 ===")
    _SPECS = {0: {"R": sp.Rational(1, 2), "B": 12}, 1: {"R": sp.Rational(1, 4), "B": 3}}
    _NAMES = {0: "max_modulus_half", 1: "max_modulus_qtr"}
    fam = max_modulus_family(
        "MaxModulusSelfTest",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    insts = []
    for case in (0, 1):
        inst, _ = certify_max_modulus_point(fam, {"case": case}, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = MaxModulusEmitter().emit_body(_View(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n")
    print(body)
