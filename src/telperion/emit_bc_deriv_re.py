"""Real-part → derivative bound emitter — the Borel-Caratheodory + Cauchy engine.

The composite estimate at the heart of the de la Vallee Poussin entire-part
argument: an analytic function's derivative at the CENTRE of a disk is controlled
by the sup of its REAL PART (not, as in the plain Cauchy estimate `cauchy_deriv`,
by a boundary NORM bound).  For `h : ℂ → ℂ` holomorphic on `Metric.ball c R`, if

    (h z).re - (h c).re ≤ M'   for all z ∈ ball c R   (M' > 0),

then for any `0 < r < R`

    ‖deriv h c‖ ≤ 2 M' / (R - r).

Proof (verbatim `examples/zero_free_bridge/lean/DlvpBCDeriv.lean:norm_deriv_le_of_re_le`):
shift `f(w) = h(c+w) - h(c)` (centred, `f 0 = 0`, `Re f ≤ M'`);
`Complex.borelCaratheodory_zero` bounds `‖f‖ ≤ 2 M' r/(R-r)` on the sphere `‖z‖ = r`;
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy) gives
`‖deriv f 0‖ = ‖deriv h c‖ ≤ (2 M' r/(R-r))/r = 2 M'/(R-r)`.

Certificate: `(R, r, M')` with `0 < r < R` and `M' > 0`.  The EXACT self-check is
the collapse of the two-step constant `(2 M' r/(R-r))/r = 2 M'/(R-r)` over ℚ (the
`field_simp` step), plus the well-posedness `0 < r < R`, `0 < M'`.

NEGATIVE CONTROL: `r ≤ 0`, `r ≥ R`, or `M' ≤ 0` is REFUSED at certification with a
``ValueError`` (the bound `2 M'/(R-r)` would be degenerate or the geometry empty).
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
class BCDerivReCertificate:
    """A verified real-part → derivative bound certificate.

    ``R`` (outer radius), ``r`` (Cauchy radius, ``0 < r < R``) and ``M'`` (the
    real-part oscillation bound, ``> 0``).  The certified facts are the
    well-posedness ``0 < r < R``, ``0 < M'`` and the EXACT rational identity
    ``(2 M' r/(R-r))/r = 2 M'/(R-r)`` (checked over ℚ).  The Lean is a
    concrete-parameter copy of `norm_deriv_le_of_re_le`.
    """

    R: sp.Rational
    r: sp.Rational
    Mp: sp.Rational


def bc_deriv_re_certificate(R, r, Mp) -> BCDerivReCertificate:
    """Build and EXACTLY self-check a real-part → derivative bound certificate.

    Refuses (``ValueError``): ``r ≤ 0`` / ``r ≥ R`` (empty geometry) or ``M' ≤ 0``
    (degenerate bound) — the negative controls.
    """
    Rq, rq, Mq = sp.nsimplify(R), sp.nsimplify(r), sp.nsimplify(Mp)
    for nm, v in (("R", Rq), ("r", rq), ("M'", Mq)):
        if not v.is_rational:
            raise ValueError(f"bc_deriv_re parameter {nm} must be rational; got {v!r}")
    if rq <= 0:
        raise ValueError(f"bc_deriv_re needs r > 0 (Cauchy radius); got r={rq}")
    if rq >= Rq:
        raise ValueError(f"bc_deriv_re needs r < R (nested disks); got r={rq}, R={Rq}")
    if Mq <= 0:
        raise ValueError(f"bc_deriv_re needs M' > 0 (real-part oscillation); got M'={Mq}")
    # EXACT self-check of the two-step constant collapse over ℚ.
    lhs = (2 * Mq * rq / (Rq - rq)) / rq
    rhs = 2 * Mq / (Rq - rq)
    if sp.simplify(lhs - rhs) != 0:
        raise ValueError(
            "bc_deriv_re constant self-check failed (2 M' r/(R-r)/r ≠ 2 M'/(R-r)) — rejected"
        )
    return BCDerivReCertificate(R=Rq, r=rq, Mp=Mq)


def certify_bc_deriv_re_point(family, pt, name):
    """Certify one bc_deriv_re instance from ``family.special[1](pt)``.

    ``spec(pt)`` returns a dict ``{"R":…, "r":…, "Mp":…}`` or a tuple ``(R, r, Mp)``.
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = bc_deriv_re_certificate(spec["R"], spec["r"], spec["Mp"])
    elif isinstance(spec, (tuple, list)):
        cert = bc_deriv_re_certificate(spec[0], spec[1], spec[2])
    else:
        raise ValueError(f"bc_deriv_re spec must be a dict or (R, r, Mp) tuple; got {spec!r}")
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BCDerivReEmitter(Emitter):
    """Emit the real-part → derivative bound ``‖deriv h c‖ ≤ 2 M'/(R - r)`` from
    ``(h z).re - (h c).re ≤ M'`` on the disk (Borel-Caratheodory + Cauchy), a
    concrete-parameter copy of `norm_deriv_le_of_re_le`.  One theorem per instance."""

    def __post_init__(self):
        self.kind = "bc_deriv_re"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex Metric\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: BCDerivReCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr, rr, Mr = rat_lean(cert.R), rat_lean(cert.r), rat_lean(cert.Mp)
            lines.append(
                f"/-- Real-part → derivative bound on `ball c {Rr}`: `h` holomorphic with\n"
                f"    `(h z).re - (h c).re ≤ {Mr}` throughout implies `‖deriv h c‖ ≤ 2·{Mr}/({Rr} - {rr})`\n"
                f"    (Borel-Caratheodory + Cauchy).  A concrete copy of `norm_deriv_le_of_re_le`. -/\n"
                f"theorem {base} (h : ℂ → ℂ) (c : ℂ)\n"
                f"    (hana : DifferentiableOn ℂ h (ball c ({Rr} : ℝ)))\n"
                f"    (hbound : ∀ z ∈ ball c ({Rr} : ℝ), (h z).re - (h c).re ≤ ({Mr} : ℝ)) :\n"
                f"    ‖deriv h c‖ ≤ 2 * ({Mr} : ℝ) / (({Rr} : ℝ) - {rr}) := by\n"
                f"  have hr : (0 : ℝ) < {rr} := by norm_num\n"
                f"  have hrR : ({rr} : ℝ) < {Rr} := by norm_num\n"
                f"  have hM' : (0 : ℝ) < {Mr} := by norm_num\n"
                f"  have hR : (0 : ℝ) < {Rr} := by norm_num\n"
                f"  have hRr : (0 : ℝ) < ({Rr} - {rr}) := by norm_num\n"
                f"  set f : ℂ → ℂ := fun w => h (c + w) - h c with hf_def\n"
                f"  have hcball : c ∈ ball c ({Rr} : ℝ) := mem_ball_self hR\n"
                f"  have hhc : DifferentiableAt ℂ h c :=\n"
                f"    (hana c hcball).differentiableAt (isOpen_ball.mem_nhds hcball)\n"
                f"  have hmaps : ∀ w ∈ ball (0 : ℂ) ({Rr} : ℝ), c + w ∈ ball c ({Rr} : ℝ) := by\n"
                f"    intro w hw\n"
                f"    rw [mem_ball_zero_iff] at hw\n"
                f"    rw [mem_ball_iff_norm]\n"
                f"    simpa using hw\n"
                f"  have hf_deriv0 : HasDerivAt f (deriv h c) 0 := by\n"
                f"    have hbase : HasDerivAt h (deriv h c) (c + 0) := by simpa using hhc.hasDerivAt\n"
                f"    exact (hbase.comp_const_add c 0).sub_const (h c)\n"
                f"  have hf_diffR : DifferentiableOn ℂ f (ball 0 ({Rr} : ℝ)) := by\n"
                f"    intro w hw\n"
                f"    have hcw : DifferentiableAt ℂ h (c + w) :=\n"
                f"      (hana _ (hmaps w hw)).differentiableAt (isOpen_ball.mem_nhds (hmaps w hw))\n"
                f"    have h1 : DifferentiableAt ℂ (fun w => h (c + w)) w := hcw.comp w (by fun_prop)\n"
                f"    exact (h1.sub_const (h c)).differentiableWithinAt\n"
                f"  have hf0 : f 0 = 0 := by simp [hf_def]\n"
                f"  have hmaps_re : Set.MapsTo f (ball 0 ({Rr} : ℝ)) {{z | z.re ≤ ({Mr} : ℝ)}} := by\n"
                f"    intro w hw\n"
                f"    simp only [Set.mem_setOf_eq, hf_def, Complex.sub_re]\n"
                f"    exact hbound _ (hmaps w hw)\n"
                f"  have hsphere : ∀ z ∈ sphere (0 : ℂ) ({rr} : ℝ),\n"
                f"      ‖f z‖ ≤ 2 * ({Mr} : ℝ) * {rr} / ({Rr} - {rr}) := by\n"
                f"    intro z hz\n"
                f"    rw [mem_sphere_zero_iff_norm] at hz\n"
                f"    have hzball : z ∈ ball (0 : ℂ) ({Rr} : ℝ) := by\n"
                f"      rw [mem_ball_zero_iff, hz]; exact hrR\n"
                f"    have := Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hzball hf0\n"
                f"    rwa [hz] at this\n"
                f"  have hdcc : DiffContOnCl ℂ f (ball 0 ({rr} : ℝ)) := by\n"
                f"    refine ⟨hf_diffR.mono (ball_subset_ball hrR.le), ?_⟩\n"
                f"    rw [closure_ball 0 hr.ne']\n"
                f"    exact hf_diffR.continuousOn.mono (closedBall_subset_ball hrR)\n"
                f"  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsphere\n"
                f"  rw [hf_deriv0.deriv] at hcauchy\n"
                f"  calc ‖deriv h c‖ ≤ 2 * ({Mr} : ℝ) * {rr} / ({Rr} - {rr}) / {rr} := hcauchy\n"
                f"    _ = 2 * ({Mr} : ℝ) / (({Rr} : ℝ) - {rr}) := by field_simp\n"
            )
            nthm += 1
        return "".join(lines), nthm


def bc_deriv_re_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a real-part → derivative bound family (kind='bc_deriv_re').

    ``spec``: a callable ``pt -> {"R":…, "r":…, "Mp":…}`` or ``pt -> (R, r, Mp)``.
    Refuses ``r ≤ 0``, ``r ≥ R``, or ``M' ≤ 0`` at certification."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("bc_deriv_re", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive certificate R=3/2, r=1/2, M'=6 ===")
    cert = bc_deriv_re_certificate(sp.Rational(3, 2), sp.Rational(1, 2), 6)
    print(f"cert OK: R={cert.R}, r={cert.r}, M'={cert.Mp}")

    print("\n=== NEGATIVE CONTROL: r ≥ R (r=2, R=1) must raise ===")
    try:
        bc_deriv_re_certificate(1, 2, 6)
        raise SystemExit("FAIL: r ≥ R was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: M' ≤ 0 (M'=0) must raise ===")
    try:
        bc_deriv_re_certificate(2, 1, 0)
        raise SystemExit("FAIL: M'=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: r ≤ 0 (r=0) must raise ===")
    try:
        bc_deriv_re_certificate(2, 0, 6)
        raise SystemExit("FAIL: r=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean: R=3/2,r=1/2,M'=6 and R=1,r=1/4,M'=2 ===")
    _SPECS = {0: {"R": sp.Rational(3, 2), "r": sp.Rational(1, 2), "Mp": 6},
              1: {"R": 1, "r": sp.Rational(1, 4), "Mp": 2}}
    _NAMES = {0: "bc_deriv_re_a", 1: "bc_deriv_re_b"}
    fam = bc_deriv_re_family(
        "BCDerivReSelfTest",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    insts = []
    for case in (0, 1):
        inst, _ = certify_bc_deriv_re_point(fam, {"case": case}, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    body, nthm = BCDerivReEmitter().emit_body(_View(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n")
    print(body)
