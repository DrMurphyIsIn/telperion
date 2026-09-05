"""Entire-part bound emitter — ‖logDeriv g c‖ bounded by the oscillation of log‖g‖.

The full (i-b') composition of the de la Vallee Poussin entire-part argument, for
a zero-free holomorphic `g` on a disk: the log-derivative at the centre is bounded
by the boundary oscillation of `log‖g‖`.  For `g : ℂ → ℂ` holomorphic and zero-free
on `Metric.ball c R`, if

    log‖g z‖ - log‖g c‖ ≤ M'   for all z ∈ ball c R   (M' > 0),

then for any `0 < r < R`

    ‖logDeriv g c‖ ≤ 2 M' / (R - r).

This is `examples/zero_free_bridge/lean/DlvpEntireBound.lean:norm_logDeriv_le_of_log_norm_le`,
composed from the analytic log branch (`DlvpLogBranch`, giving `deriv h = logDeriv g`
and `Re h = log‖g‖`) and the real-part → derivative bound (`DlvpBCDeriv`, Borel-
Caratheodory + Cauchy).  The emitted file is SELF-CONTAINED (`import Mathlib`): it
carries the three generic helper lemmas as a preamble, then a concrete-parameter
wrapper per instance.

Certificate: `(R, r, M')` with `0 < r < R` and `M' > 0` — identical shape (and
constant self-check `(2 M' r/(R-r))/r = 2 M'/(R-r)`) to `bc_deriv_re`, since the
entire-part bound reuses the same geometry.

NEGATIVE CONTROL: `r ≤ 0`, `r ≥ R`, or `M' ≤ 0` is REFUSED with a ``ValueError``.
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


# The three generic helper lemmas (verbatim from DlvpLogBranch / DlvpBCDeriv /
# DlvpEntireBound), emitted once so the file is self-contained under `import Mathlib`.
# A plain string (NOT an f-string): the set-builder `{z | z.re ≤ M'}` is literal.
_PREAMBLE = r"""open Complex Metric

/-- Analytic log branch on a disk (helper): a zero-free holomorphic `g` on `ball c r`
    admits an analytic branch `h` of `log g`. -/
private theorem log_branch_of_analytic_nonvanishing {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hne : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, (∀ z ∈ ball c r, HasDerivAt h (logDeriv g z) z) ∧
      h c = Complex.log (g c) ∧
      (∀ z ∈ ball c r, Complex.exp (h z) = g z) ∧
      (∀ z ∈ ball c r, (h z).re = Real.log ‖g z‖) := by
  have hcball : c ∈ ball c r := mem_ball_self hr
  have hg_an : AnalyticOnNhd ℂ g (ball c r) := hg.analyticOnNhd isOpen_ball
  have hlog_diff : DifferentiableOn ℂ (logDeriv g) (ball c r) := by
    intro z hz
    have hderivg : DifferentiableAt ℂ (deriv g) z := (hg_an z hz).deriv.differentiableAt
    have hgz : DifferentiableAt ℂ g z := (hg_an z hz).differentiableAt
    exact (hderivg.div hgz (hne z hz)).differentiableWithinAt
  obtain ⟨h, hhc, hh⟩ := (hlog_diff.isExactOn_ball).with_val_at c (Complex.log (g c))
  have hφ : ∀ z ∈ ball c r, HasDerivAt (fun w => g w * Complex.exp (-h w)) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z := (hg_an z hz).differentiableAt.hasDerivAt
    have hexp : HasDerivAt (fun w => Complex.exp (-h w))
        (Complex.exp (-h z) * (-(logDeriv g z))) z := ((hh z hz).neg).cexp
    have hprod := hgz.mul hexp
    have hgz0 := hne z hz
    have hderiv0 : deriv g z * Complex.exp (-h z)
        + g z * (Complex.exp (-h z) * (-(logDeriv g z))) = 0 := by
      rw [logDeriv_apply]; field_simp; ring
    rw [hderiv0] at hprod
    exact hprod
  have hconst : ∀ z ∈ ball c r,
      (fun w => g w * Complex.exp (-h w)) z = (fun w => g w * Complex.exp (-h w)) c := by
    intro z hz
    refine (convex_ball c r).is_const_of_fderivWithin_eq_zero
      (fun x hx => (hφ x hx).differentiableAt.differentiableWithinAt) ?_ hz hcball
    intro x hx
    rw [fderivWithin_of_isOpen isOpen_ball hx]
    simpa using (hφ x hx).hasFDerivAt.fderiv
  have hφc : g c * Complex.exp (-h c) = 1 := by
    rw [hhc, Complex.exp_neg, Complex.exp_log (hne c hcball), mul_inv_cancel₀ (hne c hcball)]
  have hexp_eq : ∀ z ∈ ball c r, Complex.exp (h z) = g z := by
    intro z hz
    have key : g z * Complex.exp (-h z) = 1 := (hconst z hz).trans hφc
    rw [Complex.exp_neg] at key
    have hexpne : Complex.exp (h z) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hexpne] at key
    exact key.symm
  refine ⟨h, hh, hhc, hexp_eq, ?_⟩
  intro z hz
  have hnorm : ‖g z‖ = Real.exp (h z).re := by rw [← hexp_eq z hz, Complex.norm_exp]
  rw [hnorm, Real.log_exp]

/-- Real-part → derivative bound (helper): Borel-Caratheodory + Cauchy. -/
private theorem norm_deriv_le_of_re_le {h : ℂ → ℂ} {c : ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hana : DifferentiableOn ℂ h (ball c R)) (hM' : 0 < M')
    (hbound : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ M') :
    ‖deriv h c‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hRr : (0 : ℝ) < R - r := by linarith
  set f : ℂ → ℂ := fun w => h (c + w) - h c with hf_def
  have hcball : c ∈ ball c R := mem_ball_self hR
  have hhc : DifferentiableAt ℂ h c := (hana c hcball).differentiableAt (isOpen_ball.mem_nhds hcball)
  have hmaps : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball_iff_norm]
    simpa using hw
  have hf_deriv0 : HasDerivAt f (deriv h c) 0 := by
    have hbase : HasDerivAt h (deriv h c) (c + 0) := by simpa using hhc.hasDerivAt
    exact (hbase.comp_const_add c 0).sub_const (h c)
  have hf_diffR : DifferentiableOn ℂ f (ball 0 R) := by
    intro w hw
    have hcw : DifferentiableAt ℂ h (c + w) :=
      (hana _ (hmaps w hw)).differentiableAt (isOpen_ball.mem_nhds (hmaps w hw))
    have h1 : DifferentiableAt ℂ (fun w => h (c + w)) w := hcw.comp w (by fun_prop)
    exact (h1.sub_const (h c)).differentiableWithinAt
  have hf0 : f 0 = 0 := by simp [hf_def]
  have hmaps_re : Set.MapsTo f (ball 0 R) {z | z.re ≤ M'} := by
    intro w hw
    simp only [Set.mem_setOf_eq, hf_def, Complex.sub_re]
    exact hbound _ (hmaps w hw)
  have hsphere : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ 2 * M' * r / (R - r) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hzball : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hz]; exact hrR
    have := Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hzball hf0
    rwa [hz] at this
  have hdcc : DiffContOnCl ℂ f (ball 0 r) := by
    refine ⟨hf_diffR.mono (ball_subset_ball hrR.le), ?_⟩
    rw [closure_ball 0 hr.ne']
    exact hf_diffR.continuousOn.mono (closedBall_subset_ball hrR)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsphere
  rw [hf_deriv0.deriv] at hcauchy
  calc ‖deriv h c‖ ≤ 2 * M' * r / (R - r) / r := hcauchy
    _ = 2 * M' / (R - r) := by field_simp

/-- Entire-part bound (helper): compose the two above via `Re h = log‖g‖`. -/
private theorem norm_logDeriv_le_of_log_norm_le {g : ℂ → ℂ} {c : ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM' : 0 < M')
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hbound : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g c‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hcball : c ∈ ball c R := mem_ball_self hR
  obtain ⟨h, hh, _hhc, _hexp, hre⟩ := log_branch_of_analytic_nonvanishing hR hg hne
  have hh_diff : DifferentiableOn ℂ h (ball c R) :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have hderiv_c : deriv h c = logDeriv g c := (hh c hcball).deriv
  have hre_bound : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ M' := by
    intro z hz
    rw [hre z hz, hre c hcball]
    exact hbound z hz
  have := norm_deriv_le_of_re_le hr hrR hh_diff hM' hre_bound
  rwa [hderiv_c] at this

"""


@dataclass(frozen=True)
class EntirePartBoundCertificate:
    """A verified entire-part bound certificate: ``(R, r, M')`` with ``0 < r < R``
    and ``M' > 0``.  Self-checked identity ``(2 M' r/(R-r))/r = 2 M'/(R-r)`` over ℚ."""

    R: sp.Rational
    r: sp.Rational
    Mp: sp.Rational


def entire_part_bound_certificate(R, r, Mp) -> EntirePartBoundCertificate:
    """Build and EXACTLY self-check an entire-part bound certificate.

    Refuses (``ValueError``): ``r ≤ 0`` / ``r ≥ R`` (empty geometry) or ``M' ≤ 0``
    (degenerate bound) — the negative controls.
    """
    Rq, rq, Mq = sp.nsimplify(R), sp.nsimplify(r), sp.nsimplify(Mp)
    for nm, v in (("R", Rq), ("r", rq), ("M'", Mq)):
        if not v.is_rational:
            raise ValueError(f"entire_part_bound parameter {nm} must be rational; got {v!r}")
    if rq <= 0:
        raise ValueError(f"entire_part_bound needs r > 0; got r={rq}")
    if rq >= Rq:
        raise ValueError(f"entire_part_bound needs r < R; got r={rq}, R={Rq}")
    if Mq <= 0:
        raise ValueError(f"entire_part_bound needs M' > 0; got M'={Mq}")
    lhs = (2 * Mq * rq / (Rq - rq)) / rq
    rhs = 2 * Mq / (Rq - rq)
    if sp.simplify(lhs - rhs) != 0:
        raise ValueError(
            "entire_part_bound constant self-check failed (2 M' r/(R-r)/r ≠ 2 M'/(R-r)) — rejected"
        )
    return EntirePartBoundCertificate(R=Rq, r=rq, Mp=Mq)


def certify_entire_part_bound_point(family, pt, name):
    """Certify one entire_part_bound instance from ``family.special[1](pt)``.

    ``spec(pt)`` returns a dict ``{"R":…, "r":…, "Mp":…}`` or a tuple ``(R, r, Mp)``.
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = entire_part_bound_certificate(spec["R"], spec["r"], spec["Mp"])
    elif isinstance(spec, (tuple, list)):
        cert = entire_part_bound_certificate(spec[0], spec[1], spec[2])
    else:
        raise ValueError(f"entire_part_bound spec must be a dict or (R, r, Mp) tuple; got {spec!r}")
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class EntirePartBoundEmitter(Emitter):
    """Emit the entire-part bound ``‖logDeriv g c‖ ≤ 2 M'/(R - r)`` from the boundary
    oscillation ``log‖g z‖ - log‖g c‖ ≤ M'`` of a zero-free `g`.  Self-contained: a
    fixed 3-lemma preamble (log branch + BC-Cauchy + composition) followed by a
    concrete-parameter wrapper per instance."""

    def __post_init__(self):
        self.kind = "entire_part_bound"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [_PREAMBLE]
        nthm = 3  # the three preamble helper lemmas are proved too
        for inst in fam.instances:
            cert: EntirePartBoundCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            Rr, rr, Mr = rat_lean(cert.R), rat_lean(cert.r), rat_lean(cert.Mp)
            lines.append(
                f"/-- Entire-part bound on `ball c {Rr}`: zero-free holomorphic `g` with\n"
                f"    `log‖g z‖ - log‖g c‖ ≤ {Mr}` throughout implies `‖logDeriv g c‖ ≤ 2·{Mr}/({Rr} - {rr})`.\n"
                f"    A concrete copy of `norm_logDeriv_le_of_log_norm_le`. -/\n"
                f"theorem {base} (g : ℂ → ℂ) (c : ℂ)\n"
                f"    (hg : DifferentiableOn ℂ g (ball c ({Rr} : ℝ)))\n"
                f"    (hne : ∀ z ∈ ball c ({Rr} : ℝ), g z ≠ 0)\n"
                f"    (hbound : ∀ z ∈ ball c ({Rr} : ℝ),\n"
                f"      Real.log ‖g z‖ - Real.log ‖g c‖ ≤ ({Mr} : ℝ)) :\n"
                f"    ‖logDeriv g c‖ ≤ 2 * ({Mr} : ℝ) / (({Rr} : ℝ) - {rr}) :=\n"
                f"  norm_logDeriv_le_of_log_norm_le (by norm_num) (by norm_num) (by norm_num) hg hne hbound\n"
            )
            nthm += 1
        return "".join(lines), nthm


def entire_part_bound_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an entire-part bound family (kind='entire_part_bound').

    ``spec``: a callable ``pt -> {"R":…, "r":…, "Mp":…}`` or ``pt -> (R, r, Mp)``.
    Refuses ``r ≤ 0``, ``r ≥ R``, or ``M' ≤ 0`` at certification."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("entire_part_bound", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive certificate R=3/2, r=1/2, M'=6 ===")
    cert = entire_part_bound_certificate(sp.Rational(3, 2), sp.Rational(1, 2), 6)
    print(f"cert OK: R={cert.R}, r={cert.r}, M'={cert.Mp}")

    print("\n=== NEGATIVE CONTROL: r ≥ R must raise ===")
    try:
        entire_part_bound_certificate(1, 2, 6)
        raise SystemExit("FAIL: r ≥ R was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== NEGATIVE CONTROL: M' ≤ 0 must raise ===")
    try:
        entire_part_bound_certificate(2, 1, 0)
        raise SystemExit("FAIL: M'=0 was NOT refused")
    except ValueError as e:
        print(f"refused as expected: {e}")

    print("\n=== emitted Lean (preamble + 1 wrapper R=3/2,r=1/2,M'=6) ===")
    _SPECS = {0: {"R": sp.Rational(3, 2), "r": sp.Rational(1, 2), "Mp": 6}}
    _NAMES = {0: "entire_part_bound_a"}
    fam = entire_part_bound_family(
        "EntirePartBoundSelfTest",
        GridSpec([("case", [0])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    inst, _ = certify_entire_part_bound_point(fam, {"case": 0}, _NAMES[0])

    class _View:
        instances = [inst]

    body, nthm = EntirePartBoundEmitter().emit_body(_View(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems (3 helpers + wrappers) --\n")
    print(body[:1500])
    print("...\n[truncated]")
