"""Log-product boundary-bound emitter — the zero-factor magnitude bound (dVP two-scale).

The recurring shape behind the de la Vallée Poussin zero-factor bound `AP` (and any Blaschke / finite
zero-product magnitude argument): for `P w = ∏_ρ (w−ρ)^{m ρ}` with nonnegative multiplicities and zeros
in an INNER disk `closedBall c R₀`, evaluated at the centre `c` and a point `z` on the OUTER sphere
`sphere c R` (`1 ≤ R₀ < R`),

    log‖P c‖ − log‖P z‖  ≤  (Σ_ρ m ρ) · (log R₀ − log(R − R₀)).

The classical two-scale trick: every factored zero is bounded AWAY from the outer sphere
(`‖z−ρ‖ ≥ R−R₀ > 0`, reverse triangle) and within `R₀` of the centre, so each per-zero log-ratio
`log‖c−ρ‖ − log‖z−ρ‖ ≤ log R₀ − log(R−R₀)` is an absolute constant; the total is that constant times
the zero count `Σ m ρ`.  `z ≠ ρ` is FREE from the separation; `R₀ ≥ 1` keeps `log R₀ ≥ 0`, absorbing the
`ρ = c` edge.  Deterministic: `norm_sub_norm_le` (separation), `Real.log_le_log` (monotone),
`Real.log_prod`/`norm_prod`/`Real.log_zpow` (log of the product), `Finset.sum_le_sum` (assembly).

Certificate: `1 ≤ R₀ < R` (a genuine two-scale annulus).  NEGATIVE CONTROL: `R₀ < 1` or `R ≤ R₀` is
REFUSED.  conjecture1_proved = False (NOT a proof of RH).
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
class LogProductBoundCertificate:
    """A verified two-scale certificate: inner radius `R₀` and outer radius `R` with `1 ≤ R₀ < R`."""

    R0: sp.Rational
    R: sp.Rational


def log_product_bound_certificate(R0, R) -> LogProductBoundCertificate:
    """Build and EXACTLY self-check a two-scale certificate.  Refuses `R₀ < 1` (log R₀ could go
    negative / degenerate) or `R ≤ R₀` (no annulus) — the negative control."""
    R0q, Rq = sp.nsimplify(R0), sp.nsimplify(R)
    if not (R0q.is_rational and Rq.is_rational):
        raise ValueError(f"log_product_bound radii must be rational; got R0={R0!r}, R={R!r}")
    if R0q < 1:
        raise ValueError(f"log_product_bound needs inner radius R₀ ≥ 1; got R₀={R0q}")
    if not (Rq > R0q):
        raise ValueError(f"log_product_bound needs outer radius R > R₀ (two-scale); got R₀={R0q}, R={Rq}")
    return LogProductBoundCertificate(R0=R0q, R=Rq)


def certify_log_product_bound_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict with keys R0, R)."""
    spec = family.special[1](pt)
    cert = log_product_bound_certificate(spec["R0"], spec["R"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class LogProductBoundEmitter(Emitter):
    """Emit the two-scale zero-factor bound `log‖P c‖ − log‖P z‖ ≤ (Σ m)·(log R₀ − log(R−R₀))`."""

    def __post_init__(self):
        self.kind = "log_product_bound"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open Complex Metric\n\n"]
        nthm = 0
        for inst in fam.instances:
            cert: LogProductBoundCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            r0, rr = rat_lean(cert.R0), rat_lean(cert.R)
            lines.append(
                f"/-- Two-scale zero-factor bound on `closedBall c {r0}` (inner) / `sphere c {rr}` (outer):\n"
                f"    `log‖∏(c-ρ)^m‖ - log‖∏(z-ρ)^m‖ ≤ (Σ m)·(log {r0} - log({rr}-{r0}))` for zeros in\n"
                f"    the inner disk (nonneg multiplicities, c not a zero).  The dVP `AP` shape. -/\n"
                f"theorem {base} {{c z : ℂ}}\n"
                f"    (hz : z ∈ sphere c ({rr} : ℝ)) (s : Finset ℂ) (m : ℂ → ℤ)\n"
                f"    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hin : ∀ ρ ∈ s, ρ ∈ closedBall c ({r0} : ℝ))\n"
                f"    (hcne : ∀ ρ ∈ s, c ≠ ρ) :\n"
                f"    Real.log ‖∏ ρ ∈ s, (c - ρ) ^ (m ρ)‖ - Real.log ‖∏ ρ ∈ s, (z - ρ) ^ (m ρ)‖\n"
                f"      ≤ (∑ ρ ∈ s, (m ρ : ℝ)) * (Real.log ({r0} : ℝ) - Real.log (({rr} : ℝ) - {r0})) := by\n"
                f"  have hR0 : (1 : ℝ) ≤ {r0} := by norm_num\n"
                f"  have hRR0 : (0 : ℝ) < ({rr} : ℝ) - {r0} := by norm_num\n"
                f"  have hsep : ∀ ρ ∈ s, ({rr} : ℝ) - {r0} ≤ ‖z - ρ‖ := by\n"
                f"    intro ρ hρ\n"
                f"    have hz' := hz; rw [mem_sphere_iff_norm] at hz'\n"
                f"    have hρ' := hin ρ hρ; rw [mem_closedBall_iff_norm] at hρ'\n"
                f"    calc ({rr} : ℝ) - {r0} ≤ ‖z - c‖ - ‖ρ - c‖ := by rw [hz']; linarith\n"
                f"      _ ≤ ‖(z - c) - (ρ - c)‖ := norm_sub_norm_le _ _\n"
                f"      _ = ‖z - ρ‖ := by rw [sub_sub_sub_cancel_right]\n"
                f"  have hzne : ∀ ρ ∈ s, z ≠ ρ := by\n"
                f"    intro ρ hρ heq\n"
                f"    have := hsep ρ hρ; rw [heq, sub_self, norm_zero] at this; linarith\n"
                f"  have hlogprod : ∀ w : ℂ, (∀ ρ ∈ s, w ≠ ρ) →\n"
                f"      Real.log ‖∏ ρ ∈ s, (w - ρ) ^ (m ρ)‖ = ∑ ρ ∈ s, (m ρ : ℝ) * Real.log ‖w - ρ‖ := by\n"
                f"    intro w hw\n"
                f"    have hne : ∀ ρ ∈ s, ‖(w - ρ) ^ (m ρ)‖ ≠ 0 := by\n"
                f"      intro ρ hρ\n"
                f"      rw [norm_zpow]\n"
                f"      exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hw ρ hρ)))\n"
                f"    rw [norm_prod, Real.log_prod hne]\n"
                f"    refine Finset.sum_congr rfl (fun ρ _ => ?_)\n"
                f"    rw [norm_zpow, Real.log_zpow]\n"
                f"  rw [hlogprod c hcne, hlogprod z hzne, ← Finset.sum_sub_distrib]\n"
                f"  have hstep : ∑ ρ ∈ s, ((m ρ : ℝ) * Real.log ‖c - ρ‖ - (m ρ : ℝ) * Real.log ‖z - ρ‖)\n"
                f"      = ∑ ρ ∈ s, (m ρ : ℝ) * (Real.log ‖c - ρ‖ - Real.log ‖z - ρ‖) :=\n"
                f"    Finset.sum_congr rfl (fun ρ _ => by ring)\n"
                f"  rw [hstep, Finset.sum_mul]\n"
                f"  refine Finset.sum_le_sum (fun ρ hρ => ?_)\n"
                f"  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hm ρ hρ)\n"
                f"  have hcρ : ‖c - ρ‖ ≤ {r0} := by\n"
                f"    have hρ' := hin ρ hρ; rw [mem_closedBall_iff_norm] at hρ'\n"
                f"    rw [norm_sub_rev]; exact hρ'\n"
                f"  have hlog1 : Real.log ‖c - ρ‖ ≤ Real.log ({r0} : ℝ) := by\n"
                f"    rcases eq_or_lt_of_le (norm_nonneg (c - ρ)) with h0 | hpos\n"
                f"    · rw [← h0, Real.log_zero]; exact Real.log_nonneg hR0\n"
                f"    · exact Real.log_le_log hpos hcρ\n"
                f"  have hlog2 : Real.log (({rr} : ℝ) - {r0}) ≤ Real.log ‖z - ρ‖ :=\n"
                f"    Real.log_le_log hRR0 (hsep ρ hρ)\n"
                f"  linarith\n"
            )
            nthm += 1
        return "".join(lines), nthm


def log_product_bound_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a log-product-bound family (kind='log_product_bound').  ``spec``: ``pt -> {"R0","R"}``.
    Refuses `R₀ < 1` or `R ≤ R₀` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("log_product_bound", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert R0=2, R=5 ===")
    c = log_product_bound_certificate(2, 5)
    print(f"cert OK: R0={c.R0} R={c.R}")
    print("\n=== NEGATIVE CONTROL: R0=1/2 (<1) must raise ===")
    try:
        log_product_bound_certificate(sp.Rational(1, 2), 5)
        raise SystemExit("FAIL: R0<1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("=== NEGATIVE CONTROL: R <= R0 must raise ===")
    try:
        log_product_bound_certificate(3, 2)
        raise SystemExit("FAIL: R<=R0 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    fam = log_product_bound_family(
        "T", GridSpec([("case", [0])]), lambda pt: "log_prod_a", spec=lambda pt: {"R0": "2", "R": "5"}
    )
    inst, _ = certify_log_product_bound_point(fam, {"case": 0}, "log_prod_a")

    class _V:
        instances = [inst]

    body, nthm = LogProductBoundEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems --\n{body[:400]}\n...[truncated]")
