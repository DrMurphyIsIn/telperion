"""Herglotz lower-bound emitter — keep the equal-height zero, drop the nonnegative rest.

The positivity move at the heart of every explicit-formula zero-free-region argument: for a Herglotz
zero-sum `Σ_ρ (m ρ)/((σ+γI) − ρ)` with nonnegative multiplicities, keeping the equal-height zero
`ρ₀ = β+γI` (whose term has real part exactly `k/(σ−β)`) and DROPPING the other zeros (each with
`Re ≥ 0`, since their real part is `< σ`) gives the lower bound

    k/(σ − β) ≤ Re(Σ_ρ (m ρ)/((σ+γI) − ρ)) .

This is `examples/zero_free_bridge/lean/DlvpHerglotzLower.lean:herglotz_re_ge`; combined with a
Borel-Caratheodory BC-SUM `-Re(ζ'/ζ) ≤ A·L − Re(Σ)` it yields the `hzero` input `-Re(ζ'/ζ) ≤ A·L −
k/(σ−β)`.  Self-contained: it carries the two rung-1 helpers (`re_smul_inv_sub_at_equal_height`,
`re_inv_sub_nonneg_of_re_lt`) as a preamble, then the general lower-bound lemma per instance.

Certificate: `(σ, β, k)` with `σ > β` and `k ≥ 1` — the kept term `k/(σ−β)` must be a genuine
POSITIVE lower bound.

NEGATIVE CONTROL: `σ ≤ β` (or `k < 1`) is REFUSED at certification with a ``ValueError``.
conjecture1_proved = False (NOT a proof of RH).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# The two rung-1 helpers, emitted once so the file is self-contained under `import Mathlib`.
# A plain string (NOT an f-string).
_PREAMBLE = r"""open Complex

/-- Equal-height contribution (helper): the zero at the same height has a real term. -/
private theorem re_smul_inv_sub_at_equal_height (σ γ β : ℝ) (k : ℝ) :
    (((k : ℂ)) / (((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I))).re = k / (σ - β) := by
  have hsub : ((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I) = ((σ - β : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Droppable zero (helper): a zero with `Re ρ < Re s` contributes a nonnegative real part. -/
private theorem re_inv_sub_nonneg_of_re_lt (s ρ : ℂ) (h : ρ.re < s.re) :
    0 ≤ (1 / (s - ρ)).re := by
  have hz : 0 < (s - ρ).re := by rw [Complex.sub_re]; linarith
  rw [one_div, Complex.inv_re]
  exact div_nonneg hz.le (Complex.normSq_nonneg _)

"""


@dataclass(frozen=True)
class HerglotzLowerCertificate:
    """A verified Herglotz lower-bound certificate: `(σ, β, k)` with `σ > β`, `k ≥ 1`.  The certified
    fact is that the kept term `k/(σ−β)` is a genuine positive lower bound; the Lean is the general
    `herglotz_re_ge` lemma (self-contained with the two rung-1 helpers)."""

    sigma: sp.Rational
    beta: sp.Rational
    k: sp.Integer


def herglotz_lower_certificate(sigma, beta, k) -> HerglotzLowerCertificate:
    """Build and EXACTLY self-check a Herglotz lower-bound certificate.  Refuses ``σ ≤ β`` (the kept
    term's denominator is non-positive) or ``k < 1`` (no zero to keep) — the negative controls."""
    sq, bq, kq = sp.nsimplify(sigma), sp.nsimplify(beta), sp.Integer(k)
    if not sq.is_rational or not bq.is_rational:
        raise ValueError(f"herglotz_lower σ, β must be rational; got {sigma!r}, {beta!r}")
    if sq <= bq:
        raise ValueError(f"herglotz_lower needs σ > β (positive kept term k/(σ−β)); got σ={sq}, β={bq}")
    if kq < 1:
        raise ValueError(f"herglotz_lower needs k ≥ 1 (a zero to keep); got k={kq}")
    return HerglotzLowerCertificate(sigma=sq, beta=bq, k=kq)


def certify_herglotz_lower_point(family, pt, name):
    """Certify one instance from ``family.special[1](pt)`` (dict ``{"sigma":…,"beta":…,"k":…}`` or
    tuple ``(sigma, beta, k)``)."""
    spec = family.special[1](pt)
    if isinstance(spec, dict):
        cert = herglotz_lower_certificate(spec["sigma"], spec["beta"], spec["k"])
    elif isinstance(spec, (tuple, list)):
        cert = herglotz_lower_certificate(spec[0], spec[1], spec[2])
    else:
        raise ValueError(f"herglotz_lower spec must be a dict or (σ, β, k) tuple; got {spec!r}")
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class HerglotzLowerEmitter(Emitter):
    """Emit the Herglotz lower bound `k/(σ−β) ≤ Re(Σ_ρ (m ρ)/((σ+γI)−ρ))` (keep the equal-height
    zero, drop the nonnegative rest), a copy of `herglotz_re_ge` with the two rung-1 helpers as a
    self-contained preamble.  One (general) theorem per instance."""

    def __post_init__(self):
        self.kind = "herglotz_lower"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [_PREAMBLE]
        nthm = 2  # the two preamble helpers are proved too
        for inst in fam.instances:
            cert: HerglotzLowerCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            lines.append(
                f"/-- Herglotz lower bound (kept term `{cert.k}/(σ−β)`, e.g. σ={cert.sigma}, β={cert.beta}):\n"
                f"    keep the equal-height zero `ρ₀ = β+γI`, drop the nonnegative rest. -/\n"
                f"theorem {base} {{s : Finset ℂ}} (m : ℂ → ℤ) (σ γ β : ℝ) (k : ℤ)\n"
                f"    (hm : ∀ ρ ∈ s, 0 ≤ m ρ)\n"
                f"    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I) (hmρ₀ : m ρ₀ = k)\n"
                f"    (hother : ∀ ρ ∈ s, ρ ≠ ρ₀ → ρ.re < σ) :\n"
                f"    (k : ℝ) / (σ - β)\n"
                f"      ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ)).re := by\n"
                f"  set z : ℂ := (σ : ℂ) + (γ : ℂ) * I with hz\n"
                f"  rw [Complex.re_sum, ← Finset.add_sum_erase _ _ hρ₀]\n"
                f"  have hterm₀ : ((m ρ₀ : ℂ) / (z - ρ₀)).re = (k : ℝ) / (σ - β) := by\n"
                f"    rw [hmρ₀, hρ₀_eq, hz]\n"
                f"    exact_mod_cast re_smul_inv_sub_at_equal_height σ γ β (k : ℝ)\n"
                f"  have hrest : 0 ≤ ∑ ρ ∈ s.erase ρ₀, ((m ρ : ℂ) / (z - ρ)).re := by\n"
                f"    apply Finset.sum_nonneg\n"
                f"    intro ρ hρ\n"
                f"    have hρs : ρ ∈ s := Finset.mem_of_mem_erase hρ\n"
                f"    have hρne : ρ ≠ ρ₀ := Finset.ne_of_mem_erase hρ\n"
                f"    have hlt : ρ.re < z.re := by rw [hz]; simpa using hother ρ hρs hρne\n"
                f"    have hdiv : (m ρ : ℂ) / (z - ρ) = (m ρ : ℂ) * (1 / (z - ρ)) := by rw [mul_one_div]\n"
                f"    rw [hdiv, ← Complex.ofReal_intCast, Complex.re_ofReal_mul]\n"
                f"    exact mul_nonneg (by exact_mod_cast hm ρ hρs) (re_inv_sub_nonneg_of_re_lt z ρ hlt)\n"
                f"  rw [hterm₀]\n"
                f"  linarith\n"
            )
            nthm += 1
        return "".join(lines), nthm


def herglotz_lower_family(
    name: str, grid: GridSpec, lean_name: Callable, spec: Callable, constants: dict | None = None
) -> InequalityFamily:
    """Build a Herglotz lower-bound family (kind='herglotz_lower').  ``spec``: ``pt -> {"sigma":…,
    "beta":…, "k":…}`` or ``pt -> (σ, β, k)``.  Refuses ``σ ≤ β`` or ``k < 1`` at certification."""
    return InequalityFamily(
        name=name, symbols=(), grid=grid, lean_name=lean_name,
        special=("herglotz_lower", spec), constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive cert σ=3/2, β=1/2, k=1 ===")
    c = herglotz_lower_certificate(sp.Rational(3, 2), sp.Rational(1, 2), 1)
    print(f"cert OK: σ={c.sigma}, β={c.beta}, k={c.k}")
    print("\n=== NEGATIVE CONTROL: σ ≤ β must raise ===")
    try:
        herglotz_lower_certificate(1, 2, 1)
        raise SystemExit("FAIL: σ ≤ β not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== NEGATIVE CONTROL: k < 1 must raise ===")
    try:
        herglotz_lower_certificate(2, 1, 0)
        raise SystemExit("FAIL: k < 1 not refused")
    except ValueError as e:
        print(f"refused as expected: {e}")
    print("\n=== emitted Lean (σ=3/2,β=1/2,k=1) [head] ===")
    fam = herglotz_lower_family(
        "T", GridSpec([("case", [0])]), lambda pt: "herglotz_a",
        spec=lambda pt: {"sigma": "3/2", "beta": "1/2", "k": 1}
    )
    inst, _ = certify_herglotz_lower_point(fam, {"case": 0}, "herglotz_a")

    class _V:
        instances = [inst]

    body, nthm = HerglotzLowerEmitter().emit_body(_V(), LeanProfile(namespace=("X",)))
    print(f"\n-- {nthm} theorems (2 helpers + wrappers) --\n{body[:700]}\n...[truncated]")
