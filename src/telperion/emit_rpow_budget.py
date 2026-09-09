"""RpowExponentBudget emitter — k-power product collapse with exponent-level
``linarith``, distilled from the OpenAI Euler blowup formalization
(``github.com/openai/NavierStokesAndEuler``, ``Euler/PacketExponentialTail.lean``
``normalized_tail_exponential``, Apache-2.0; recurring in 4+ Euler files).

The tail-decay workhorse: factors bounded by powers of a large parameter ``k``
(``Fᵢ ≤ k^{aᵢ}``) times a decaying ratio power (``ρ ≤ k^r`` with ``r < 0``)
collapse into a single ``k``-power, and the inequality is decided by LINARITH
AT THE EXPONENT LEVEL:

    F₁⋯F_m·ρ^{N+1}  ≤  k^{Σaᵢ + r(N+1)}  ≤  k^t     for all N ≥ N₀,

where the exponent margin ``Σaᵢ + r(N₀+1) ≤ t`` is certified EXACTLY (with
``r < 0`` it only improves as N grows).  The catalogued HölderYoung shape has
only exponent-sum identities; this is the full quantified inequality ledger.

Per-instance data: ``(kmin ≥ 1, [a₁, …, a_m], r < 0, N₀, t)``, all rational
(``m ∈ [1, 5]``).  Violated margin / ``r ≥ 0`` / ``kmin < 1`` refused —
negative controls.

HONESTY SEAM: the factor and ratio bounds are HYPOTHESES.
``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class RpowBudgetCert:
    """``(kmin, a, r, N0, t)`` with the exponent margin at ``N₀`` re-verified."""

    kmin: sp.Rational
    a: tuple[sp.Rational, ...]
    r: sp.Rational
    N0: int
    t: sp.Rational


def rpow_budget_certificate(kmin, a, r, N0, t) -> RpowBudgetCert:
    """Build and EXACTLY re-check an rpow-budget instance."""
    kmin = sp.Rational(sp.nsimplify(kmin))
    a = tuple(sp.Rational(sp.nsimplify(x)) for x in a)
    r = sp.Rational(sp.nsimplify(r))
    N0 = int(N0)
    t = sp.Rational(sp.nsimplify(t))
    if not kmin >= 1:
        raise ValueError(f"rpow_budget REFUSED: need kmin ≥ 1; got {kmin}")
    if not (1 <= len(a) <= 5):
        raise ValueError(f"rpow_budget REFUSED: 1 ≤ m ≤ 5 factors; got {len(a)}")
    if not r < 0:
        raise ValueError(f"rpow_budget REFUSED: need decay exponent r < 0; got {r}")
    if N0 < 0:
        raise ValueError(f"rpow_budget REFUSED: need N₀ ≥ 0; got {N0}")
    margin = sum(a) + r * (N0 + 1)
    if not margin <= t:
        raise ValueError(
            f"rpow_budget REFUSED: exponent margin Σa + r(N₀+1) ≤ t violated "
            f"({margin} > {t}) — the collapse cannot reach the target at N₀")
    return RpowBudgetCert(kmin=kmin, a=a, r=r, N0=N0, t=t)


def certify_rpow_budget_point(family, pt, name):
    """``spec(pt) -> (kmin, [a…], r, N0, t)``.  n_checks = 4."""
    kmin, a, r, N0, t = family.special[1](pt)
    cert = rpow_budget_certificate(kmin, a, r, N0, t)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 4


@dataclass
class RpowBudgetEmitter(Emitter):
    """Emit the k-power collapse: deterministic ``mul_le_mul``/``mul_nonneg``
    chains → ``rpow`` merge → ``Real.rpow_le_rpow_of_exponent_le`` with the
    exponent inequality closed by ``linarith``."""

    def __post_init__(self):
        self.kind = "rpow_budget"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: RpowBudgetCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            m = len(cert.a)
            km, rr, tt = rat_lean(cert.kmin), rat_lean(cert.r), rat_lean(cert.t)
            F = [f"F{i+1}" for i in range(m)]
            aL = [rat_lean(x) for x in cert.a]
            hyps = " ".join(
                f"(hF{i+1}0 : 0 ≤ {F[i]}) (hF{i+1} : {F[i]} ≤ k ^ (({aL[i]}) : ℝ))"
                for i in range(m))
            prodF = " * ".join(F)
            prodK = " * ".join(f"k ^ (({aL[i]}) : ℝ)" for i in range(m))
            body: list[str] = [
                "  have hk1 : (1:ℝ) ≤ k := le_trans (by norm_num) hk",
                "  have hk0 : (0:ℝ) < k := lt_of_lt_of_le one_pos hk1",
            ]
            # nonneg accumulators for the LHS product
            body.append("  have hn1 : 0 ≤ F1 := hF10")
            for j in range(2, m + 1):
                body.append(
                    f"  have hn{j} : 0 ≤ {' * '.join(F[:j])} := "
                    f"mul_nonneg hn{j-1} hF{j}0")
            # product chain
            body.append("  have hc1 : F1 ≤ k ^ ((" + aL[0] + ") : ℝ) := hF1")
            for j in range(2, m + 1):
                lhs = " * ".join(F[:j])
                rhs = " * ".join(f"k ^ (({aL[i]}) : ℝ)" for i in range(j))
                body.append(
                    f"  have hc{j} : {lhs} ≤ {rhs} := "
                    f"mul_le_mul hc{j-1} hF{j} hF{j}0 (le_trans hn{j-1} hc{j-1})")
            body.append(
                f"  have hpow : ρ ^ (N + 1) ≤ (k ^ (({rr}) : ℝ)) ^ (N + 1) := "
                f"pow_le_pow_left₀ hρ0 hρ (N + 1)")
            body.append(
                f"  have hall : {prodF} * ρ ^ (N + 1) ≤ "
                f"({prodK}) * (k ^ (({rr}) : ℝ)) ^ (N + 1) :=\n"
                f"    mul_le_mul hc{m} hpow (pow_nonneg hρ0 _) (le_trans hn{m} hc{m})")
            exp_sum = " + ".join(f"(({aL[i]}) : ℝ)" for i in range(m))
            rpow_adds = ", ".join(["← Real.rpow_add hk0"] * m)
            body.append(
                f"  have hcollapse : ({prodK}) * (k ^ (({rr}) : ℝ)) ^ (N + 1) =\n"
                f"      k ^ (({exp_sum}) + ({rr}) * ((N : ℝ) + 1)) := by\n"
                f"    rw [← Real.rpow_mul_natCast hk0.le, {rpow_adds}]\n"
                f"    congr 1\n"
                f"    push_cast\n"
                f"    ring")
            body.append(
                f"  have hNc : (({cert.N0} : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN")
            body.append(
                f"  have hexp : ({exp_sum}) + ({rr}) * ((N : ℝ) + 1) ≤ (({tt}) : ℝ) := by\n"
                f"    push_cast at hNc\n"
                f"    linarith [hNc]")
            body.append(
                f"  calc {prodF} * ρ ^ (N + 1)\n"
                f"      ≤ ({prodK}) * (k ^ (({rr}) : ℝ)) ^ (N + 1) := hall\n"
                f"    _ = k ^ (({exp_sum}) + ({rr}) * ((N : ℝ) + 1)) := hcollapse\n"
                f"    _ ≤ k ^ ((({tt}) : ℝ)) := "
                f"Real.rpow_le_rpow_of_exponent_le hk1 hexp")
            lines.append(
                f"-- {nm}: rpow exponent budget, factors ≤ k^a with a={list(cert.a)},\n"
                f"-- decay ρ ≤ k^({cert.r}), N ≥ {cert.N0}, target k^({cert.t});\n"
                f"-- margin Σa + r(N₀+1) = {sum(cert.a) + cert.r*(cert.N0+1)} ≤ {cert.t} "
                f"certified exactly.\n"
                f"-- Trust seam: the factor and ratio bounds are HYPOTHESES.\n"
                f"theorem {nm} (k : ℝ) (hk : ({km}) ≤ k)\n"
                f"    ({' '.join(F)} ρ : ℝ)\n"
                f"    {hyps}\n"
                f"    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ k ^ (({rr}) : ℝ))\n"
                f"    (N : ℕ) (hN : {cert.N0} ≤ N) :\n"
                f"    {prodF} * ρ ^ (N + 1) ≤ k ^ ((({tt}) : ℝ)) := by\n"
                + "\n".join(body) + "\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def rpow_budget_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``rpow_budget``; ``spec: pt -> (kmin, [a…], r, N0, t)``."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("rpow_budget", spec),
        constants=dict(constants or {}),
    )
