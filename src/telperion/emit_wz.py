"""WZ / Zeilberger creative-telescoping emitter — machine-checkable certificates
for hypergeometric / binomial SUM IDENTITIES `Σ_k F(n,k) = rhs(n)`.

This is the combinatorial-identity certificate family (Wilf–Zeilberger, "A=B").
The finite witness is a single RATIONAL function `R(n,k)` — the WZ mate — with
`G(n,k) := R(n,k)·F̃(n,k)` (where `F̃ = F/rhs` normalizes the sum to a constant)
satisfying the WZ equation

    F̃(n+1,k) − F̃(n,k) = G(n,k+1) − G(n,k).

Summing over `k` telescopes the right side to zero (proper-hypergeometric `G`
vanishes off the finite support), so the row-sum `Σ_k F̃(n,k)` is independent of
`n`; equal to its value at the base row, it pins the identity.

Dividing the WZ equation by `F̃(n,k)` turns it into an identity of RATIONAL
functions in `(n,k)` — the summand ratios `F(n+1,k)/F(n,k)` and `F(n,k+1)/F(n,k)`
are rational exactly because `F` is proper hypergeometric.  Clearing
denominators yields a POLYNOMIAL identity that `ring` discharges with no
hypotheses — the kernel-checkable heart of the certificate.  A WRONG mate makes
the polynomials unequal, so `ring` fails and the false certificate cannot
compile (and is already REFUSED at certification).

What this emitter ships per instance:
  * `theorem <name>_wz : ∀ n k : ℝ, <lhs> = <rhs> := by ring`
    — the cross-multiplied WZ equation, an exact polynomial identity verifying
    the mate.
Plus the reusable `Telperion.wz_row_invariant` lemma (in `WZ_PRELUDE`, proven
once by finite-sum telescoping): the WZ equation + a vanishing-boundary mate ⟹
the row-sum is `n`-invariant.  The final identity is then a base-row evaluation
(a `norm_num`/`decide` on the caller's concrete base case) fed to that lemma.

HONEST SCOPE: the emitter certifies the WZ PAIR (the hard, novel object) and
ships the reusable telescoping closure.  The boundary-vanishing of `G` and the
base-row value are the standard proper-hypergeometric assembly facts — supplied
by the caller for their concrete identity, not fabricated here.  Computing the
mate `R` itself (Zeilberger's algorithm) is upstream: Telperion is the CHECKER.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import expr_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .nonvacuity import assert_certificate_sensitive
from .workflow import Emitter

# Reusable telescoping-closure lemma, proved once by finite-sum telescoping.
# No `sorry`, no added axioms — the WZ equation plus a vanishing-boundary mate
# force the row-sum to be n-invariant, for ANY (F, G).
WZ_PRELUDE = r"""namespace Telperion

/-- WZ row-sum invariant.  If the WZ equation
    `Fn1 k − Fn k = G (k+1) − G k` holds for every `k` (with `Fn1`, `Fn` the
    summand rows at `n+1` and `n`, and `G` the WZ mate at row `n`), and `G`
    takes equal values at the two ends of the range `[0, N]`, then the finite
    row-sum is unchanged from `n` to `n+1`.  Iterating from the base row yields
    the closed-form identity. -/
theorem wz_row_invariant {Fn1 Fn G : ℕ → ℝ} {N : ℕ}
    (hwz : ∀ k, Fn1 k - Fn k = G (k + 1) - G k)
    (hbdry : G N = G 0) :
    (∑ k ∈ Finset.range N, Fn1 k) = ∑ k ∈ Finset.range N, Fn k := by
  have h : (∑ k ∈ Finset.range N, (Fn1 k - Fn k))
         = ∑ k ∈ Finset.range N, (G (k + 1) - G k) :=
    Finset.sum_congr rfl (fun k _ => hwz k)
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub] at h
  rw [hbdry] at h
  linarith

end Telperion
"""


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def _hyper_ratio(shifted: sp.Expr, base: sp.Expr, syms) -> sp.Expr:
    """Simplify a proper-hypergeometric term ratio to a rational function."""
    r = sp.combsimp(sp.simplify(shifted / base))
    return sp.cancel(r)


def certify_wz_point(family, pt, name):
    """Certify one WZ instance: (CertifiedInstance, n_checks).

    Reads (F, R, rhs, n, k) = family.special[1](pt): the summand `F(n,k)`, the
    candidate WZ mate `R(n,k)`, the claimed sum `rhs(n)`, and the symbols
    `n`, `k`.  Verifies the summand ratios are rational (proper hypergeometric),
    the WZ equation holds as an exact rational identity, and the cross-multiplied
    polynomial form is a genuine identity.  Raises ValueError (a refusal) when
    `R` is not a valid WZ mate — no Lean is emitted for a false certificate.
    """
    F, R, rhs, n, k = family.special[1](pt)
    F, R, rhs = sp.sympify(F), sp.sympify(R), sp.sympify(rhs)
    syms = (n, k)
    checks = 0

    ratio_n = _hyper_ratio(F.subs(n, n + 1), F, syms)
    ratio_k = _hyper_ratio(F.subs(k, k + 1), F, syms)
    if not ratio_n.is_rational_function(n, k):
        raise ValueError(
            f"wz instance '{name}' REFUSED: F(n+1,k)/F(n,k) = {ratio_n} is not "
            "rational — F is not proper hypergeometric in n")
    if not ratio_k.is_rational_function(n, k):
        raise ValueError(
            f"wz instance '{name}' REFUSED: F(n,k+1)/F(n,k) = {ratio_k} is not "
            "rational — F is not proper hypergeometric in k")
    checks += 2

    rhs_ratio = sp.simplify(rhs / rhs.subs(n, n + 1))       # rhs(n)/rhs(n+1)
    a = sp.together(ratio_n * rhs_ratio)                    # F̃(n+1,k)/F̃(n,k)
    b = ratio_k                                             # F̃(n,k+1)/F̃(n,k)
    lhs = sp.together(a - 1)
    rhs_side = sp.together(R.subs(k, k + 1) * b - R)
    if sp.simplify(lhs - rhs_side) != 0:
        raise ValueError(
            f"wz instance '{name}' REFUSED: WZ equation fails — "
            f"(F̃(n+1,k)/F̃(n,k) − 1) − (R(n,k+1)·b − R) = "
            f"{sp.simplify(lhs - rhs_side)} ≠ 0; R is not a valid WZ mate")
    checks += 1

    # Clear denominators by multiplying the WZ equation through by the common
    # denominator D = da·db·dR·dR1.  This yields a POLYNOMIAL identity
    #   termA − termB − termC + termD ≡ 0
    # that `ring` discharges hypothesis-free.  The four terms are kept as
    # DISTINCT products (never combined) so the emitted goal is non-vacuous — a
    # wrong mate makes it a false polynomial identity and `ring` fails.
    na, da = sp.fraction(sp.together(a))   # R-INDEPENDENT summand-ratio parts
    nb, db = sp.fraction(sp.together(b))

    def _terms(Rx):
        """The four cleared-identity products as a function of the mate Rx."""
        nRx, dRx = sp.fraction(sp.together(Rx))
        nR1x, dR1x = sp.fraction(sp.together(Rx.subs(k, k + 1)))
        return ((na, dR1x, db, dRx),      #  a·D
                (da, dR1x, db, dRx),      #  1·D
                (nR1x, nb, da, dRx),      #  R(n,k+1)·b·D
                (nRx, da, dR1x, db))      #  R·D

    def _cleared(Rx):
        tA, tB, tC, tD = _terms(Rx)
        return sp.prod(tA) - sp.prod(tB) - sp.prod(tC) + sp.prod(tD)

    # Non-vacuity / load-bearing check (Telperion at its own output): the emitted
    # identity must vanish for the true mate AND be broken by a corruption — so a
    # wrong mate cannot compile, and the claim cannot collapse to a tautology.
    assert_certificate_sensitive(
        _cleared, R, [lambda r: r + 1, lambda r: r + 2], label=f"wz '{name}'")
    checks += 1

    termA, termB, termC, termD = _terms(R)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(),
        payload=(n, k, termA, termB, termC, termD),
    )
    return inst, checks


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class WZEmitter(Emitter):
    """Emit the cross-multiplied WZ equation as an exact `ring` polynomial
    identity — the kernel-checkable certificate of the WZ mate.  With the
    reusable `Telperion.wz_row_invariant` lemma (`WZ_PRELUDE`) plus the caller's
    concrete base-row evaluation, this closes `Σ_k F(n,k) = rhs(n)`.
    Deterministic order: grid order."""

    def __post_init__(self):
        self.kind = "wz"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            n, k, termA, termB, termC, termD = inst.payload  # type: ignore[misc]

            def _prod(factors):
                # Render as an UNEXPANDED product of factor-polynomials, so the
                # goal stays non-vacuous (ring normalizes; a wrong mate fails).
                parts = [f"({expr_lean(sp.expand(f), (n, k))})"
                         for f in factors if sp.expand(f) != 1]
                return " * ".join(parts) if parts else "1"

            stmt = (f"{_prod(termA)} - {_prod(termB)} "
                    f"- {_prod(termC)} + {_prod(termD)}")
            lines.append(
                f"-- {inst.lean_name}: WZ certificate for  Σ_k F(n,k) = rhs(n).\n"
                f"-- Denominator-cleared WZ equation (verifies the mate R); pair with\n"
                f"-- Telperion.wz_row_invariant + the base-row value to close the sum.\n"
                f"theorem {inst.lean_name}_wz : ∀ n k : ℝ, {stmt} = 0 := by\n"
                f"  intro n k\n"
                f"  ring\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def wz_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    n: sp.Symbol | None = None,
    k: sp.Symbol | None = None,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a WZ / Zeilberger family (kind='wz').

    spec: a callable ``pt -> (F, R, rhs, n, k)`` giving the summand ``F(n,k)``,
    the candidate WZ mate ``R(n,k)``, the claimed sum ``rhs(n)``, and the symbols
    ``n``, ``k``.  ``certify_wz_point`` verifies the WZ equation exactly and
    refuses a non-mate — no Lean is emitted for a false certificate.

    The polynomial identity is a function of ``(n, k)`` only, so the family's
    ``symbols`` are ``(n, k)`` (defaulted from the first grid instance's spec if
    not supplied).
    """
    if n is None:
        n = sp.Symbol("n")
    if k is None:
        k = sp.Symbol("k")
    return InequalityFamily(
        name=name,
        symbols=(n, k),
        grid=grid,
        lean_name=lean_name,
        special=("wz", spec),
        constants=dict(constants or {}),
    )
