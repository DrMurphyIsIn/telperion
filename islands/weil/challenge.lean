module

public import Weil.Definitions

/-!
# Telperion challenge overlay for AxiomMath/Weil

Pinned library: https://github.com/AxiomMath/Weil at commit
27cdb2049be62ee2911429b47f54774078450e32.

This file is NOT part of the library. The library ships no statement-only challenge module, so
the Telperion lead wrote this one (option A, 2026-11-06). It is a trusted statement layer:
bb checks it against the library statement by statement.

It states two of the library's theorems, the point-count statements, and proves neither:

* the classical form of the Riemann hypothesis for the zeta series,
  `Weil.exists_zetaSeries_mul_prod_even_eq_prod_odd`;
* the rationality of the zeta series, `AlgebraicGeometry.exists_mul_zetaSeries_eq`.

Each theorem has the same fully qualified name as the library's and, copied verbatim, the same
statement, under the same `open`, `universe` and `variable` commands as in its source file. The
`-- upstream:` comment above each theorem gives the line of the library's declaration. The
`@[weil "..."]` tags are left out, because they are not part of the statements.

The overlay imports only `Weil.Definitions`, the library's module of the definitions that enter
its statements. That module's import closure contains no module that declares either theorem,
so the overlay's declarations do not clash with the library's.

At replay the overlay is placed at `Weil/TelperionChallenge.lean` in a fresh copy of the pinned
tree, as the only added file. Comparator then compares each statement with the theorem of the
same name in the solution module
`Weil.AlgebraicGeometry.EtaleCohomology.Trace.WeilRiemannHypothesisForm`, which imports both.
-/

@[expose] public noncomputable section

section WeilRiemannHypothesisForm

-- The context of Weil/AlgebraicGeometry/EtaleCohomology/Trace/WeilRiemannHypothesisForm.lean,
-- lines 37-44 and 117-118.
open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Stacks.Frobenius IntermediateField
  Polynomial

universe u

namespace Weil

variable {k : Type u} [Field k] [Fintype k]

variable (B : BigEtaleSite.{u}) (S : B.Scheme) (f : S.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ)
  [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

-- upstream: Weil/AlgebraicGeometry/EtaleCohomology/Trace/WeilRiemannHypothesisForm.lean:206
omit [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)] in
/-- **The Weil conjectures** (FK, Introduction). Let `X` be a smooth, geometrically irreducible
scheme of dimension `d`, proper over the finite field `k` with `q` elements, and `f_X ∈ ℚ⟦t⟧` its
zeta series. There are polynomials `f_0, …, f_{2d} ∈ ℤ[t]` with `f_j(0) = 1`, `f_0 = 1 - t`,
`f_{2d} = 1 - q^d t`, such that every `λ ∈ ℂ^×` with `f_j(λ⁻¹) = 0` has `|λ| = q ^ (j / 2)`, and
`f_X · f_0 f_2 ⋯ f_{2d} = f_1 f_3 ⋯ f_{2d-1}` in `ℚ⟦t⟧`. -/
theorem exists_zetaSeries_mul_prod_even_eq_prod_odd {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (d : ℕ) [IsProper f] [SmoothOfRelativeDimension d f] [GeometricallyIrreducible f] :
    ∃ P : ℕ → ℤ[X],
      (∀ j ≤ 2 * d, (P j).coeff 0 = 1) ∧ P 0 = 1 - Polynomial.X ∧
      P (2 * d) = 1 - C ((Fintype.card k : ℤ) ^ d) * Polynomial.X ∧
      (∀ j ≤ 2 * d, ∀ z : ℂ, z ≠ 0 → aeval z⁻¹ (P j) = 0 →
        ‖z‖ = (Fintype.card k : ℝ) ^ ((j : ℝ) / 2)) ∧
      zetaSeries f * ∏ j ∈ (Finset.range (2 * d + 1)).filter Even,
          (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
        ∏ j ∈ (Finset.range (2 * d + 1)).filter (¬ Even ·),
          (((P j).map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) := by sorry

end Weil

end WeilRiemannHypothesisForm

section ZetaRationality

-- The context of Weil/AlgebraicGeometry/EtaleCohomology/Trace/ZetaRationality.lean,
-- lines 52-54 and 113-117.
open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology PowerSeries

universe u

namespace AlgebraicGeometry

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

variable {k : Type u} [Field k] [Finite k]

-- upstream: Weil/AlgebraicGeometry/EtaleCohomology/Trace/ZetaRationality.lean:170
/-- **Rationality of the zeta series** (Dwork; FK, Introduction (1)). Let `X` be a scheme of
finite type over a finite field `k` and `f_X ∈ ℚ⟦t⟧` its zeta series. Then there are polynomials
`P, Q ∈ ℚ[t]` with `Q(0) = 1` and `Q f_X = P` in `ℚ⟦t⟧`: `f_X` is the expansion at `t = 0` of
the rational function `P / Q`. -/
theorem exists_mul_zetaSeries_eq {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧ (Q : ℚ⟦X⟧) * zetaSeries f = P := by sorry

end AlgebraicGeometry

end ZetaRationality
