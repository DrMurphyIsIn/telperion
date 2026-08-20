/- telperion 0.1.6 | family Handelman | input-hash c76018a9110380db
   2 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Handelman

-- handelman_1_minus_x2: Handelman certificate  p = Σ c_α ∏ ℓ_i^α (nonneg combination of constraint products) on the polytope.
theorem handelman_1_minus_x2 : ∀ x y : ℝ, (0:ℝ) ≤ 1 - x → (0:ℝ) ≤ 1 + x → (0:ℝ) ≤ 1 - x ^ 2 := by
  intro x y h1 h2
  have t1 : (0:ℝ) ≤ 1 * (1 - x)^1 * (1 + x)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg h1 1)) (pow_nonneg h2 1)
  have hid : (1 - x ^ 2 : ℝ) = 1 * (1 - x)^1 * (1 + x)^1 := by ring
  rw [hid]; linarith

-- handelman_xy: Handelman certificate  p = Σ c_α ∏ ℓ_i^α (nonneg combination of constraint products) on the polytope.
theorem handelman_xy : ∀ x y : ℝ, (0:ℝ) ≤ x → (0:ℝ) ≤ y → (0:ℝ) ≤ x * y := by
  intro x y hx hy
  have t1 : (0:ℝ) ≤ 1 * (x)^1 * (y)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg hx 1)) (pow_nonneg hy 1)
  have hid : (x * y : ℝ) = 1 * (x)^1 * (y)^1 := by ring
  rw [hid]; linarith

end Handelman
end G1
