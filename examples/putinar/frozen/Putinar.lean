/- telperion 0.1.6 | family Putinar | input-hash 4a222859548f121e
   2 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Putinar

-- putinar_x2y_plus_y: Putinar certificate  p = σ_0 + Σ σ_i·g_i on the constraint set.
theorem putinar_x2y_plus_y : ∀ x y : ℝ, (0:ℝ) ≤ y → (0:ℝ) ≤ y + x ^ 2 * y := by
  intro x y hy
  have t1 : (0:ℝ) ≤ (1 * (x)^2 + 1 * (1)^2) * (y) := mul_nonneg (by positivity) hy
  have hid : (y + x ^ 2 * y : ℝ) = (1 * (x)^2 + 1 * (1)^2) * (y) := by ring
  rw [hid]; linarith

-- putinar_x_plus_y: Putinar certificate  p = σ_0 + Σ σ_i·g_i on the constraint set.
theorem putinar_x_plus_y : ∀ x y : ℝ, (0:ℝ) ≤ x → (0:ℝ) ≤ y → (0:ℝ) ≤ x + y := by
  intro x y hx hy
  have t1 : (0:ℝ) ≤ (1 * (1)^2) * (x) := mul_nonneg (by positivity) hx
  have t2 : (0:ℝ) ≤ (1 * (1)^2) * (y) := mul_nonneg (by positivity) hy
  have hid : (x + y : ℝ) = (1 * (1)^2) * (x) + (1 * (1)^2) * (y) := by ring
  rw [hid]; linarith

end Putinar
end G1
