/- telperion 0.1.6 | family SOSRef | input-hash c4c423b0e702f9b3
   2 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace SOSRef

-- sos_ref_x2_plus_1: SOS-Positivstellensatz refutation — the system is unsatisfiable over ℝ (−1 = σ₀ + Σσ_ig_i + Σλ_jh_j).
theorem sos_ref_x2_plus_1 : ∀ x : ℝ, 1 + x ^ 2 = 0 → False := by
  intro x he1
  have s0 : (0:ℝ) ≤ 1 * (x)^2 := by positivity
  have key : (-1:ℝ) = 1 * (x)^2 := by linear_combination (0 - 1) * he1
  linarith

-- sos_ref_x_nonneg_and_x_plus_1: SOS-Positivstellensatz refutation — the system is unsatisfiable over ℝ (−1 = σ₀ + Σσ_ig_i + Σλ_jh_j).
theorem sos_ref_x_nonneg_and_x_plus_1 : ∀ x : ℝ, (0:ℝ) ≤ x → 1 + x = 0 → False := by
  intro x hg1 he1
  have t1 : (0:ℝ) ≤ (1 * (1)^2) * (x) := mul_nonneg (by positivity) hg1
  have key : (-1:ℝ) = (1 * (1)^2) * (x) := by linear_combination (0 - 1) * he1
  linarith

end SOSRef
end G1
