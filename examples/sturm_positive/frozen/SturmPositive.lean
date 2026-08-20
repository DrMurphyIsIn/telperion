/- telperion 0.1.6 | family SturmPositive | input-hash bae20970da47d413
   3 theorems, 22 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace SturmPositive

-- sturm_x2_plus_1: Sturm strict-interval positivity — 0 < p on [-2, 2] (Sturm excludes roots; Bernstein bounds p − 3/8 ≥ 0).
theorem sturm_x2_plus_1 : ∀ x : ℝ, (-2) ≤ x → x ≤ 2 → (0:ℝ) < 1 + x ^ 2 := by
  intro x hlo hhi
  have hxa : (0:ℝ) ≤ 2 + x := by linarith
  have hbx : (0:ℝ) ≤ 2 - x := by linarith
  have t0 : (0:ℝ) ≤ (37 / 131072) * (2 - x)^7 := mul_nonneg ((by norm_num : (0:ℝ) ≤ (37 / 131072))) (pow_nonneg hbx 7)
  have t1 : (0:ℝ) ≤ (131 / 131072) * (2 + x)^1 * (2 - x)^6 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (131 / 131072))) (pow_nonneg hxa 1)) (pow_nonneg hbx 6)
  have t2 : (0:ℝ) ≤ (137 / 131072) * (2 + x)^2 * (2 - x)^5 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (137 / 131072))) (pow_nonneg hxa 2)) (pow_nonneg hbx 5)
  have t3 : (0:ℝ) ≤ (15 / 131072) * (2 + x)^3 * (2 - x)^4 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (15 / 131072))) (pow_nonneg hxa 3)) (pow_nonneg hbx 4)
  have t4 : (0:ℝ) ≤ (15 / 131072) * (2 + x)^4 * (2 - x)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (15 / 131072))) (pow_nonneg hxa 4)) (pow_nonneg hbx 3)
  have t5 : (0:ℝ) ≤ (137 / 131072) * (2 + x)^5 * (2 - x)^2 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (137 / 131072))) (pow_nonneg hxa 5)) (pow_nonneg hbx 2)
  have t6 : (0:ℝ) ≤ (131 / 131072) * (2 + x)^6 * (2 - x)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (131 / 131072))) (pow_nonneg hxa 6)) (pow_nonneg hbx 1)
  have t7 : (0:ℝ) ≤ (37 / 131072) * (2 + x)^7 := mul_nonneg ((by norm_num : (0:ℝ) ≤ (37 / 131072))) (pow_nonneg hxa 7)
  have hpg : (0:ℝ) ≤ (5 + 8 * x ^ 2) / (8) := by
    have hid : ((5 + 8 * x ^ 2) / (8) : ℝ) = (37 / 131072) * (2 - x)^7 + (131 / 131072) * (2 + x)^1 * (2 - x)^6 + (137 / 131072) * (2 + x)^2 * (2 - x)^5 + (15 / 131072) * (2 + x)^3 * (2 - x)^4 + (15 / 131072) * (2 + x)^4 * (2 - x)^3 + (137 / 131072) * (2 + x)^5 * (2 - x)^2 + (131 / 131072) * (2 + x)^6 * (2 - x)^1 + (37 / 131072) * (2 + x)^7 := by ring
    rw [hid]; linarith
  have hg : (0:ℝ) < (3 / 8) := by norm_num
  linarith

-- sturm_x2_minus_3x_plus_3: Sturm strict-interval positivity — 0 < p on [0, 3] (Sturm excludes roots; Bernstein bounds p − 3/8 ≥ 0).
theorem sturm_x2_minus_3x_plus_3 : ∀ x : ℝ, 0 ≤ x → x ≤ 3 → (0:ℝ) < 3 + x ^ 2 - 3 * x := by
  intro x hlo hhi
  have hxa : (0:ℝ) ≤ x := by linarith
  have hbx : (0:ℝ) ≤ 3 - x := by linarith
  have t0 : (0:ℝ) ≤ (7 / 5832) * (3 - x)^7 := mul_nonneg ((by norm_num : (0:ℝ) ≤ (7 / 5832))) (pow_nonneg hbx 7)
  have t1 : (0:ℝ) ≤ (25 / 5832) * (x)^1 * (3 - x)^6 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (25 / 5832))) (pow_nonneg hxa 1)) (pow_nonneg hbx 6)
  have t2 : (0:ℝ) ≤ (1 / 216) * (x)^2 * (3 - x)^5 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (1 / 216))) (pow_nonneg hxa 2)) (pow_nonneg hbx 5)
  have t3 : (0:ℝ) ≤ (5 / 5832) * (x)^3 * (3 - x)^4 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (5 / 5832))) (pow_nonneg hxa 3)) (pow_nonneg hbx 4)
  have t4 : (0:ℝ) ≤ (5 / 5832) * (x)^4 * (3 - x)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (5 / 5832))) (pow_nonneg hxa 4)) (pow_nonneg hbx 3)
  have t5 : (0:ℝ) ≤ (1 / 216) * (x)^5 * (3 - x)^2 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (1 / 216))) (pow_nonneg hxa 5)) (pow_nonneg hbx 2)
  have t6 : (0:ℝ) ≤ (25 / 5832) * (x)^6 * (3 - x)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (25 / 5832))) (pow_nonneg hxa 6)) (pow_nonneg hbx 1)
  have t7 : (0:ℝ) ≤ (7 / 5832) * (x)^7 := mul_nonneg ((by norm_num : (0:ℝ) ≤ (7 / 5832))) (pow_nonneg hxa 7)
  have hpg : (0:ℝ) ≤ (21 + 8 * x ^ 2 - 24 * x) / (8) := by
    have hid : ((21 + 8 * x ^ 2 - 24 * x) / (8) : ℝ) = (7 / 5832) * (3 - x)^7 + (25 / 5832) * (x)^1 * (3 - x)^6 + (1 / 216) * (x)^2 * (3 - x)^5 + (5 / 5832) * (x)^3 * (3 - x)^4 + (5 / 5832) * (x)^4 * (3 - x)^3 + (1 / 216) * (x)^5 * (3 - x)^2 + (25 / 5832) * (x)^6 * (3 - x)^1 + (7 / 5832) * (x)^7 := by ring
    rw [hid]; linarith
  have hg : (0:ℝ) < (3 / 8) := by norm_num
  linarith

-- sturm_shifted_parabola: Sturm strict-interval positivity — 0 < p on [6, 10] (Sturm excludes roots; Bernstein bounds p − 7/8 ≥ 0).
theorem sturm_shifted_parabola : ∀ x : ℝ, 6 ≤ x → x ≤ 10 → (0:ℝ) < 11 + x ^ 2 - 7 * x := by
  intro x hlo hhi
  have hxa : (0:ℝ) ≤ x - 6 := by linarith
  have hbx : (0:ℝ) ≤ 10 - x := by linarith
  have t0 : (0:ℝ) ≤ (33 / 128) * (10 - x)^2 := mul_nonneg ((by norm_num : (0:ℝ) ≤ (33 / 128))) (pow_nonneg hbx 2)
  have t1 : (0:ℝ) ≤ (113 / 64) * (x - 6)^1 * (10 - x)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (113 / 64))) (pow_nonneg hxa 1)) (pow_nonneg hbx 1)
  have t2 : (0:ℝ) ≤ (321 / 128) * (x - 6)^2 := mul_nonneg ((by norm_num : (0:ℝ) ≤ (321 / 128))) (pow_nonneg hxa 2)
  have hpg : (0:ℝ) ≤ (81 + 8 * x ^ 2 - 56 * x) / (8) := by
    have hid : ((81 + 8 * x ^ 2 - 56 * x) / (8) : ℝ) = (33 / 128) * (10 - x)^2 + (113 / 64) * (x - 6)^1 * (10 - x)^1 + (321 / 128) * (x - 6)^2 := by ring
    rw [hid]; linarith
  have hg : (0:ℝ) < (7 / 8) := by norm_num
  linarith

end SturmPositive
end G1
