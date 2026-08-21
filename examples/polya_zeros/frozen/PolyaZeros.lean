/- telperion 0.1.6 | family PolyaZeros | input-hash 7eaf605097792d46
   3 theorems, 21 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace PolyaZeros

-- polya_zeros_cauchy: Pólya-with-zeros certificate  (Σxᵢ)^1 · p = Q with all Q-coefficients ≥ 0 (CPR 2011) — nonnegativity with zeros allowed on faces.
theorem polya_zeros_cauchy : ∀ x y : ℝ, (0:ℝ) ≤ x → (0:ℝ) ≤ y → (0:ℝ) < x + y → (0:ℝ) ≤ x ^ 2 + y ^ 2 - x * y := by
  intro x y h1 h2 hs
  have hpow : (0:ℝ) < (x + y)^1 := pow_pos hs 1
  have t1 : (0:ℝ) ≤ 1 * (y)^3 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg h2 3)
  have t2 : (0:ℝ) ≤ 1 * (x)^3 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg h1 3)
  have hid : (x + y)^1 * (x ^ 2 + y ^ 2 - x * y) = 1 * (y)^3 + 1 * (x)^3 := by ring
  have hkey : (0:ℝ) ≤ (x + y)^1 * (x ^ 2 + y ^ 2 - x * y) := by rw [hid]; linarith
  nlinarith [hkey, hpow]

-- polya_zeros_face_tie: Pólya-with-zeros certificate  (Σxᵢ)^1 · p = Q with all Q-coefficients ≥ 0 (CPR 2011) — nonnegativity with zeros allowed on faces.
theorem polya_zeros_face_tie : ∀ x y : ℝ, (0:ℝ) ≤ x → (0:ℝ) ≤ y → (0:ℝ) < x + y → (0:ℝ) ≤ x ^ 3 * y + x * y ^ 3 - x ^ 2 * y ^ 2 := by
  intro x y h1 h2 hs
  have hpow : (0:ℝ) < (x + y)^1 := pow_pos hs 1
  have t1 : (0:ℝ) ≤ 1 * (x)^1 * (y)^4 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg h1 1)) (pow_nonneg h2 4)
  have t2 : (0:ℝ) ≤ 1 * (x)^4 * (y)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg h1 4)) (pow_nonneg h2 1)
  have hid : (x + y)^1 * (x ^ 3 * y + x * y ^ 3 - x ^ 2 * y ^ 2) = 1 * (x)^1 * (y)^4 + 1 * (x)^4 * (y)^1 := by ring
  have hkey : (0:ℝ) ≤ (x + y)^1 * (x ^ 3 * y + x * y ^ 3 - x ^ 2 * y ^ 2) := by rw [hid]; linarith
  nlinarith [hkey, hpow]

-- polya_zeros_cpr_near_tie: Pólya-with-zeros certificate  (Σxᵢ)^13 · p = Q with all Q-coefficients ≥ 0 (CPR 2011) — nonnegativity with zeros allowed on faces.
theorem polya_zeros_cpr_near_tie : ∀ x y : ℝ, (0:ℝ) ≤ x → (0:ℝ) ≤ y → (0:ℝ) < x + y → (0:ℝ) ≤ (4 * x ^ 2 + 4 * y ^ 2 - 7 * x * y) / (4) := by
  intro x y h1 h2 hs
  have hpow : (0:ℝ) < (x + y)^13 := pow_pos hs 13
  have t1 : (0:ℝ) ≤ 1 * (y)^15 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg h2 15)
  have t2 : (0:ℝ) ≤ (45 / 4) * (x)^1 * (y)^14 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (45 / 4))) (pow_nonneg h1 1)) (pow_nonneg h2 14)
  have t3 : (0:ℝ) ≤ (225 / 4) * (x)^2 * (y)^13 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (225 / 4))) (pow_nonneg h1 2)) (pow_nonneg h2 13)
  have t4 : (0:ℝ) ≤ (325 / 2) * (x)^3 * (y)^12 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (325 / 2))) (pow_nonneg h1 3)) (pow_nonneg h2 12)
  have t5 : (0:ℝ) ≤ (585 / 2) * (x)^4 * (y)^11 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (585 / 2))) (pow_nonneg h1 4)) (pow_nonneg h2 11)
  have t6 : (0:ℝ) ≤ (1287 / 4) * (x)^5 * (y)^10 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (1287 / 4))) (pow_nonneg h1 5)) (pow_nonneg h2 10)
  have t7 : (0:ℝ) ≤ (715 / 4) * (x)^6 * (y)^9 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (715 / 4))) (pow_nonneg h1 6)) (pow_nonneg h2 9)
  have t8 : (0:ℝ) ≤ (715 / 4) * (x)^9 * (y)^6 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (715 / 4))) (pow_nonneg h1 9)) (pow_nonneg h2 6)
  have t9 : (0:ℝ) ≤ (1287 / 4) * (x)^10 * (y)^5 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (1287 / 4))) (pow_nonneg h1 10)) (pow_nonneg h2 5)
  have t10 : (0:ℝ) ≤ (585 / 2) * (x)^11 * (y)^4 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (585 / 2))) (pow_nonneg h1 11)) (pow_nonneg h2 4)
  have t11 : (0:ℝ) ≤ (325 / 2) * (x)^12 * (y)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (325 / 2))) (pow_nonneg h1 12)) (pow_nonneg h2 3)
  have t12 : (0:ℝ) ≤ (225 / 4) * (x)^13 * (y)^2 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (225 / 4))) (pow_nonneg h1 13)) (pow_nonneg h2 2)
  have t13 : (0:ℝ) ≤ (45 / 4) * (x)^14 * (y)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ (45 / 4))) (pow_nonneg h1 14)) (pow_nonneg h2 1)
  have t14 : (0:ℝ) ≤ 1 * (x)^15 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg h1 15)
  have hid : (x + y)^13 * ((4 * x ^ 2 + 4 * y ^ 2 - 7 * x * y) / (4)) = 1 * (y)^15 + (45 / 4) * (x)^1 * (y)^14 + (225 / 4) * (x)^2 * (y)^13 + (325 / 2) * (x)^3 * (y)^12 + (585 / 2) * (x)^4 * (y)^11 + (1287 / 4) * (x)^5 * (y)^10 + (715 / 4) * (x)^6 * (y)^9 + (715 / 4) * (x)^9 * (y)^6 + (1287 / 4) * (x)^10 * (y)^5 + (585 / 2) * (x)^11 * (y)^4 + (325 / 2) * (x)^12 * (y)^3 + (225 / 4) * (x)^13 * (y)^2 + (45 / 4) * (x)^14 * (y)^1 + 1 * (x)^15 := by ring
  have hkey : (0:ℝ) ≤ (x + y)^13 * ((4 * x ^ 2 + 4 * y ^ 2 - 7 * x * y) / (4)) := by rw [hid]; linarith
  nlinarith [hkey, hpow]

end PolyaZeros
end G1
