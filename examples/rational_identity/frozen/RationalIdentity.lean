/- telperion 0.1.6 | family RationalIdentity | input-hash d644f51895cb9aee
   2 theorems, 9 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace RationalIdentity

-- rational_identity_g1v1: rational-function identity on the ray 3 < n (denominator roots ['1']).
theorem rational_identity_g1v1 : ∀ n : ℚ, (3 : ℚ) < n → ((n * ((-1) + ((1 * n) / (2)))) / (((-2) + (2 * n)))) = ((n * ((-2) + n)) / (((-4) + (4 * n)))) := by
  intro n hn
  have hL0 : (((-2) + (2 * n)) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hR0 : (((-4) + (4 * n)) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  rw [div_eq_div_iff hL0 hR0]
  ring

-- rational_identity_g2_product: rational-function identity on the ray 3 < n (denominator roots ['1', '3']).
theorem rational_identity_g2_product : ∀ n : ℚ, (3 : ℚ) < n → ((n * ((-2) + n)) / (((-4) + (4 * n)) * ((-3) + n))) = ((n * ((-2) + n)) / (((-6) + (2 * n)) * ((-2) + (2 * n)))) := by
  intro n hn
  have hL0 : (((-4) + (4 * n)) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hL1 : (((-3) + n) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hR0 : (((-6) + (2 * n)) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hR1 : (((-2) + (2 * n)) : ℚ) ≠ 0 := ne_of_gt (by linarith)
  rw [div_eq_div_iff (mul_ne_zero hL0 hL1) (mul_ne_zero hR0 hR1)]
  ring

end RationalIdentity
end G1
