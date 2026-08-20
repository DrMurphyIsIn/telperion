/- telperion 0.1.6 | family RationalSOS | input-hash f250aa242d69845d
   1 theorems, 5 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace RationalSOS

-- rational_sos_motzkin: rational-SOS (Artin denominator) — 0 ≤ p via q·p = Σ dᵢℓᵢ² with q = x**2*y**2 + x**2 + y**2 + 1 > 0 (reaches nonneg-but-not-SOS p).
theorem rational_sos_motzkin : ∀ x y : ℝ, (0:ℝ) ≤ 1 + x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 := by
  intro x y
  have hq : (0:ℝ) < 1 + x ^ 2 + y ^ 2 + x ^ 2 * y ^ 2 := by positivity
  have hqp : (0:ℝ) ≤ 1 + x ^ 2 + y ^ 2 + x ^ 6 * y ^ 2 + x ^ 2 * y ^ 6 + x ^ 6 * y ^ 4 + x ^ 4 * y ^ 6 - 2 * x ^ 2 * y ^ 2 - 2 * x ^ 4 * y ^ 2 - 2 * x ^ 2 * y ^ 4 - x ^ 4 * y ^ 4 := by
    have h : (1 + x ^ 2 + y ^ 2 + x ^ 6 * y ^ 2 + x ^ 2 * y ^ 6 + x ^ 6 * y ^ 4 + x ^ 4 * y ^ 6 - 2 * x ^ 2 * y ^ 2 - 2 * x ^ 4 * y ^ 2 - 2 * x ^ 2 * y ^ 4 - x ^ 4 * y ^ 4 : ℝ) = 1 * (1 + (-1) * x ^ 2 * y ^ 2)^2 + 1 * (x + (-1) * x ^ 3 * y ^ 2)^2 + 1 * (y + (-1) * x ^ 2 * y ^ 3)^2 + 1 * (y * x ^ 3 + (-1) * x * y ^ 3)^2 := by ring
    rw [h]; positivity
  by_contra hlt
  push_neg at hlt
  nlinarith [hqp, mul_pos hq (by linarith : (0:ℝ) < -(1 + x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2))]

end RationalSOS
end G1
