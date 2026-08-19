/- telperion 0.1.5 | family Bernoulli | input-hash 7c64922f224ea611
   6 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace Bernoulli

theorem bernoulli_k1 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 0 := by
  have hkey : 0 = 0 := by
    ring
  rw [hkey]
  positivity

theorem bernoulli_k2 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x ^ 2 := by
  have hkey : x ^ 2 = x ^ 2 := by
    ring
  rw [hkey]
  positivity

theorem bernoulli_k3 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 3 * x ^ 2 + x ^ 3 := by
  have hkey : 3 * x ^ 2 + x ^ 3 = 3 * x ^ 2 + x ^ 3 := by
    ring
  rw [hkey]
  positivity

theorem bernoulli_k4 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 6 * x ^ 2 + 4 * x ^ 3 + x ^ 4 := by
  have hkey : 6 * x ^ 2 + 4 * x ^ 3 + x ^ 4 = 6 * x ^ 2 + 4 * x ^ 3 + x ^ 4 := by
    ring
  rw [hkey]
  positivity

theorem bernoulli_k5 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 10 * x ^ 2 + 10 * x ^ 3 + 5 * x ^ 4 + x ^ 5 := by
  have hkey : 10 * x ^ 2 + 10 * x ^ 3 + 5 * x ^ 4 + x ^ 5 = 10 * x ^ 2 + 10 * x ^ 3 + 5 * x ^ 4 + x ^ 5 := by
    ring
  rw [hkey]
  positivity

theorem bernoulli_k6 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 15 * x ^ 2 + 20 * x ^ 3 + 15 * x ^ 4 + 6 * x ^ 5 + x ^ 6 := by
  have hkey : 15 * x ^ 2 + 20 * x ^ 3 + 15 * x ^ 4 + 6 * x ^ 5 + x ^ 6 = 15 * x ^ 2 + 20 * x ^ 3 + 15 * x ^ 4 + 6 * x ^ 5 + x ^ 6 := by
    ring
  rw [hkey]
  positivity

end Bernoulli
