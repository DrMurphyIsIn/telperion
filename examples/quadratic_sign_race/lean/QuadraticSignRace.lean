/- telperion 0.1.6 | family QuadraticSignRace | input-hash 8fb3846c9ce80b87
   4 theorems, 12 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace QuadraticSignRace

-- sq_sub_10m_sub_7_switch: quadratic sign race, P(m) = (1 : ℝ)·m² + (-10 : ℝ)·m + (-7 : ℝ): negative on [5, 10], positive from 11 (sharp switch); never zero at an
-- integer m ≥ 5.  Certificate: vertex -b/(2a) ≤ 5 (monotone), endpoint
-- signs by norm_num, Taylor identity at the anchor 11 by ring.
theorem sq_sub_10m_sub_7_switch :
    (∀ m : ℤ, 5 ≤ m → m ≤ 10 → (1 : ℝ) * (m : ℝ) ^ 2 + (-10 : ℝ) * (m : ℝ) + (-7 : ℝ) < 0) ∧
    (∀ m : ℤ, 11 ≤ m → 0 < (1 : ℝ) * (m : ℝ) ^ 2 + (-10 : ℝ) * (m : ℝ) + (-7 : ℝ)) ∧
    (∀ m : ℤ, 5 ≤ m → (1 : ℝ) * (m : ℝ) ^ 2 + (-10 : ℝ) * (m : ℝ) + (-7 : ℝ) ≠ 0) := by
  have hneg : ∀ m : ℤ, 5 ≤ m → m ≤ 10 → (1 : ℝ) * (m : ℝ) ^ 2 + (-10 : ℝ) * (m : ℝ) + (-7 : ℝ) < 0 := by
    intro m h1 h2
    have h1' : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    have h2' : (m : ℝ) ≤ (10 : ℝ) := by exact_mod_cast h2
    have hid : ((1 : ℝ) * (10 : ℝ) ^ 2 + (-10 : ℝ) * (10 : ℝ) + (-7 : ℝ)) - ((1 : ℝ) * (m : ℝ) ^ 2 + (-10 : ℝ) * (m : ℝ) + (-7 : ℝ))
        = ((10 : ℝ) - (m : ℝ)) * ((1 : ℝ) * ((10 : ℝ) + (m : ℝ)) + (-10 : ℝ)) := by ring
    have hf : (0 : ℝ) ≤ (1 : ℝ) * ((10 : ℝ) + (m : ℝ)) + (-10 : ℝ) := by linarith
    have hp : (0 : ℝ) ≤ ((10 : ℝ) - (m : ℝ)) * ((1 : ℝ) * ((10 : ℝ) + (m : ℝ)) + (-10 : ℝ)) :=
      mul_nonneg (by linarith) hf
    have hr : (1 : ℝ) * (10 : ℝ) ^ 2 + (-10 : ℝ) * (10 : ℝ) + (-7 : ℝ) < 0 := by norm_num
    linarith
  have hpos : ∀ m : ℤ, 11 ≤ m → 0 < (1 : ℝ) * (m : ℝ) ^ 2 + (-10 : ℝ) * (m : ℝ) + (-7 : ℝ) := by
    intro m h
    have h' : (11 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hid : (1 : ℝ) * (m : ℝ) ^ 2 + (-10 : ℝ) * (m : ℝ) + (-7 : ℝ)
        = (1 : ℝ) * ((m : ℝ) - (11 : ℝ)) ^ 2 + (12 : ℝ) * ((m : ℝ) - (11 : ℝ)) + (4 : ℝ) := by ring
    rw [hid]
    have t1 : (0 : ℝ) ≤ (1 : ℝ) * ((m : ℝ) - (11 : ℝ)) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    have t2 : (0 : ℝ) ≤ (12 : ℝ) * ((m : ℝ) - (11 : ℝ)) := mul_nonneg (by norm_num) (by linarith)
    have t3 : (0 : ℝ) < (4 : ℝ) := by norm_num
    linarith
  refine ⟨hneg, hpos, fun m h => ?_⟩
  by_cases hm : m ≤ 10
  · exact (hneg m h hm).ne
  · exact (hpos m (by omega)).ne'

-- choose2_overtakes_3m_add_20: quadratic sign race, P(m) = (1/2 : ℝ)·m² + (-7/2 : ℝ)·m + (-20 : ℝ): negative on [4, 10], positive from 11 (sharp switch); never zero at an
-- integer m ≥ 4.  Certificate: vertex -b/(2a) ≤ 4 (monotone), endpoint
-- signs by norm_num, Taylor identity at the anchor 11 by ring.
theorem choose2_overtakes_3m_add_20 :
    (∀ m : ℤ, 4 ≤ m → m ≤ 10 → (1/2 : ℝ) * (m : ℝ) ^ 2 + (-7/2 : ℝ) * (m : ℝ) + (-20 : ℝ) < 0) ∧
    (∀ m : ℤ, 11 ≤ m → 0 < (1/2 : ℝ) * (m : ℝ) ^ 2 + (-7/2 : ℝ) * (m : ℝ) + (-20 : ℝ)) ∧
    (∀ m : ℤ, 4 ≤ m → (1/2 : ℝ) * (m : ℝ) ^ 2 + (-7/2 : ℝ) * (m : ℝ) + (-20 : ℝ) ≠ 0) := by
  have hneg : ∀ m : ℤ, 4 ≤ m → m ≤ 10 → (1/2 : ℝ) * (m : ℝ) ^ 2 + (-7/2 : ℝ) * (m : ℝ) + (-20 : ℝ) < 0 := by
    intro m h1 h2
    have h1' : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    have h2' : (m : ℝ) ≤ (10 : ℝ) := by exact_mod_cast h2
    have hid : ((1/2 : ℝ) * (10 : ℝ) ^ 2 + (-7/2 : ℝ) * (10 : ℝ) + (-20 : ℝ)) - ((1/2 : ℝ) * (m : ℝ) ^ 2 + (-7/2 : ℝ) * (m : ℝ) + (-20 : ℝ))
        = ((10 : ℝ) - (m : ℝ)) * ((1/2 : ℝ) * ((10 : ℝ) + (m : ℝ)) + (-7/2 : ℝ)) := by ring
    have hf : (0 : ℝ) ≤ (1/2 : ℝ) * ((10 : ℝ) + (m : ℝ)) + (-7/2 : ℝ) := by linarith
    have hp : (0 : ℝ) ≤ ((10 : ℝ) - (m : ℝ)) * ((1/2 : ℝ) * ((10 : ℝ) + (m : ℝ)) + (-7/2 : ℝ)) :=
      mul_nonneg (by linarith) hf
    have hr : (1/2 : ℝ) * (10 : ℝ) ^ 2 + (-7/2 : ℝ) * (10 : ℝ) + (-20 : ℝ) < 0 := by norm_num
    linarith
  have hpos : ∀ m : ℤ, 11 ≤ m → 0 < (1/2 : ℝ) * (m : ℝ) ^ 2 + (-7/2 : ℝ) * (m : ℝ) + (-20 : ℝ) := by
    intro m h
    have h' : (11 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hid : (1/2 : ℝ) * (m : ℝ) ^ 2 + (-7/2 : ℝ) * (m : ℝ) + (-20 : ℝ)
        = (1/2 : ℝ) * ((m : ℝ) - (11 : ℝ)) ^ 2 + (15/2 : ℝ) * ((m : ℝ) - (11 : ℝ)) + (2 : ℝ) := by ring
    rw [hid]
    have t1 : (0 : ℝ) ≤ (1/2 : ℝ) * ((m : ℝ) - (11 : ℝ)) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    have t2 : (0 : ℝ) ≤ (15/2 : ℝ) * ((m : ℝ) - (11 : ℝ)) := mul_nonneg (by norm_num) (by linarith)
    have t3 : (0 : ℝ) < (2 : ℝ) := by norm_num
    linarith
  refine ⟨hneg, hpos, fun m h => ?_⟩
  by_cases hm : m ≤ 10
  · exact (hneg m h hm).ne
  · exact (hpos m (by omega)).ne'

-- sq_sub_3m_add_1_pos: quadratic sign race, P(m) = (1 : ℝ)·m² + (-3 : ℝ)·m + (1 : ℝ): positive for all m ≥ 3; never zero at an
-- integer m ≥ 3.  Certificate: vertex -b/(2a) ≤ 3 (monotone), endpoint
-- signs by norm_num, Taylor identity at the anchor 3 by ring.
theorem sq_sub_3m_add_1_pos :
    (∀ m : ℤ, 3 ≤ m → 0 < (1 : ℝ) * (m : ℝ) ^ 2 + (-3 : ℝ) * (m : ℝ) + (1 : ℝ)) ∧
    (∀ m : ℤ, 3 ≤ m → (1 : ℝ) * (m : ℝ) ^ 2 + (-3 : ℝ) * (m : ℝ) + (1 : ℝ) ≠ 0) := by
  have htail : ∀ m : ℤ, 3 ≤ m → 0 < (1 : ℝ) * (m : ℝ) ^ 2 + (-3 : ℝ) * (m : ℝ) + (1 : ℝ) := by
    intro m h
    have h' : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hid : (1 : ℝ) * (m : ℝ) ^ 2 + (-3 : ℝ) * (m : ℝ) + (1 : ℝ)
        = (1 : ℝ) * ((m : ℝ) - (3 : ℝ)) ^ 2 + (3 : ℝ) * ((m : ℝ) - (3 : ℝ)) + (1 : ℝ) := by ring
    rw [hid]
    have t1 : (0 : ℝ) ≤ (1 : ℝ) * ((m : ℝ) - (3 : ℝ)) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    have t2 : (0 : ℝ) ≤ (3 : ℝ) * ((m : ℝ) - (3 : ℝ)) := mul_nonneg (by norm_num) (by linarith)
    have t3 : (0 : ℝ) < (1 : ℝ) := by norm_num
    linarith
  refine ⟨htail, fun m h => ?_⟩
  exact (htail m h).ne'

-- neg_sq_sub_8m_sub_17_neg: quadratic sign race, P(m) = (-1 : ℝ)·m² + (-8 : ℝ)·m + (-17 : ℝ): negative for all m ≥ -3; never zero at an
-- integer m ≥ -3.  Certificate: vertex -b/(2a) ≤ -3 (monotone), endpoint
-- signs by norm_num, Taylor identity at the anchor -3 by ring.
theorem neg_sq_sub_8m_sub_17_neg :
    (∀ m : ℤ, -3 ≤ m → (-1 : ℝ) * (m : ℝ) ^ 2 + (-8 : ℝ) * (m : ℝ) + (-17 : ℝ) < 0) ∧
    (∀ m : ℤ, -3 ≤ m → (-1 : ℝ) * (m : ℝ) ^ 2 + (-8 : ℝ) * (m : ℝ) + (-17 : ℝ) ≠ 0) := by
  have htail : ∀ m : ℤ, -3 ≤ m → (-1 : ℝ) * (m : ℝ) ^ 2 + (-8 : ℝ) * (m : ℝ) + (-17 : ℝ) < 0 := by
    intro m h
    have h' : (-3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hid : (-1 : ℝ) * (m : ℝ) ^ 2 + (-8 : ℝ) * (m : ℝ) + (-17 : ℝ)
        = (-1 : ℝ) * ((m : ℝ) - (-3 : ℝ)) ^ 2 + (-2 : ℝ) * ((m : ℝ) - (-3 : ℝ)) + (-2 : ℝ) := by ring
    rw [hid]
    have t1 : (0 : ℝ) ≤ (1 : ℝ) * ((m : ℝ) - (-3 : ℝ)) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    have t2 : (0 : ℝ) ≤ (2 : ℝ) * ((m : ℝ) - (-3 : ℝ)) := mul_nonneg (by norm_num) (by linarith)
    have t3 : (-2 : ℝ) < 0 := by norm_num
    linarith
  refine ⟨htail, fun m h => ?_⟩
  exact (htail m h).ne

end QuadraticSignRace
