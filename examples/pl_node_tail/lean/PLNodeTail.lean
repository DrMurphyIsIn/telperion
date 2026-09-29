/- telperion 0.1.6 | family PLNodeTail | input-hash 08c2dba7e8beaa39
   9 theorems, 11 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace PLNodeTail

-- pl_tail_log_half: piecewise-linear node-condition tail.  For all m ≥ 2 and y ∈ (0, 1],
-- m·U(y) + L(y) ≤ 0, with U below the PL function on nodes (1/4, 0), (1/2, -1/20), (3/4, -1/8), (1, -1/5)
-- and L ≤ 0 below y† = 1/2, L ≤ 2/3·(y − y†) above.  Certificate: the node
-- condition (M+1)·|U_i| ≥ s·(y_i − y†) at every node beyond y†; per segment the
-- convex-combination identity (ring).  U, L and their conditions are HYPOTHESES.
theorem pl_tail_log_half (U L : ℝ → ℝ)
    (hU0 : ∀ y : ℝ, 0 < y → y ≤ (1/4 : ℝ) → U y ≤ 0)
    (hU1 : ∀ y : ℝ, (1/4 : ℝ) ≤ y → y ≤ (1/2 : ℝ) → U y ≤ ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))))
    (hU2 : ∀ y : ℝ, (1/2 : ℝ) ≤ y → y ≤ (3/4 : ℝ) → U y ≤ ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))))
    (hU3 : ∀ y : ℝ, (3/4 : ℝ) ≤ y → y ≤ (1 : ℝ) → U y ≤ ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))))
    (hL1 : ∀ y : ℝ, 0 < y → y ≤ (1/2 : ℝ) → L y ≤ 0)
    (hL2 : ∀ y : ℝ, (1/2 : ℝ) < y → y ≤ 1 → L y ≤ (2/3 : ℝ) * (y - (1/2 : ℝ))) :
    ∀ m : ℕ, 2 ≤ m → ∀ y : ℝ, 0 < y → y ≤ 1 → (m : ℝ) * U y + L y ≤ 0 := by
  intro m hm y hy0 hy1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  rcases le_or_gt y (1/4 : ℝ) with h0 | h0
  · have hu := hU0 y hy0 h0
    have hmu := mul_le_mul_of_nonneg_left hu hm0
    rcases le_or_gt y (1/2 : ℝ) with hd | hd
    · have hL := hL1 y hy0 hd
      linarith
    · have hL := hL2 y hd hy1
      linarith
  · rcases le_or_gt y (1/2 : ℝ) with h1 | h1
    · have hu := hU1 y (le_of_lt h0) h1
      have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
      rcases le_or_gt y (1/2 : ℝ) with hd | hd
      · have hL := hL1 y hy0 hd
        have hub : ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))) ≤ 0 := by linarith
        have hmub := mul_le_mul_of_nonneg_left hub hm0
        linarith
      · have hL := hL2 y hd hy1
        linarith
    · rcases le_or_gt y (3/4 : ℝ) with h2 | h2
      · have hu := hU2 y (le_of_lt h1) h2
        have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
        rcases le_or_gt y (1/2 : ℝ) with hd | hd
        · have hL := hL1 y hy0 hd
          have hub : ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) ≤ 0 := by linarith
          have hmub := mul_le_mul_of_nonneg_left hub hm0
          linarith
        · have hL := hL2 y hd hy1
          have hA : ((m : ℝ) * (-1/20 : ℝ) + (2/3 : ℝ) * ((1/2 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hB : ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hid : ((3/4 : ℝ) - (1/2 : ℝ)) * ((m : ℝ) * ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ)))
              = ((3/4 : ℝ) - y) * ((m : ℝ) * (-1/20 : ℝ) + (2/3 : ℝ) * ((1/2 : ℝ) - (1/2 : ℝ))) + (y - (1/2 : ℝ)) * ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) := by ring
          have p1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ (3/4 : ℝ) - y)
          have p2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ y - (1/2 : ℝ))
          have hseg : ((3/4 : ℝ) - (1/2 : ℝ)) * ((m : ℝ) * ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ))) ≤ 0 := by
            rw [hid]; linarith
          linarith
      · have hu := hU3 y (le_of_lt h2) hy1
        have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
        rcases le_or_gt y (1/2 : ℝ) with hd | hd
        · have hL := hL1 y hy0 hd
          have hub : ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) ≤ 0 := by linarith
          have hmub := mul_le_mul_of_nonneg_left hub hm0
          linarith
        · have hL := hL2 y hd hy1
          have hA : ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hB : ((m : ℝ) * (-1/5 : ℝ) + (2/3 : ℝ) * ((1 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hid : ((1 : ℝ) - (3/4 : ℝ)) * ((m : ℝ) * ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ)))
              = ((1 : ℝ) - y) * ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) + (y - (3/4 : ℝ)) * ((m : ℝ) * (-1/5 : ℝ) + (2/3 : ℝ) * ((1 : ℝ) - (1/2 : ℝ))) := by ring
          have p1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ (1 : ℝ) - y)
          have p2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ y - (3/4 : ℝ))
          have hseg : ((1 : ℝ) - (3/4 : ℝ)) * ((m : ℝ) * ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ))) ≤ 0 := by
            rw [hid]; linarith
          linarith

-- pl_tail_log_half_L_nonpos / pl_tail_log_half_L_tangent: L(y) = log(1+y) − log(1+y†) meets hL1 (log
-- monotone) and hL2 (log x ≤ x − 1 at x = (1+y)/(1+y†), then s ≥ 1/(1+y†)).
theorem pl_tail_log_half_L_nonpos : ∀ y : ℝ, 0 < y → y ≤ (1/2 : ℝ) → Real.log (1 + y) - Real.log (1 + (1/2 : ℝ)) ≤ 0 := by
  intro y hy h
  have := Real.log_le_log (by linarith) (by linarith : 1 + y ≤ 1 + (1/2 : ℝ))
  linarith

theorem pl_tail_log_half_L_tangent :
    ∀ y : ℝ, (1/2 : ℝ) < y → y ≤ 1 → Real.log (1 + y) - Real.log (1 + (1/2 : ℝ)) ≤ (2/3 : ℝ) * (y - (1/2 : ℝ)) := by
  intro y hy h
  have hpos : (0 : ℝ) < (1 + y) / (1 + (1/2 : ℝ)) := div_pos (by linarith) (by norm_num)
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 : Real.log ((1 + y) / (1 + (1/2 : ℝ))) = Real.log (1 + y) - Real.log (1 + (1/2 : ℝ)) :=
    Real.log_div (by linarith) (by norm_num)
  have h3 : (1 + y) / (1 + (1/2 : ℝ)) - 1 = (2/3 : ℝ) * (y - (1/2 : ℝ)) := by ring
  linarith

-- pl_tail_log_half_concrete: hypothesis-free instance, U = min(0, segment lines) (below every
-- segment line, so it meets every U hypothesis) and L = log(1+y) − log(1+y†).
theorem pl_tail_log_half_concrete :
    ∀ m : ℕ, 2 ≤ m → ∀ y : ℝ, 0 < y → y ≤ 1 →
      (m : ℝ) * min 0 (min ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))) (min ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) (((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ)))))) + (Real.log (1 + y) - Real.log (1 + (1/2 : ℝ))) ≤ 0 :=
  pl_tail_log_half (fun y => min 0 (min ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))) (min ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) (((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))))))) (fun y => Real.log (1 + y) - Real.log (1 + (1/2 : ℝ)))
    (fun _ _ _ => min_le_left _ _)
    (fun _ _ _ => le_trans (min_le_right _ _) (min_le_left _ _))
    (fun _ _ _ => le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    (fun _ _ _ => le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_refl _))))
    pl_tail_log_half_L_nonpos pl_tail_log_half_L_tangent

-- pl_tail_log_third: piecewise-linear node-condition tail.  For all m ≥ 15 and y ∈ (0, 1],
-- m·U(y) + L(y) ≤ 0, with U below the PL function on nodes (1/3, 0), (2/3, -1/40), (1, -1/30)
-- and L ≤ 0 below y† = 1/3, L ≤ 3/4·(y − y†) above.  Certificate: the node
-- condition (M+1)·|U_i| ≥ s·(y_i − y†) at every node beyond y†; per segment the
-- convex-combination identity (ring).  U, L and their conditions are HYPOTHESES.
theorem pl_tail_log_third (U L : ℝ → ℝ)
    (hU0 : ∀ y : ℝ, 0 < y → y ≤ (1/3 : ℝ) → U y ≤ 0)
    (hU1 : ∀ y : ℝ, (1/3 : ℝ) ≤ y → y ≤ (2/3 : ℝ) → U y ≤ ((0 : ℝ) + (-3/40 : ℝ) * (y - (1/3 : ℝ))))
    (hU2 : ∀ y : ℝ, (2/3 : ℝ) ≤ y → y ≤ (1 : ℝ) → U y ≤ ((-1/40 : ℝ) + (-1/40 : ℝ) * (y - (2/3 : ℝ))))
    (hL1 : ∀ y : ℝ, 0 < y → y ≤ (1/3 : ℝ) → L y ≤ 0)
    (hL2 : ∀ y : ℝ, (1/3 : ℝ) < y → y ≤ 1 → L y ≤ (3/4 : ℝ) * (y - (1/3 : ℝ))) :
    ∀ m : ℕ, 15 ≤ m → ∀ y : ℝ, 0 < y → y ≤ 1 → (m : ℝ) * U y + L y ≤ 0 := by
  intro m hm y hy0 hy1
  have hmR : (15 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  rcases le_or_gt y (1/3 : ℝ) with h0 | h0
  · have hu := hU0 y hy0 h0
    have hmu := mul_le_mul_of_nonneg_left hu hm0
    rcases le_or_gt y (1/3 : ℝ) with hd | hd
    · have hL := hL1 y hy0 hd
      linarith
    · have hL := hL2 y hd hy1
      linarith
  · rcases le_or_gt y (2/3 : ℝ) with h1 | h1
    · have hu := hU1 y (le_of_lt h0) h1
      have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((0 : ℝ) + (-3/40 : ℝ) * (y - (1/3 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
      rcases le_or_gt y (1/3 : ℝ) with hd | hd
      · have hL := hL1 y hy0 hd
        have hub : ((0 : ℝ) + (-3/40 : ℝ) * (y - (1/3 : ℝ))) ≤ 0 := by linarith
        have hmub := mul_le_mul_of_nonneg_left hub hm0
        linarith
      · have hL := hL2 y hd hy1
        have hA : ((m : ℝ) * (0 : ℝ) + (3/4 : ℝ) * ((1/3 : ℝ) - (1/3 : ℝ))) ≤ 0 := by linarith
        have hB : ((m : ℝ) * (-1/40 : ℝ) + (3/4 : ℝ) * ((2/3 : ℝ) - (1/3 : ℝ))) ≤ 0 := by linarith
        have hid : ((2/3 : ℝ) - (1/3 : ℝ)) * ((m : ℝ) * ((0 : ℝ) + (-3/40 : ℝ) * (y - (1/3 : ℝ))) + (3/4 : ℝ) * (y - (1/3 : ℝ)))
            = ((2/3 : ℝ) - y) * ((m : ℝ) * (0 : ℝ) + (3/4 : ℝ) * ((1/3 : ℝ) - (1/3 : ℝ))) + (y - (1/3 : ℝ)) * ((m : ℝ) * (-1/40 : ℝ) + (3/4 : ℝ) * ((2/3 : ℝ) - (1/3 : ℝ))) := by ring
        have p1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ (2/3 : ℝ) - y)
        have p2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ y - (1/3 : ℝ))
        have hseg : ((2/3 : ℝ) - (1/3 : ℝ)) * ((m : ℝ) * ((0 : ℝ) + (-3/40 : ℝ) * (y - (1/3 : ℝ))) + (3/4 : ℝ) * (y - (1/3 : ℝ))) ≤ 0 := by
          rw [hid]; linarith
        linarith
    · have hu := hU2 y (le_of_lt h1) hy1
      have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((-1/40 : ℝ) + (-1/40 : ℝ) * (y - (2/3 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
      rcases le_or_gt y (1/3 : ℝ) with hd | hd
      · have hL := hL1 y hy0 hd
        have hub : ((-1/40 : ℝ) + (-1/40 : ℝ) * (y - (2/3 : ℝ))) ≤ 0 := by linarith
        have hmub := mul_le_mul_of_nonneg_left hub hm0
        linarith
      · have hL := hL2 y hd hy1
        have hA : ((m : ℝ) * (-1/40 : ℝ) + (3/4 : ℝ) * ((2/3 : ℝ) - (1/3 : ℝ))) ≤ 0 := by linarith
        have hB : ((m : ℝ) * (-1/30 : ℝ) + (3/4 : ℝ) * ((1 : ℝ) - (1/3 : ℝ))) ≤ 0 := by linarith
        have hid : ((1 : ℝ) - (2/3 : ℝ)) * ((m : ℝ) * ((-1/40 : ℝ) + (-1/40 : ℝ) * (y - (2/3 : ℝ))) + (3/4 : ℝ) * (y - (1/3 : ℝ)))
            = ((1 : ℝ) - y) * ((m : ℝ) * (-1/40 : ℝ) + (3/4 : ℝ) * ((2/3 : ℝ) - (1/3 : ℝ))) + (y - (2/3 : ℝ)) * ((m : ℝ) * (-1/30 : ℝ) + (3/4 : ℝ) * ((1 : ℝ) - (1/3 : ℝ))) := by ring
        have p1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ (1 : ℝ) - y)
        have p2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ y - (2/3 : ℝ))
        have hseg : ((1 : ℝ) - (2/3 : ℝ)) * ((m : ℝ) * ((-1/40 : ℝ) + (-1/40 : ℝ) * (y - (2/3 : ℝ))) + (3/4 : ℝ) * (y - (1/3 : ℝ))) ≤ 0 := by
          rw [hid]; linarith
        linarith

-- pl_tail_log_third_L_nonpos / pl_tail_log_third_L_tangent: L(y) = log(1+y) − log(1+y†) meets hL1 (log
-- monotone) and hL2 (log x ≤ x − 1 at x = (1+y)/(1+y†), then s ≥ 1/(1+y†)).
theorem pl_tail_log_third_L_nonpos : ∀ y : ℝ, 0 < y → y ≤ (1/3 : ℝ) → Real.log (1 + y) - Real.log (1 + (1/3 : ℝ)) ≤ 0 := by
  intro y hy h
  have := Real.log_le_log (by linarith) (by linarith : 1 + y ≤ 1 + (1/3 : ℝ))
  linarith

theorem pl_tail_log_third_L_tangent :
    ∀ y : ℝ, (1/3 : ℝ) < y → y ≤ 1 → Real.log (1 + y) - Real.log (1 + (1/3 : ℝ)) ≤ (3/4 : ℝ) * (y - (1/3 : ℝ)) := by
  intro y hy h
  have hpos : (0 : ℝ) < (1 + y) / (1 + (1/3 : ℝ)) := div_pos (by linarith) (by norm_num)
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 : Real.log ((1 + y) / (1 + (1/3 : ℝ))) = Real.log (1 + y) - Real.log (1 + (1/3 : ℝ)) :=
    Real.log_div (by linarith) (by norm_num)
  have h3 : (1 + y) / (1 + (1/3 : ℝ)) - 1 = (3/4 : ℝ) * (y - (1/3 : ℝ)) := by ring
  linarith

-- pl_tail_log_third_concrete: hypothesis-free instance, U = min(0, segment lines) (below every
-- segment line, so it meets every U hypothesis) and L = log(1+y) − log(1+y†).
theorem pl_tail_log_third_concrete :
    ∀ m : ℕ, 15 ≤ m → ∀ y : ℝ, 0 < y → y ≤ 1 →
      (m : ℝ) * min 0 (min ((0 : ℝ) + (-3/40 : ℝ) * (y - (1/3 : ℝ))) (((-1/40 : ℝ) + (-1/40 : ℝ) * (y - (2/3 : ℝ))))) + (Real.log (1 + y) - Real.log (1 + (1/3 : ℝ))) ≤ 0 :=
  pl_tail_log_third (fun y => min 0 (min ((0 : ℝ) + (-3/40 : ℝ) * (y - (1/3 : ℝ))) (((-1/40 : ℝ) + (-1/40 : ℝ) * (y - (2/3 : ℝ)))))) (fun y => Real.log (1 + y) - Real.log (1 + (1/3 : ℝ)))
    (fun _ _ _ => min_le_left _ _)
    (fun _ _ _ => le_trans (min_le_right _ _) (min_le_left _ _))
    (fun _ _ _ => le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_refl _)))
    pl_tail_log_third_L_nonpos pl_tail_log_third_L_tangent

-- pl_tail_abstract: piecewise-linear node-condition tail.  For all m ≥ 2 and y ∈ (0, 1],
-- m·U(y) + L(y) ≤ 0, with U below the PL function on nodes (1/4, 0), (1/2, -1/20), (3/4, -1/8), (1, -1/5)
-- and L ≤ 0 below y† = 1/2, L ≤ 2/3·(y − y†) above.  Certificate: the node
-- condition (M+1)·|U_i| ≥ s·(y_i − y†) at every node beyond y†; per segment the
-- convex-combination identity (ring).  U, L and their conditions are HYPOTHESES.
theorem pl_tail_abstract (U L : ℝ → ℝ)
    (hU0 : ∀ y : ℝ, 0 < y → y ≤ (1/4 : ℝ) → U y ≤ 0)
    (hU1 : ∀ y : ℝ, (1/4 : ℝ) ≤ y → y ≤ (1/2 : ℝ) → U y ≤ ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))))
    (hU2 : ∀ y : ℝ, (1/2 : ℝ) ≤ y → y ≤ (3/4 : ℝ) → U y ≤ ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))))
    (hU3 : ∀ y : ℝ, (3/4 : ℝ) ≤ y → y ≤ (1 : ℝ) → U y ≤ ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))))
    (hL1 : ∀ y : ℝ, 0 < y → y ≤ (1/2 : ℝ) → L y ≤ 0)
    (hL2 : ∀ y : ℝ, (1/2 : ℝ) < y → y ≤ 1 → L y ≤ (2/3 : ℝ) * (y - (1/2 : ℝ))) :
    ∀ m : ℕ, 2 ≤ m → ∀ y : ℝ, 0 < y → y ≤ 1 → (m : ℝ) * U y + L y ≤ 0 := by
  intro m hm y hy0 hy1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  rcases le_or_gt y (1/4 : ℝ) with h0 | h0
  · have hu := hU0 y hy0 h0
    have hmu := mul_le_mul_of_nonneg_left hu hm0
    rcases le_or_gt y (1/2 : ℝ) with hd | hd
    · have hL := hL1 y hy0 hd
      linarith
    · have hL := hL2 y hd hy1
      linarith
  · rcases le_or_gt y (1/2 : ℝ) with h1 | h1
    · have hu := hU1 y (le_of_lt h0) h1
      have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
      rcases le_or_gt y (1/2 : ℝ) with hd | hd
      · have hL := hL1 y hy0 hd
        have hub : ((0 : ℝ) + (-1/5 : ℝ) * (y - (1/4 : ℝ))) ≤ 0 := by linarith
        have hmub := mul_le_mul_of_nonneg_left hub hm0
        linarith
      · have hL := hL2 y hd hy1
        linarith
    · rcases le_or_gt y (3/4 : ℝ) with h2 | h2
      · have hu := hU2 y (le_of_lt h1) h2
        have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
        rcases le_or_gt y (1/2 : ℝ) with hd | hd
        · have hL := hL1 y hy0 hd
          have hub : ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) ≤ 0 := by linarith
          have hmub := mul_le_mul_of_nonneg_left hub hm0
          linarith
        · have hL := hL2 y hd hy1
          have hA : ((m : ℝ) * (-1/20 : ℝ) + (2/3 : ℝ) * ((1/2 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hB : ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hid : ((3/4 : ℝ) - (1/2 : ℝ)) * ((m : ℝ) * ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ)))
              = ((3/4 : ℝ) - y) * ((m : ℝ) * (-1/20 : ℝ) + (2/3 : ℝ) * ((1/2 : ℝ) - (1/2 : ℝ))) + (y - (1/2 : ℝ)) * ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) := by ring
          have p1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ (3/4 : ℝ) - y)
          have p2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ y - (1/2 : ℝ))
          have hseg : ((3/4 : ℝ) - (1/2 : ℝ)) * ((m : ℝ) * ((-1/20 : ℝ) + (-3/10 : ℝ) * (y - (1/2 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ))) ≤ 0 := by
            rw [hid]; linarith
          linarith
      · have hu := hU3 y (le_of_lt h2) hy1
        have hmu : (m : ℝ) * U y ≤ (m : ℝ) * ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) := mul_le_mul_of_nonneg_left hu hm0
        rcases le_or_gt y (1/2 : ℝ) with hd | hd
        · have hL := hL1 y hy0 hd
          have hub : ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) ≤ 0 := by linarith
          have hmub := mul_le_mul_of_nonneg_left hub hm0
          linarith
        · have hL := hL2 y hd hy1
          have hA : ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hB : ((m : ℝ) * (-1/5 : ℝ) + (2/3 : ℝ) * ((1 : ℝ) - (1/2 : ℝ))) ≤ 0 := by linarith
          have hid : ((1 : ℝ) - (3/4 : ℝ)) * ((m : ℝ) * ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ)))
              = ((1 : ℝ) - y) * ((m : ℝ) * (-1/8 : ℝ) + (2/3 : ℝ) * ((3/4 : ℝ) - (1/2 : ℝ))) + (y - (3/4 : ℝ)) * ((m : ℝ) * (-1/5 : ℝ) + (2/3 : ℝ) * ((1 : ℝ) - (1/2 : ℝ))) := by ring
          have p1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ (1 : ℝ) - y)
          have p2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ y - (3/4 : ℝ))
          have hseg : ((1 : ℝ) - (3/4 : ℝ)) * ((m : ℝ) * ((-1/8 : ℝ) + (-3/10 : ℝ) * (y - (3/4 : ℝ))) + (2/3 : ℝ) * (y - (1/2 : ℝ))) ≤ 0 := by
            rw [hid]; linarith
          linarith

end PLNodeTail
