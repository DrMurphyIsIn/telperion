/- telperion 0.1.6 | family LogCombination | input-hash 62990fe54570e27d
   5 theorems, 5 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace LogCombination

noncomputable def FSTAR : ℝ := Real.log (621 / 64) / 11

-- ===== F*-folding, MONOTONE route: 1·log(7/4) ≤ 4·FSTAR (FSTAR = log(621/64)/11) =====
-- Fold: 11·(1·log 7/4) = log(7/4^11) ≤ log(621/64^4) = 4·log(621/64).
-- Reduces to the rational power fact (7/4)^11 ≤ (621/64)^4 (norm_num);
-- log-monotonicity (Real.log_le_log) carries it, TIGHT AT THE TIE.
-- DOGFOOD: regenerates BG R3Cert.BGSCL.log74_le_4fstar.
theorem log74_le_4fstar : Real.log (7/4 : ℝ) ≤ (4 * FSTAR : ℝ) := by
  rw [FSTAR]
  have key : 11 * Real.log (7/4 : ℝ) ≤ 4 * Real.log (621/64 : ℝ) := by
    have e1 : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) = 11 * Real.log (7/4 : ℝ) := by
      rw [Real.log_pow]; norm_num
    have e2 : Real.log ((621/64 : ℝ) ^ (4 : ℕ)) = 4 * Real.log (621/64 : ℝ) := by
      rw [Real.log_pow]; norm_num
    have hle : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) ≤ Real.log ((621/64 : ℝ) ^ (4 : ℕ)) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [e1, e2] at hle; linarith
  linarith

-- ===== F*-folding, TANGENT route: 1·log(5/4) − 1·FSTAR ≤ 1/20 (FSTAR = log(621/64)/11) =====
-- Fold: 11·(1·log 5/4 − 1·FSTAR) = log((5/4)^11·(621/64)⁻¹)
-- ≤ (5/4)^11·(621/64)⁻¹ − 1  (Real.log_le_sub_one_of_pos), and the fold − 1
-- ≤ 11/20 is a rational norm_num fact.  TIGHT AT THE TIE (no F* lower bound).
-- DOGFOOD: regenerates BG R3Cert.BGSCL.log54_sub_fstar_le.
theorem log54_sub_fstar_le : Real.log (5/4 : ℝ) - (FSTAR : ℝ) ≤ (1/20 : ℝ) := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (5/4 : ℝ) ^ (11 : ℕ) * (64/621) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((5/4 : ℝ) ^ (11 : ℕ) * (64/621))
      = 11 * Real.log (5/4 : ℝ) - Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621 : ℝ) = (621/64 : ℝ)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (5/4 : ℝ) ^ (11 : ℕ) * (64/621) - 1 ≤ 11/20 := by norm_num
  linarith

-- ===== F*-folding, MONOTONE route (generic, N=1): 2·log(3/2) ≤ 1·log(9/4) =====
-- Fold: 2·log 3/2 = log(3/2^2) ≤ log(9/4^1) = 1·log(9/4).
-- Reduces to the rational power fact (3/2)^2 ≤ (9/4)^1 (norm_num).
-- Reuse of the SAME fold beyond BG (no prelude FSTAR symbol).
theorem log32_sq_le_log94 : (2 : ℝ) * Real.log (3/2 : ℝ) ≤ Real.log (9/4 : ℝ) := by
  have e1 : Real.log ((3/2 : ℝ) ^ (2 : ℕ)) = 2 * Real.log (3/2 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have e2 : Real.log ((9/4 : ℝ) ^ (1 : ℕ)) = 1 * Real.log (9/4 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have hle : Real.log ((3/2 : ℝ) ^ (2 : ℕ)) ≤ Real.log ((9/4 : ℝ) ^ (1 : ℕ)) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [e1, e2] at hle; linarith

-- ===== F*-folding, TANGENT route: 1·log(5/4) − 1·FSTAR ≤ 1/40 (FSTAR = log(621/64)/11) =====
-- Fold: 11·(1·log 5/4 − 1·FSTAR) = log((5/4)^11·(621/64)⁻¹)
-- ≤ (5/4)^11·(621/64)⁻¹ − 1  (Real.log_le_sub_one_of_pos), and the fold − 1
-- ≤ 11/40 is a rational norm_num fact.  TIGHT AT THE TIE (no F* lower bound).
-- DOGFOOD: regenerates BG R3Cert.BGSCL.log54_sub_fstar_le.
theorem log54_sub_fstar_le_40 : Real.log (5/4 : ℝ) - (FSTAR : ℝ) ≤ (1/40 : ℝ) := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (5/4 : ℝ) ^ (11 : ℕ) * (64/621) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((5/4 : ℝ) ^ (11 : ℕ) * (64/621))
      = 11 * Real.log (5/4 : ℝ) - Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64/621 : ℝ) = (621/64 : ℝ)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (5/4 : ℝ) ^ (11 : ℕ) * (64/621) - 1 ≤ 11/40 := by norm_num
  linarith

-- ===== F*-folding, TANGENT route (general k=4): 1·log(7/4) − 4·FSTAR ≤ -1/2688 (FSTAR = log(621/64)/11) =====
-- Fold: 11·(1·log 7/4 − 4·FSTAR) = log((7/4)^11·((621/64)^4)⁻¹)
-- ≤ (7/4)^11·((621/64)^4)⁻¹ − 1  (Real.log_le_sub_one_of_pos); the fold − 1
-- ≤ -11/2688 is a rational norm_num fact.  TIGHT AT THE TIE (no F* lower bound).
theorem log74_le_4fstar_broom : Real.log (7/4 : ℝ) - (4 * FSTAR : ℝ) ≤ (-1/2688 : ℝ) := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (7/4 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (4 : ℕ))⁻¹) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((7/4 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (4 : ℕ))⁻¹))
      = 11 * Real.log (7/4 : ℝ) - 4 * Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_inv, Real.log_pow]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (7/4 : ℝ) ^ (11 : ℕ) * (((621/64 : ℝ) ^ (4 : ℕ))⁻¹) - 1 ≤ -11/2688 := by norm_num
  linarith

end LogCombination
