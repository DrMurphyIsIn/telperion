/- telperion 0.1.6 | family LogCombination | input-hash 99a479c3c1abeae3
   10 theorems, 10 generation-time self-checks passed.
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

-- ===== F*-folding, TIGHT route (k=-1): 1·log(7/9) − -1·FSTAR ≤ -1/24 (FSTAR = log(621/64)/11) =====
-- Fold X = (7/9)^11·(621/64)^(−-1) (≈ 0.6114); goal ⟺ log X ≤ Q = -11/24.
-- Degree-1 tangent (log x ≤ x−1) is TOO LOOSE here (X−1 > Q); use the TIGHT
-- route: log X ≤ Q ⟺ X ≤ exp Q (Real.log_le_iff_le_exp), exp Q = (exp(−Q))⁻¹
-- (Real.exp_neg), exp(−Q) ≤ U via degree-3 Taylor (Real.exp_bound'), X·U ≤ 1.
theorem log79_add_fstar : Real.log (7/9 : ℝ) - (-1 * FSTAR : ℝ) ≤ (-1/24 : ℝ) := by
  rw [FSTAR]
  have hXpos : (0 : ℝ) < (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) := by positivity
  have hsplit : Real.log ((7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)))
      = 11 * Real.log (7/9 : ℝ) + 1 * Real.log (621/64 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_pow]
    push_cast; ring
  have hexp := Real.exp_bound' (x := (11/24 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  have hU : (∑ m ∈ Finset.range 3, (11/24 : ℝ) ^ m / m.factorial)
      + (11/24 : ℝ) ^ 3 * (3 + 1) / ((3 : ℕ).factorial * 3) ≤ (98585/62208 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexpU : Real.exp (11/24 : ℝ) ≤ (98585/62208 : ℝ) := le_trans hexp hU
  have hexppos : (0 : ℝ) < Real.exp (11/24 : ℝ) := Real.exp_pos _
  have hprod : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * Real.exp (11/24 : ℝ) ≤ 1 := by
    have hmono : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * Real.exp (11/24 : ℝ)
        ≤ (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * (98585/62208 : ℝ) :=
      mul_le_mul_of_nonneg_left hexpU (le_of_lt hXpos)
    have hXU : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) * (98585/62208 : ℝ) ≤ 1 := by norm_num
    linarith
  have hXle : (7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ)) ≤ Real.exp (-(11/24) : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div (Real.exp (11/24) : ℝ), le_div_iff₀ hexppos]
    linarith [hprod]
  have hlogle : Real.log ((7/9 : ℝ) ^ (11 : ℕ) * ((621/64 : ℝ) ^ (1 : ℕ))) ≤ (-11/24 : ℝ) := by
    rw [Real.log_le_iff_le_exp hXpos]
    have hEq : (-(11/24) : ℝ) = (-11/24 : ℝ) := by norm_num
    rw [hEq] at hXle; exact hXle
  rw [hsplit] at hlogle
  linarith

-- ===== log_combination EXACT CANCELLATION: (1 : ℝ) * Real.log (12 : ℝ) + (-2 : ℝ) * Real.log (2 : ℝ) + (-1 : ℝ) * Real.log (3 : ℝ) = 0 =====
-- Scale D = 1: ∏ rᵢ^(D·cᵢ) = 1 is the rational identity below (norm_num);
-- no enclosure, so the certificate holds at ZERO margin.
theorem log12_eq_2log2_add_log3 :
    (1 : ℝ) * Real.log (12 : ℝ) + (-2 : ℝ) * Real.log (2 : ℝ) + (-1 : ℝ) * Real.log (3 : ℝ) = 0 := by
  have ep_f0 : Real.log ((12 : ℝ) ^ (1 : ℕ)) = (1 : ℝ) * Real.log (12 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have en_f0 : Real.log ((2 : ℝ) ^ (2 : ℕ)) = (2 : ℝ) * Real.log (2 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have en_f1 : Real.log ((3 : ℝ) ^ (1 : ℕ)) = (1 : ℝ) * Real.log (3 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have en_m1 : Real.log ((2 : ℝ) ^ (2 : ℕ) * (3 : ℝ) ^ (1 : ℕ))
      = Real.log ((2 : ℝ) ^ (2 : ℕ)) + Real.log ((3 : ℝ) ^ (1 : ℕ)) :=
    Real.log_mul (by positivity) (by positivity)
  have e_num : ((12 : ℝ) ^ (1 : ℕ)) = ((2 : ℝ) ^ (2 : ℕ) * (3 : ℝ) ^ (1 : ℕ)) := by norm_num
  have e_log : Real.log ((12 : ℝ) ^ (1 : ℕ)) = Real.log ((2 : ℝ) ^ (2 : ℕ) * (3 : ℝ) ^ (1 : ℕ)) := by rw [e_num]
  linarith

-- ===== log_combination EXACT CANCELLATION: (1/2 : ℝ) * Real.log (9/4 : ℝ) + (1/3 : ℝ) * Real.log (8/27 : ℝ) = 0 =====
-- Scale D = 6: ∏ rᵢ^(D·cᵢ) = 1 is the rational identity below (norm_num);
-- no enclosure, so the certificate holds at ZERO margin.
theorem half_log94_add_third_log827_eq_zero :
    (1/2 : ℝ) * Real.log (9/4 : ℝ) + (1/3 : ℝ) * Real.log (8/27 : ℝ) = 0 := by
  have ep_f0 : Real.log ((9/4 : ℝ) ^ (3 : ℕ)) = (3 : ℝ) * Real.log (9/4 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have ep_f1 : Real.log ((8/27 : ℝ) ^ (2 : ℕ)) = (2 : ℝ) * Real.log (8/27 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have ep_m1 : Real.log ((9/4 : ℝ) ^ (3 : ℕ) * (8/27 : ℝ) ^ (2 : ℕ))
      = Real.log ((9/4 : ℝ) ^ (3 : ℕ)) + Real.log ((8/27 : ℝ) ^ (2 : ℕ)) :=
    Real.log_mul (by positivity) (by positivity)
  have en_one : Real.log (1 : ℝ) = 0 := Real.log_one
  have e_num : ((9/4 : ℝ) ^ (3 : ℕ) * (8/27 : ℝ) ^ (2 : ℕ)) = ((1 : ℝ)) := by norm_num
  have e_log : Real.log ((9/4 : ℝ) ^ (3 : ℕ) * (8/27 : ℝ) ^ (2 : ℕ)) = Real.log ((1 : ℝ)) := by rw [e_num]
  linarith

-- ===== log_combination MIXED (exact + bounded): lo = 0, hi = 1/100 =====
-- Exact group cancels to 0 (rational identity, zero margin); the remainder folds to
-- log(101/100)/1 and is enclosed by 1 − 1/X ≤ log X ≤ X − 1.
theorem log12_cancel_add_log101_mixed :
    (0 : ℝ) ≤ (1 : ℝ) * Real.log (12 : ℝ) + (-2 : ℝ) * Real.log (2 : ℝ) + (-1 : ℝ) * Real.log (3 : ℝ) + (1 : ℝ) * Real.log (101/100 : ℝ) ∧
    (1 : ℝ) * Real.log (12 : ℝ) + (-2 : ℝ) * Real.log (2 : ℝ) + (-1 : ℝ) * Real.log (3 : ℝ) + (1 : ℝ) * Real.log (101/100 : ℝ) ≤ (1/100 : ℝ) := by
  have ep_f0 : Real.log ((12 : ℝ) ^ (1 : ℕ)) = (1 : ℝ) * Real.log (12 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have en_f0 : Real.log ((2 : ℝ) ^ (2 : ℕ)) = (2 : ℝ) * Real.log (2 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have en_f1 : Real.log ((3 : ℝ) ^ (1 : ℕ)) = (1 : ℝ) * Real.log (3 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have en_m1 : Real.log ((2 : ℝ) ^ (2 : ℕ) * (3 : ℝ) ^ (1 : ℕ))
      = Real.log ((2 : ℝ) ^ (2 : ℕ)) + Real.log ((3 : ℝ) ^ (1 : ℕ)) :=
    Real.log_mul (by positivity) (by positivity)
  have e_num : ((12 : ℝ) ^ (1 : ℕ)) = ((2 : ℝ) ^ (2 : ℕ) * (3 : ℝ) ^ (1 : ℕ)) := by norm_num
  have e_log : Real.log ((12 : ℝ) ^ (1 : ℕ)) = Real.log ((2 : ℝ) ^ (2 : ℕ) * (3 : ℝ) ^ (1 : ℕ)) := by rw [e_num]
  have rp_f0 : Real.log ((101/100 : ℝ) ^ (1 : ℕ)) = (1 : ℝ) * Real.log (101/100 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have rn_one : Real.log (1 : ℝ) = 0 := Real.log_one
  have r_div : Real.log (((101/100 : ℝ) ^ (1 : ℕ)) / ((1 : ℝ)))
      = Real.log ((101/100 : ℝ) ^ (1 : ℕ)) - Real.log ((1 : ℝ)) :=
    Real.log_div (by positivity) (by positivity)
  have r_fold : (((101/100 : ℝ) ^ (1 : ℕ)) / ((1 : ℝ))) = (101/100 : ℝ) := by norm_num
  rw [r_fold] at r_div
  have r_up := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 101/100)
  have r_lo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 101/100)
  have r_inv : (1 : ℝ) - (101/100 : ℝ)⁻¹ = 1/101 := by norm_num
  constructor <;> linarith

-- ===== log_combination MIXED (exact + bounded): lo = 1/20, hi = 1/10 =====
-- Exact group cancels to 0 (rational identity, zero margin); the remainder folds to
-- log(5/4)/3 and is enclosed by 1 − 1/X ≤ log X ≤ X − 1 plus the R hypotheses.
theorem log94_cancel_add_log54_R_mixed (R : ℝ) (hR_lo : (-1/100 : ℝ) ≤ R) (hR_hi : R ≤ (1/100 : ℝ)) :
    (1/20 : ℝ) ≤ (1/2 : ℝ) * Real.log (9/4 : ℝ) + (-1 : ℝ) * Real.log (3/2 : ℝ) + (1/3 : ℝ) * Real.log (5/4 : ℝ) + R ∧
    (1/2 : ℝ) * Real.log (9/4 : ℝ) + (-1 : ℝ) * Real.log (3/2 : ℝ) + (1/3 : ℝ) * Real.log (5/4 : ℝ) + R ≤ (1/10 : ℝ) := by
  have ep_f0 : Real.log ((9/4 : ℝ) ^ (1 : ℕ)) = (1 : ℝ) * Real.log (9/4 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have en_f0 : Real.log ((3/2 : ℝ) ^ (2 : ℕ)) = (2 : ℝ) * Real.log (3/2 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have e_num : ((9/4 : ℝ) ^ (1 : ℕ)) = ((3/2 : ℝ) ^ (2 : ℕ)) := by norm_num
  have e_log : Real.log ((9/4 : ℝ) ^ (1 : ℕ)) = Real.log ((3/2 : ℝ) ^ (2 : ℕ)) := by rw [e_num]
  have rp_f0 : Real.log ((5/4 : ℝ) ^ (1 : ℕ)) = (1 : ℝ) * Real.log (5/4 : ℝ) := by
    rw [Real.log_pow]; norm_num
  have rn_one : Real.log (1 : ℝ) = 0 := Real.log_one
  have r_div : Real.log (((5/4 : ℝ) ^ (1 : ℕ)) / ((1 : ℝ)))
      = Real.log ((5/4 : ℝ) ^ (1 : ℕ)) - Real.log ((1 : ℝ)) :=
    Real.log_div (by positivity) (by positivity)
  have r_fold : (((5/4 : ℝ) ^ (1 : ℕ)) / ((1 : ℝ))) = (5/4 : ℝ) := by norm_num
  rw [r_fold] at r_div
  have r_up := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5/4)
  have r_lo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5/4)
  have r_inv : (1 : ℝ) - (5/4 : ℝ)⁻¹ = 1/5 := by norm_num
  constructor <;> linarith

end LogCombination
