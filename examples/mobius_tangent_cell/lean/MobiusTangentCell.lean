/- telperion 0.1.6 | family MobiusTangentCell | input-hash 5bca6dbab5f46d8a
   52 theorems, 49 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace MobiusTangentCell

/-! ### Generic lemmas of the mobius_tangent_cell template (emitted once per family).
Tangent-line cells with a Mobius term and a convex majorant checked at the two endpoints.
conjecture1_proved = False. -/

/-- Concavity of `log` as a tangent bound at `u`, with `log u <= H`. -/
theorem pade_log1p_mtc_log_tangent (u y H : ℝ) (hu : 0 < u) (hy : 0 < y) (hH : Real.log u ≤ H) :
    Real.log y ≤ H + (y - u) / u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hu)
  rw [Real.log_div hy.ne' hu.ne'] at h
  have e : (y - u) / u = y / u - 1 := by field_simp
  linarith

/-- For `s <= 0` the Mobius term `s / w` is concave in `w > 0`: tangent majorant at `c`. -/
theorem pade_log1p_mtc_mobius_tangent (s w c d : ℝ) (hs : s ≤ 0) (hw : 0 < w) (hc : 0 < c)
    (hd : d = c ^ 2) : s / w ≤ s / c - s * (w - c) / d := by
  subst hd
  have e : s / c - s * (w - c) / c ^ 2 - s / w = -s * (w - c) ^ 2 / (w * c ^ 2) := by
    field_simp; ring
  have h : 0 ≤ -s * (w - c) ^ 2 / (w * c ^ 2) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (sq_nonneg _)
    · positivity
  linarith

/-- For `s >= 0`, `m + k x + s / (B + A x)` is convex on `[p, q]` (where `B + A x > 0`):
nonpositive at both endpoints implies nonpositive throughout. -/
theorem pade_log1p_mtc_convex_endpoint (m k s A B p q x : ℝ) (hs : 0 ≤ s) (hpx : p ≤ x) (hxq : x ≤ q)
    (hwp : 0 < B + A * p) (hwq : 0 < B + A * q)
    (hP : m + k * p + s / (B + A * p) ≤ 0) (hQ : m + k * q + s / (B + A * q) ≤ 0) :
    m + k * x + s / (B + A * x) ≤ 0 := by
  rcases eq_or_lt_of_le (le_trans hpx hxq) with hpq | hpq
  · have hx : x = p := le_antisymm (hpq ▸ hxq) hpx
    rw [hx]; exact hP
  set wp := B + A * p with hwp_def
  set wq := B + A * q with hwq_def
  set u := q - x with hu_def
  set v := x - p with hv_def
  have hu : 0 ≤ u := by rw [hu_def]; linarith
  have hv : 0 ≤ v := by rw [hv_def]; linarith
  have hD : 0 < u + v := by rw [hu_def, hv_def]; linarith
  have hwx : B + A * x = (u * wp + v * wq) / (u + v) := by
    rw [eq_div_iff hD.ne', hu_def, hv_def, hwp_def, hwq_def]; ring
  have hwxpos : 0 < u * wp + v * wq := by
    rcases eq_or_lt_of_le hu with h0 | h0
    · rw [← h0]; nlinarith
    · nlinarith
  -- convexity of 1/w along the chord, in Cauchy-Schwarz form
  have hcs : (u + v) ^ 2 * (wp * wq) ≤ (u * wq + v * wp) * (u * wp + v * wq) := by
    nlinarith [mul_nonneg (mul_nonneg hu hv) (sq_nonneg (wp - wq))]
  have hinv : s / (B + A * x) ≤ (u * (s / wp) + v * (s / wq)) / (u + v) := by
    rw [hwx, div_div_eq_mul_div, div_le_div_iff₀ hwxpos hD]
    have e : (u * (s / wp) + v * (s / wq)) = s * (u * wq + v * wp) / (wp * wq) := by
      field_simp
    rw [e, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hwp hwq)]
    have := mul_le_mul_of_nonneg_left hcs hs
    nlinarith [this]
  have hsum : u * (m + k * p + s / wp) + v * (m + k * q + s / wq) ≤ 0 := by
    nlinarith [mul_nonneg hu (by linarith : 0 ≤ -(m + k * p + s / wp)),
               mul_nonneg hv (by linarith : 0 ≤ -(m + k * q + s / wq))]
  have hkey : m + k * x + (u * (s / wp) + v * (s / wq)) / (u + v) ≤ 0 := by
    rw [← sub_nonpos]
    have e : m + k * x + (u * (s / wp) + v * (s / wq)) / (u + v) - 0
        = (u * (m + k * p + s / wp) + v * (m + k * q + s / wq)) / (u + v) := by
      field_simp; rw [hu_def, hv_def]; ring
    rw [e]; exact div_nonpos_of_nonpos_of_nonneg hsum hD.le
  linarith

/-- `log 323/256 <= H` (u = 2^0 * 323/256, order-8 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH0 : Real.log (323 / 256) ≤ (116241081994953 / 500000000000000) := by
  have hx : |((-67 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 8
  rw [show (1 : ℝ) - (-67 / 256) = (323 / 256) by norm_num] at h
  generalize Real.log (323 / 256) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 329/256 <= H` (u = 2^0 * 329/256, order-8 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH1 : Real.log (329 / 256) ≤ (250896643061 / 1000000000000) := by
  have hx : |((-73 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 8
  rw [show (1 : ℝ) - (-73 / 256) = (329 / 256) by norm_num] at h
  generalize Real.log (329 / 256) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 335/256 <= H` (u = 2^0 * 335/256, order-8 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH2 : Real.log (335 / 256) ≤ (268987586425887 / 1000000000000000) := by
  have hx : |((-79 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 8
  rw [show (1 : ℝ) - (-79 / 256) = (335 / 256) by norm_num] at h
  generalize Real.log (335 / 256) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 341/256 <= H` (u = 2^0 * 341/256, order-8 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH3 : Real.log (341 / 256) ≤ (143387130721599 / 500000000000000) := by
  have hx : |((-85 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 8
  rw [show (1 : ℝ) - (-85 / 256) = (341 / 256) by norm_num] at h
  generalize Real.log (341 / 256) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 175/128 <= H` (u = 2^1 * 175/256, order-8 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH4 : Real.log (175 / 128) ≤ (39100893806697 / 125000000000000) := by
  have hx : |((81 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 8
  rw [show (1 : ℝ) - (81 / 256) = (175 / 256) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (175 / 256) = Real.log (175 / 128) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (175 / 256) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 181/128 <= H` (u = 2^1 * 181/256, order-7 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH5 : Real.log (181 / 128) ≤ (346552713162591 / 1000000000000000) := by
  have hx : |((75 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 7
  rw [show (1 : ℝ) - (75 / 256) = (181 / 256) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (181 / 256) = Real.log (181 / 128) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (181 / 256) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 187/128 <= H` (u = 2^1 * 187/256, order-6 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH6 : Real.log (187 / 128) ≤ (379239169203203 / 1000000000000000) := by
  have hx : |((69 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 6
  rw [show (1 : ℝ) - (69 / 256) = (187 / 256) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (187 / 256) = Real.log (187 / 128) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (187 / 256) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 193/128 <= H` (u = 2^1 * 193/256, order-5 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH7 : Real.log (193 / 128) ≤ (411001546438591 / 1000000000000000) := by
  have hx : |((63 / 256) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 5
  rw [show (1 : ℝ) - (63 / 256) = (193 / 256) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (193 / 256) = Real.log (193 / 128) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (193 / 256) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 101/64 <= H` (u = 2^1 * 101/128, order-5 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH8 : Real.log (101 / 64) ≤ (57045876368031 / 125000000000000) := by
  have hx : |((27 / 128) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 5
  rw [show (1 : ℝ) - (27 / 128) = (101 / 128) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (101 / 128) = Real.log (101 / 64) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (101 / 128) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 55/32 <= H` (u = 2^1 * 55/64, order-4 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH9 : Real.log (55 / 32) ≤ (4231826095029 / 7812500000000) := by
  have hx : |((9 / 64) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  rw [show (1 : ℝ) - (9 / 64) = (55 / 64) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (55 / 64) = Real.log (55 / 32) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (55 / 64) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 61/32 <= H` (u = 2^1 * 61/64, order-2 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem pade_log1p_logH10 : Real.log (61 / 32) ≤ (645281610231353 / 1000000000000000) := by
  have hx : |((3 / 64) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  rw [show (1 : ℝ) - (3 / 64) = (61 / 64) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (61 / 64) = Real.log (61 / 32) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (61 / 64) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- Cell [1/4, 35/128], tangent point t = 67/256, Mobius mode `convex`: Psi(p) = -2.0047e-05, Psi(q) = -4.7435e-05.
    conjecture1_proved = False. -/
theorem pade_log1p_cell0 (x : ℝ) (hpx : (1 / 4) ≤ x) (hxq : x ≤ (35 / 128)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (323 / 256) ((1) + (1) * x) (116241081994953 / 500000000000000) (by norm_num) hy0 pade_log1p_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-177641630515630181 / 161500000000000000) (701 / 1292) (27) (16) (24) (1 / 4) (35 / 128) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [35/128, 19/64], tangent point t = 73/256, Mobius mode `convex`: Psi(p) = -3.9423e-05, Psi(q) = -7.3131e-05.
    conjecture1_proved = False. -/
theorem pade_log1p_cell1 (x : ℝ) (hpx : (35 / 128) ≤ x) (hxq : x ≤ (19 / 64)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (329 / 256) ((1) + (1) * x) (250896643061 / 1000000000000) (by norm_num) hy0 pade_log1p_logH1
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-360580004432931 / 329000000000000) (695 / 1316) (27) (16) (24) (35 / 128) (19 / 64) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [19/64, 41/128], tangent point t = 79/256, Mobius mode `convex`: Psi(p) = -5.5953e-05, Psi(q) = -9.6688e-05.
    conjecture1_proved = False. -/
theorem pade_log1p_cell2 (x : ℝ) (hpx : (19 / 64) ≤ x) (hxq : x ≤ (41 / 128)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (335 / 256) ((1) + (1) * x) (268987586425887 / 1000000000000000) (by norm_num) hy0 pade_log1p_logH2
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-73152831709465571 / 67000000000000000) (689 / 1340) (27) (16) (24) (19 / 64) (41 / 128) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [41/128, 11/32], tangent point t = 85/256, Mobius mode `convex`: Psi(p) = -6.2891e-05, Psi(q) = -1.1135e-04.
    conjecture1_proved = False. -/
theorem pade_log1p_cell3 (x : ℝ) (hpx : (41 / 128) ≤ x) (hxq : x ≤ (11 / 32)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (341 / 256) ((1) + (1) * x) (143387130721599 / 500000000000000) (by norm_num) hy0 pade_log1p_logH3
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-185417488423934741 / 170500000000000000) (683 / 1364) (27) (16) (24) (41 / 128) (11 / 32) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [11/32, 25/64], tangent point t = 47/128, Mobius mode `convex`: Psi(p) = -1.8969e-05, Psi(q) = -1.4426e-04.
    conjecture1_proved = False. -/
theorem pade_log1p_cell4 (x : ℝ) (hpx : (11 / 32) ≤ x) (hxq : x ≤ (25 / 64)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (175 / 128) ((1) + (1) * x) (39100893806697 / 125000000000000) (by norm_num) hy0 pade_log1p_logH4
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-945668743353121 / 875000000000000) (337 / 700) (27) (16) (24) (11 / 32) (25 / 64) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [25/64, 7/16], tangent point t = 53/128, Mobius mode `convex`: Psi(p) = -1.1614e-04, Psi(q) = -2.7996e-04.
    conjecture1_proved = False. -/
theorem pade_log1p_cell5 (x : ℝ) (hpx : (25 / 64) ≤ x) (hxq : x ≤ (7 / 16)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (181 / 128) ((1) + (1) * x) (346552713162591 / 1000000000000000) (by norm_num) hy0 pade_log1p_logH5
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-193898958917571029 / 181000000000000000) (331 / 724) (27) (16) (24) (25 / 64) (7 / 16) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [7/16, 31/64], tangent point t = 59/128, Mobius mode `convex`: Psi(p) = -2.1087e-04, Psi(q) = -4.1810e-04.
    conjecture1_proved = False. -/
theorem pade_log1p_cell6 (x : ℝ) (hpx : (7 / 16) ≤ x) (hxq : x ≤ (31 / 64)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (187 / 128) ((1) + (1) * x) (379239169203203 / 1000000000000000) (by norm_num) hy0 pade_log1p_logH6
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-198457275359001039 / 187000000000000000) (325 / 748) (27) (16) (24) (7 / 16) (31 / 64) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [31/64, 17/32], tangent point t = 65/128, Mobius mode `convex`: Psi(p) = -2.4254e-04, Psi(q) = -4.9768e-04.
    conjecture1_proved = False. -/
theorem pade_log1p_cell7 (x : ℝ) (hpx : (31 / 64) ≤ x) (hxq : x ≤ (17 / 32)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (193 / 128) ((1) + (1) * x) (411001546438591 / 1000000000000000) (by norm_num) hy0 pade_log1p_logH7
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-202801701537351937 / 193000000000000000) (319 / 772) (27) (16) (24) (31 / 64) (17 / 32) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [17/32, 5/8], tangent point t = 37/64, Mobius mode `convex`: Psi(p) = -3.7923e-04, Psi(q) = -1.0624e-03.
    conjecture1_proved = False. -/
theorem pade_log1p_cell8 (x : ℝ) (hpx : (17 / 32) ≤ x) (hxq : x ≤ (5 / 8)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (101 / 64) ((1) + (1) * x) (57045876368031 / 125000000000000) (by norm_num) hy0 pade_log1p_logH8
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-13066491486828869 / 12625000000000000) (155 / 404) (27) (16) (24) (17 / 32) (5 / 8) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [5/8, 13/16], tangent point t = 23/32, Mobius mode `convex`: Psi(p) = -4.0673e-06, Psi(q) = -2.1761e-03.
    conjecture1_proved = False. -/
theorem pade_log1p_cell9 (x : ℝ) (hpx : (5 / 8) ≤ x) (hxq : x ≤ (13 / 16)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (55 / 32) ((1) + (1) * x) (4231826095029 / 7812500000000) (by norm_num) hy0 pade_log1p_logH9
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-86067100454681 / 85937500000000) (73 / 220) (27) (16) (24) (5 / 8) (13 / 16) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [13/16, 1], tangent point t = 29/32, Mobius mode `convex`: Psi(p) = -2.2940e-03, Psi(q) = -5.5381e-03.
    conjecture1_proved = False. -/
theorem pade_log1p_cell10 (x : ℝ) (hpx : (13 / 16) ≤ x) (hxq : x ≤ (1)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (61 / 32) ((1) + (1) * x) (645281610231353 / 1000000000000000) (by norm_num) hy0 pade_log1p_logH10
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-58262821775887467 / 61000000000000000) (67 / 244) (27) (16) (24) (13 / 16) (1) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- `F <= 0` on the whole interval [1/4, 1], from 11 cell(s) tiling it at shared breakpoints.
    conjecture1_proved = False. -/
theorem pade_log1p (x : ℝ) (hpx : (1 / 4) ≤ x) (hxq : x ≤ (1)) :
    (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) ≤ 0 := by
  rcases le_or_gt x (35 / 128) with h0 | h0
  · exact pade_log1p_cell0 x hpx h0
  rcases le_or_gt x (19 / 64) with h1 | h1
  · exact pade_log1p_cell1 x h0.le h1
  rcases le_or_gt x (41 / 128) with h2 | h2
  · exact pade_log1p_cell2 x h1.le h2
  rcases le_or_gt x (11 / 32) with h3 | h3
  · exact pade_log1p_cell3 x h2.le h3
  rcases le_or_gt x (25 / 64) with h4 | h4
  · exact pade_log1p_cell4 x h3.le h4
  rcases le_or_gt x (7 / 16) with h5 | h5
  · exact pade_log1p_cell5 x h4.le h5
  rcases le_or_gt x (31 / 64) with h6 | h6
  · exact pade_log1p_cell6 x h5.le h6
  rcases le_or_gt x (17 / 32) with h7 | h7
  · exact pade_log1p_cell7 x h6.le h7
  rcases le_or_gt x (5 / 8) with h8 | h8
  · exact pade_log1p_cell8 x h7.le h8
  rcases le_or_gt x (13 / 16) with h9 | h9
  · exact pade_log1p_cell9 x h8.le h9
  exact pade_log1p_cell10 x h9.le hxq

/-- The original two-sided form `lhs <= rhs` on [1/4, 1] (lhs - rhs is identically the template F).
    conjecture1_proved = False. -/
theorem pade_log1p_sides (x : ℝ) (hpx : (1 / 4) ≤ x) (hxq : x ≤ (1)) :
    Real.log (((1) + x)) ≤ ((x * ((6) + x)) / ((6) + ((4) * x))) := by
  have hF := pade_log1p x hpx hxq
  have hd0 : ((24) + ((16) * x)) ≠ 0 := (by linarith : (0 : ℝ) < ((24) + ((16) * x))).ne'
  have hd1 : ((6) + ((4) * x)) ≠ 0 := (by linarith : (0 : ℝ) < ((6) + ((4) * x))).ne'
  have hg0 : Real.log (((1) + x)) = Real.log ((1) + (1) * x) := by congr 1; ring
  have e : Real.log (((1) + x)) - ((x * ((6) + x)) / ((6) + ((4) * x))) = (-9 / 8) + (-1 / 4) * x + (1) * Real.log ((1) + (1) * x) + (27) / ((24) + (16) * x) := by
    rw [hg0]
    field_simp
    ring
  linarith

/-- `log 1/5 <= H` (u = 2^-2 * 4/5, order-2 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_gt_d9).
    conjecture1_proved = False. -/
theorem logmean_lower_logH0 : Real.log (1 / 5) ≤ (-7981471803 / 5000000000) := by
  have hx : |((1 / 5) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  rw [show (1 : ℝ) - (1 / 5) = (4 / 5) by norm_num] at h
  have hs : Real.log (4 / 5) - ((2 : ℕ) : ℝ) * Real.log 2 = Real.log (1 / 5) := by
    rw [← Real.log_pow, ← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_gt_d9
  rw [← hs]
  generalize Real.log (4 / 5) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 9/20 <= H` (u = 2^-1 * 9/10, order-1 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_gt_d9).
    conjecture1_proved = False. -/
theorem logmean_lower_logH1 : Real.log (9 / 20) ≤ (-97754508648611 / 125000000000000) := by
  have hx : |((1 / 10) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  rw [show (1 : ℝ) - (1 / 10) = (9 / 10) by norm_num] at h
  have hs : Real.log (9 / 10) - ((1 : ℕ) : ℝ) * Real.log 2 = Real.log (9 / 20) := by
    rw [← Real.log_pow, ← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_gt_d9
  rw [← hs]
  generalize Real.log (9 / 10) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- Cell [1/10, 3/10], tangent point t = 1/5, Mobius mode `convex`: Psi(p) = -4.5993e-01, Psi(q) = -1.9371e-02.
    conjecture1_proved = False. -/
theorem logmean_lower_cell0 (x : ℝ) (hpx : (1 / 10) ≤ x) (hxq : x ≤ (3 / 10)) :
    (-2) + (0) * x + (1) * Real.log ((0) + (1) * x) + (4) / ((1) + (1) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (0) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (1 / 5) ((0) + (1) * x) (-7981471803 / 5000000000) (by norm_num) hy0 logmean_lower_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-22981471803 / 5000000000) (5) (4) (1) (1) (1 / 10) (3 / 10) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Cell [3/10, 1/2], tangent point t = 9/20, Mobius mode `convex`: Psi(p) = -3.8446e-02, Psi(q) = -4.2583e-03.
    conjecture1_proved = False. -/
theorem logmean_lower_cell1 (x : ℝ) (hpx : (3 / 10) ≤ x) (hxq : x ≤ (1 / 2)) :
    (-2) + (0) * x + (1) * Real.log ((0) + (1) * x) + (4) / ((1) + (1) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (0) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (9 / 20) ((0) + (1) * x) (-97754508648611 / 125000000000000) (by norm_num) hy0 logmean_lower_logH1
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hM := pade_log1p_mtc_convex_endpoint (-472754508648611 / 125000000000000) (20 / 9) (4) (1) (1) (3 / 10) (1 / 2) x
    (by norm_num) hpx hxq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- `F <= 0` on the whole interval [1/10, 1/2], from 2 cell(s) tiling it at shared breakpoints.
    conjecture1_proved = False. -/
theorem logmean_lower (x : ℝ) (hpx : (1 / 10) ≤ x) (hxq : x ≤ (1 / 2)) :
    (-2) + (0) * x + (1) * Real.log ((0) + (1) * x) + (4) / ((1) + (1) * x) ≤ 0 := by
  rcases le_or_gt x (3 / 10) with h0 | h0
  · exact logmean_lower_cell0 x hpx h0
  exact logmean_lower_cell1 x h0.le hxq

/-- The original two-sided form `lhs <= rhs` on [1/10, 1/2] (lhs - rhs is identically the template F).
    conjecture1_proved = False. -/
theorem logmean_lower_sides (x : ℝ) (hpx : (1 / 10) ≤ x) (hxq : x ≤ (1 / 2)) :
    Real.log (x) ≤ (((-2) + ((2) * x)) / ((1) + x)) := by
  have hF := logmean_lower x hpx hxq
  have hd0 : ((1) + x) ≠ 0 := (by linarith : (0 : ℝ) < ((1) + x)).ne'
  have hg0 : Real.log (x) = Real.log ((0) + (1) * x) := by congr 1; ring
  have e : Real.log (x) - (((-2) + ((2) * x)) / ((1) + x)) = (-2) + (0) * x + (1) * Real.log ((0) + (1) * x) + (4) / ((1) + (1) * x) := by
    rw [hg0]
    field_simp
    ring
  linarith

/-- `log 4 <= H` (u = 2^2 * 1, order-3 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem concave_mobius_logH0 : Real.log (4) ≤ (108304247 / 78125000) := by
  have hx : |((0) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 3
  rw [show (1 : ℝ) - (0) = (1) by norm_num] at h
  have hs : ((2 : ℕ) : ℝ) * Real.log 2 + Real.log (1) = Real.log (4) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (1) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 5/4 <= H` (u = 2^0 * 5/4, order-3 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem concave_mobius_logH1 : Real.log (5 / 4) ≤ (229166666666667 / 1000000000000000) := by
  have hx : |((-1 / 4) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 3
  rw [show (1 : ℝ) - (-1 / 4) = (5 / 4) by norm_num] at h
  generalize Real.log (5 / 4) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 33/8 <= H` (u = 2^2 * 33/32, order-4 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem concave_mobius_logH2 : Real.log (33 / 8) ≤ (1417066045221151 / 1000000000000000) := by
  have hx : |((-1 / 32) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  rw [show (1 : ℝ) - (-1 / 32) = (33 / 32) by norm_num] at h
  have hs : ((2 : ℕ) : ℝ) * Real.log 2 + Real.log (33 / 32) = Real.log (33 / 8) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (33 / 32) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 11/8 <= H` (u = 2^1 * 11/16, order-4 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem concave_mobius_logH3 : Real.log (11 / 8) ≤ (32359722722371 / 100000000000000) := by
  have hx : |((5 / 16) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  rw [show (1 : ℝ) - (5 / 16) = (11 / 16) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (11 / 16) = Real.log (11 / 8) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (11 / 16) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 19/4 <= H` (u = 2^2 * 19/16, order-1 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem concave_mobius_logH4 : Real.log (19 / 4) ≤ (1617063592369231 / 1000000000000000) := by
  have hx : |((-3 / 16) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  rw [show (1 : ℝ) - (-3 / 16) = (19 / 16) by norm_num] at h
  have hs : ((2 : ℕ) : ℝ) * Real.log 2 + Real.log (19 / 16) = Real.log (19 / 4) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (19 / 16) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 2 <= H` (u = 2^1 * 1, order-1 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem concave_mobius_logH5 : Real.log (2) ≤ (108304247 / 156250000) := by
  have hx : |((0) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  rw [show (1 : ℝ) - (0) = (1) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (1) = Real.log (2) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (1) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- Cell [0, 1], tangent point t = 1, Mobius mode `tangent`: Psi(p) = -5.7686e-02, Psi(q) = -7.6862e-03.
    conjecture1_proved = False. -/
theorem concave_mobius_cell0 (x : ℝ) (hpx : (0) ≤ x) (hxq : x ≤ (1)) :
    (8 / 25) + (-1) * x + (1 / 2) * Real.log ((3) + (1) * x) + (1) * Real.log ((1 / 4) + (1) * x) + (-1) / ((2) + (2) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (3) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (4) ((3) + (1) * x) (108304247 / 78125000) (by norm_num) hy0 concave_mobius_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 2))
  have hy1 : (0 : ℝ) < (1 / 4) + (1) * x := by linarith
  have hl1 := pade_log1p_mtc_log_tangent (5 / 4) ((1 / 4) + (1) * x) (229166666666667 / 1000000000000000) (by norm_num) hy1 concave_mobius_logH1
  have hk1 := mul_le_mul_of_nonneg_left hl1 (by norm_num : (0 : ℝ) ≤ (1))
  have hw : (0 : ℝ) < (2) + (2) * x := by linarith
  have hM := pade_log1p_mtc_mobius_tangent (-1) ((2) + (2) * x) (4) (16) (by norm_num) hw (by norm_num) (by norm_num)
  linarith

/-- Cell [1, 3/2], tangent point t = 9/8, Mobius mode `tangent`: Psi(p) = -3.0653e-03, Psi(q) = -2.3460e-02.
    conjecture1_proved = False. -/
theorem concave_mobius_cell1 (x : ℝ) (hpx : (1) ≤ x) (hxq : x ≤ (3 / 2)) :
    (8 / 25) + (-1) * x + (1 / 2) * Real.log ((3) + (1) * x) + (1) * Real.log ((1 / 4) + (1) * x) + (-1) / ((2) + (2) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (3) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (33 / 8) ((3) + (1) * x) (1417066045221151 / 1000000000000000) (by norm_num) hy0 concave_mobius_logH2
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 2))
  have hy1 : (0 : ℝ) < (1 / 4) + (1) * x := by linarith
  have hl1 := pade_log1p_mtc_log_tangent (11 / 8) ((1 / 4) + (1) * x) (32359722722371 / 100000000000000) (by norm_num) hy1 concave_mobius_logH3
  have hk1 := mul_le_mul_of_nonneg_left hl1 (by norm_num : (0 : ℝ) ≤ (1))
  have hw : (0 : ℝ) < (2) + (2) * x := by linarith
  have hM := pade_log1p_mtc_mobius_tangent (-1) ((2) + (2) * x) (17 / 4) (289 / 16) (by norm_num) hw (by norm_num) (by norm_num)
  linarith

/-- Cell [3/2, 2], tangent point t = 7/4, Mobius mode `tangent`: Psi(p) = -2.7984e-02, Psi(q) = -1.9229e-01.
    conjecture1_proved = False. -/
theorem concave_mobius_cell2 (x : ℝ) (hpx : (3 / 2) ≤ x) (hxq : x ≤ (2)) :
    (8 / 25) + (-1) * x + (1 / 2) * Real.log ((3) + (1) * x) + (1) * Real.log ((1 / 4) + (1) * x) + (-1) / ((2) + (2) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (3) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (19 / 4) ((3) + (1) * x) (1617063592369231 / 1000000000000000) (by norm_num) hy0 concave_mobius_logH4
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 2))
  have hy1 : (0 : ℝ) < (1 / 4) + (1) * x := by linarith
  have hl1 := pade_log1p_mtc_log_tangent (2) ((1 / 4) + (1) * x) (108304247 / 156250000) (by norm_num) hy1 concave_mobius_logH5
  have hk1 := mul_le_mul_of_nonneg_left hl1 (by norm_num : (0 : ℝ) ≤ (1))
  have hw : (0 : ℝ) < (2) + (2) * x := by linarith
  have hM := pade_log1p_mtc_mobius_tangent (-1) ((2) + (2) * x) (11 / 2) (121 / 4) (by norm_num) hw (by norm_num) (by norm_num)
  linarith

/-- `F <= 0` on the whole interval [0, 2], from 3 cell(s) tiling it at shared breakpoints.
    conjecture1_proved = False. -/
theorem concave_mobius (x : ℝ) (hpx : (0) ≤ x) (hxq : x ≤ (2)) :
    (8 / 25) + (-1) * x + (1 / 2) * Real.log ((3) + (1) * x) + (1) * Real.log ((1 / 4) + (1) * x) + (-1) / ((2) + (2) * x) ≤ 0 := by
  rcases le_or_gt x (1) with h0 | h0
  · exact concave_mobius_cell0 x hpx h0
  rcases le_or_gt x (3 / 2) with h1 | h1
  · exact concave_mobius_cell1 x h0.le h1
  exact concave_mobius_cell2 x h1.le hxq

/-- The original two-sided form `lhs <= rhs` on [0, 2] (lhs - rhs is identically the template F).
    conjecture1_proved = False. -/
theorem concave_mobius_sides (x : ℝ) (hpx : (0) ≤ x) (hxq : x ≤ (2)) :
    ((Real.log (((3) + x)) / (2)) + Real.log (((1 / 4) + x))) ≤ ((-8 / 25) + x + (1 / ((2) + ((2) * x)))) := by
  have hF := concave_mobius x hpx hxq
  have hd0 : (2) ≠ 0 := by norm_num
  have hd1 : ((2) + ((2) * x)) ≠ 0 := (by linarith : (0 : ℝ) < ((2) + ((2) * x))).ne'
  have hg0 : Real.log (((3) + x)) = Real.log ((3) + (1) * x) := by congr 1; ring
  have hg1 : Real.log (((1 / 4) + x)) = Real.log ((1 / 4) + (1) * x) := by congr 1; ring
  have e : ((Real.log (((3) + x)) / (2)) + Real.log (((1 / 4) + x))) - ((-8 / 25) + x + (1 / ((2) + ((2) * x)))) = (8 / 25) + (-1) * x + (1 / 2) * Real.log ((3) + (1) * x) + (1) * Real.log ((1 / 4) + (1) * x) + (-1) / ((2) + (2) * x) := by
    rw [hg0, hg1]
    field_simp
    ring
  linarith

/-- `log 1 <= H` (Real.log_one).
    conjecture1_proved = False. -/
theorem no_mobius_logH0 : Real.log (1) ≤ (0) := by
  norm_num

/-- Cell [-1/2, 1/2], tangent point t = 0, Mobius mode `none`: Psi(p) = -1.5000e-01, Psi(q) = -5.0000e-02.
    conjecture1_proved = False. -/
theorem no_mobius_cell0 (x : ℝ) (hpx : (-1 / 2) ≤ x) (hxq : x ≤ (1 / 2)) :
    (-1 / 10) + (-9 / 10) * x + (1) * Real.log ((1) + (1) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (1) + (1) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (1) ((1) + (1) * x) (0) (by norm_num) hy0 no_mobius_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  linarith

/-- `F <= 0` on the whole interval [-1/2, 1/2], from 1 cell(s) tiling it at shared breakpoints.
    conjecture1_proved = False. -/
theorem no_mobius (x : ℝ) (hpx : (-1 / 2) ≤ x) (hxq : x ≤ (1 / 2)) :
    (-1 / 10) + (-9 / 10) * x + (1) * Real.log ((1) + (1) * x) ≤ 0 := by
  exact no_mobius_cell0 x hpx hxq

/-- The original two-sided form `lhs <= rhs` on [-1/2, 1/2] (lhs - rhs is identically the template F).
    conjecture1_proved = False. -/
theorem no_mobius_sides (x : ℝ) (hpx : (-1 / 2) ≤ x) (hxq : x ≤ (1 / 2)) :
    Real.log (((1) + x)) ≤ ((1 / 10) + (((9) * x) / (10))) := by
  have hF := no_mobius x hpx hxq
  have hd0 : (10) ≠ 0 := by norm_num
  have hg0 : Real.log (((1) + x)) = Real.log ((1) + (1) * x) := by congr 1; ring
  have e : Real.log (((1) + x)) - ((1 / 10) + (((9) * x) / (10))) = (-1 / 10) + (-9 / 10) * x + (1) * Real.log ((1) + (1) * x) := by
    rw [hg0]
    field_simp
    ring
  linarith

/-- `log 351/160 <= H` (u = 2^1 * 351/320, order-2 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem zhu_band0_logH0 : Real.log (351 / 160) ≤ (39316823417433 / 50000000000000) := by
  have hx : |((-31 / 320) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  rw [show (1 : ℝ) - (-31 / 320) = (351 / 320) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (351 / 320) = Real.log (351 / 160) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (351 / 320) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- Cell [15/4, 23/5], tangent point t = 351/80, Mobius mode `tangent`: Psi(p) = -2.4150e-01, Psi(q) = -3.6118e-03.
    conjecture1_proved = False. -/
theorem zhu_band0_cell0 (x : ℝ) (hpx : (15 / 4) ≤ x) (hxq : x ≤ (23 / 5)) :
    (-1243 / 2000) + (0) * x + (1) * Real.log ((0) + (1 / 2) * x) + (-1) / ((0) + (1) * x) ≤ 0 := by
  have hy0 : (0 : ℝ) < (0) + (1 / 2) * x := by linarith
  have hl0 := pade_log1p_mtc_log_tangent (351 / 160) ((0) + (1 / 2) * x) (39316823417433 / 50000000000000) (by norm_num) hy0 zhu_band0_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1))
  have hw : (0 : ℝ) < (0) + (1) * x := by linarith
  have hM := pade_log1p_mtc_mobius_tangent (-1) ((0) + (1) * x) (351 / 80) (123201 / 6400) (by norm_num) hw (by norm_num) (by norm_num)
  linarith

/-- `F <= 0` on the whole interval [15/4, 23/5], from 1 cell(s) tiling it at shared breakpoints.
    conjecture1_proved = False. -/
theorem zhu_band0 (x : ℝ) (hpx : (15 / 4) ≤ x) (hxq : x ≤ (23 / 5)) :
    (-1243 / 2000) + (0) * x + (1) * Real.log ((0) + (1 / 2) * x) + (-1) / ((0) + (1) * x) ≤ 0 := by
  exact zhu_band0_cell0 x hpx hxq

/-- The original two-sided form `lhs <= rhs` on [15/4, 23/5] (lhs - rhs is identically the template F).
    conjecture1_proved = False. -/
theorem zhu_band0_sides (x : ℝ) (hpx : (15 / 4) ≤ x) (hxq : x ≤ (23 / 5)) :
    (((-1) / x) + Real.log ((x / (2)))) ≤ (1243 / 2000) := by
  have hF := zhu_band0 x hpx hxq
  have hd0 : (2) ≠ 0 := by norm_num
  have hd1 : x ≠ 0 := (by linarith : (0 : ℝ) < x).ne'
  have hg0 : Real.log ((x / (2))) = Real.log ((0) + (1 / 2) * x) := by congr 1; ring
  have e : (((-1) / x) + Real.log ((x / (2)))) - (1243 / 2000) = (-1243 / 2000) + (0) * x + (1) * Real.log ((0) + (1 / 2) * x) + (-1) / ((0) + (1) * x) := by
    rw [hg0]
    field_simp
    ring
  linarith

end MobiusTangentCell
