/- telperion 0.1.6 | family BohrMollerupGammaRatio | input-hash 7630afe89718e1cb
   36 theorems, 18 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import BohrMollerupPrelude

namespace BohrMollerupGammaRatio

/-! ### `gamma_3_8_over_7_8`: `(2.174 : ℝ) ≤ Γ(3/8) / Γ(7/8) ≤ (2.177 : ℝ)` at `n = 400` (`2` blocks of `200`), brackets at scale `1000000000000` -/

/-- `∏_{k<400} (8 k + 7)`, in `2` blocks of `200`. Only the kernel evaluates it. -/
def gamma_3_8_over_7_8_gA : ℕ :=
  ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (8 * (200 * c + j) + 7)

/-- `∏_{k<400} (8 k + 3)`, in `2` blocks of `200`. -/
def gamma_3_8_over_7_8_gB : ℕ :=
  ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (8 * (200 * c + j) + 3)

lemma gamma_3_8_over_7_8_gA_eq : (∏ k ∈ Finset.range 400, (8 * k + 7)) = gamma_3_8_over_7_8_gA := by
  rw [show (400 : ℕ) = 2 * 200 from rfl, BohrMollerupPrelude.prod_range_chunk]
  rfl

lemma gamma_3_8_over_7_8_gB_eq : (∏ k ∈ Finset.range 400, (8 * k + 3)) = gamma_3_8_over_7_8_gB := by
  rw [show (400 : ℕ) = 2 * 200 from rfl, BohrMollerupPrelude.prod_range_chunk]
  rfl

lemma gamma_3_8_over_7_8_P_eq : (∏ k ∈ Finset.range 400, ((7 : ℝ) / 8 + k) / ((3 : ℝ) / 8 + k)) = (gamma_3_8_over_7_8_gA : ℝ) / gamma_3_8_over_7_8_gB := by
  rw [← gamma_3_8_over_7_8_gA_eq, ← gamma_3_8_over_7_8_gB_eq, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : (3 : ℝ) / 8 + k ≠ 0 := by positivity
  have h1' : (8 : ℝ) * k + 3 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma gamma_3_8_over_7_8_gB_pos : 0 < gamma_3_8_over_7_8_gB := by
  unfold gamma_3_8_over_7_8_gB
  exact Finset.prod_pos fun c _ => Finset.prod_pos fun j _ => by omega

/-- `LOn u2 gB ≤ LOd n l1 gA`: the lower claim against the certified lower bound. -/
lemma gamma_3_8_over_7_8_key_lo : 1087 * 189148321800636 * gamma_3_8_over_7_8_gB ≤ 500 * 400 * 23629697132 * gamma_3_8_over_7_8_gA := by
  decide +kernel

/-- `HId u3 gA ≤ HIn n l4 gB`: the upper claim against the certified upper bound. -/
lemma gamma_3_8_over_7_8_key_hi : 1000 * 9457416090032 * gamma_3_8_over_7_8_gA ≤ 2177 * 400 * 472741662745 * gamma_3_8_over_7_8_gB := by
  decide +kernel

lemma gamma_3_8_over_7_8_hA : (23629697132 : ℝ) / 1000000000000 ≤ ((400 : ℝ) + 3 / 8) ^ ((3 : ℝ) / 8 - 1) := by
  have := BohrMollerupPrelude.rpow_rat_neg_div_lower 3203 8 5 8 23629697132 1000000000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_3_8_over_7_8_hB : (400 : ℝ) ^ ((7 : ℝ) / 8) ≤ (189148321800636 : ℝ) / 1000000000000 := by
  have := BohrMollerupPrelude.rpow_div_upper 400 7 8 189148321800636 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_3_8_over_7_8_hC : (400 : ℝ) ^ ((3 : ℝ) / 8) ≤ (9457416090032 : ℝ) / 1000000000000 := by
  have := BohrMollerupPrelude.rpow_div_upper 400 3 8 9457416090032 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_3_8_over_7_8_hD : (472741662745 : ℝ) / 1000000000000 ≤ ((400 : ℝ) + 7 / 8) ^ ((7 : ℝ) / 8 - 1) := by
  have := BohrMollerupPrelude.rpow_rat_neg_div_lower 3207 8 1 8 472741662745 1000000000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

/-- The real-number argument for abstract `gA gB : ℕ`, so that no tactic tries to
evaluate the products. -/
theorem gamma_3_8_over_7_8_aux (gA gB : ℕ) (gB_pos : 0 < gB)
    (P_eq : (∏ k ∈ Finset.range 400, ((7 : ℝ) / 8 + k) / ((3 : ℝ) / 8 + k)) = (gA : ℝ) / gB)
    (key_lo : 1087 * 189148321800636 * gB ≤ 500 * 400 * 23629697132 * gA)
    (key_hi : 1000 * 9457416090032 * gA ≤ 2177 * 400 * 472741662745 * gB) :
    (2.174 : ℝ) ≤ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ∧ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ≤ (2.177 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := BohrMollerupPrelude.Gamma_ratio_bounds 400 (by norm_num)
    (x₁ := 3 / 8) (x₂ := 7 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [P_eq] at hlo hhi
  clear P_eq
  push_cast at hlo hhi
  have hgA : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
  have hgB : (0 : ℝ) < gB := Nat.cast_pos.mpr gB_pos
  have hY : (0 : ℝ) < (400 : ℝ) ^ ((7 : ℝ) / 8) := by positivity
  have hD' : (0 : ℝ) < ((400 : ℝ) + 7 / 8) ^ ((7 : ℝ) / 8 - 1) := by positivity
  have hkey1 : (1087 : ℝ) * 189148321800636 * gB ≤ 500 * 400 * 23629697132 * gA := by
    exact_mod_cast key_lo
  have hkey2 : (1000 : ℝ) * 9457416090032 * gA ≤ 2177 * 400 * 472741662745 * gB := by
    exact_mod_cast key_hi
  clear key_lo key_hi gB_pos
  constructor
  · calc (2.174 : ℝ)
        ≤ (400 : ℝ) * ((23629697132 : ℝ) / 1000000000000) / ((189148321800636 : ℝ) / 1000000000000) * ((gA : ℝ) / gB) := by
          rw [show (400 : ℝ) * ((23629697132 : ℝ) / 1000000000000) / ((189148321800636 : ℝ) / 1000000000000) * ((gA : ℝ) / gB)
              = (400 * 23629697132 * gA) / (189148321800636 * gB) by field_simp]
          rw [le_div_iff₀ (by positivity)]
          linarith
      _ ≤ (400 : ℝ) * ((400 : ℝ) + 3 / 8) ^ ((3 : ℝ) / 8 - 1) / (400 : ℝ) ^ ((7 : ℝ) / 8) * ((gA : ℝ) / gB) := by
          gcongr
          · exact gamma_3_8_over_7_8_hA
          · exact gamma_3_8_over_7_8_hB
      _ ≤ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) := hlo
  · calc Real.Gamma (3 / 8) / Real.Gamma (7 / 8)
        ≤ (400 : ℝ) ^ ((3 : ℝ) / 8) / ((400 : ℝ) * ((400 : ℝ) + 7 / 8) ^ ((7 : ℝ) / 8 - 1)) * ((gA : ℝ) / gB) := hhi
      _ ≤ ((9457416090032 : ℝ) / 1000000000000) / ((400 : ℝ) * ((472741662745 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB) := by
          gcongr
          · exact gamma_3_8_over_7_8_hC
          · exact gamma_3_8_over_7_8_hD
      _ ≤ (2.177 : ℝ) := by
          rw [show ((9457416090032 : ℝ) / 1000000000000) / ((400 : ℝ) * ((472741662745 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB)
              = (9457416090032 * gA) / (400 * 472741662745 * gB) by field_simp]
          rw [div_le_iff₀ (by positivity)]
          linarith

/-- `(2.174 : ℝ) ≤ Γ(3/8) / Γ(7/8) ≤ (2.177 : ℝ)`, about Mathlib's `Real.Gamma`. -/
theorem gamma_3_8_over_7_8 :
    (2.174 : ℝ) ≤ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ∧ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ≤ (2.177 : ℝ) :=
  gamma_3_8_over_7_8_aux gamma_3_8_over_7_8_gA gamma_3_8_over_7_8_gB gamma_3_8_over_7_8_gB_pos gamma_3_8_over_7_8_P_eq gamma_3_8_over_7_8_key_lo gamma_3_8_over_7_8_key_hi

example : (2.174 : ℝ) ≤ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ∧ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ≤ (2.177 : ℝ) := gamma_3_8_over_7_8

/-! ### `gamma_1_3_over_2_3`: `(1.977 : ℝ) ≤ Γ(1/3) / Γ(2/3) ≤ (1.98 : ℝ)` at `n = 400` (`2` blocks of `200`), brackets at scale `1000000000000` -/

/-- `∏_{k<400} (3 k + 2)`, in `2` blocks of `200`. Only the kernel evaluates it. -/
def gamma_1_3_over_2_3_gA : ℕ :=
  ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (3 * (200 * c + j) + 2)

/-- `∏_{k<400} (3 k + 1)`, in `2` blocks of `200`. -/
def gamma_1_3_over_2_3_gB : ℕ :=
  ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (3 * (200 * c + j) + 1)

lemma gamma_1_3_over_2_3_gA_eq : (∏ k ∈ Finset.range 400, (3 * k + 2)) = gamma_1_3_over_2_3_gA := by
  rw [show (400 : ℕ) = 2 * 200 from rfl, BohrMollerupPrelude.prod_range_chunk]
  rfl

lemma gamma_1_3_over_2_3_gB_eq : (∏ k ∈ Finset.range 400, (3 * k + 1)) = gamma_1_3_over_2_3_gB := by
  rw [show (400 : ℕ) = 2 * 200 from rfl, BohrMollerupPrelude.prod_range_chunk]
  rfl

lemma gamma_1_3_over_2_3_P_eq : (∏ k ∈ Finset.range 400, ((2 : ℝ) / 3 + k) / ((1 : ℝ) / 3 + k)) = (gamma_1_3_over_2_3_gA : ℝ) / gamma_1_3_over_2_3_gB := by
  rw [← gamma_1_3_over_2_3_gA_eq, ← gamma_1_3_over_2_3_gB_eq, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : (1 : ℝ) / 3 + k ≠ 0 := by positivity
  have h1' : (3 : ℝ) * k + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma gamma_1_3_over_2_3_gB_pos : 0 < gamma_1_3_over_2_3_gB := by
  unfold gamma_1_3_over_2_3_gB
  exact Finset.prod_pos fun c _ => Finset.prod_pos fun j _ => by omega

/-- `LOn u2 gB ≤ LOd n l1 gA`: the lower claim against the certified lower bound. -/
lemma gamma_1_3_over_2_3_key_lo : 1977 * 54288352331899 * gamma_1_3_over_2_3_gB ≤ 1000 * 400 * 18409931173 * gamma_1_3_over_2_3_gA := by
  decide +kernel

/-- `HId u3 gA ≤ HIn n l4 gB`: the upper claim against the certified upper bound. -/
lemma gamma_1_3_over_2_3_key_hi : 50 * 7368062997281 * gamma_1_3_over_2_3_gA ≤ 99 * 400 * 135645564010 * gamma_1_3_over_2_3_gB := by
  decide +kernel

lemma gamma_1_3_over_2_3_hA : (18409931173 : ℝ) / 1000000000000 ≤ ((400 : ℝ) + 1 / 3) ^ ((1 : ℝ) / 3 - 1) := by
  have := BohrMollerupPrelude.rpow_rat_neg_div_lower 1201 3 2 3 18409931173 1000000000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_1_3_over_2_3_hB : (400 : ℝ) ^ ((2 : ℝ) / 3) ≤ (54288352331899 : ℝ) / 1000000000000 := by
  have := BohrMollerupPrelude.rpow_div_upper 400 2 3 54288352331899 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_1_3_over_2_3_hC : (400 : ℝ) ^ ((1 : ℝ) / 3) ≤ (7368062997281 : ℝ) / 1000000000000 := by
  have := BohrMollerupPrelude.rpow_div_upper 400 1 3 7368062997281 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_1_3_over_2_3_hD : (135645564010 : ℝ) / 1000000000000 ≤ ((400 : ℝ) + 2 / 3) ^ ((2 : ℝ) / 3 - 1) := by
  have := BohrMollerupPrelude.rpow_rat_neg_div_lower 1202 3 1 3 135645564010 1000000000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

/-- The real-number argument for abstract `gA gB : ℕ`, so that no tactic tries to
evaluate the products. -/
theorem gamma_1_3_over_2_3_aux (gA gB : ℕ) (gB_pos : 0 < gB)
    (P_eq : (∏ k ∈ Finset.range 400, ((2 : ℝ) / 3 + k) / ((1 : ℝ) / 3 + k)) = (gA : ℝ) / gB)
    (key_lo : 1977 * 54288352331899 * gB ≤ 1000 * 400 * 18409931173 * gA)
    (key_hi : 50 * 7368062997281 * gA ≤ 99 * 400 * 135645564010 * gB) :
    (1.977 : ℝ) ≤ Real.Gamma (1 / 3) / Real.Gamma (2 / 3) ∧ Real.Gamma (1 / 3) / Real.Gamma (2 / 3) ≤ (1.98 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := BohrMollerupPrelude.Gamma_ratio_bounds 400 (by norm_num)
    (x₁ := 1 / 3) (x₂ := 2 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [P_eq] at hlo hhi
  clear P_eq
  push_cast at hlo hhi
  have hgA : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
  have hgB : (0 : ℝ) < gB := Nat.cast_pos.mpr gB_pos
  have hY : (0 : ℝ) < (400 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  have hD' : (0 : ℝ) < ((400 : ℝ) + 2 / 3) ^ ((2 : ℝ) / 3 - 1) := by positivity
  have hkey1 : (1977 : ℝ) * 54288352331899 * gB ≤ 1000 * 400 * 18409931173 * gA := by
    exact_mod_cast key_lo
  have hkey2 : (50 : ℝ) * 7368062997281 * gA ≤ 99 * 400 * 135645564010 * gB := by
    exact_mod_cast key_hi
  clear key_lo key_hi gB_pos
  constructor
  · calc (1.977 : ℝ)
        ≤ (400 : ℝ) * ((18409931173 : ℝ) / 1000000000000) / ((54288352331899 : ℝ) / 1000000000000) * ((gA : ℝ) / gB) := by
          rw [show (400 : ℝ) * ((18409931173 : ℝ) / 1000000000000) / ((54288352331899 : ℝ) / 1000000000000) * ((gA : ℝ) / gB)
              = (400 * 18409931173 * gA) / (54288352331899 * gB) by field_simp]
          rw [le_div_iff₀ (by positivity)]
          linarith
      _ ≤ (400 : ℝ) * ((400 : ℝ) + 1 / 3) ^ ((1 : ℝ) / 3 - 1) / (400 : ℝ) ^ ((2 : ℝ) / 3) * ((gA : ℝ) / gB) := by
          gcongr
          · exact gamma_1_3_over_2_3_hA
          · exact gamma_1_3_over_2_3_hB
      _ ≤ Real.Gamma (1 / 3) / Real.Gamma (2 / 3) := hlo
  · calc Real.Gamma (1 / 3) / Real.Gamma (2 / 3)
        ≤ (400 : ℝ) ^ ((1 : ℝ) / 3) / ((400 : ℝ) * ((400 : ℝ) + 2 / 3) ^ ((2 : ℝ) / 3 - 1)) * ((gA : ℝ) / gB) := hhi
      _ ≤ ((7368062997281 : ℝ) / 1000000000000) / ((400 : ℝ) * ((135645564010 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB) := by
          gcongr
          · exact gamma_1_3_over_2_3_hC
          · exact gamma_1_3_over_2_3_hD
      _ ≤ (1.98 : ℝ) := by
          rw [show ((7368062997281 : ℝ) / 1000000000000) / ((400 : ℝ) * ((135645564010 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB)
              = (7368062997281 * gA) / (400 * 135645564010 * gB) by field_simp]
          rw [div_le_iff₀ (by positivity)]
          linarith

/-- `(1.977 : ℝ) ≤ Γ(1/3) / Γ(2/3) ≤ (1.98 : ℝ)`, about Mathlib's `Real.Gamma`. -/
theorem gamma_1_3_over_2_3 :
    (1.977 : ℝ) ≤ Real.Gamma (1 / 3) / Real.Gamma (2 / 3) ∧ Real.Gamma (1 / 3) / Real.Gamma (2 / 3) ≤ (1.98 : ℝ) :=
  gamma_1_3_over_2_3_aux gamma_1_3_over_2_3_gA gamma_1_3_over_2_3_gB gamma_1_3_over_2_3_gB_pos gamma_1_3_over_2_3_P_eq gamma_1_3_over_2_3_key_lo gamma_1_3_over_2_3_key_hi

example : (1.977 : ℝ) ≤ Real.Gamma (1 / 3) / Real.Gamma (2 / 3) ∧ Real.Gamma (1 / 3) / Real.Gamma (2 / 3) ≤ (1.98 : ℝ) := gamma_1_3_over_2_3

/-! ### `gamma_1_2_over_1_4`: `(0.4886 : ℝ) ≤ Γ(1/2) / Γ(1/4) ≤ (0.4892 : ℝ)` at `n = 400` (`2` blocks of `200`), brackets at scale `1000000000000` -/

/-- `∏_{k<400} (4 k + 1)`, in `2` blocks of `200`. Only the kernel evaluates it. -/
def gamma_1_2_over_1_4_gA : ℕ :=
  ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (4 * (200 * c + j) + 1)

/-- `∏_{k<400} (4 k + 2)`, in `2` blocks of `200`. -/
def gamma_1_2_over_1_4_gB : ℕ :=
  ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (4 * (200 * c + j) + 2)

lemma gamma_1_2_over_1_4_gA_eq : (∏ k ∈ Finset.range 400, (4 * k + 1)) = gamma_1_2_over_1_4_gA := by
  rw [show (400 : ℕ) = 2 * 200 from rfl, BohrMollerupPrelude.prod_range_chunk]
  rfl

lemma gamma_1_2_over_1_4_gB_eq : (∏ k ∈ Finset.range 400, (4 * k + 2)) = gamma_1_2_over_1_4_gB := by
  rw [show (400 : ℕ) = 2 * 200 from rfl, BohrMollerupPrelude.prod_range_chunk]
  rfl

lemma gamma_1_2_over_1_4_P_eq : (∏ k ∈ Finset.range 400, ((1 : ℝ) / 4 + k) / ((1 : ℝ) / 2 + k)) = (gamma_1_2_over_1_4_gA : ℝ) / gamma_1_2_over_1_4_gB := by
  rw [← gamma_1_2_over_1_4_gA_eq, ← gamma_1_2_over_1_4_gB_eq, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : (1 : ℝ) / 2 + k ≠ 0 := by positivity
  have h1' : (4 : ℝ) * k + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma gamma_1_2_over_1_4_gB_pos : 0 < gamma_1_2_over_1_4_gB := by
  unfold gamma_1_2_over_1_4_gB
  exact Finset.prod_pos fun c _ => Finset.prod_pos fun j _ => by omega

/-- `LOn u2 gB ≤ LOd n l1 gA`: the lower claim against the certified lower bound. -/
lemma gamma_1_2_over_1_4_key_lo : 2443 * 4472135955000 * gamma_1_2_over_1_4_gB ≤ 5000 * 400 * 49968779266 * gamma_1_2_over_1_4_gA := by
  decide +kernel

/-- `HId u3 gA ≤ HIn n l4 gB`: the upper claim against the certified upper bound. -/
lemma gamma_1_2_over_1_4_key_hi : 2500 * 20000000000000 * gamma_1_2_over_1_4_gA ≤ 1223 * 400 * 11175101967 * gamma_1_2_over_1_4_gB := by
  decide +kernel

lemma gamma_1_2_over_1_4_hA : (49968779266 : ℝ) / 1000000000000 ≤ ((400 : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 - 1) := by
  have := BohrMollerupPrelude.rpow_rat_neg_div_lower 801 2 1 2 49968779266 1000000000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_1_2_over_1_4_hB : (400 : ℝ) ^ ((1 : ℝ) / 4) ≤ (4472135955000 : ℝ) / 1000000000000 := by
  have := BohrMollerupPrelude.rpow_div_upper 400 1 4 4472135955000 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_1_2_over_1_4_hC : (400 : ℝ) ^ ((1 : ℝ) / 2) ≤ (20000000000000 : ℝ) / 1000000000000 := by
  have := BohrMollerupPrelude.rpow_div_upper 400 1 2 20000000000000 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma gamma_1_2_over_1_4_hD : (11175101967 : ℝ) / 1000000000000 ≤ ((400 : ℝ) + 1 / 4) ^ ((1 : ℝ) / 4 - 1) := by
  have := BohrMollerupPrelude.rpow_rat_neg_div_lower 1601 4 3 4 11175101967 1000000000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

/-- The real-number argument for abstract `gA gB : ℕ`, so that no tactic tries to
evaluate the products. -/
theorem gamma_1_2_over_1_4_aux (gA gB : ℕ) (gB_pos : 0 < gB)
    (P_eq : (∏ k ∈ Finset.range 400, ((1 : ℝ) / 4 + k) / ((1 : ℝ) / 2 + k)) = (gA : ℝ) / gB)
    (key_lo : 2443 * 4472135955000 * gB ≤ 5000 * 400 * 49968779266 * gA)
    (key_hi : 2500 * 20000000000000 * gA ≤ 1223 * 400 * 11175101967 * gB) :
    (0.4886 : ℝ) ≤ Real.Gamma (1 / 2) / Real.Gamma (1 / 4) ∧ Real.Gamma (1 / 2) / Real.Gamma (1 / 4) ≤ (0.4892 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := BohrMollerupPrelude.Gamma_ratio_bounds 400 (by norm_num)
    (x₁ := 1 / 2) (x₂ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [P_eq] at hlo hhi
  clear P_eq
  push_cast at hlo hhi
  have hgA : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
  have hgB : (0 : ℝ) < gB := Nat.cast_pos.mpr gB_pos
  have hY : (0 : ℝ) < (400 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hD' : (0 : ℝ) < ((400 : ℝ) + 1 / 4) ^ ((1 : ℝ) / 4 - 1) := by positivity
  have hkey1 : (2443 : ℝ) * 4472135955000 * gB ≤ 5000 * 400 * 49968779266 * gA := by
    exact_mod_cast key_lo
  have hkey2 : (2500 : ℝ) * 20000000000000 * gA ≤ 1223 * 400 * 11175101967 * gB := by
    exact_mod_cast key_hi
  clear key_lo key_hi gB_pos
  constructor
  · calc (0.4886 : ℝ)
        ≤ (400 : ℝ) * ((49968779266 : ℝ) / 1000000000000) / ((4472135955000 : ℝ) / 1000000000000) * ((gA : ℝ) / gB) := by
          rw [show (400 : ℝ) * ((49968779266 : ℝ) / 1000000000000) / ((4472135955000 : ℝ) / 1000000000000) * ((gA : ℝ) / gB)
              = (400 * 49968779266 * gA) / (4472135955000 * gB) by field_simp]
          rw [le_div_iff₀ (by positivity)]
          linarith
      _ ≤ (400 : ℝ) * ((400 : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 - 1) / (400 : ℝ) ^ ((1 : ℝ) / 4) * ((gA : ℝ) / gB) := by
          gcongr
          · exact gamma_1_2_over_1_4_hA
          · exact gamma_1_2_over_1_4_hB
      _ ≤ Real.Gamma (1 / 2) / Real.Gamma (1 / 4) := hlo
  · calc Real.Gamma (1 / 2) / Real.Gamma (1 / 4)
        ≤ (400 : ℝ) ^ ((1 : ℝ) / 2) / ((400 : ℝ) * ((400 : ℝ) + 1 / 4) ^ ((1 : ℝ) / 4 - 1)) * ((gA : ℝ) / gB) := hhi
      _ ≤ ((20000000000000 : ℝ) / 1000000000000) / ((400 : ℝ) * ((11175101967 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB) := by
          gcongr
          · exact gamma_1_2_over_1_4_hC
          · exact gamma_1_2_over_1_4_hD
      _ ≤ (0.4892 : ℝ) := by
          rw [show ((20000000000000 : ℝ) / 1000000000000) / ((400 : ℝ) * ((11175101967 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB)
              = (20000000000000 * gA) / (400 * 11175101967 * gB) by field_simp]
          rw [div_le_iff₀ (by positivity)]
          linarith

/-- `(0.4886 : ℝ) ≤ Γ(1/2) / Γ(1/4) ≤ (0.4892 : ℝ)`, about Mathlib's `Real.Gamma`. -/
theorem gamma_1_2_over_1_4 :
    (0.4886 : ℝ) ≤ Real.Gamma (1 / 2) / Real.Gamma (1 / 4) ∧ Real.Gamma (1 / 2) / Real.Gamma (1 / 4) ≤ (0.4892 : ℝ) :=
  gamma_1_2_over_1_4_aux gamma_1_2_over_1_4_gA gamma_1_2_over_1_4_gB gamma_1_2_over_1_4_gB_pos gamma_1_2_over_1_4_P_eq gamma_1_2_over_1_4_key_lo gamma_1_2_over_1_4_key_hi

example : (0.4886 : ℝ) ≤ Real.Gamma (1 / 2) / Real.Gamma (1 / 4) ∧ Real.Gamma (1 / 2) / Real.Gamma (1 / 4) ≤ (0.4892 : ℝ) := gamma_1_2_over_1_4

end BohrMollerupGammaRatio
