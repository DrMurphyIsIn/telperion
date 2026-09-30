/- telperion 0.1.6 | family GapBudgetMultiplicity | input-hash e92f999a119a02f6
   59 theorems, 40 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace GapBudgetMultiplicity

/-- The tangent step for the certified concave family `c * log`: for `c >= 0`,
    `c log x <= c log x0 + (c / x0) (x - x0)` (`Real.log_le_sub_one_of_pos` at `x / x0`).
    conjecture1_proved = False. -/
theorem gapBudget_log_tangent {c x x0 : ℝ} (hc : 0 ≤ c) (hx0 : 0 < x0) (hx : 0 < x) :
    c * Real.log x ≤ c * Real.log x0 + c / x0 * (x - x0) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hx0)
  rw [Real.log_div hx.ne' hx0.ne'] at h
  have h2 : c * (Real.log x - Real.log x0) ≤ c * (x / x0 - 1) :=
    mul_le_mul_of_nonneg_left h hc
  have e : c * (x / x0 - 1) = c / x0 * (x - x0) := by field_simp
  linarith

/-- The budget of the SEPARABLE model: `sum ell = M` and `B <= sum w` give
    `sum gamma <= tau M - B` for `gamma = tau ell - w`. -/
theorem gapBudget_of_sep {α : Type*} (m : Multiset α) (w ℓ γ : α → ℝ) (τ M B : ℝ)
    (hγ : ∀ a, γ a = τ * ℓ a - w a)
    (hℓ : (m.map ℓ).sum = M) (hB : B ≤ (m.map w).sum) :
    (m.map γ).sum ≤ τ * M - B := by
  have e : (m.map γ).sum = τ * (m.map ℓ).sum - (m.map w).sum := by
    rw [show γ = fun a => τ * ℓ a - w a from funext hγ, Multiset.sum_map_sub,
      Multiset.sum_map_mul_left]
  rw [e, hℓ]
  linarith

/-- The budget of the CONCAVE model `Phi = sum w + c log (sum y / M)`: the tangent at `x0`
    with slope `c / x0` gives `sum gamma <= tau M + c log x0 - c - B` for
    `gamma = tau ell - w - (c / x0 / M) y`. -/
theorem gapBudget_of_concave {α : Type*} (m : Multiset α) (w ℓ y γ : α → ℝ)
    (τ M B c x0 : ℝ) (hγ : ∀ a, γ a = τ * ℓ a - w a - c / x0 / M * y a)
    (hc : 0 ≤ c) (hx0 : 0 < x0) (hdom : 0 < (m.map y).sum / M)
    (hℓ : (m.map ℓ).sum = M)
    (hB : B ≤ (m.map w).sum + c * Real.log ((m.map y).sum / M)) :
    (m.map γ).sum ≤ τ * M + c * Real.log x0 - c / x0 * x0 - B := by
  have ht := gapBudget_log_tangent hc hx0 hdom
  have e : (m.map γ).sum
      = τ * (m.map ℓ).sum - (m.map w).sum - c / x0 / M * (m.map y).sum := by
    rw [show γ = fun a => τ * ℓ a - w a - c / x0 / M * y a from funext hγ,
      Multiset.sum_map_sub, Multiset.sum_map_sub, Multiset.sum_map_mul_left,
      Multiset.sum_map_mul_left]
  have e2 : c / x0 / M * (m.map y).sum = c / x0 * ((m.map y).sum / M) := by ring
  rw [e, hℓ, e2]
  linarith

/-- One atom's share of the budget: with every gap in `m` nonnegative,
    `count a * g <= theta` for any `g <= gamma a`. -/
theorem gapBudget_count_mul_le {α : Type*} [DecidableEq α] (m : Multiset α) (γ : α → ℝ)
    (θ : ℝ) (hγ : ∀ a ∈ m, 0 ≤ γ a) (hbud : (m.map γ).sum ≤ θ) (a : α) (g : ℝ)
    (hg : g ≤ γ a) : (m.count a : ℝ) * g ≤ θ := by
  rw [← Multiset.filter_add_not (· = a) m, Multiset.map_add, Multiset.sum_add,
    Multiset.filter_eq' m a, Multiset.map_replicate, Multiset.sum_replicate,
    nsmul_eq_mul] at hbud
  have hrest : 0 ≤ ((m.filter (fun b => ¬ b = a)).map γ).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
      exact hγ b (Multiset.mem_of_mem_filter hb)
  have := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α := ℝ) (m.count a))
  linarith

/-- The integer cap: `x g <= theta < (cap + 1) g` with `g > 0` forces `x <= cap`. -/
theorem gapBudget_nat_cap {x : ℕ} {g θ : ℝ} (cap : ℕ) (hg : 0 < g)
    (h : (x : ℝ) * g ≤ θ) (hcap : θ < ((cap : ℝ) + 1) * g) : x ≤ cap := by
  by_contra hc
  have h1 : (cap : ℝ) + 1 ≤ x := by exact_mod_cast Nat.succ_le_of_lt (not_le.mp hc)
  nlinarith

/-- The joint knapsack: `sum_{a in A} count a * g a <= theta` for gap lower bounds on `A`. -/
theorem gapBudget_knapsack {α : Type*} [DecidableEq α] (m : Multiset α) (γ g : α → ℝ)
    (θ : ℝ) (hγ : ∀ a ∈ m, 0 ≤ γ a) (hbud : (m.map γ).sum ≤ θ) (A : Finset α)
    (hg : ∀ a ∈ A, g a ≤ γ a) : ∑ a ∈ A, (m.count a : ℝ) * g a ≤ θ := by
  have h1 : ∑ a ∈ A, (m.count a : ℝ) * g a ≤ ∑ a ∈ A, (m.count a : ℝ) * γ a :=
    Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hg a ha) (Nat.cast_nonneg _)
  have h2 : ∑ a ∈ A, (m.count a : ℝ) * γ a
      = ∑ a ∈ A with a ∈ m.toFinset, (m.count a : ℝ) * γ a := by
    refine (Finset.sum_filter_of_ne fun a _ hne => ?_).symm
    by_contra hn
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hn
    simp [hn] at hne
  have h3 : ∑ a ∈ A with a ∈ m.toFinset, (m.count a : ℝ) * γ a
      ≤ ∑ a ∈ m.toFinset, (m.count a : ℝ) * γ a :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => (Finset.mem_filter.mp ha).2)
      fun a ha _ => mul_nonneg (Nat.cast_nonneg _) (hγ a (Multiset.mem_toFinset.mp ha))
  have h4 : (m.map γ).sum = ∑ a ∈ m.toFinset, (m.count a : ℝ) * γ a := by
    rw [Finset.sum_multiset_map_count]
    simp [nsmul_eq_mul]
  linarith

/-- `maxprod_mod0` -- the gap-budget model (kind gap_budget_multiplicity).
    Atoms k in [1, oo], normalisation sum ell = 3*t, price tau = log(3)/3.
    conjecture1_proved = False. -/
noncomputable def maxprod_mod0_w (k : ℕ) : ℝ := Real.log (k : ℝ)
noncomputable def maxprod_mod0_ell (k : ℕ) : ℝ := (k : ℝ)
noncomputable def maxprod_mod0_gap (k : ℕ) : ℝ :=
  (1 / 3 * Real.log 3) * maxprod_mod0_ell k - maxprod_mod0_w k

/-- `maxprod_mod0_enc0` -- a certified RATIONAL ENCLOSURE of `Real.log 2`.
    Route: Real.log_two_gt_d9 / Real.log_two_lt_d9.
    Exact fold [6931471803/10000000000, 108304247/156250000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_enc0 :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧ Real.log 2 < (108304247 / 156250000 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  norm_num at h1 h2
  constructor <;> linarith

/-- `maxprod_mod0_enc1` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 4)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-24086684149372061194723/83726747183417875496960, -72260052448115588669849/251180241550253626490880], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_enc1 :
    (-(24086684149372061194723 / 83726747183417875496960) : ℝ) ≤ Real.log (3 / 4) ∧
      Real.log (3 / 4) ≤ (-(72260052448115588669849 / 251180241550253626490880) : ℝ) := by
  have hx : |((1 / 4) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (1 / 4) = (3 / 4) by norm_num] at h
  generalize Real.log (3 / 4) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `maxprod_mod0_enc2` -- a certified RATIONAL ENCLOSURE of `Real.log 3`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [179654752543714987187393692273/163528803092613038080000000000, 538964258121732532782051441059/490586409277839114240000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_enc2 :
    (179654752543714987187393692273 / 163528803092613038080000000000 : ℝ) < Real.log 3 ∧
      Real.log 3 < (538964258121732532782051441059 / 490586409277839114240000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc0
  obtain ⟨h1lo, h1hi⟩ := maxprod_mod0_enc1
  have hfold : Real.log 3 = Real.log 2 + Real.log 2 + Real.log (3 / 4) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : (2 * 2 : ℝ) ≠ 0) (by norm_num : ((3 / 4) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `maxprod_mod0_gap_1_enc` -- a certified RATIONAL ENCLOSURE of `1 / 3 * Real.log 3`.
    Route: constant scaling (linarith).
    Exact fold [179654752543714987187393692273/490586409277839114240000000000, 538964258121732532782051441059/1471759227833517342720000000000], inside the stated bracket with slack (47120533192196248732273/490586409277839114240000000000, 1329907040685708726158941/1471759227833517342720000000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_gap_1_enc :
    (91551 / 250000 : ℝ) < 1 / 3 * Real.log 3 ∧ 1 / 3 * Real.log 3 < (73241 / 200000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc2
  constructor <;> linarith

/-- `maxprod_mod0_gap_1` -- listed atom: the gap at k = 1 is at least 91551/250000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod0_gap_1 : (91551 / 250000 : ℝ) ≤ maxprod_mod0_gap 1 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_1_enc
  norm_num [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap]
  linarith

/-- `maxprod_mod0_gap_2_enc` -- a certified RATIONAL ENCLOSURE of `2 / 3 * Real.log 3 - Real.log 2`.
    Route: the exact interval fold (linarith).
    Exact fold [9630459278850414211681124977/245293204638919557120000000000, 28891378695078620813293074851/735879613916758671360000000000], inside the stated bracket with slack (2771521793479592804977/245293204638919557120000000000, 726706521158141643245149/735879613916758671360000000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_gap_2_enc :
    (39261 / 1000000 : ℝ) < 2 / 3 * Real.log 3 - Real.log 2 ∧
      2 / 3 * Real.log 3 - Real.log 2 < (19631 / 500000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc2
  obtain ⟨h1lo, h1hi⟩ := maxprod_mod0_enc0
  constructor <;> linarith

/-- `maxprod_mod0_gap_2` -- listed atom: the gap at k = 2 is at least 39261/1000000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod0_gap_2 : (39261 / 1000000 : ℝ) ≤ maxprod_mod0_gap 2 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_2_enc
  norm_num [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap]
  linarith

/-- `maxprod_mod0_gap_3` -- listed atom: the gap at k = 3 is at least 0 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem maxprod_mod0_gap_3 : (0 : ℝ) ≤ maxprod_mod0_gap 3 := by
  have e : maxprod_mod0_gap 3 = (0 : ℝ) := by
    simp only [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap]
    ring_nf
  exact e.symm.le

/-- `maxprod_mod0_enc3` -- a certified RATIONAL ENCLOSURE of `Real.log 4`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [6931471803/5000000000, 108304247/78125000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_enc3 :
    (6931471803 / 5000000000 : ℝ) < Real.log 4 ∧ Real.log 4 < (108304247 / 78125000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc0
  have hfold : Real.log 4 = Real.log 2 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `maxprod_mod0_gap_4_enc` -- a certified RATIONAL ENCLOSURE of `(-1) * Real.log 4 + 4 / 3 * Real.log 3`.
    Route: the exact interval fold (linarith).
    Exact fold [9630459278850414211681124977/122646602319459778560000000000, 28891378695078620813293074851/367939806958379335680000000000], inside the stated bracket with slack (2771521793479592804977/122646602319459778560000000000, 358766714199762307565149/367939806958379335680000000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_gap_4_enc :
    (39261 / 500000 : ℝ) < (-1) * Real.log 4 + 4 / 3 * Real.log 3 ∧
      (-1) * Real.log 4 + 4 / 3 * Real.log 3 < (78523 / 1000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc3
  obtain ⟨h1lo, h1hi⟩ := maxprod_mod0_enc2
  constructor <;> linarith

/-- `maxprod_mod0_gap_4` -- listed atom: the gap at k = 4 is at least 39261/500000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod0_gap_4 : (39261 / 500000 : ℝ) ≤ maxprod_mod0_gap 4 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_4_enc
  norm_num [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap]
  linarith

/-- `maxprod_mod0_enc4` -- a certified RATIONAL ENCLOSURE of `Real.log (5 / 4)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [33629550671690590118849/150708144930152175894528, 33629550671690947067441/150708144930152175894528], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_enc4 :
    (33629550671690590118849 / 150708144930152175894528 : ℝ) ≤ Real.log (5 / 4) ∧
      Real.log (5 / 4) ≤ (33629550671690947067441 / 150708144930152175894528 : ℝ) := by
  have hx : |((-(1 / 4)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (-(1 / 4)) = (5 / 4) by norm_num] at h
  generalize Real.log (5 / 4) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `maxprod_mod0_enc5` -- a certified RATIONAL ENCLOSURE of `Real.log 5`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [2368705098484844067004418230457/1471759227833517342720000000000, 2368705099956606780664029323177/1471759227833517342720000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_enc5 :
    (2368705098484844067004418230457 / 1471759227833517342720000000000 : ℝ) < Real.log 5 ∧
      Real.log 5 < (2368705099956606780664029323177 / 1471759227833517342720000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc0
  obtain ⟨h1lo, h1hi⟩ := maxprod_mod0_enc4
  have hfold : Real.log 5 = Real.log 2 + Real.log 2 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : (2 * 2 : ℝ) ≠ 0) (by norm_num : ((5 / 4) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `maxprod_mod0_gap_5_enc` -- a certified RATIONAL ENCLOSURE of `(-1) * Real.log 5 + 5 / 3 * Real.log 3`.
    Route: the exact interval fold (linarith).
    Exact fold [14823463099959910324858002769/66898146719705333760000000000, 14823463278355390768447226129/66898146719705333760000000000], inside the stated bracket with slack (37953514163059649682769/66898146719705333760000000000, 28766237076202094853871/66898146719705333760000000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem maxprod_mod0_gap_5_enc :
    (110791 / 500000 : ℝ) < (-1) * Real.log 5 + 5 / 3 * Real.log 3 ∧
      (-1) * Real.log 5 + 5 / 3 * Real.log 3 < (221583 / 1000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc5
  obtain ⟨h1lo, h1hi⟩ := maxprod_mod0_enc2
  constructor <;> linarith

/-- `maxprod_mod0_gap_5` -- the tail anchor: the gap at k = 5 is at least 110791/500000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod0_gap_5 : (110791 / 500000 : ℝ) ≤ maxprod_mod0_gap 5 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_5_enc
  norm_num [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap]
  linarith

/-- `maxprod_mod0_tail` -- the certified TAIL: every atom k >= 5 has gap at least 110791/500000.
    The gap is P k - 1 log(k + 0) + d with P >= 91551/250000 >= 1/5; the
    log tangent at K0 + s (convexity) makes it nondecreasing from the anchor.
    conjecture1_proved = False. -/
theorem maxprod_mod0_tail (k : ℕ) (hk : 5 ≤ k) : (110791 / 500000 : ℝ) ≤ maxprod_mod0_gap k := by
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0 := maxprod_mod0_gap_5
  have ht := gapBudget_log_tangent (c := 1) (x := (k : ℝ)) (x0 := 5) (by norm_num)
    (by norm_num) (by linarith)
  obtain ⟨hp0, hp1⟩ := maxprod_mod0_gap_1_enc
  have hprod : 0 ≤ (1 / 3 * Real.log 3 - 1 / 5) * ((k : ℝ) - 5) :=
    mul_nonneg (by linarith) (by linarith)
  simp only [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap] at h0 ⊢
  norm_num at h0 ht
  linarith

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `maxprod_mod0_bench` -- the benchmark meets EVERY hypothesis of `maxprod_mod0` and ATTAINS `B`:
    `Phi(bench) = B`, `sum ell(bench) = M`, its atoms lie in the alphabet,
    so the main theorem is not vacuous and applies to every optimum.
    conjecture1_proved = False. -/
theorem maxprod_mod0_bench (t : ℕ) :
    ((Multiset.replicate t 3 : Multiset ℕ).map maxprod_mod0_w).sum = Real.log 3 * (t : ℝ) ∧
    ((Multiset.replicate t 3 : Multiset ℕ).map maxprod_mod0_ell).sum = 3 * (t : ℝ) ∧
    (∀ k ∈ (Multiset.replicate t 3 : Multiset ℕ), 1 ≤ k) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · norm_num [maxprod_mod0_w, maxprod_mod0_ell, maxprod_mod0_gap, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · intro k hk
    simp only [Multiset.mem_replicate] at hk
    omega

/-- `maxprod_mod0` -- the GAP-BUDGET PRUNING.  Any multiset of atoms in the alphabet with
    the benchmark's normalisation and at least its value `B` (attained, see
    `maxprod_mod0_bench`) obeys the budget sum gamma <= theta <= 0, hence
    the caps / exclusions / knapsack below.  Conditional pruning only; it does not
    identify the optimum.  conjecture1_proved = False. -/
theorem maxprod_mod0 (t : ℕ) (m : Multiset ℕ)
    (hA : ∀ k ∈ m, 1 ≤ k)
    (hl : (m.map maxprod_mod0_ell).sum = 3 * (t : ℝ))
    (hB : Real.log 3 * (t : ℝ) ≤ (m.map maxprod_mod0_w).sum) :
    m.count 1 = 0 ∧
      m.count 2 = 0 ∧
      m.count 4 = 0 ∧
      (∀ k ∈ m, k < 5) := by
  have hbud0 := gapBudget_of_sep m maxprod_mod0_w maxprod_mod0_ell maxprod_mod0_gap (1 / 3 * Real.log 3)
    (3 * (t : ℝ)) _ (fun _ => rfl) hl hB
  have hbud : (m.map maxprod_mod0_gap).sum ≤ (0 : ℝ) := by
    linarith
  have hγ : ∀ k ∈ m, 0 ≤ maxprod_mod0_gap k := by
    intro k hk
    have h1 := hA k hk
    by_cases hK : 5 ≤ k
    · linarith [maxprod_mod0_tail k hK]
    · interval_cases k
      all_goals linarith [maxprod_mod0_gap_1, maxprod_mod0_gap_2, maxprod_mod0_gap_3, maxprod_mod0_gap_4]
  have hc := gapBudget_count_mul_le m maxprod_mod0_gap _ hγ hbud
  have c1 : m.count 1 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 1 _ maxprod_mod0_gap_1) (by norm_num))
  have c2 : m.count 2 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 2 _ maxprod_mod0_gap_2) (by norm_num))
  have c4 : m.count 4 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 4 _ maxprod_mod0_gap_4) (by norm_num))
  have ctail3 : ∀ k ∈ m, k < 5 := by
    intro k hk
    by_contra hlt
    have hK : 5 ≤ k := by omega
    have h1 : 1 ≤ m.count k := Multiset.one_le_count_iff_mem.mpr hk
    have := gapBudget_nat_cap 0 (by norm_num) (hc k _ (maxprod_mod0_tail k hK)) (by norm_num)
    omega
  exact ⟨c1, c2, c4, ctail3⟩

/-- `maxprod_mod2` -- the gap-budget model (kind gap_budget_multiplicity).
    Atoms k in [1, oo], normalisation sum ell = 3*t + 2, price tau = log(3)/3.
    conjecture1_proved = False. -/
noncomputable def maxprod_mod2_w (k : ℕ) : ℝ := Real.log (k : ℝ)
noncomputable def maxprod_mod2_ell (k : ℕ) : ℝ := (k : ℝ)
noncomputable def maxprod_mod2_gap (k : ℕ) : ℝ :=
  (1 / 3 * Real.log 3) * maxprod_mod2_ell k - maxprod_mod2_w k

/-- `maxprod_mod2_gap_1` -- listed atom: the gap at k = 1 is at least 91551/250000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod2_gap_1 : (91551 / 250000 : ℝ) ≤ maxprod_mod2_gap 1 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_1_enc
  norm_num [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap]
  linarith

/-- `maxprod_mod2_gap_2` -- listed atom: the gap at k = 2 is at least 39261/1000000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod2_gap_2 : (39261 / 1000000 : ℝ) ≤ maxprod_mod2_gap 2 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_2_enc
  norm_num [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap]
  linarith

/-- `maxprod_mod2_gap_3` -- listed atom: the gap at k = 3 is at least 0 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem maxprod_mod2_gap_3 : (0 : ℝ) ≤ maxprod_mod2_gap 3 := by
  have e : maxprod_mod2_gap 3 = (0 : ℝ) := by
    simp only [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap]
    ring_nf
  exact e.symm.le

/-- `maxprod_mod2_gap_4` -- listed atom: the gap at k = 4 is at least 39261/500000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod2_gap_4 : (39261 / 500000 : ℝ) ≤ maxprod_mod2_gap 4 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_4_enc
  norm_num [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap]
  linarith

/-- `maxprod_mod2_gap_5` -- the tail anchor: the gap at k = 5 is at least 110791/500000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod2_gap_5 : (110791 / 500000 : ℝ) ≤ maxprod_mod2_gap 5 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_5_enc
  norm_num [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap]
  linarith

/-- `maxprod_mod2_tail` -- the certified TAIL: every atom k >= 5 has gap at least 110791/500000.
    The gap is P k - 1 log(k + 0) + d with P >= 91551/250000 >= 1/5; the
    log tangent at K0 + s (convexity) makes it nondecreasing from the anchor.
    conjecture1_proved = False. -/
theorem maxprod_mod2_tail (k : ℕ) (hk : 5 ≤ k) : (110791 / 500000 : ℝ) ≤ maxprod_mod2_gap k := by
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0 := maxprod_mod2_gap_5
  have ht := gapBudget_log_tangent (c := 1) (x := (k : ℝ)) (x0 := 5) (by norm_num)
    (by norm_num) (by linarith)
  obtain ⟨hp0, hp1⟩ := maxprod_mod0_gap_1_enc
  have hprod : 0 ≤ (1 / 3 * Real.log 3 - 1 / 5) * ((k : ℝ) - 5) :=
    mul_nonneg (by linarith) (by linarith)
  simp only [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap] at h0 ⊢
  norm_num at h0 ht
  linarith

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `maxprod_mod2_bench` -- the benchmark meets EVERY hypothesis of `maxprod_mod2` and ATTAINS `B`:
    `Phi(bench) = B`, `sum ell(bench) = M`, its atoms lie in the alphabet,
    so the main theorem is not vacuous and applies to every optimum.
    conjecture1_proved = False. -/
theorem maxprod_mod2_bench (t : ℕ) :
    ((Multiset.replicate 1 2 + Multiset.replicate t 3 : Multiset ℕ).map maxprod_mod2_w).sum = Real.log 3 * (t : ℝ) + Real.log 2 ∧
    ((Multiset.replicate 1 2 + Multiset.replicate t 3 : Multiset ℕ).map maxprod_mod2_ell).sum = 3 * (t : ℝ) + 2 ∧
    (∀ k ∈ (Multiset.replicate 1 2 + Multiset.replicate t 3 : Multiset ℕ), 1 ≤ k) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · norm_num [maxprod_mod2_w, maxprod_mod2_ell, maxprod_mod2_gap, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · intro k hk
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hk
    omega

/-- `maxprod_mod2` -- the GAP-BUDGET PRUNING.  Any multiset of atoms in the alphabet with
    the benchmark's normalisation and at least its value `B` (attained, see
    `maxprod_mod2_bench`) obeys the budget sum gamma <= theta <= 19631/500000, hence
    the caps / exclusions / knapsack below.  Conditional pruning only; it does not
    identify the optimum.  conjecture1_proved = False. -/
theorem maxprod_mod2 (t : ℕ) (m : Multiset ℕ)
    (hA : ∀ k ∈ m, 1 ≤ k)
    (hl : (m.map maxprod_mod2_ell).sum = 3 * (t : ℝ) + 2)
    (hB : Real.log 3 * (t : ℝ) + Real.log 2 ≤ (m.map maxprod_mod2_w).sum) :
    m.count 1 = 0 ∧
      m.count 2 ≤ 1 ∧
      m.count 4 = 0 ∧
      (∀ k ∈ m, k < 5) := by
  have hbud0 := gapBudget_of_sep m maxprod_mod2_w maxprod_mod2_ell maxprod_mod2_gap (1 / 3 * Real.log 3)
    (3 * (t : ℝ) + 2) _ (fun _ => rfl) hl hB
  have hbud : (m.map maxprod_mod2_gap).sum ≤ (19631 / 500000 : ℝ) := by
    obtain ⟨ht0, ht1⟩ := maxprod_mod0_gap_2_enc
    linarith
  have hγ : ∀ k ∈ m, 0 ≤ maxprod_mod2_gap k := by
    intro k hk
    have h1 := hA k hk
    by_cases hK : 5 ≤ k
    · linarith [maxprod_mod2_tail k hK]
    · interval_cases k
      all_goals linarith [maxprod_mod2_gap_1, maxprod_mod2_gap_2, maxprod_mod2_gap_3, maxprod_mod2_gap_4]
  have hc := gapBudget_count_mul_le m maxprod_mod2_gap _ hγ hbud
  have c1 : m.count 1 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 1 _ maxprod_mod2_gap_1) (by norm_num))
  have c2 : m.count 2 ≤ 1 :=
    gapBudget_nat_cap 1 (by norm_num) (hc 2 _ maxprod_mod2_gap_2) (by norm_num)
  have c4 : m.count 4 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 4 _ maxprod_mod2_gap_4) (by norm_num))
  have ctail3 : ∀ k ∈ m, k < 5 := by
    intro k hk
    by_contra hlt
    have hK : 5 ≤ k := by omega
    have h1 : 1 ≤ m.count k := Multiset.one_le_count_iff_mem.mpr hk
    have := gapBudget_nat_cap 0 (by norm_num) (hc k _ (maxprod_mod2_tail k hK)) (by norm_num)
    omega
  exact ⟨c1, c2, c4, ctail3⟩

/-- `maxprod_mod1` -- the gap-budget model (kind gap_budget_multiplicity).
    Atoms k in [1, oo], normalisation sum ell = 3*t + 4, price tau = log(3)/3.
    conjecture1_proved = False. -/
noncomputable def maxprod_mod1_w (k : ℕ) : ℝ := Real.log (k : ℝ)
noncomputable def maxprod_mod1_ell (k : ℕ) : ℝ := (k : ℝ)
noncomputable def maxprod_mod1_gap (k : ℕ) : ℝ :=
  (1 / 3 * Real.log 3) * maxprod_mod1_ell k - maxprod_mod1_w k

/-- `maxprod_mod1_gap_1` -- listed atom: the gap at k = 1 is at least 91551/250000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod1_gap_1 : (91551 / 250000 : ℝ) ≤ maxprod_mod1_gap 1 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_1_enc
  norm_num [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap]
  linarith

/-- `maxprod_mod1_gap_2` -- listed atom: the gap at k = 2 is at least 39261/1000000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod1_gap_2 : (39261 / 1000000 : ℝ) ≤ maxprod_mod1_gap 2 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_2_enc
  norm_num [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap]
  linarith

/-- `maxprod_mod1_gap_3` -- listed atom: the gap at k = 3 is at least 0 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem maxprod_mod1_gap_3 : (0 : ℝ) ≤ maxprod_mod1_gap 3 := by
  have e : maxprod_mod1_gap 3 = (0 : ℝ) := by
    simp only [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap]
    ring_nf
  exact e.symm.le

/-- `maxprod_mod1_gap_4` -- listed atom: the gap at k = 4 is at least 39261/500000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod1_gap_4 : (39261 / 500000 : ℝ) ≤ maxprod_mod1_gap 4 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_4_enc
  norm_num [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap]
  linarith

/-- `maxprod_mod1_gap_5` -- the tail anchor: the gap at k = 5 is at least 110791/500000 (the stated lower end of a rational enclosure; the generator refuses a bound the fold does not imply).
    conjecture1_proved = False. -/
theorem maxprod_mod1_gap_5 : (110791 / 500000 : ℝ) ≤ maxprod_mod1_gap 5 := by
  obtain ⟨h0, h1⟩ := maxprod_mod0_gap_5_enc
  norm_num [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap]
  linarith

/-- `maxprod_mod1_tail` -- the certified TAIL: every atom k >= 5 has gap at least 110791/500000.
    The gap is P k - 1 log(k + 0) + d with P >= 91551/250000 >= 1/5; the
    log tangent at K0 + s (convexity) makes it nondecreasing from the anchor.
    conjecture1_proved = False. -/
theorem maxprod_mod1_tail (k : ℕ) (hk : 5 ≤ k) : (110791 / 500000 : ℝ) ≤ maxprod_mod1_gap k := by
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0 := maxprod_mod1_gap_5
  have ht := gapBudget_log_tangent (c := 1) (x := (k : ℝ)) (x0 := 5) (by norm_num)
    (by norm_num) (by linarith)
  obtain ⟨hp0, hp1⟩ := maxprod_mod0_gap_1_enc
  have hprod : 0 ≤ (1 / 3 * Real.log 3 - 1 / 5) * ((k : ℝ) - 5) :=
    mul_nonneg (by linarith) (by linarith)
  simp only [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap] at h0 ⊢
  norm_num at h0 ht
  linarith

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `maxprod_mod1_bench` -- the benchmark meets EVERY hypothesis of `maxprod_mod1` and ATTAINS `B`:
    `Phi(bench) = B`, `sum ell(bench) = M`, its atoms lie in the alphabet,
    so the main theorem is not vacuous and applies to every optimum.
    conjecture1_proved = False. -/
theorem maxprod_mod1_bench (t : ℕ) :
    ((Multiset.replicate t 3 + Multiset.replicate 1 4 : Multiset ℕ).map maxprod_mod1_w).sum = Real.log 3 * (t : ℝ) + Real.log 4 ∧
    ((Multiset.replicate t 3 + Multiset.replicate 1 4 : Multiset ℕ).map maxprod_mod1_ell).sum = 3 * (t : ℝ) + 4 ∧
    (∀ k ∈ (Multiset.replicate t 3 + Multiset.replicate 1 4 : Multiset ℕ), 1 ≤ k) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · norm_num [maxprod_mod1_w, maxprod_mod1_ell, maxprod_mod1_gap, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · intro k hk
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hk
    omega

/-- `maxprod_mod1` -- the GAP-BUDGET PRUNING.  Any multiset of atoms in the alphabet with
    the benchmark's normalisation and at least its value `B` (attained, see
    `maxprod_mod1_bench`) obeys the budget sum gamma <= theta <= 78523/1000000, hence
    the caps / exclusions / knapsack below.  Conditional pruning only; it does not
    identify the optimum.  conjecture1_proved = False. -/
theorem maxprod_mod1 (t : ℕ) (m : Multiset ℕ)
    (hA : ∀ k ∈ m, 1 ≤ k)
    (hl : (m.map maxprod_mod1_ell).sum = 3 * (t : ℝ) + 4)
    (hB : Real.log 3 * (t : ℝ) + Real.log 4 ≤ (m.map maxprod_mod1_w).sum) :
    m.count 1 = 0 ∧
      m.count 2 ≤ 2 ∧
      m.count 4 ≤ 1 ∧
      (∀ k ∈ m, k < 5) ∧
      [m.count 2, m.count 4] ∈ [[0, 0], [0, 1], [1, 0], [2, 0]] := by
  have hbud0 := gapBudget_of_sep m maxprod_mod1_w maxprod_mod1_ell maxprod_mod1_gap (1 / 3 * Real.log 3)
    (3 * (t : ℝ) + 4) _ (fun _ => rfl) hl hB
  have hbud : (m.map maxprod_mod1_gap).sum ≤ (78523 / 1000000 : ℝ) := by
    obtain ⟨ht0, ht1⟩ := maxprod_mod0_gap_4_enc
    linarith
  have hγ : ∀ k ∈ m, 0 ≤ maxprod_mod1_gap k := by
    intro k hk
    have h1 := hA k hk
    by_cases hK : 5 ≤ k
    · linarith [maxprod_mod1_tail k hK]
    · interval_cases k
      all_goals linarith [maxprod_mod1_gap_1, maxprod_mod1_gap_2, maxprod_mod1_gap_3, maxprod_mod1_gap_4]
  have hc := gapBudget_count_mul_le m maxprod_mod1_gap _ hγ hbud
  have c1 : m.count 1 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 1 _ maxprod_mod1_gap_1) (by norm_num))
  have c2 : m.count 2 ≤ 2 :=
    gapBudget_nat_cap 2 (by norm_num) (hc 2 _ maxprod_mod1_gap_2) (by norm_num)
  have c4 : m.count 4 ≤ 1 :=
    gapBudget_nat_cap 1 (by norm_num) (hc 4 _ maxprod_mod1_gap_4) (by norm_num)
  have ctail3 : ∀ k ∈ m, k < 5 := by
    intro k hk
    by_contra hlt
    have hK : 5 ≤ k := by omega
    have h1 : 1 ≤ m.count k := Multiset.one_le_count_iff_mem.mpr hk
    have := gapBudget_nat_cap 0 (by norm_num) (hc k _ (maxprod_mod1_tail k hK)) (by norm_num)
    omega
  have hkn := gapBudget_knapsack m maxprod_mod1_gap (fun k => if k = 2 then (39261 / 1000000) else (39261 / 500000)) _ hγ hbud {2, 4} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simpa using maxprod_mod1_gap_2
    · simpa using maxprod_mod1_gap_4)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at hkn
  norm_num at hkn
  have hdec : ∀ x2 ∈ List.range 3, ∀ x4 ∈ List.range 2, x2 * 39261 + x4 * 78522 ≤ 78523 →
      [x2, x4] ∈ [[0, 0], [0, 1], [1, 0], [2, 0]] := by decide
  have hint : ((m.count 2 * 39261 + m.count 4 * 78522 : ℕ) : ℝ) ≤ 78523 := by push_cast; linarith
  have ckn := hdec _ (List.mem_range.mpr (Nat.lt_succ_of_le c2)) _ (List.mem_range.mpr (Nat.lt_succ_of_le c4)) (by exact_mod_cast hint)
  exact ⟨c1, c2, c4, ctail3, ckn⟩

/-- `concave_sharp` -- the gap-budget model (kind gap_budget_multiplicity).
    Atoms k in [1, 6], normalisation sum ell = 10, price tau = 64/99, concave part 12 * log(sum y / M) tangent at x0 = 11/5.
    conjecture1_proved = False. -/
noncomputable def concave_sharp_w (k : ℕ) : ℝ := -(1 / 9 * (k : ℝ) ^ 2)
noncomputable def concave_sharp_ell (_k : ℕ) : ℝ := 1
noncomputable def concave_sharp_y (k : ℕ) : ℝ := (k : ℝ)
noncomputable def concave_sharp_gap (k : ℕ) : ℝ :=
  (64 / 99) * concave_sharp_ell k - concave_sharp_w k - (12) / (11 / 5) / (10) * concave_sharp_y k

/-- `concave_sharp_gap_1` -- listed atom: the gap at k = 1 is at least 7/33 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_sharp_gap_1 : (7 / 33 : ℝ) ≤ concave_sharp_gap 1 := by
  have e : concave_sharp_gap 1 = (7 / 33 : ℝ) := by
    simp only [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y]
    ring_nf
  exact e.symm.le

/-- `concave_sharp_gap_2` -- listed atom: the gap at k = 2 is at least 0 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_sharp_gap_2 : (0 : ℝ) ≤ concave_sharp_gap 2 := by
  have e : concave_sharp_gap 2 = (0 : ℝ) := by
    simp only [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y]
    ring_nf
  exact e.symm.le

/-- `concave_sharp_gap_3` -- listed atom: the gap at k = 3 is at least 1/99 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_sharp_gap_3 : (1 / 99 : ℝ) ≤ concave_sharp_gap 3 := by
  have e : concave_sharp_gap 3 = (1 / 99 : ℝ) := by
    simp only [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y]
    ring_nf
  exact e.symm.le

/-- `concave_sharp_gap_4` -- listed atom: the gap at k = 4 is at least 8/33 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_sharp_gap_4 : (8 / 33 : ℝ) ≤ concave_sharp_gap 4 := by
  have e : concave_sharp_gap 4 = (8 / 33 : ℝ) := by
    simp only [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y]
    ring_nf
  exact e.symm.le

/-- `concave_sharp_gap_5` -- listed atom: the gap at k = 5 is at least 23/33 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_sharp_gap_5 : (23 / 33 : ℝ) ≤ concave_sharp_gap 5 := by
  have e : concave_sharp_gap 5 = (23 / 33 : ℝ) := by
    simp only [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y]
    ring_nf
  exact e.symm.le

/-- `concave_sharp_gap_6` -- listed atom: the gap at k = 6 is at least 136/99 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_sharp_gap_6 : (136 / 99 : ℝ) ≤ concave_sharp_gap 6 := by
  have e : concave_sharp_gap 6 = (136 / 99 : ℝ) := by
    simp only [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y]
    ring_nf
  exact e.symm.le

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `concave_sharp_bench` -- the benchmark meets EVERY hypothesis of `concave_sharp` and ATTAINS `B`:
    `Phi(bench) = B`, `sum ell(bench) = M`, its atoms lie in the alphabet and its mean is positive,
    so the main theorem is not vacuous and applies to every optimum.
    conjecture1_proved = False. -/
theorem concave_sharp_bench :
    ((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_sharp_w).sum + 12 * Real.log (((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_sharp_y).sum / 10) = 12 * Real.log (11 / 5) - 50 / 9 ∧
    ((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_sharp_ell).sum = 10 ∧
    (∀ k ∈ (Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ), 1 ≤ k ∧ k ≤ 6) ∧
    0 < ((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_sharp_y).sum / 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · norm_num [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · intro k hk
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hk
    omega
  · norm_num [concave_sharp_w, concave_sharp_ell, concave_sharp_gap, concave_sharp_y, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

/-- `concave_sharp` -- the GAP-BUDGET PRUNING.  Any multiset of atoms in the alphabet with
    the benchmark's normalisation and at least its value `B` (attained, see
    `concave_sharp_bench`) obeys the budget sum gamma <= theta <= 2/99, hence
    the caps / exclusions / knapsack below.  Conditional pruning only; it does not
    identify the optimum.  conjecture1_proved = False. -/
theorem concave_sharp (m : Multiset ℕ)
    (hA : ∀ k ∈ m, 1 ≤ k ∧ k ≤ 6)
    (hl : (m.map concave_sharp_ell).sum = 10)
    (hdom : 0 < (m.map concave_sharp_y).sum / 10)
    (hB : 12 * Real.log (11 / 5) - 50 / 9 ≤ (m.map concave_sharp_w).sum + 12 * Real.log ((m.map concave_sharp_y).sum / 10)) :
    m.count 1 = 0 ∧
      m.count 3 ≤ 2 ∧
      m.count 4 = 0 ∧
      m.count 5 = 0 ∧
      m.count 6 = 0 := by
  have hbud0 := gapBudget_of_concave m concave_sharp_w concave_sharp_ell concave_sharp_y concave_sharp_gap (64 / 99)
    (10) _ (12) (11 / 5) (fun _ => rfl) (by norm_num) (by norm_num) hdom hl hB
  have hbud : (m.map concave_sharp_gap).sum ≤ (2 / 99 : ℝ) := by
    linarith
  have hγ : ∀ k ∈ m, 0 ≤ concave_sharp_gap k := by
    intro k hk
    obtain ⟨h1, h2⟩ := hA k hk
    interval_cases k
    all_goals linarith [concave_sharp_gap_1, concave_sharp_gap_2, concave_sharp_gap_3, concave_sharp_gap_4, concave_sharp_gap_5, concave_sharp_gap_6]
  have hc := gapBudget_count_mul_le m concave_sharp_gap _ hγ hbud
  have c1 : m.count 1 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 1 _ concave_sharp_gap_1) (by norm_num))
  have c3 : m.count 3 ≤ 2 :=
    gapBudget_nat_cap 2 (by norm_num) (hc 3 _ concave_sharp_gap_3) (by norm_num)
  have c4 : m.count 4 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 4 _ concave_sharp_gap_4) (by norm_num))
  have c5 : m.count 5 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 5 _ concave_sharp_gap_5) (by norm_num))
  have c6 : m.count 6 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 6 _ concave_sharp_gap_6) (by norm_num))
  exact ⟨c1, c3, c4, c5, c6⟩

/-- `concave_knapsack` -- the gap-budget model (kind gap_budget_multiplicity).
    Atoms k in [1, 6], normalisation sum ell = 10, price tau = 4/5, concave part 12 * log(sum y / M) tangent at x0 = 2.
    conjecture1_proved = False. -/
noncomputable def concave_knapsack_w (k : ℕ) : ℝ := -(1 / 9 * (k : ℝ) ^ 2)
noncomputable def concave_knapsack_ell (_k : ℕ) : ℝ := 1
noncomputable def concave_knapsack_y (k : ℕ) : ℝ := (k : ℝ)
noncomputable def concave_knapsack_gap (k : ℕ) : ℝ :=
  (4 / 5) * concave_knapsack_ell k - concave_knapsack_w k - (12) / (2) / (10) * concave_knapsack_y k

/-- `concave_knapsack_gap_1` -- listed atom: the gap at k = 1 is at least 14/45 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_knapsack_gap_1 : (14 / 45 : ℝ) ≤ concave_knapsack_gap 1 := by
  have e : concave_knapsack_gap 1 = (14 / 45 : ℝ) := by
    simp only [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y]
    ring_nf
  exact e.symm.le

/-- `concave_knapsack_gap_2` -- listed atom: the gap at k = 2 is at least 2/45 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_knapsack_gap_2 : (2 / 45 : ℝ) ≤ concave_knapsack_gap 2 := by
  have e : concave_knapsack_gap 2 = (2 / 45 : ℝ) := by
    simp only [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y]
    ring_nf
  exact e.symm.le

/-- `concave_knapsack_gap_3` -- listed atom: the gap at k = 3 is at least 0 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_knapsack_gap_3 : (0 : ℝ) ≤ concave_knapsack_gap 3 := by
  have e : concave_knapsack_gap 3 = (0 : ℝ) := by
    simp only [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y]
    ring_nf
  exact e.symm.le

/-- `concave_knapsack_gap_4` -- listed atom: the gap at k = 4 is at least 8/45 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_knapsack_gap_4 : (8 / 45 : ℝ) ≤ concave_knapsack_gap 4 := by
  have e : concave_knapsack_gap 4 = (8 / 45 : ℝ) := by
    simp only [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y]
    ring_nf
  exact e.symm.le

/-- `concave_knapsack_gap_5` -- listed atom: the gap at k = 5 is at least 26/45 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_knapsack_gap_5 : (26 / 45 : ℝ) ≤ concave_knapsack_gap 5 := by
  have e : concave_knapsack_gap 5 = (26 / 45 : ℝ) := by
    simp only [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y]
    ring_nf
  exact e.symm.le

/-- `concave_knapsack_gap_6` -- listed atom: the gap at k = 6 is at least 6/5 (exact: the gap is rational).
    conjecture1_proved = False. -/
theorem concave_knapsack_gap_6 : (6 / 5 : ℝ) ≤ concave_knapsack_gap 6 := by
  have e : concave_knapsack_gap 6 = (6 / 5 : ℝ) := by
    simp only [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y]
    ring_nf
  exact e.symm.le

/-- `concave_knapsack_enc0` -- a certified RATIONAL ENCLOSURE of `Real.log (11 / 10)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [51031251726630891454928591335441/535422888000000000000000000000000, 3402083448442059430328580687887/35694859200000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem concave_knapsack_enc0 :
    (51031251726630891454928591335441 / 535422888000000000000000000000000 : ℝ) ≤ Real.log (11 / 10) ∧
      Real.log (11 / 10) ≤ (3402083448442059430328580687887 / 35694859200000000000000000000000 : ℝ) := by
  have hx : |((-(1 / 10)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (-(1 / 10)) = (11 / 10) by norm_num] at h
  generalize Real.log (11 / 10) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `concave_knapsack_enc1` -- a certified RATIONAL ENCLOSURE of `Real.log (11 / 5)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [422158116811913597854928591335441/535422888000000000000000000000000, 28143874471975002790328580687887/35694859200000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem concave_knapsack_enc1 :
    (422158116811913597854928591335441 / 535422888000000000000000000000000 : ℝ) < Real.log (11 / 5) ∧
      Real.log (11 / 5) < (28143874471975002790328580687887 / 35694859200000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc0
  obtain ⟨h1lo, h1hi⟩ := concave_knapsack_enc0
  have hfold : Real.log (11 / 5) = Real.log 2 + Real.log (11 / 10) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : ((11 / 10) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `concave_knapsack_theta_enc` -- a certified RATIONAL ENCLOSURE of `12 * Real.log 2 - 12 * Real.log (11 / 5) + 14 / 9`.
    Route: the exact interval fold (linarith).
    Exact fold [11025251203394598727042773809017/26771144400000000000000000000000, 55126257623241657635214225993677/133855722000000000000000000000000], inside the stated bracket with slack (10491709398727042773809017/26771144400000000000000000000000, 79790906342364785774006323/133855722000000000000000000000000).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem concave_knapsack_theta_enc :
    (411833 / 1000000 : ℝ) < 12 * Real.log 2 - 12 * Real.log (11 / 5) + 14 / 9 ∧
      12 * Real.log 2 - 12 * Real.log (11 / 5) + 14 / 9 < (205917 / 500000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := maxprod_mod0_enc0
  obtain ⟨h1lo, h1hi⟩ := concave_knapsack_enc1
  constructor <;> linarith

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `concave_knapsack_bench` -- the benchmark meets EVERY hypothesis of `concave_knapsack` and ATTAINS `B`:
    `Phi(bench) = B`, `sum ell(bench) = M`, its atoms lie in the alphabet and its mean is positive,
    so the main theorem is not vacuous and applies to every optimum.
    conjecture1_proved = False. -/
theorem concave_knapsack_bench :
    ((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_knapsack_w).sum + 12 * Real.log (((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_knapsack_y).sum / 10) = 12 * Real.log (11 / 5) - 50 / 9 ∧
    ((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_knapsack_ell).sum = 10 ∧
    (∀ k ∈ (Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ), 1 ≤ k ∧ k ≤ 6) ∧
    0 < ((Multiset.replicate 8 2 + Multiset.replicate 2 3 : Multiset ℕ).map concave_knapsack_y).sum / 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · norm_num [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    all_goals ring_nf
  · intro k hk
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hk
    omega
  · norm_num [concave_knapsack_w, concave_knapsack_ell, concave_knapsack_gap, concave_knapsack_y, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

/-- `concave_knapsack` -- the GAP-BUDGET PRUNING.  Any multiset of atoms in the alphabet with
    the benchmark's normalisation and at least its value `B` (attained, see
    `concave_knapsack_bench`) obeys the budget sum gamma <= theta <= 205917/500000, hence
    the caps / exclusions / knapsack below.  Conditional pruning only; it does not
    identify the optimum.  conjecture1_proved = False. -/
theorem concave_knapsack (m : Multiset ℕ)
    (hA : ∀ k ∈ m, 1 ≤ k ∧ k ≤ 6)
    (hl : (m.map concave_knapsack_ell).sum = 10)
    (hdom : 0 < (m.map concave_knapsack_y).sum / 10)
    (hB : 12 * Real.log (11 / 5) - 50 / 9 ≤ (m.map concave_knapsack_w).sum + 12 * Real.log ((m.map concave_knapsack_y).sum / 10)) :
    m.count 1 ≤ 1 ∧
      m.count 2 ≤ 9 ∧
      m.count 4 ≤ 2 ∧
      m.count 5 = 0 ∧
      m.count 6 = 0 ∧
      [m.count 1, m.count 2, m.count 4] ∈ [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 0], [0, 2, 1], [0, 3, 0], [0, 3, 1], [0, 4, 0], [0, 4, 1], [0, 5, 0], [0, 5, 1], [0, 6, 0], [0, 7, 0], [0, 8, 0], [0, 9, 0], [1, 0, 0], [1, 1, 0], [1, 2, 0]] := by
  have hbud0 := gapBudget_of_concave m concave_knapsack_w concave_knapsack_ell concave_knapsack_y concave_knapsack_gap (4 / 5)
    (10) _ (12) (2) (fun _ => rfl) (by norm_num) (by norm_num) hdom hl hB
  have hbud : (m.map concave_knapsack_gap).sum ≤ (205917 / 500000 : ℝ) := by
    obtain ⟨ht0, ht1⟩ := concave_knapsack_theta_enc
    linarith
  have hγ : ∀ k ∈ m, 0 ≤ concave_knapsack_gap k := by
    intro k hk
    obtain ⟨h1, h2⟩ := hA k hk
    interval_cases k
    all_goals linarith [concave_knapsack_gap_1, concave_knapsack_gap_2, concave_knapsack_gap_3, concave_knapsack_gap_4, concave_knapsack_gap_5, concave_knapsack_gap_6]
  have hc := gapBudget_count_mul_le m concave_knapsack_gap _ hγ hbud
  have c1 : m.count 1 ≤ 1 :=
    gapBudget_nat_cap 1 (by norm_num) (hc 1 _ concave_knapsack_gap_1) (by norm_num)
  have c2 : m.count 2 ≤ 9 :=
    gapBudget_nat_cap 9 (by norm_num) (hc 2 _ concave_knapsack_gap_2) (by norm_num)
  have c4 : m.count 4 ≤ 2 :=
    gapBudget_nat_cap 2 (by norm_num) (hc 4 _ concave_knapsack_gap_4) (by norm_num)
  have c5 : m.count 5 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 5 _ concave_knapsack_gap_5) (by norm_num))
  have c6 : m.count 6 = 0 :=
    Nat.le_zero.mp (gapBudget_nat_cap 0 (by norm_num) (hc 6 _ concave_knapsack_gap_6) (by norm_num))
  have hkn := gapBudget_knapsack m concave_knapsack_gap (fun k => if k = 1 then (14 / 45) else if k = 2 then (2 / 45) else (8 / 45)) _ hγ hbud {1, 2, 4} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simpa using concave_knapsack_gap_1
    · simpa using concave_knapsack_gap_2
    · simpa using concave_knapsack_gap_4)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at hkn
  norm_num at hkn
  have hdec : ∀ x1 ∈ List.range 2, ∀ x2 ∈ List.range 10, ∀ x4 ∈ List.range 3, x1 * 1400000 + x2 * 200000 + x4 * 800000 ≤ 1853253 →
      [x1, x2, x4] ∈ [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 0], [0, 2, 1], [0, 3, 0], [0, 3, 1], [0, 4, 0], [0, 4, 1], [0, 5, 0], [0, 5, 1], [0, 6, 0], [0, 7, 0], [0, 8, 0], [0, 9, 0], [1, 0, 0], [1, 1, 0], [1, 2, 0]] := by decide
  have hint : ((m.count 1 * 1400000 + m.count 2 * 200000 + m.count 4 * 800000 : ℕ) : ℝ) ≤ 1853253 := by push_cast; linarith
  have ckn := hdec _ (List.mem_range.mpr (Nat.lt_succ_of_le c1)) _ (List.mem_range.mpr (Nat.lt_succ_of_le c2)) _ (List.mem_range.mpr (Nat.lt_succ_of_le c4)) (by exact_mod_cast hint)
  exact ⟨c1, c2, c4, c5, c6, ckn⟩

/-! ### Cross-check (appended by generate.py, not emitter output)

The `N = 3t + 4` pruning in its classical PRODUCT form: a multiset of positive parts with sum
`3t + 4` and product at least `4 * 3^t` (the classical optimum) has no 1s, at most two 2s, at most
one 4, no part >= 5, and the (2s, 4s) counts in the decided list.  Proved by feeding the emitted
`maxprod_mod1` (so the emitted statement is the one the kernel checks against this one). -/
theorem maxprod_mod1_classical (t : ℕ) (m : Multiset ℕ) (hA : ∀ k ∈ m, 1 ≤ k)
    (hsum : m.sum = 3 * t + 4) (hprod : 4 * 3 ^ t ≤ m.prod) :
    m.count 1 = 0 ∧ m.count 2 ≤ 2 ∧ m.count 4 ≤ 1 ∧ (∀ k ∈ m, k < 5) ∧
      [m.count 2, m.count 4] ∈ [[0, 0], [0, 1], [1, 0], [2, 0]] := by
  have hne : ∀ x ∈ m.map (fun k : ℕ => (k : ℝ)), x ≠ 0 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp hx
    have : (1 : ℝ) ≤ k := by exact_mod_cast hA k hk
    positivity
  apply maxprod_mod1 t m hA
  · have h := congrArg (fun n : ℕ => (n : ℝ)) hsum
    simp only [Nat.cast_multiset_sum] at h
    simp only [maxprod_mod1_ell]
    rw [h]
    push_cast
    ring
  · have hw : (m.map maxprod_mod1_w).sum = Real.log ((m.map (fun k : ℕ => (k : ℝ))).prod) := by
      rw [Real.log_multiset_prod hne, Multiset.map_map]
      rfl
    have hp : ((4 * 3 ^ t : ℕ) : ℝ) ≤ ((m.prod : ℕ) : ℝ) := by exact_mod_cast hprod
    rw [Nat.cast_multiset_prod] at hp
    have hl := Real.log_le_log (by positivity) hp
    have h43 : Real.log ((4 * 3 ^ t : ℕ) : ℝ) = Real.log 4 + t * Real.log 3 := by
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rw [hw]
    linarith

end GapBudgetMultiplicity

#print axioms GapBudgetMultiplicity.gapBudget_log_tangent
#print axioms GapBudgetMultiplicity.gapBudget_of_sep
#print axioms GapBudgetMultiplicity.gapBudget_of_concave
#print axioms GapBudgetMultiplicity.gapBudget_count_mul_le
#print axioms GapBudgetMultiplicity.gapBudget_nat_cap
#print axioms GapBudgetMultiplicity.gapBudget_knapsack
#print axioms GapBudgetMultiplicity.maxprod_mod0
#print axioms GapBudgetMultiplicity.maxprod_mod0_bench
#print axioms GapBudgetMultiplicity.maxprod_mod2
#print axioms GapBudgetMultiplicity.maxprod_mod2_bench
#print axioms GapBudgetMultiplicity.maxprod_mod1
#print axioms GapBudgetMultiplicity.maxprod_mod1_bench
#print axioms GapBudgetMultiplicity.concave_sharp
#print axioms GapBudgetMultiplicity.concave_sharp_bench
#print axioms GapBudgetMultiplicity.concave_knapsack
#print axioms GapBudgetMultiplicity.concave_knapsack_bench
#print axioms GapBudgetMultiplicity.maxprod_mod1_tail
#print axioms GapBudgetMultiplicity.maxprod_mod1_classical
