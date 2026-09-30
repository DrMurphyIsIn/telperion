/- telperion 0.1.6 | family SingleCrossingLadder | input-hash 261ed994f649c18c
   133 theorems, 7 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SingleCrossingLadder

set_option linter.unusedVariables false

/-! ## Generic single-crossing ladder (emitted once per file)

`logSum L x = sum kappa * log (1 + beta * x)` over `L = [(kappa, beta), ...]`; `polyEval` is
Horner evaluation of an ascending coefficient list.  The cores below are proved once. -/

noncomputable def logSum : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | p :: L, x => p.1 * Real.log (1 + p.2 * x) + logSum L x

noncomputable def logSumDeriv : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | p :: L, x => p.1 * p.2 / (1 + p.2 * x) + logSumDeriv L x

theorem logSum_zero (L : List (ℝ × ℝ)) : logSum L 0 = 0 := by
  induction L with
  | nil => simp [logSum]
  | cons p L ih => simp [logSum, ih]

theorem hasDerivAt_logSum (L : List (ℝ × ℝ)) (x : ℝ) (h : ∀ p ∈ L, 0 < 1 + p.2 * x) :
    HasDerivAt (logSum L) (logSumDeriv L x) x := by
  induction L with
  | nil => simpa [logSum, logSumDeriv] using hasDerivAt_const x (0 : ℝ)
  | cons p L ih =>
    have hp : 0 < 1 + p.2 * x := h p (by simp)
    have hL : ∀ q ∈ L, 0 < 1 + q.2 * x := fun q hq => h q (by simp [hq])
    have h1 : HasDerivAt (fun y => 1 + p.2 * y) p.2 x := by
      simpa using ((hasDerivAt_id x).const_mul p.2).const_add 1
    have h3 := ((h1.log hp.ne').const_mul p.1).add (ih hL)
    have hfun : logSum (p :: L) = fun y => p.1 * Real.log (1 + p.2 * y) + logSum L y := by
      funext y; rfl
    have hv : logSumDeriv (p :: L) x = p.1 * (p.2 / (1 + p.2 * x)) + logSumDeriv L x := by
      simp only [logSumDeriv]; ring
    rw [hfun, hv]
    exact h3

noncomputable def polyEval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: L, x => a + x * polyEval L x

noncomputable def polyDeriv : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: L, x => polyEval L x + x * polyDeriv L x

theorem hasDerivAt_polyEval (L : List ℝ) (x : ℝ) :
    HasDerivAt (polyEval L) (polyDeriv L x) x := by
  induction L with
  | nil => simpa [polyEval, polyDeriv] using hasDerivAt_const x (0 : ℝ)
  | cons a L ih =>
    have hfun : polyEval (a :: L) = fun y => a + y * polyEval L y := by funext y; rfl
    have h := ((hasDerivAt_id x).mul ih).const_add a
    have hv : polyDeriv (a :: L) x = 1 * polyEval L x + id x * polyDeriv L x := by
      simp [polyDeriv]
    rw [hfun, hv]
    exact h

theorem up_of_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f' x) :
    f a < f b := by
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  have := hpos c hc
  rw [hcs, lt_div_iff₀ (by linarith)] at this
  linarith

theorem down_of_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) (hneg : ∀ x ∈ Set.Ioo a b, f' x < 0) :
    f b < f a := by
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  have := hneg c hc
  rw [hcs, div_lt_iff₀ (by linarith)] at this
  linarith

/-- `N` changes sign once, `+ -> -`, on `S ∩ (0, oo)`: positive up to `a`, negative from
`b` on, strictly decreasing on the crossing cell `[a, b]`. -/
theorem sign_change_of_cell {S : Set ℝ} [S.OrdConnected] {N N' : ℝ → ℝ} {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb : b ∈ S)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt N (N' x) x) (hN' : ∀ x ∈ Set.Icc a b, N' x < 0)
    (hleft : ∀ x ∈ S, 0 < x → x ≤ a → 0 < N x) (hright : ∀ x ∈ S, b ≤ x → N x < 0)
    (h0 : (0 : ℝ) ∈ S) :
    ∃ s, 0 < s ∧ (∀ x ∈ S, 0 < x → x < s → 0 < N x) ∧ (∀ x ∈ S, s < x → N x < 0) := by
  have hS : Set.Icc 0 b ⊆ S := Set.OrdConnected.out ‹_› h0 hb
  have haS : a ∈ S := hS ⟨ha0.le, hab.le⟩
  have hNa : 0 < N a := hleft a haS ha0 le_rfl
  have hNb : N b < 0 := hright b hb le_rfl
  have hcont : ContinuousOn N (Set.Icc a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨s, hs, _⟩ := intermediate_value_Ioo' hab.le hcont ⟨hNb, hNa⟩
  have hNs : N s = 0 := by assumption
  refine ⟨s, by linarith [hs.1], ?_, ?_⟩
  · intro x hx hx0 hxs
    rcases le_or_gt x a with h | h
    · exact hleft x hx hx0 h
    · have := down_of_deriv (f := N) hxs
        (fun y hy => hd y ⟨by linarith [hy.1], by linarith [hy.2, hs.2]⟩)
        (fun y hy => hN' y ⟨by linarith [hy.1], by linarith [hy.2, hs.2]⟩)
      linarith
  · intro x hx hsx
    rcases le_or_gt b x with h | h
    · exact hright x hx h
    · have := down_of_deriv (f := N) hsx
        (fun y hy => hd y ⟨by linarith [hy.1, hs.1], by linarith [hy.2]⟩)
        (fun y hy => hN' y ⟨by linarith [hy.1, hs.1], by linarith [hy.2]⟩)
      linarith

/-- Single crossing: `D 0 = 0`, `D' * P = N` with `P > 0`, `N` changes sign once `+ -> -`
at `s`, and `D lo > 0 > D hi`.  Then `D` has exactly one zero `c` on `S ∩ (0, oo)`, it lies
in `(lo, hi)`, and `D > 0` before it, `D < 0` after it. -/
theorem single_crossing_core {S : Set ℝ} [S.OrdConnected] (h0 : (0 : ℝ) ∈ S)
    {D D' P N : ℝ → ℝ} (hD0 : D 0 = 0)
    (hd : ∀ x ∈ S, HasDerivAt D (D' x) x)
    (hfac : ∀ x ∈ S, 0 < x → D' x * P x = N x) (hP : ∀ x ∈ S, 0 < x → 0 < P x)
    {s : ℝ} (hs : 0 < s) (hNpos : ∀ x ∈ S, 0 < x → x < s → 0 < N x)
    (hNneg : ∀ x ∈ S, s < x → N x < 0)
    {lo hi : ℝ} (hlo0 : 0 < lo) (hlohi : lo < hi) (hhi : hi ∈ S)
    (hDlo : 0 < D lo) (hDhi : D hi < 0) :
    ∃ c ∈ Set.Ioo lo hi, D c = 0 ∧
      ∀ x ∈ S, 0 < x → (x < c → 0 < D x) ∧ (c < x → D x < 0) := by
  have hsub : ∀ a ∈ S, ∀ b ∈ S, Set.Icc a b ⊆ S :=
    fun a ha b hb => Set.OrdConnected.out ‹_› ha hb
  have hpos' : ∀ x ∈ S, 0 < x → 0 < N x → 0 < D' x := by
    intro x hx hx0 hN
    have h1 := hfac x hx hx0; have h2 := hP x hx hx0
    by_contra hc; have hc := not_lt.mp hc
    nlinarith
  have hneg' : ∀ x ∈ S, 0 < x → N x < 0 → D' x < 0 := by
    intro x hx hx0 hN
    have h1 := hfac x hx hx0; have h2 := hP x hx hx0
    by_contra hc; have hc := not_lt.mp hc
    nlinarith
  have up : ∀ a ∈ S, ∀ b ∈ S, 0 ≤ a → a < b → b ≤ s → D a < D b := by
    intro a ha b hb ha0 hab hbs
    refine up_of_deriv hab (fun x hx => hd x (hsub a ha b hb hx)) ?_
    intro x hx
    have hxS := hsub a ha b hb (Set.Ioo_subset_Icc_self hx)
    exact hpos' x hxS (by linarith [hx.1]) (hNpos x hxS (by linarith [hx.1]) (by linarith [hx.2]))
  have down : ∀ a ∈ S, ∀ b ∈ S, s ≤ a → a < b → D b < D a := by
    intro a ha b hb hsa hab
    refine down_of_deriv hab (fun x hx => hd x (hsub a ha b hb hx)) ?_
    intro x hx
    have hxS := hsub a ha b hb (Set.Ioo_subset_Icc_self hx)
    exact hneg' x hxS (by linarith [hx.1]) (hNneg x hxS (by linarith [hx.1]))
  have hshi : s < hi := by
    by_contra hc; have hc := not_lt.mp hc
    have := up 0 h0 hi hhi le_rfl (by linarith) hc
    linarith
  set m := max s lo with hm
  have hmS : m ∈ S := hsub 0 h0 hi hhi ⟨by positivity, by
    rcases le_total s lo with h | h
    · simp [hm, h]; linarith
    · simp [hm, h]; linarith⟩
  have hDm : 0 < D m := by
    rcases le_total s lo with h | h
    · simpa [hm, h] using hDlo
    · have hms : m = s := by simp [hm, h]
      rw [hms]
      rw [hms] at hmS
      have := up 0 h0 s hmS le_rfl hs le_rfl
      linarith
  have hmhi : m < hi := max_lt hshi hlohi
  have hcont : ContinuousOn D (Set.Icc m hi) :=
    fun x hx => (hd x (hsub m hmS hi hhi hx)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hDc⟩ := intermediate_value_Ioo' hmhi.le hcont ⟨hDhi, hDm⟩
  have hcS : c ∈ S := hsub m hmS hi hhi (Set.Ioo_subset_Icc_self hc)
  have hsm : s ≤ m := le_max_left _ _
  have hlom : lo ≤ m := le_max_right _ _
  refine ⟨c, ⟨by linarith [hc.1], hc.2⟩, hDc, ?_⟩
  intro x hx hx0
  constructor
  · intro hxc
    rcases le_or_gt x s with h | h
    · have := up 0 h0 x hx le_rfl hx0 h
      linarith
    · have := down x hx c hcS h.le hxc
      linarith
  · intro hcx
    have := down c hcS x hx (by linarith [hc.1]) hcx
    linarith

/-- Domination: `D 0 = 0` and `N < 0` on `S ∩ (0, oo)` give `D < 0` there. -/
theorem dominated_core {S : Set ℝ} [S.OrdConnected] (h0 : (0 : ℝ) ∈ S)
    {D D' P N : ℝ → ℝ} (hD0 : D 0 = 0)
    (hd : ∀ x ∈ S, HasDerivAt D (D' x) x)
    (hfac : ∀ x ∈ S, 0 < x → D' x * P x = N x) (hP : ∀ x ∈ S, 0 < x → 0 < P x)
    (hNneg : ∀ x ∈ S, 0 < x → N x < 0) :
    ∀ x ∈ S, 0 < x → D x < 0 := by
  intro x hx hx0
  have hsub : Set.Icc 0 x ⊆ S := Set.OrdConnected.out ‹_› h0 hx
  have := down_of_deriv hx0 (fun y hy => hd y (hsub hy)) (by
    intro y hy
    have hyS := hsub (Set.Ioo_subset_Icc_self hy)
    have h1 := hfac y hyS hy.1; have h2 := hP y hyS hy.1; have h3 := hNneg y hyS hy.1
    by_contra hc; have hc := not_lt.mp hc
    nlinarith)
  linarith

/-- The best-member ladder.  Consecutive members `F j`, `F (j+1)` (`a ≤ j ≤ J`) cross at
`Λ j` (`F j` ahead before, `F (j+1)` ahead after) and the breakpoints are nondecreasing.
Then on `(Λ (j-1), Λ j)` (open at the ends of the window) `F j` is the unique maximum of
`F a, ..., F (J+1)`. -/
theorem ladder_core {S : Set ℝ} {F : ℕ → ℝ → ℝ} {Λ : ℕ → ℝ} {a J : ℕ}
    (hcross : ∀ j, a ≤ j → j ≤ J → ∀ x ∈ S, 0 < x →
      (x < Λ j → F (j + 1) x < F j x) ∧ (Λ j < x → F j x < F (j + 1) x))
    (hmono : ∀ j, a ≤ j → j < J → Λ j ≤ Λ (j + 1)) :
    ∀ j, a ≤ j → j ≤ J + 1 → ∀ x ∈ S, 0 < x →
      (j = a ∨ Λ (j - 1) < x) → (j = J + 1 ∨ x < Λ j) →
      ∀ k, a ≤ k → k ≤ J + 1 → k ≠ j → F k x < F j x := by
  have hmon : ∀ i i', a ≤ i → i ≤ i' → i' ≤ J → Λ i ≤ Λ i' := by
    intro i i' hi hii' hi'
    induction i', hii' using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact le_trans (ih (by omega)) (hmono k (by omega) (by omega))
  intro j hja hjJ x hx hx0 hleft hright k hka hkJ hkj
  rcases lt_or_gt_of_ne hkj with hkj | hkj
  · have hbelow : ∀ i, a ≤ i → i < j → Λ i < x := by
      intro i hia hij
      rcases hleft with h | h
      · omega
      · exact lt_of_le_of_lt (hmon i (j - 1) hia (by omega) (by omega)) h
    have climb : ∀ i, k ≤ i → i ≤ j → F k x ≤ F i x ∧ (k < i → F k x < F i x) := by
      intro i hki hij
      induction i, hki using Nat.le_induction with
      | base => exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
      | succ m hm ih =>
        have hstep := (hcross m (by omega) (by omega) x hx hx0).2 (hbelow m (by omega) (by omega))
        have ih' := ih (by omega)
        exact ⟨le_trans ih'.1 hstep.le, fun _ => lt_of_le_of_lt ih'.1 hstep⟩
    exact (climb j hkj.le le_rfl).2 hkj
  · have habove : ∀ i, j ≤ i → i ≤ J → x < Λ i := by
      intro i hji hiJ
      rcases hright with h | h
      · omega
      · exact lt_of_lt_of_le h (hmon j i hja hji hiJ)
    have desc : ∀ i, j ≤ i → i ≤ k → F i x ≤ F j x ∧ (j < i → F i x < F j x) := by
      intro i hji hik
      induction i, hji using Nat.le_induction with
      | base => exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
      | succ m hm ih =>
        have hstep := (hcross m (by omega) (by omega) x hx hx0).1 (habove m hm (by omega))
        have ih' := ih (by omega)
        exact ⟨le_trans hstep.le ih'.1, fun _ => lt_of_lt_of_le hstep ih'.1⟩
    exact (desc k hkj.le le_rfl).2 hkj

/-! ## Instance `arm_ladder`

Family `F_j(x) = ((j - 1)/(2*j + 1)) log(1 + (1/2) x) + (1/(2*j + 1)) log(1 + ((2*j + 1)/(2*j + 2)) x)` on `S = Ici 0`, members j = 1..7.
Pairs: 2 dominated, 4 crossing (brackets 3: (861/2000, 43051/100000), 4: (87247/100000, 5453/6250), 5: (119239/100000, 2981/2500), 6: (143559/100000, 3589/2500)).
conjecture1_proved = False. -/

noncomputable def arm_ladder_terms (j : ℕ) : List (ℝ × ℝ) :=
  [(((-1 : ℝ) + (j : ℝ)) / ((1 : ℝ) + (2 : ℝ) * (j : ℝ)), ((1 : ℝ)) / ((2 : ℝ))), (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * (j : ℝ)), ((1 : ℝ) + (2 : ℝ) * (j : ℝ)) / ((2 : ℝ) + (2 : ℝ) * (j : ℝ)))]

noncomputable def arm_ladder_F (j : ℕ) (x : ℝ) : ℝ := logSum (arm_ladder_terms j) x

/-- The domain `S`. -/
abbrev arm_ladder_S : Set ℝ := Set.Ici (0 : ℝ)

theorem arm_ladder_argpos (j : ℕ) (hj : 1 ≤ j ∧ j ≤ 7) :
    ∀ x ∈ arm_ladder_S, ∀ p ∈ arm_ladder_terms j, 0 < 1 + p.2 * x := by
  obtain ⟨hj1, hj2⟩ := hj
  intro x hx p hp
  have hx0 : (0 : ℝ) ≤ x := (Set.mem_Ici.mp hx)
  interval_cases j <;>
  · simp only [arm_ladder_terms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> norm_num <;> nlinarith

/-! ### Pair j = 1: `D = F 1 - F 2`, `D' * P = N`,
`N = -x**2/48 - x/30 - 1/60` -/

theorem arm_ladder_p1_P_pos (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    0 < (1 + (1 / 2 : ℝ) * x) * (1 + (3 / 4 : ℝ) * x) * (1 + (5 / 6 : ℝ) * x) := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (3 / 4 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (5 / 6 : ℝ) * x := by nlinarith
  positivity

theorem arm_ladder_p1_fac (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    (logSumDeriv (arm_ladder_terms 1) x - logSumDeriv (arm_ladder_terms 2) x) *
      ((1 + (1 / 2 : ℝ) * x) * (1 + (3 / 4 : ℝ) * x) * (1 + (5 / 6 : ℝ) * x)) = polyEval [(-1 / 60 : ℝ), (-1 / 30 : ℝ), (-1 / 48 : ℝ)] x := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (3 / 4 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (5 / 6 : ℝ) * x := by nlinarith
  have hne0 : 1 + (1 / 2 : ℝ) * x ≠ 0 := by nlinarith [hpos0]
  have hne1 : 1 + (3 / 4 : ℝ) * x ≠ 0 := by nlinarith [hpos1]
  have hne2 : 1 + (5 / 6 : ℝ) * x ≠ 0 := by nlinarith [hpos2]
  simp only [logSumDeriv, arm_ladder_terms, polyEval]
  norm_num at hne0 hne1 hne2 ⊢
  field_simp
  ring

theorem arm_ladder_p1_R0 (x : ℝ) (hs : 0 ≤ x - (0 : ℝ)) :
    polyEval [(-1 / 60 : ℝ), (-1 / 30 : ℝ), (-1 / 48 : ℝ)] x < 0 := by
  simp only [polyEval]
  linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]

/-- `F 2` beats `F 1` on all of `S ∩ (0, oo)` (no crossing). -/
theorem arm_ladder_p1_dom : ∀ x ∈ arm_ladder_S, 0 < x → arm_ladder_F 1 x < arm_ladder_F 2 x := by
  have hD0 : arm_ladder_F 1 0 - arm_ladder_F 2 0 = 0 := by simp [arm_ladder_F, logSum_zero]
  have hd : ∀ x ∈ arm_ladder_S, HasDerivAt (fun y => arm_ladder_F 1 y - arm_ladder_F 2 y)
      (logSumDeriv (arm_ladder_terms 1) x - logSumDeriv (arm_ladder_terms 2) x) x :=
    fun x hx => (hasDerivAt_logSum _ x (arm_ladder_argpos 1 (by norm_num) x hx)).sub
      (hasDerivAt_logSum _ x (arm_ladder_argpos 2 (by norm_num) x hx))
  have hN : ∀ x ∈ arm_ladder_S, 0 < x → polyEval [(-1 / 60 : ℝ), (-1 / 30 : ℝ), (-1 / 48 : ℝ)] x < 0 := by
    intro x hx hx0
    exact arm_ladder_p1_R0 x (by linarith)
  intro x hx hx0
  have := dominated_core (S := arm_ladder_S) (P := fun x => (1 + (1 / 2 : ℝ) * x) * (1 + (3 / 4 : ℝ) * x) * (1 + (5 / 6 : ℝ) * x))
    (Set.self_mem_Ici) hD0 hd arm_ladder_p1_fac arm_ladder_p1_P_pos hN x hx hx0
  linarith

/-! ### Pair j = 2: `D = F 2 - F 3`, `D' * P = N`,
`N = -x**2/96 - 3*x/280 - 1/840` -/

theorem arm_ladder_p2_P_pos (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    0 < (1 + (1 / 2 : ℝ) * x) * (1 + (5 / 6 : ℝ) * x) * (1 + (7 / 8 : ℝ) * x) := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (5 / 6 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (7 / 8 : ℝ) * x := by nlinarith
  positivity

theorem arm_ladder_p2_fac (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    (logSumDeriv (arm_ladder_terms 2) x - logSumDeriv (arm_ladder_terms 3) x) *
      ((1 + (1 / 2 : ℝ) * x) * (1 + (5 / 6 : ℝ) * x) * (1 + (7 / 8 : ℝ) * x)) = polyEval [(-1 / 840 : ℝ), (-3 / 280 : ℝ), (-1 / 96 : ℝ)] x := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (5 / 6 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (7 / 8 : ℝ) * x := by nlinarith
  have hne0 : 1 + (1 / 2 : ℝ) * x ≠ 0 := by nlinarith [hpos0]
  have hne1 : 1 + (5 / 6 : ℝ) * x ≠ 0 := by nlinarith [hpos1]
  have hne2 : 1 + (7 / 8 : ℝ) * x ≠ 0 := by nlinarith [hpos2]
  simp only [logSumDeriv, arm_ladder_terms, polyEval]
  norm_num at hne0 hne1 hne2 ⊢
  field_simp
  ring

theorem arm_ladder_p2_R0 (x : ℝ) (hs : 0 ≤ x - (0 : ℝ)) :
    polyEval [(-1 / 840 : ℝ), (-3 / 280 : ℝ), (-1 / 96 : ℝ)] x < 0 := by
  simp only [polyEval]
  linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]

/-- `F 3` beats `F 2` on all of `S ∩ (0, oo)` (no crossing). -/
theorem arm_ladder_p2_dom : ∀ x ∈ arm_ladder_S, 0 < x → arm_ladder_F 2 x < arm_ladder_F 3 x := by
  have hD0 : arm_ladder_F 2 0 - arm_ladder_F 3 0 = 0 := by simp [arm_ladder_F, logSum_zero]
  have hd : ∀ x ∈ arm_ladder_S, HasDerivAt (fun y => arm_ladder_F 2 y - arm_ladder_F 3 y)
      (logSumDeriv (arm_ladder_terms 2) x - logSumDeriv (arm_ladder_terms 3) x) x :=
    fun x hx => (hasDerivAt_logSum _ x (arm_ladder_argpos 2 (by norm_num) x hx)).sub
      (hasDerivAt_logSum _ x (arm_ladder_argpos 3 (by norm_num) x hx))
  have hN : ∀ x ∈ arm_ladder_S, 0 < x → polyEval [(-1 / 840 : ℝ), (-3 / 280 : ℝ), (-1 / 96 : ℝ)] x < 0 := by
    intro x hx hx0
    exact arm_ladder_p2_R0 x (by linarith)
  intro x hx hx0
  have := dominated_core (S := arm_ladder_S) (P := fun x => (1 + (1 / 2 : ℝ) * x) * (1 + (5 / 6 : ℝ) * x) * (1 + (7 / 8 : ℝ) * x))
    (Set.self_mem_Ici) hD0 hd arm_ladder_p2_fac arm_ladder_p2_P_pos hN x hx hx0
  linarith

/-! ### Pair j = 3: `D = F 3 - F 4`, `D' * P = N`,
`N = -x**2/160 - x/210 + 1/840` -/

theorem arm_ladder_p3_P_pos (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    0 < (1 + (1 / 2 : ℝ) * x) * (1 + (7 / 8 : ℝ) * x) * (1 + (9 / 10 : ℝ) * x) := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (7 / 8 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (9 / 10 : ℝ) * x := by nlinarith
  positivity

theorem arm_ladder_p3_fac (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    (logSumDeriv (arm_ladder_terms 3) x - logSumDeriv (arm_ladder_terms 4) x) *
      ((1 + (1 / 2 : ℝ) * x) * (1 + (7 / 8 : ℝ) * x) * (1 + (9 / 10 : ℝ) * x)) = polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (7 / 8 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (9 / 10 : ℝ) * x := by nlinarith
  have hne0 : 1 + (1 / 2 : ℝ) * x ≠ 0 := by nlinarith [hpos0]
  have hne1 : 1 + (7 / 8 : ℝ) * x ≠ 0 := by nlinarith [hpos1]
  have hne2 : 1 + (9 / 10 : ℝ) * x ≠ 0 := by nlinarith [hpos2]
  simp only [logSumDeriv, arm_ladder_terms, polyEval]
  norm_num at hne0 hne1 hne2 ⊢
  field_simp
  ring

theorem arm_ladder_p3_L0 (x : ℝ) (hs : 0 ≤ x - (0 : ℝ)) (ht : 0 ≤ (1 / 8 : ℝ) - x) :
    0 < polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x := by
  simp only [polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem arm_ladder_p3_R0 (x : ℝ) (hs : 0 ≤ x - (1 / 4 : ℝ)) :
    polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x < 0 := by
  simp only [polyEval]
  linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]

theorem arm_ladder_p3_C (x : ℝ) (hs : 0 ≤ x - (1 / 8 : ℝ)) (ht : 0 ≤ (1 / 4 : ℝ) - x) :
    polyDeriv [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x < 0 := by
  simp only [polyDeriv, polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem arm_ladder_p3_sign : ∃ s, 0 < s ∧
    (∀ x ∈ arm_ladder_S, 0 < x → x < s → 0 < polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x) ∧
    (∀ x ∈ arm_ladder_S, s < x → polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x < 0) := by
  have hleft : ∀ x ∈ arm_ladder_S, 0 < x → x ≤ (1 / 8 : ℝ) → 0 < polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x := by
    intro x hx hx0 hxa
    exact arm_ladder_p3_L0 x (by linarith) (by linarith)
  have hright : ∀ x ∈ arm_ladder_S, (1 / 4 : ℝ) ≤ x → polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x < 0 := by
    intro x hx hxb
    exact arm_ladder_p3_R0 x (by linarith)
  exact sign_change_of_cell (S := arm_ladder_S) (N' := polyDeriv [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)])
    (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num))
    (fun x _ => hasDerivAt_polyEval [(1 / 840 : ℝ), (-1 / 210 : ℝ), (-1 / 160 : ℝ)] x)
    (fun x hx => arm_ladder_p3_C x (by linarith [hx.1]) (by linarith [hx.2]))
    hleft hright (Set.self_mem_Ici)

/-- `arm_ladder_p3_vlo_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (4861 / 4000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [31362974910341003774643930177208475977312460409193762603824567250104441891446569122472272832108193931424152941797387408257716247/160877170351189280281136793124864000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 31362974910341003774683733320891628106428043287248712582942536782918251362711867399520562292738864547167566452326659672711595479/160877170351189280281136793124864000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vlo_a0 :
    (31362974910341003774643930177208475977312460409193762603824567250104441891446569122472272832108193931424152941797387408257716247 / 160877170351189280281136793124864000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (4861 / 4000) ∧
      Real.log (4861 / 4000) ≤ (31362974910341003774683733320891628106428043287248712582942536782918251362711867399520562292738864547167566452326659672711595479 / 160877170351189280281136793124864000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(861 / 4000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(861 / 4000)) = (4861 / 4000) by norm_num] at h
  generalize Real.log (4861 / 4000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p3_vlo_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 2)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [35924703057241649235421/88601219586316881100800, 35924703098499807205021/88601219586316881100800], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vlo_a1 :
    (35924703057241649235421 / 88601219586316881100800 : ℝ) ≤ Real.log (3 / 2) ∧
      Real.log (3 / 2) ≤ (35924703098499807205021 / 88601219586316881100800 : ℝ) := by
  have hx : |((-(1 / 2)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(1 / 2)) = (3 / 2) by norm_num] at h
  generalize Real.log (3 / 2) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p3_vlo_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (22027 / 24000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-5395194894764599428704762624681471675128063845326082658516571241358438988189653574040109527116819788090493710351958903117585047352669660817253262531157703/62892159518828781475499353295909401553873405019425555349504000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1798398298254866476234920874893823820590627504559600008981566223766168517303397947278479078038566780398867617744443443430696068380647464334204066181056557/20964053172942927158499784431969800517957801673141851783168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vlo_a2 :
    (-(5395194894764599428704762624681471675128063845326082658516571241358438988189653574040109527116819788090493710351958903117585047352669660817253262531157703 / 62892159518828781475499353295909401553873405019425555349504000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (22027 / 24000) ∧
      Real.log (22027 / 24000) ≤ (-(1798398298254866476234920874893823820590627504559600008981566223766168517303397947278479078038566780398867617744443443430696068380647464334204066181056557 / 20964053172942927158499784431969800517957801673141851783168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((1973 / 24000) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (1973 / 24000) = (22027 / 24000) by norm_num] at h
  generalize Real.log (22027 / 24000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p3_vlo_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (22027 / 16000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [221159194837906822290536712534270872885306907073219890020798996345057171129913810685558795201714982331004569186128452065706564479120633731010214112157265267/691813754707116596230492886255003417092607455213681108844544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 73719731720019235294884395404022843641982506370419039646472531538572146309662622579936730141575765415612456204811122122262343247812877892323755272008377873/230604584902372198743497628751667805697535818404560369614848000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vlo_a3 :
    (221159194837906822290536712534270872885306907073219890020798996345057171129913810685558795201714982331004569186128452065706564479120633731010214112157265267 / 691813754707116596230492886255003417092607455213681108844544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (22027 / 16000) ∧
      Real.log (22027 / 16000) ≤ (73719731720019235294884395404022843641982506370419039646472531538572146309662622579936730141575765415612456204811122122262343247812877892323755272008377873 / 230604584902372198743497628751667805697535818404560369614848000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p3_vlo_a2
  have hfold : Real.log (22027 / 16000) = Real.log (3 / 2) + Real.log (22027 / 24000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((22027 / 24000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p3_vlo_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (27749 / 30000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-85799095948288182933842833773193874516167142959451194143747193004693526240549008754665251498553724944286051053623109330750660887517285812370866149571810834051/1100022564517543092580064115004800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -28599698649429394311280944591064624778108208310829971301434887326821162552466018875279946362176238558159292336140868862106558064793254089161147594646999954369/366674188172514364193354705001600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vlo_a4 :
    (-(85799095948288182933842833773193874516167142959451194143747193004693526240549008754665251498553724944286051053623109330750660887517285812370866149571810834051 / 1100022564517543092580064115004800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (27749 / 30000) ∧
      Real.log (27749 / 30000) ≤ (-(28599698649429394311280944591064624778108208310829971301434887326821162552466018875279946362176238558159292336140868862106558064793254089161147594646999954369 / 366674188172514364193354705001600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((2251 / 30000) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (2251 / 30000) = (27749 / 30000) by norm_num] at h
  generalize Real.log (27749 / 30000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p3_vlo_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (27749 / 20000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [18959035359816093343391833411951447168165747979648515031188470105016130197865841644491302552707698687142839418230362666802596795393827062506796518443588903471/57895924448291741714740216579200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 6319678462258661350618326543464945809810838864967102854509183561746254602501788480248423875674934812728458298097849007257549575537197153202044863439631581349/19298641482763913904913405526400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vlo_a5 :
    (18959035359816093343391833411951447168165747979648515031188470105016130197865841644491302552707698687142839418230362666802596795393827062506796518443588903471 / 57895924448291741714740216579200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (27749 / 20000) ∧
      Real.log (27749 / 20000) ≤ (6319678462258661350618326543464945809810838864967102854509183561746254602501788480248423875674934812728458298097849007257549575537197153202044863439631581349 / 19298641482763913904913405526400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p3_vlo_a4
  have hfold : Real.log (27749 / 20000) = Real.log (3 / 2) + Real.log (27749 / 30000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((27749 / 30000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p3_vhi_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (243051 / 200000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [583908677310680778992760437905616951641014131757851982499618746547803949480234559397921674510745787462376885300089762491394235967702155641280892160376308154630925876931236394886729141371/2995111067383690375483883520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 583908677310680778993502041044384605896805102439911949493787232546963457905597482943678101755014853370173964109410664471131686421459776356071050831903952679628098672676252029627290604347/2995111067383690375483883520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vhi_a0 :
    (583908677310680778992760437905616951641014131757851982499618746547803949480234559397921674510745787462376885300089762491394235967702155641280892160376308154630925876931236394886729141371 / 2995111067383690375483883520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (243051 / 200000) ∧
      Real.log (243051 / 200000) ≤ (583908677310680778993502041044384605896805102439911949493787232546963457905597482943678101755014853370173964109410664471131686421459776356071050831903952679628098672676252029627290604347 / 2995111067383690375483883520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(43051 / 200000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(43051 / 200000)) = (243051 / 200000) by norm_num] at h
  generalize Real.log (243051 / 200000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p3_vhi_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (367119 / 400000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-1242736752546777308577376539603938601902527428279376696244956492517789719761098432137900218640225085882324400874513857148467255306684825890002259720400629023124036477121315081360474692200367552041/14487741556120375338769865222526074880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -414245584182259102859125513201312850956463927532769630425957413203013333015931538695938886399031428638726880713291076257905303746695582294400646245628109131129033496010973787691940549948025862179/4829247185373458446256621740842024960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vhi_a1 :
    (-(1242736752546777308577376539603938601902527428279376696244956492517789719761098432137900218640225085882324400874513857148467255306684825890002259720400629023124036477121315081360474692200367552041 / 14487741556120375338769865222526074880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (367119 / 400000) ∧
      Real.log (367119 / 400000) ≤ (-(414245584182259102859125513201312850956463927532769630425957413203013333015931538695938886399031428638726880713291076257905303746695582294400646245628109131129033496010973787691940549948025862179 / 4829247185373458446256621740842024960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((32881 / 400000) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (32881 / 400000) = (367119 / 400000) by norm_num] at h
  generalize Real.log (367119 / 400000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p3_vhi_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (1101357 / 800000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [171538405197818997758562118260094411248054539693356418657594203980822602971811169180077769679991663485839837004647634920427138692345006448518434825170347073217628278625136478468130566955541942517/536583020597050938472957971204669440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 4631536947087493322686020734056983712730608217401691108722127760390960000952205383912183340802905714083819357860126771226284088759913253116798061263115672606612899511967078636924178350155922413463/14487741556120375338769865222526074880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vhi_a2 :
    (171538405197818997758562118260094411248054539693356418657594203980822602971811169180077769679991663485839837004647634920427138692345006448518434825170347073217628278625136478468130566955541942517 / 536583020597050938472957971204669440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (1101357 / 800000) ∧
      Real.log (1101357 / 800000) ≤ (4631536947087493322686020734056983712730608217401691108722127760390960000952205383912183340802905714083819357860126771226284088759913253116798061263115672606612899511967078636924178350155922413463 / 14487741556120375338769865222526074880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p3_vhi_a1
  have hfold : Real.log (1101357 / 800000) = Real.log (3 / 2) + Real.log (367119 / 400000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((367119 / 400000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p3_vhi_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (1387459 / 1500000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-9977585884173208407054117222523150206059445867545071952144774397084153969093728171596351970733699777973724473951451766046263740229621567933042316009451871794959111157492168008209086702183860916298040025814537421/127932379172054620105615979053080081939697265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -3325861961391069469018039074174383394989024525216415890418787475456573530074193184899537883310466034016024746965575691398778107348663139458828443030492779374525704458198033698661396820600464935526229206302196399/42644126390684873368538659684360027313232421875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vhi_a3 :
    (-(9977585884173208407054117222523150206059445867545071952144774397084153969093728171596351970733699777973724473951451766046263740229621567933042316009451871794959111157492168008209086702183860916298040025814537421 / 127932379172054620105615979053080081939697265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (1387459 / 1500000) ∧
      Real.log (1387459 / 1500000) ≤ (-(3325861961391069469018039074174383394989024525216415890418787475456573530074193184899537883310466034016024746965575691398778107348663139458828443030492779374525704458198033698661396820600464935526229206302196399 / 42644126390684873368538659684360027313232421875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((112541 / 1500000) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (112541 / 1500000) = (1387459 / 1500000) by norm_num] at h
  generalize Real.log (1387459 / 1500000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p3_vhi_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (1387459 / 1000000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [5990917795329343329968918143094586918034740641576862176689780216601965496045695504274221668185080931749757400224942397455384285147164115785574948810648382333320847104478619974826100601587707888969380276308521148797/18294330221603810675103085004590451717376708984375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1996972601282768230464609143580191230845642828394909128458324317121497542801319085496866082686603357135708461183922676129974730649141171057387532646639532549442824262477681181091420254654133514219749223498785914943/6098110073867936891701028334863483905792236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p3_vhi_a4 :
    (5990917795329343329968918143094586918034740641576862176689780216601965496045695504274221668185080931749757400224942397455384285147164115785574948810648382333320847104478619974826100601587707888969380276308521148797 / 18294330221603810675103085004590451717376708984375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (1387459 / 1000000) ∧
      Real.log (1387459 / 1000000) ≤ (1996972601282768230464609143580191230845642828394909128458324317121497542801319085496866082686603357135708461183922676129974730649141171057387532646639532549442824262477681181091420254654133514219749223498785914943 / 6098110073867936891701028334863483905792236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p3_vhi_a3
  have hfold : Real.log (1387459 / 1000000) = Real.log (3 / 2) + Real.log (1387459 / 1500000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((1387459 / 1500000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

theorem arm_ladder_p3_vlo : 0 < arm_ladder_F 3 (861 / 2000 : ℝ) - arm_ladder_F 4 (861 / 2000 : ℝ) := by
  have h0 := arm_ladder_p3_vlo_a0
  have h1 := arm_ladder_p3_vlo_a1
  have h2 := arm_ladder_p3_vlo_a2
  have h3 := arm_ladder_p3_vlo_a3
  have h4 := arm_ladder_p3_vlo_a4
  have h5 := arm_ladder_p3_vlo_a5
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

theorem arm_ladder_p3_vhi : arm_ladder_F 3 (43051 / 100000 : ℝ) - arm_ladder_F 4 (43051 / 100000 : ℝ) < 0 := by
  have h0 := arm_ladder_p3_vhi_a0
  have h1 := arm_ladder_p3_vlo_a1
  have h2 := arm_ladder_p3_vhi_a1
  have h3 := arm_ladder_p3_vhi_a2
  have h4 := arm_ladder_p3_vhi_a3
  have h5 := arm_ladder_p3_vhi_a4
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

/-- (a) `F 3` and `F 4` cross EXACTLY ONCE on `S ∩ (0, oo)`, at a point of
`(861/2000, 43051/100000)`: `F 3` is ahead before it, `F 4` after it. -/
theorem arm_ladder_p3_cross : ∃ c ∈ Set.Ioo ((861 / 2000 : ℝ)) ((43051 / 100000 : ℝ)),
    arm_ladder_F 3 c = arm_ladder_F 4 c ∧ ∀ x ∈ arm_ladder_S, 0 < x →
      (x < c → arm_ladder_F 4 x < arm_ladder_F 3 x) ∧ (c < x → arm_ladder_F 3 x < arm_ladder_F 4 x) := by
  have hD0 : arm_ladder_F 3 0 - arm_ladder_F 4 0 = 0 := by simp [arm_ladder_F, logSum_zero]
  have hd : ∀ x ∈ arm_ladder_S, HasDerivAt (fun y => arm_ladder_F 3 y - arm_ladder_F 4 y)
      (logSumDeriv (arm_ladder_terms 3) x - logSumDeriv (arm_ladder_terms 4) x) x :=
    fun x hx => (hasDerivAt_logSum _ x (arm_ladder_argpos 3 (by norm_num) x hx)).sub
      (hasDerivAt_logSum _ x (arm_ladder_argpos 4 (by norm_num) x hx))
  obtain ⟨s, hs, hNp, hNn⟩ := arm_ladder_p3_sign
  obtain ⟨c, hc, hDc, hsg⟩ := single_crossing_core (S := arm_ladder_S)
    (P := fun x => (1 + (1 / 2 : ℝ) * x) * (1 + (7 / 8 : ℝ) * x) * (1 + (9 / 10 : ℝ) * x)) (Set.self_mem_Ici) hD0 hd arm_ladder_p3_fac arm_ladder_p3_P_pos
    hs hNp hNn (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num)) arm_ladder_p3_vlo arm_ladder_p3_vhi
  refine ⟨c, hc, by linarith, fun x hx hx0 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := (hsg x hx hx0).1 h; linarith
  · have := (hsg x hx hx0).2 h; linarith

/-! ### Pair j = 4: `D = F 4 - F 5`, `D' * P = N`,
`N = -x**2/240 - x/396 + 1/660` -/

theorem arm_ladder_p4_P_pos (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    0 < (1 + (1 / 2 : ℝ) * x) * (1 + (9 / 10 : ℝ) * x) * (1 + (11 / 12 : ℝ) * x) := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (9 / 10 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (11 / 12 : ℝ) * x := by nlinarith
  positivity

theorem arm_ladder_p4_fac (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    (logSumDeriv (arm_ladder_terms 4) x - logSumDeriv (arm_ladder_terms 5) x) *
      ((1 + (1 / 2 : ℝ) * x) * (1 + (9 / 10 : ℝ) * x) * (1 + (11 / 12 : ℝ) * x)) = polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (9 / 10 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (11 / 12 : ℝ) * x := by nlinarith
  have hne0 : 1 + (1 / 2 : ℝ) * x ≠ 0 := by nlinarith [hpos0]
  have hne1 : 1 + (9 / 10 : ℝ) * x ≠ 0 := by nlinarith [hpos1]
  have hne2 : 1 + (11 / 12 : ℝ) * x ≠ 0 := by nlinarith [hpos2]
  simp only [logSumDeriv, arm_ladder_terms, polyEval]
  norm_num at hne0 hne1 hne2 ⊢
  field_simp
  ring

theorem arm_ladder_p4_L0 (x : ℝ) (hs : 0 ≤ x - (0 : ℝ)) (ht : 0 ≤ (1 / 4 : ℝ) - x) :
    0 < polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x := by
  simp only [polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem arm_ladder_p4_R0 (x : ℝ) (hs : 0 ≤ x - (3 / 8 : ℝ)) :
    polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x < 0 := by
  simp only [polyEval]
  linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]

theorem arm_ladder_p4_C (x : ℝ) (hs : 0 ≤ x - (1 / 4 : ℝ)) (ht : 0 ≤ (3 / 8 : ℝ) - x) :
    polyDeriv [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x < 0 := by
  simp only [polyDeriv, polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem arm_ladder_p4_sign : ∃ s, 0 < s ∧
    (∀ x ∈ arm_ladder_S, 0 < x → x < s → 0 < polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x) ∧
    (∀ x ∈ arm_ladder_S, s < x → polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x < 0) := by
  have hleft : ∀ x ∈ arm_ladder_S, 0 < x → x ≤ (1 / 4 : ℝ) → 0 < polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x := by
    intro x hx hx0 hxa
    exact arm_ladder_p4_L0 x (by linarith) (by linarith)
  have hright : ∀ x ∈ arm_ladder_S, (3 / 8 : ℝ) ≤ x → polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x < 0 := by
    intro x hx hxb
    exact arm_ladder_p4_R0 x (by linarith)
  exact sign_change_of_cell (S := arm_ladder_S) (N' := polyDeriv [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)])
    (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num))
    (fun x _ => hasDerivAt_polyEval [(1 / 660 : ℝ), (-1 / 396 : ℝ), (-1 / 240 : ℝ)] x)
    (fun x hx => arm_ladder_p4_C x (by linarith [hx.1]) (by linarith [hx.2]))
    hleft hright (Set.self_mem_Ici)

/-- `arm_ladder_p4_vlo_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (95749 / 100000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-4251370547110358354146490835972808494851073753847841260162248812041222779642503508364437390318368108917291089099287615796822518898256798387428839333852481269525800556937807/97867641952960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4251370547110358354146490835972808494851073641454304638227703319625721186220407718720925500116957436177863160302386448508845983145434452598124630091337050930366797593040399/97867641952960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vlo_a0 :
    (-(4251370547110358354146490835972808494851073753847841260162248812041222779642503508364437390318368108917291089099287615796822518898256798387428839333852481269525800556937807 / 97867641952960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (95749 / 100000) ∧
      Real.log (95749 / 100000) ≤ (-(4251370547110358354146490835972808494851073641454304638227703319625721186220407718720925500116957436177863160302386448508845983145434452598124630091337050930366797593040399 / 97867641952960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((4251 / 100000) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (4251 / 100000) = (95749 / 100000) by norm_num] at h
  generalize Real.log (95749 / 100000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p4_vlo_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (287247 / 200000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [12436120752571141798636946405536242201095359049899407717683050666973530804345481268564082475998252793770030827726150046855315295866711863766012477393817779074396444004514829743/34351542325488960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 12436120768567325218930426563388415052657859089349539071982076134811371863636636890728955149458947939901570030733862356573395059915952507138058254837940695123441254044842819951/34351542325488960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vlo_a1 :
    (12436120752571141798636946405536242201095359049899407717683050666973530804345481268564082475998252793770030827726150046855315295866711863766012477393817779074396444004514829743 / 34351542325488960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (287247 / 200000) ∧
      Real.log (287247 / 200000) ≤ (12436120768567325218930426563388415052657859089349539071982076134811371863636636890728955149458947939901570030733862356573395059915952507138058254837940695123441254044842819951 / 34351542325488960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p4_vlo_a0
  have hfold : Real.log (287247 / 200000) = Real.log (3 / 2) + Real.log (95749 / 100000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((95749 / 100000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p4_vlo_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (1785223 / 1500000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [65277607460465919253342008249730934180983958639277436587075584932498454465608760597687925989056092749946514761353490793208697493554626432613491158417023908316941009310055169345284121030663244038849476795359780883/374990070417397892371690588094294071197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 21759202486821973084447836810917730245314339183665086371660653640421818180261599178527926914660752836353601629258425488308929594879882764222457423370734517962478955465119258706198773870467528351931765168348980977/124996690139132630790563529364764690399169921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vlo_a2 :
    (65277607460465919253342008249730934180983958639277436587075584932498454465608760597687925989056092749946514761353490793208697493554626432613491158417023908316941009310055169345284121030663244038849476795359780883 / 374990070417397892371690588094294071197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (1785223 / 1500000) ∧
      Real.log (1785223 / 1500000) ≤ (21759202486821973084447836810917730245314339183665086371660653640421818180261599178527926914660752836353601629258425488308929594879882764222457423370734517962478955465119258706198773870467528351931765168348980977 / 124996690139132630790563529364764690399169921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(285223 / 1500000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(285223 / 1500000)) = (1785223 / 1500000) by norm_num] at h
  generalize Real.log (1785223 / 1500000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p4_vlo_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (1785223 / 1000000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [64979576047249782773882410103797796663214474469674005960234266432463242118386575082771189870727771732234007913644693747169400550572833303351433856366690148586765361783706495634239952188168309967615993561812574484017/112122031054801969819135485840193927288055419921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 21659858699820224030140087557956691214388664289220274542973263543118471458087549209067350147483565098069726887148269221004369948869084946502514769587849620870781207684070658353153433387269790977227597785336345312123/37374010351600656606378495280064642429351806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vlo_a3 :
    (64979576047249782773882410103797796663214474469674005960234266432463242118386575082771189870727771732234007913644693747169400550572833303351433856366690148586765361783706495634239952188168309967615993561812574484017 / 112122031054801969819135485840193927288055419921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (1785223 / 1000000) ∧
      Real.log (1785223 / 1000000) ≤ (21659858699820224030140087557956691214388664289220274542973263543118471458087549209067350147483565098069726887148269221004369948869084946502514769587849620870781207684070658353153433387269790977227597785336345312123 / 37374010351600656606378495280064642429351806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p4_vlo_a2
  have hfold : Real.log (1785223 / 1000000) = Real.log (3 / 2) + Real.log (1785223 / 1500000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((1785223 / 1500000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p4_vlo_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (2159717 / 1800000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [27688326913557901041446291858578011958018225289624958880731388345395397460280907841249550535539501091700737232681132980034180705201062184959023118592777627395830644490698046314748839355302634756292347498498683884937/151974567286249745749264306215569303526991537908209418240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 9229442304519300347149823751676645833367949415828826391257549897422916851330728714163596630301792251979051694892697023673705510798972009316021015645885443564854013689337066267761188955261654446769814085333546337603/50658189095416581916421435405189767842330512636069806080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vlo_a4 :
    (27688326913557901041446291858578011958018225289624958880731388345395397460280907841249550535539501091700737232681132980034180705201062184959023118592777627395830644490698046314748839355302634756292347498498683884937 / 151974567286249745749264306215569303526991537908209418240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (2159717 / 1800000) ∧
      Real.log (2159717 / 1800000) ≤ (9229442304519300347149823751676645833367949415828826391257549897422916851330728714163596630301792251979051694892697023673705510798972009316021015645885443564854013689337066267761188955261654446769814085333546337603 / 50658189095416581916421435405189767842330512636069806080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(359717 / 1800000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(359717 / 1800000)) = (2159717 / 1800000) by norm_num] at h
  generalize Real.log (2159717 / 1800000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p4_vlo_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (2159717 / 1200000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [5253453601895489978976460948168740083171334517918407051737140490905611615310641637720561796208205946570631601922419587060834159129474246174060183446633978082107684970041061547926402315017802044487785146970510816761/8939680428602926220544959189151135501587737524012318720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 134703938616880848089222790448555116266814231362328788917907465599198718784301939883093197422180055438819238438428493319790522673298515879258013645456495219750470650177995774967245198892586671704840787716441386143/229222575092382723603716902285926551322762500615700480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vlo_a5 :
    (5253453601895489978976460948168740083171334517918407051737140490905611615310641637720561796208205946570631601922419587060834159129474246174060183446633978082107684970041061547926402315017802044487785146970510816761 / 8939680428602926220544959189151135501587737524012318720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (2159717 / 1200000) ∧
      Real.log (2159717 / 1200000) ≤ (134703938616880848089222790448555116266814231362328788917907465599198718784301939883093197422180055438819238438428493319790522673298515879258013645456495219750470650177995774967245198892586671704840787716441386143 / 229222575092382723603716902285926551322762500615700480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p4_vlo_a4
  have hfold : Real.log (2159717 / 1200000) = Real.log (3 / 2) + Real.log (2159717 / 1800000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((2159717 / 1800000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p4_vhi_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (17953 / 18750)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-698817093278826374111344201231982843597837333703320416342781048875861000341963040391829803727091254105834553274558590713062726360112821955765471910979/16088238302437954030765432821462466308527593541328867426537708394025265106960786987144729209830984473228454589843750000000000000000000000000000000000000, -77646343697647374901260466803553649288648590586112994599060239698967023599905686663807961703450226265170086567612959049315098632380751570186374561067/1787582033604217114529492535718051812058621504592096380726412043780585011884531887460525467758998274803161621093750000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vhi_a0 :
    (-(698817093278826374111344201231982843597837333703320416342781048875861000341963040391829803727091254105834553274558590713062726360112821955765471910979 / 16088238302437954030765432821462466308527593541328867426537708394025265106960786987144729209830984473228454589843750000000000000000000000000000000000000) : ℝ) ≤ Real.log (17953 / 18750) ∧
      Real.log (17953 / 18750) ≤ (-(77646343697647374901260466803553649288648590586112994599060239698967023599905686663807961703450226265170086567612959049315098632380751570186374561067 / 1787582033604217114529492535718051812058621504592096380726412043780585011884531887460525467758998274803161621093750000000000000000000000000000000000000) : ℝ) := by
  have hx : |((797 / 18750) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (797 / 18750) = (17953 / 18750) by norm_num] at h
  generalize Real.log (17953 / 18750) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p4_vhi_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (17953 / 12500)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [2912201092752519930330404539529955312510281356048141706810244891945185773634706785259766253500677140926241083446095572598299370471704554607825882208573/8044119151218977015382716410731233154263796770664433713268854197012632553480393493572364604915492236614227294921875000000000000000000000000000000000000, 323577899610928312171541361409770586140753505650270686925104724869703932601591929937918320875207031869611231605193836341725512486289994021196485571029/893791016802108557264746267859025906029310752296048190363206021890292505942265943730262733879499137401580810546875000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vhi_a1 :
    (2912201092752519930330404539529955312510281356048141706810244891945185773634706785259766253500677140926241083446095572598299370471704554607825882208573 / 8044119151218977015382716410731233154263796770664433713268854197012632553480393493572364604915492236614227294921875000000000000000000000000000000000000 : ℝ) ≤ Real.log (17953 / 12500) ∧
      Real.log (17953 / 12500) ≤ (323577899610928312171541361409770586140753505650270686925104724869703932601591929937918320875207031869611231605193836341725512486289994021196485571029 / 893791016802108557264746267859025906029310752296048190363206021890292505942265943730262733879499137401580810546875000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p4_vhi_a0
  have hfold : Real.log (17953 / 12500) = Real.log (3 / 2) + Real.log (17953 / 18750) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((17953 / 18750) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p4_vhi_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (111577 / 93750)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [155868197305134631601476040363548005292378731348756463948936222691898054859469223540391312450789847253745894008395268404609862060837635445438102881175512438891017208614892221/895365744843132289727334674660333606997325213234996241294835117008900548353652952074448062184724647649680662198079517111182212829589843750000000000000000000000000000000000000, 51956065768378210533826543632378026072829400244853777775171065607819472540532314120267483354736186229636915687418939155756509785310022029342261731487815761791729027740457599/298455248281044096575778224886777868999108404411665413764945039002966849451217650691482687394908215883226887399359839037060737609863281250000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vhi_a2 :
    (155868197305134631601476040363548005292378731348756463948936222691898054859469223540391312450789847253745894008395268404609862060837635445438102881175512438891017208614892221 / 895365744843132289727334674660333606997325213234996241294835117008900548353652952074448062184724647649680662198079517111182212829589843750000000000000000000000000000000000000 : ℝ) ≤ Real.log (111577 / 93750) ∧
      Real.log (111577 / 93750) ≤ (51956065768378210533826543632378026072829400244853777775171065607819472540532314120267483354736186229636915687418939155756509785310022029342261731487815761791729027740457599 / 298455248281044096575778224886777868999108404411665413764945039002966849451217650691482687394908215883226887399359839037060737609863281250000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(17827 / 93750)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(17827 / 93750)) = (111577 / 93750) by norm_num] at h
  generalize Real.log (111577 / 93750) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p4_vhi_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (111577 / 62500)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [15261993106579618114896638201801051403862310175375946017091413208566787494900296788856631181512278016266973793938929748950459975278732977295230326980576329762377101127977069/26334286613033302639039255137068635499921329801029301214553974029673545539813322119836707711315430813225901829355279915034770965576171875000000000000000000000000000000000000, 5087331039614158639817598767934030827626754327510597186875007099784094608580370120988088355942650947886540707012382285956211400082073516147204313470694415321743461861104911/8778095537677767546346418379022878499973776600343100404851324676557848513271107373278902570438476937741967276451759971678256988525390625000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vhi_a3 :
    (15261993106579618114896638201801051403862310175375946017091413208566787494900296788856631181512278016266973793938929748950459975278732977295230326980576329762377101127977069 / 26334286613033302639039255137068635499921329801029301214553974029673545539813322119836707711315430813225901829355279915034770965576171875000000000000000000000000000000000000 : ℝ) ≤ Real.log (111577 / 62500) ∧
      Real.log (111577 / 62500) ≤ (5087331039614158639817598767934030827626754327510597186875007099784094608580370120988088355942650947886540707012382285956211400082073516147204313470694415321743461861104911 / 8778095537677767546346418379022878499973776600343100404851324676557848513271107373278902570438476937741967276451759971678256988525390625000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p4_vhi_a2
  have hfold : Real.log (111577 / 62500) = Real.log (3 / 2) + Real.log (111577 / 93750) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((111577 / 93750) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p4_vhi_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (134983 / 112500)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [1520608096551724325879717490928068102222728506015075151356852919720551663017271782565797064795539958194371264468167604480025703577157795046703174472909866663321672119133103627737/8346018812226837114208274492900458963071715158883167338844161596968056204826069688351708464324474334716796875000000000000000000000000000000000000000000000000000000000000000000000, 506869365517241441959964090706750190069394626871677085150831831187291263187374593854053671410123374917112458908884980371809991942658410382139206130432591238390123117955195770803/2782006270742279038069424830966819654357238386294389112948053865656018734942023229450569488108158111572265625000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vhi_a4 :
    (1520608096551724325879717490928068102222728506015075151356852919720551663017271782565797064795539958194371264468167604480025703577157795046703174472909866663321672119133103627737 / 8346018812226837114208274492900458963071715158883167338844161596968056204826069688351708464324474334716796875000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (134983 / 112500) ∧
      Real.log (134983 / 112500) ≤ (506869365517241441959964090706750190069394626871677085150831831187291263187374593854053671410123374917112458908884980371809991942658410382139206130432591238390123117955195770803 / 2782006270742279038069424830966819654357238386294389112948053865656018734942023229450569488108158111572265625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(22483 / 112500)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(22483 / 112500)) = (134983 / 112500) by norm_num] at h
  generalize Real.log (134983 / 112500) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p4_vhi_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (134983 / 75000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [4904627514561019012528090890214800702222350031749933140343072184023142186504534494235375696312372085763302557717033758979435889540073215578929736972909866663321672119133103627737/8346018812226837114208274492900458963071715158883167338844161596968056204826069688351708464324474334716796875000000000000000000000000000000000000000000000000000000000000000000000, 1634875839482478958841474537637474636847296393658670546785987637237704375994883278303049078240235963670384971185267124963290019826903329205381393630432591238390123117955195770803/2782006270742279038069424830966819654357238386294389112948053865656018734942023229450569488108158111572265625000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p4_vhi_a5 :
    (4904627514561019012528090890214800702222350031749933140343072184023142186504534494235375696312372085763302557717033758979435889540073215578929736972909866663321672119133103627737 / 8346018812226837114208274492900458963071715158883167338844161596968056204826069688351708464324474334716796875000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (134983 / 75000) ∧
      Real.log (134983 / 75000) ≤ (1634875839482478958841474537637474636847296393658670546785987637237704375994883278303049078240235963670384971185267124963290019826903329205381393630432591238390123117955195770803 / 2782006270742279038069424830966819654357238386294389112948053865656018734942023229450569488108158111572265625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p4_vhi_a4
  have hfold : Real.log (134983 / 75000) = Real.log (3 / 2) + Real.log (134983 / 112500) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((134983 / 112500) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

theorem arm_ladder_p4_vlo : 0 < arm_ladder_F 4 (87247 / 100000 : ℝ) - arm_ladder_F 5 (87247 / 100000 : ℝ) := by
  have h0 := arm_ladder_p3_vlo_a1
  have h1 := arm_ladder_p4_vlo_a0
  have h2 := arm_ladder_p4_vlo_a1
  have h3 := arm_ladder_p4_vlo_a2
  have h4 := arm_ladder_p4_vlo_a3
  have h5 := arm_ladder_p4_vlo_a4
  have h6 := arm_ladder_p4_vlo_a5
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

theorem arm_ladder_p4_vhi : arm_ladder_F 4 (5453 / 6250 : ℝ) - arm_ladder_F 5 (5453 / 6250 : ℝ) < 0 := by
  have h0 := arm_ladder_p3_vlo_a1
  have h1 := arm_ladder_p4_vhi_a0
  have h2 := arm_ladder_p4_vhi_a1
  have h3 := arm_ladder_p4_vhi_a2
  have h4 := arm_ladder_p4_vhi_a3
  have h5 := arm_ladder_p4_vhi_a4
  have h6 := arm_ladder_p4_vhi_a5
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

/-- (a) `F 4` and `F 5` cross EXACTLY ONCE on `S ∩ (0, oo)`, at a point of
`(87247/100000, 5453/6250)`: `F 4` is ahead before it, `F 5` after it. -/
theorem arm_ladder_p4_cross : ∃ c ∈ Set.Ioo ((87247 / 100000 : ℝ)) ((5453 / 6250 : ℝ)),
    arm_ladder_F 4 c = arm_ladder_F 5 c ∧ ∀ x ∈ arm_ladder_S, 0 < x →
      (x < c → arm_ladder_F 5 x < arm_ladder_F 4 x) ∧ (c < x → arm_ladder_F 4 x < arm_ladder_F 5 x) := by
  have hD0 : arm_ladder_F 4 0 - arm_ladder_F 5 0 = 0 := by simp [arm_ladder_F, logSum_zero]
  have hd : ∀ x ∈ arm_ladder_S, HasDerivAt (fun y => arm_ladder_F 4 y - arm_ladder_F 5 y)
      (logSumDeriv (arm_ladder_terms 4) x - logSumDeriv (arm_ladder_terms 5) x) x :=
    fun x hx => (hasDerivAt_logSum _ x (arm_ladder_argpos 4 (by norm_num) x hx)).sub
      (hasDerivAt_logSum _ x (arm_ladder_argpos 5 (by norm_num) x hx))
  obtain ⟨s, hs, hNp, hNn⟩ := arm_ladder_p4_sign
  obtain ⟨c, hc, hDc, hsg⟩ := single_crossing_core (S := arm_ladder_S)
    (P := fun x => (1 + (1 / 2 : ℝ) * x) * (1 + (9 / 10 : ℝ) * x) * (1 + (11 / 12 : ℝ) * x)) (Set.self_mem_Ici) hD0 hd arm_ladder_p4_fac arm_ladder_p4_P_pos
    hs hNp hNn (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num)) arm_ladder_p4_vlo arm_ladder_p4_vhi
  refine ⟨c, hc, by linarith, fun x hx hx0 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := (hsg x hx hx0).1 h; linarith
  · have := (hsg x hx hx0).2 h; linarith

/-! ### Pair j = 5: `D = F 5 - F 6`, `D' * P = N`,
`N = -x**2/336 - 3*x/2002 + 17/12012` -/

theorem arm_ladder_p5_P_pos (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    0 < (1 + (1 / 2 : ℝ) * x) * (1 + (11 / 12 : ℝ) * x) * (1 + (13 / 14 : ℝ) * x) := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (11 / 12 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (13 / 14 : ℝ) * x := by nlinarith
  positivity

theorem arm_ladder_p5_fac (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    (logSumDeriv (arm_ladder_terms 5) x - logSumDeriv (arm_ladder_terms 6) x) *
      ((1 + (1 / 2 : ℝ) * x) * (1 + (11 / 12 : ℝ) * x) * (1 + (13 / 14 : ℝ) * x)) = polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (11 / 12 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (13 / 14 : ℝ) * x := by nlinarith
  have hne0 : 1 + (1 / 2 : ℝ) * x ≠ 0 := by nlinarith [hpos0]
  have hne1 : 1 + (11 / 12 : ℝ) * x ≠ 0 := by nlinarith [hpos1]
  have hne2 : 1 + (13 / 14 : ℝ) * x ≠ 0 := by nlinarith [hpos2]
  simp only [logSumDeriv, arm_ladder_terms, polyEval]
  norm_num at hne0 hne1 hne2 ⊢
  field_simp
  ring

theorem arm_ladder_p5_L0 (x : ℝ) (hs : 0 ≤ x - (0 : ℝ)) (ht : 0 ≤ (3 / 8 : ℝ) - x) :
    0 < polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x := by
  simp only [polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem arm_ladder_p5_R0 (x : ℝ) (hs : 0 ≤ x - (1 / 2 : ℝ)) :
    polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x < 0 := by
  simp only [polyEval]
  linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]

theorem arm_ladder_p5_C (x : ℝ) (hs : 0 ≤ x - (3 / 8 : ℝ)) (ht : 0 ≤ (1 / 2 : ℝ) - x) :
    polyDeriv [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x < 0 := by
  simp only [polyDeriv, polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem arm_ladder_p5_sign : ∃ s, 0 < s ∧
    (∀ x ∈ arm_ladder_S, 0 < x → x < s → 0 < polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x) ∧
    (∀ x ∈ arm_ladder_S, s < x → polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x < 0) := by
  have hleft : ∀ x ∈ arm_ladder_S, 0 < x → x ≤ (3 / 8 : ℝ) → 0 < polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x := by
    intro x hx hx0 hxa
    exact arm_ladder_p5_L0 x (by linarith) (by linarith)
  have hright : ∀ x ∈ arm_ladder_S, (1 / 2 : ℝ) ≤ x → polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x < 0 := by
    intro x hx hxb
    exact arm_ladder_p5_R0 x (by linarith)
  exact sign_change_of_cell (S := arm_ladder_S) (N' := polyDeriv [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)])
    (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num))
    (fun x _ => hasDerivAt_polyEval [(17 / 12012 : ℝ), (-3 / 2002 : ℝ), (-1 / 336 : ℝ)] x)
    (fun x hx => arm_ladder_p5_C x (by linarith [hx.1]) (by linarith [hx.2]))
    hleft hright (Set.self_mem_Ici)

/-- `arm_ladder_p5_vlo_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (106413 / 100000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [102160617094458224690339834049574572848553055706251493553121395994115078331725810493722012390872486049828814576689450798985076417931502505419260921187610619749588211497181921/1643574983843520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 102160617094458224690339834049574572850061832200738066261104783783092364487149223624846681167628761602256134971892026523404102693478460820853315944291671727800072528284625697/1643574983843520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vlo_a0 :
    (102160617094458224690339834049574572848553055706251493553121395994115078331725810493722012390872486049828814576689450798985076417931502505419260921187610619749588211497181921 / 1643574983843520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (106413 / 100000) ∧
      Real.log (106413 / 100000) ≤ (102160617094458224690339834049574572850061832200738066261104783783092364487149223624846681167628761602256134971892026523404102693478460820853315944291671727800072528284625697 / 1643574983843520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(6413 / 100000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(6413 / 100000)) = (106413 / 100000) by norm_num] at h
  generalize Real.log (106413 / 100000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p5_vlo_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (319239 / 200000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [8454302177374536215010678129750045566837013300268766429084335355935265861648983915430942136299597346548116960343583958788835840597246527559611870133063716817245470326469001131/18079324822278720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 8454302185793377885407751160221847324666109841708118728872152621614016009358641459873313492843916377624817484690812291757445129628263069029386475387208389005800797811130882667/18079324822278720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vlo_a1 :
    (8454302177374536215010678129750045566837013300268766429084335355935265861648983915430942136299597346548116960343583958788835840597246527559611870133063716817245470326469001131 / 18079324822278720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (319239 / 200000) ∧
      Real.log (319239 / 200000) ≤ (8454302185793377885407751160221847324666109841708118728872152621614016009358641459873313492843916377624817484690812291757445129628263069029386475387208389005800797811130882667 / 18079324822278720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p5_vlo_a0
  have hfold : Real.log (319239 / 200000) = Real.log (3 / 2) + Real.log (106413 / 100000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((106413 / 100000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p5_vlo_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (2511629 / 2700000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-130129638682249371848023194940273791113271533642974488252813234891682966462789703090645802268250031040308020566373277367759069954756857386956786035574873987092170116887739290107492022261255530577774389692958527519594878169/1799353309160571250980513145614188178312544104544899392661337920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -43376546227416457282674398313424597028826330348515458006893424737440389142028387010729574447602868546583480959914041377051719258680669665092457637335110239018542043303653227979756979544747598555780580910159405797244965811/599784436386857083660171048538062726104181368181633130887112640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vlo_a2 :
    (-(130129638682249371848023194940273791113271533642974488252813234891682966462789703090645802268250031040308020566373277367759069954756857386956786035574873987092170116887739290107492022261255530577774389692958527519594878169 / 1799353309160571250980513145614188178312544104544899392661337920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (2511629 / 2700000) ∧
      Real.log (2511629 / 2700000) ≤ (-(43376546227416457282674398313424597028826330348515458006893424737440389142028387010729574447602868546583480959914041377051719258680669665092457637335110239018542043303653227979756979544747598555780580910159405797244965811 / 599784436386857083660171048538062726104181368181633130887112640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((188371 / 2700000) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (188371 / 2700000) = (2511629 / 2700000) by norm_num] at h
  generalize Real.log (2511629 / 2700000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p5_vlo_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (2511629 / 1200000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [1329020328518462021561789647437779318831612951823507963843330883060096449554444622318289744606749968959691979433626722632240930045243142613043213964425126012907829883112260709892507977738744469422225610307041472480405121831/1799353309160571250980513145614188178312544104544899392661337920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 443006776731413459364031316006143651267727865410255216311990702488830561629839841901623941177397131453416519040085958622948280741319330334907542362664889760981457956696346772020243020455252401444219419089840594202755034189/599784436386857083660171048538062726104181368181633130887112640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vlo_a3 :
    (1329020328518462021561789647437779318831612951823507963843330883060096449554444622318289744606749968959691979433626722632240930045243142613043213964425126012907829883112260709892507977738744469422225610307041472480405121831 / 1799353309160571250980513145614188178312544104544899392661337920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (2511629 / 1200000) ∧
      Real.log (2511629 / 1200000) ≤ (443006776731413459364031316006143651267727865410255216311990702488830561629839841901623941177397131453416519040085958622948280741319330334907542362664889760981457956696346772020243020455252401444219419089840594202755034189 / 599784436386857083660171048538062726104181368181633130887112640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p5_vlo_a2
  have hfold : Real.log (2511629 / 1200000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (2511629 / 2700000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((2511629 / 2700000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p5_vlo_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (983369 / 1050000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-408195264258621332252925415426616252601706027300026258666600045354155889601622601329708268054115912747685910753900714896942880694939841897247928881950785558023787599042280960194377134648156087951653745412831/6226189194965070581688606862741649392129139089303332829400897026062011718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -45355029362069036916991712825179583621963495357832313254453192999792959457831282362648548613871302021189202955584583578660105546334537734132736525112020737092707257203878591763006263828289558796732915721063/691798799440563397965400762526849932458793232144814758822321891784667968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vlo_a4 :
    (-(408195264258621332252925415426616252601706027300026258666600045354155889601622601329708268054115912747685910753900714896942880694939841897247928881950785558023787599042280960194377134648156087951653745412831 / 6226189194965070581688606862741649392129139089303332829400897026062011718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (983369 / 1050000) ∧
      Real.log (983369 / 1050000) ≤ (-(45355029362069036916991712825179583621963495357832313254453192999792959457831282362648548613871302021189202955584583578660105546334537734132736525112020737092707257203878591763006263828289558796732915721063 / 691798799440563397965400762526849932458793232144814758822321891784667968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((66631 / 1050000) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (66631 / 1050000) = (983369 / 1050000) by norm_num] at h
  generalize Real.log (983369 / 1050000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p5_vlo_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (2950107 / 1400000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [8210663285111837490222703824446683670980885741291763665694028647052844678279575003331623526150284115095703232416175658259254903385875664335638279670394764012727145017079041378117640454084031536700920296577299/11015565498784355644525996757158302770690015311844358082786202430725097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 912295921707875812377331966244424659427255325304175269604754408548920678662384831279508716686768500186632503905504198283909044033408125547303619994032578695912902544946984029957758148611487703667318687570427/1223951722087150627169555195239811418965557256871595342531800270080566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vlo_a5 :
    (8210663285111837490222703824446683670980885741291763665694028647052844678279575003331623526150284115095703232416175658259254903385875664335638279670394764012727145017079041378117640454084031536700920296577299 / 11015565498784355644525996757158302770690015311844358082786202430725097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (2950107 / 1400000) ∧
      Real.log (2950107 / 1400000) ≤ (912295921707875812377331966244424659427255325304175269604754408548920678662384831279508716686768500186632503905504198283909044033408125547303619994032578695912902544946984029957758148611487703667318687570427 / 1223951722087150627169555195239811418965557256871595342531800270080566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p5_vlo_a4
  have hfold : Real.log (2950107 / 1400000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (983369 / 1050000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((983369 / 1050000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p5_vhi_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (7981 / 7500)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [10303487664439931892222508857558003903230217526189148654039359902015511582439866019255305122979289965655573542767382562269934456648294249/165755666670126519303348454174862336429896458867006003856658935546875000000000000000000000000000000000000000000000000000000000000000000000, 3434495888146643964074169619186001301127546809817595984711284627762703705977199801913680313354487723714879982348003557866011892118383331/55251888890042173101116151391620778809965486289002001285552978515625000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vhi_a0 :
    (10303487664439931892222508857558003903230217526189148654039359902015511582439866019255305122979289965655573542767382562269934456648294249 / 165755666670126519303348454174862336429896458867006003856658935546875000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (7981 / 7500) ∧
      Real.log (7981 / 7500) ≤ (3434495888146643964074169619186001301127546809817595984711284627762703705977199801913680313354487723714879982348003557866011892118383331 / 55251888890042173101116151391620778809965486289002001285552978515625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(481 / 7500)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(481 / 7500)) = (7981 / 7500) by norm_num] at h
  generalize Real.log (7981 / 7500) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p5_vhi_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (7981 / 5000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [1007651150108159922174818115465573010009479281523397540116937747819223759729405085780006401033621516623834956055975973309509147936427825237/2154823666711644750943529904273210373588653965271078050136566162109375000000000000000000000000000000000000000000000000000000000000000000000, 335883717037192628245648501329127675888278007764268399226265967241072729340028784021595529534652651931730939770524046252258154597538983303/718274555570548250314509968091070124529551321757026016712188720703125000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vhi_a1 :
    (1007651150108159922174818115465573010009479281523397540116937747819223759729405085780006401033621516623834956055975973309509147936427825237 / 2154823666711644750943529904273210373588653965271078050136566162109375000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (7981 / 5000) ∧
      Real.log (7981 / 5000) ≤ (335883717037192628245648501329127675888278007764268399226265967241072729340028784021595529534652651931730939770524046252258154597538983303 / 718274555570548250314509968091070124529551321757026016712188720703125000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p5_vhi_a0
  have hfold : Real.log (7981 / 5000) = Real.log (3 / 2) + Real.log (7981 / 7500) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((7981 / 7500) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p5_vhi_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (62791 / 67500)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-1970955371477607336917429200372427640566184077075198614390602428715233474068854276751069587765762110416042728454955895661554164715657413050752908410371249875697607343137/27254819784821398708057323483881398154278748158229230266791538739301614668875117786228656768798828125000000000000000000000000000000000000000000000000000000000000000000000, -656985123825869112305809733457475880053713433166085178894403763049165957228871921182158686999078296560851718773285309807576598075252876499787587830827998301387552403403/9084939928273799569352441161293799384759582719409743422263846246433871556291705928742885589599609375000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vhi_a2 :
    (-(1970955371477607336917429200372427640566184077075198614390602428715233474068854276751069587765762110416042728454955895661554164715657413050752908410371249875697607343137 / 27254819784821398708057323483881398154278748158229230266791538739301614668875117786228656768798828125000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ Real.log (62791 / 67500) ∧
      Real.log (62791 / 67500) ≤ (-(656985123825869112305809733457475880053713433166085178894403763049165957228871921182158686999078296560851718773285309807576598075252876499787587830827998301387552403403 / 9084939928273799569352441161293799384759582719409743422263846246433871556291705928742885589599609375000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) := by
  have hx : |((4709 / 67500) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (4709 / 67500) = (62791 / 67500) by norm_num] at h
  generalize Real.log (62791 / 67500) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p5_vhi_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (62791 / 30000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [342223625784642754961533934124806290785105047119192291759898934711569056139871958822774902813197121167232889643752143933249409735722495853137200557023688752113140675166671/463331936341963778036974499225983768622738718689896914535456158568127449370877002365887165069580078125000000000000000000000000000000000000000000000000000000000000000000000, 114074542072051415605702212174124969029069681187845327947642654508503934294913555654389517074556308602157410440603144478585319079058591724503611006875924028876411609142149/154443978780654592678991499741994589540912906229965638178485386189375816456959000788629055023193359375000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vhi_a3 :
    (342223625784642754961533934124806290785105047119192291759898934711569056139871958822774902813197121167232889643752143933249409735722495853137200557023688752113140675166671 / 463331936341963778036974499225983768622738718689896914535456158568127449370877002365887165069580078125000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (62791 / 30000) ∧
      Real.log (62791 / 30000) ≤ (114074542072051415605702212174124969029069681187845327947642654508503934294913555654389517074556308602157410440603144478585319079058591724503611006875924028876411609142149 / 154443978780654592678991499741994589540912906229965638178485386189375816456959000788629055023193359375000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p5_vhi_a2
  have hfold : Real.log (62791 / 30000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (62791 / 67500) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((62791 / 67500) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p5_vhi_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (73753 / 78750)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-37225163251392735498948504280964543678308177498271874785542440366033773050269461492794397284261399291309999805435452115696082740784745000856983638158729191030201042051619/567832380190120680547388990295340805106113859187084892298917837153448684213107803102546636058942097768920120870461687445640563964843750000000000000000000000000000000000000, -12408387750464245166316168093654847892647004245899530406563805679472170956750328004515670233921838989411323797652173809735642239605481857452489382404024906775197781731361/189277460063373560182462996765113601702037953062361630766305945717816228071035934367515545352980699256306706956820562481880187988281250000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vhi_a4 :
    (-(37225163251392735498948504280964543678308177498271874785542440366033773050269461492794397284261399291309999805435452115696082740784745000856983638158729191030201042051619 / 567832380190120680547388990295340805106113859187084892298917837153448684213107803102546636058942097768920120870461687445640563964843750000000000000000000000000000000000000) : ℝ) ≤ Real.log (73753 / 78750) ∧
      Real.log (73753 / 78750) ≤ (-(12408387750464245166316168093654847892647004245899530406563805679472170956750328004515670233921838989411323797652173809735642239605481857452489382404024906775197781731361 / 189277460063373560182462996765113601702037953062361630766305945717816228071035934367515545352980699256306706956820562481880187988281250000000000000000000000000000000000000) : ℝ) := by
  have hx : |((4997 / 78750) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (4997 / 78750) = (73753 / 78750) by norm_num] at h
  generalize Real.log (73753 / 78750) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p5_vhi_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (73753 / 35000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [618592165780791264375196726938190960900005277875462886399147844513758914262746636355691576322727736742281407028479435713351094530425875602849025737639696568044515927422153/829908863354791763876953139662421176693551024965739457975341454301194230773003712226798929624607681354575561272213235497474670410156250000000000000000000000000000000000000, 206197388851234707896995581009237790256764032730739783345962952721218203501181175749550819146402002008699855291728967975561838594775005711051595611712000335745629090943107/276636287784930587958984379887473725564517008321913152658447151433731410257667904075599643208202560451525187090737745165824890136718750000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p5_vhi_a5 :
    (618592165780791264375196726938190960900005277875462886399147844513758914262746636355691576322727736742281407028479435713351094530425875602849025737639696568044515927422153 / 829908863354791763876953139662421176693551024965739457975341454301194230773003712226798929624607681354575561272213235497474670410156250000000000000000000000000000000000000 : ℝ) ≤ Real.log (73753 / 35000) ∧
      Real.log (73753 / 35000) ≤ (206197388851234707896995581009237790256764032730739783345962952721218203501181175749550819146402002008699855291728967975561838594775005711051595611712000335745629090943107 / 276636287784930587958984379887473725564517008321913152658447151433731410257667904075599643208202560451525187090737745165824890136718750000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p5_vhi_a4
  have hfold : Real.log (73753 / 35000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (73753 / 78750) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((73753 / 78750) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

theorem arm_ladder_p5_vlo : 0 < arm_ladder_F 5 (119239 / 100000 : ℝ) - arm_ladder_F 6 (119239 / 100000 : ℝ) := by
  have h0 := arm_ladder_p3_vlo_a1
  have h1 := arm_ladder_p5_vlo_a0
  have h2 := arm_ladder_p5_vlo_a1
  have h3 := arm_ladder_p5_vlo_a2
  have h4 := arm_ladder_p5_vlo_a3
  have h5 := arm_ladder_p5_vlo_a4
  have h6 := arm_ladder_p5_vlo_a5
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

theorem arm_ladder_p5_vhi : arm_ladder_F 5 (2981 / 2500 : ℝ) - arm_ladder_F 6 (2981 / 2500 : ℝ) < 0 := by
  have h0 := arm_ladder_p3_vlo_a1
  have h1 := arm_ladder_p5_vhi_a0
  have h2 := arm_ladder_p5_vhi_a1
  have h3 := arm_ladder_p5_vhi_a2
  have h4 := arm_ladder_p5_vhi_a3
  have h5 := arm_ladder_p5_vhi_a4
  have h6 := arm_ladder_p5_vhi_a5
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

/-- (a) `F 5` and `F 6` cross EXACTLY ONCE on `S ∩ (0, oo)`, at a point of
`(119239/100000, 2981/2500)`: `F 5` is ahead before it, `F 6` after it. -/
theorem arm_ladder_p5_cross : ∃ c ∈ Set.Ioo ((119239 / 100000 : ℝ)) ((2981 / 2500 : ℝ)),
    arm_ladder_F 5 c = arm_ladder_F 6 c ∧ ∀ x ∈ arm_ladder_S, 0 < x →
      (x < c → arm_ladder_F 6 x < arm_ladder_F 5 x) ∧ (c < x → arm_ladder_F 5 x < arm_ladder_F 6 x) := by
  have hD0 : arm_ladder_F 5 0 - arm_ladder_F 6 0 = 0 := by simp [arm_ladder_F, logSum_zero]
  have hd : ∀ x ∈ arm_ladder_S, HasDerivAt (fun y => arm_ladder_F 5 y - arm_ladder_F 6 y)
      (logSumDeriv (arm_ladder_terms 5) x - logSumDeriv (arm_ladder_terms 6) x) x :=
    fun x hx => (hasDerivAt_logSum _ x (arm_ladder_argpos 5 (by norm_num) x hx)).sub
      (hasDerivAt_logSum _ x (arm_ladder_argpos 6 (by norm_num) x hx))
  obtain ⟨s, hs, hNp, hNn⟩ := arm_ladder_p5_sign
  obtain ⟨c, hc, hDc, hsg⟩ := single_crossing_core (S := arm_ladder_S)
    (P := fun x => (1 + (1 / 2 : ℝ) * x) * (1 + (11 / 12 : ℝ) * x) * (1 + (13 / 14 : ℝ) * x)) (Set.self_mem_Ici) hD0 hd arm_ladder_p5_fac arm_ladder_p5_P_pos
    hs hNp hNn (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num)) arm_ladder_p5_vlo arm_ladder_p5_vhi
  refine ⟨c, hc, by linarith, fun x hx hx0 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := (hsg x hx hx0).1 h; linarith
  · have := (hsg x hx hx0).2 h; linarith

/-! ### Pair j = 6: `D = F 6 - F 7`, `D' * P = N`,
`N = -x**2/448 - x/1040 + 9/7280` -/

theorem arm_ladder_p6_P_pos (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    0 < (1 + (1 / 2 : ℝ) * x) * (1 + (13 / 14 : ℝ) * x) * (1 + (15 / 16 : ℝ) * x) := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (13 / 14 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (15 / 16 : ℝ) * x := by nlinarith
  positivity

theorem arm_ladder_p6_fac (x : ℝ) (hx : x ∈ arm_ladder_S) (hx0 : 0 < x) :
    (logSumDeriv (arm_ladder_terms 6) x - logSumDeriv (arm_ladder_terms 7) x) *
      ((1 + (1 / 2 : ℝ) * x) * (1 + (13 / 14 : ℝ) * x) * (1 + (15 / 16 : ℝ) * x)) = polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x := by
  have hpos0 : 0 < 1 + (1 / 2 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (13 / 14 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (15 / 16 : ℝ) * x := by nlinarith
  have hne0 : 1 + (1 / 2 : ℝ) * x ≠ 0 := by nlinarith [hpos0]
  have hne1 : 1 + (13 / 14 : ℝ) * x ≠ 0 := by nlinarith [hpos1]
  have hne2 : 1 + (15 / 16 : ℝ) * x ≠ 0 := by nlinarith [hpos2]
  simp only [logSumDeriv, arm_ladder_terms, polyEval]
  norm_num at hne0 hne1 hne2 ⊢
  field_simp
  ring

theorem arm_ladder_p6_L0 (x : ℝ) (hs : 0 ≤ x - (0 : ℝ)) (ht : 0 ≤ (1 / 2 : ℝ) - x) :
    0 < polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x := by
  simp only [polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem arm_ladder_p6_R0 (x : ℝ) (hs : 0 ≤ x - (5 / 8 : ℝ)) :
    polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x < 0 := by
  simp only [polyEval]
  linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]

theorem arm_ladder_p6_C (x : ℝ) (hs : 0 ≤ x - (1 / 2 : ℝ)) (ht : 0 ≤ (5 / 8 : ℝ) - x) :
    polyDeriv [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x < 0 := by
  simp only [polyDeriv, polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem arm_ladder_p6_sign : ∃ s, 0 < s ∧
    (∀ x ∈ arm_ladder_S, 0 < x → x < s → 0 < polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x) ∧
    (∀ x ∈ arm_ladder_S, s < x → polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x < 0) := by
  have hleft : ∀ x ∈ arm_ladder_S, 0 < x → x ≤ (1 / 2 : ℝ) → 0 < polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x := by
    intro x hx hx0 hxa
    exact arm_ladder_p6_L0 x (by linarith) (by linarith)
  have hright : ∀ x ∈ arm_ladder_S, (5 / 8 : ℝ) ≤ x → polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x < 0 := by
    intro x hx hxb
    exact arm_ladder_p6_R0 x (by linarith)
  exact sign_change_of_cell (S := arm_ladder_S) (N' := polyDeriv [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)])
    (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num))
    (fun x _ => hasDerivAt_polyEval [(9 / 7280 : ℝ), (-1 / 1040 : ℝ), (-1 / 448 : ℝ)] x)
    (fun x hx => arm_ladder_p6_C x (by linarith [hx.1]) (by linarith [hx.2]))
    hleft hright (Set.self_mem_Ici)

/-- `arm_ladder_p6_vlo_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 2)`.
    Route: the order-48 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [328097054436574012171846638201421/809186901352438211724918443212800, 328097054436579761790592920199021/809186901352438211724918443212800], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vlo_a0 :
    (328097054436574012171846638201421 / 809186901352438211724918443212800 : ℝ) ≤ Real.log (3 / 2) ∧
      Real.log (3 / 2) ≤ (328097054436579761790592920199021 / 809186901352438211724918443212800 : ℝ) := by
  have hx : |((-(1 / 2)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 48
  rw [show (1 : ℝ) - (-(1 / 2)) = (3 / 2) by norm_num] at h
  generalize Real.log (3 / 2) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p6_vlo_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (343559 / 300000)`.
    Route: the order-48 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [4880869372301829187523774012181014872339878102337621253188170853989844201475686168653123517432251485427424412646468239614991129328001732163044304086096393429923786481660583914684035685819766390710936758767197735576495192068940159694162659293713876054519815655082359797989457079854511/36000881900932468564732728319333745169601584000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 4880869372301829187523774012181014872340604798042095734613758189484173596972280270311143122197814802407762757356193851522262549324174919237541563349379149971863336781788836486388701637902095579093876854727065856072801884945780068508746761790079530961975118207576250467751120253258063/36000881900932468564732728319333745169601584000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vlo_a1 :
    (4880869372301829187523774012181014872339878102337621253188170853989844201475686168653123517432251485427424412646468239614991129328001732163044304086096393429923786481660583914684035685819766390710936758767197735576495192068940159694162659293713876054519815655082359797989457079854511 / 36000881900932468564732728319333745169601584000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (343559 / 300000) ∧
      Real.log (343559 / 300000) ≤ (4880869372301829187523774012181014872340604798042095734613758189484173596972280270311143122197814802407762757356193851522262549324174919237541563349379149971863336781788836486388701637902095579093876854727065856072801884945780068508746761790079530961975118207576250467751120253258063 / 36000881900932468564732728319333745169601584000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(43559 / 300000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 48
  rw [show (1 : ℝ) - (-(43559 / 300000)) = (343559 / 300000) by norm_num] at h
  generalize Real.log (343559 / 300000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p6_vlo_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (343559 / 200000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [573062405365114268458818425983822785854887889670665689680149315554051954427434751956825470361559398965996328772072407681304212699702787804165356104427783364596178770697277179384651365703855232231969139376361238641434779598238818382580890870799266142867188260589002059319795079349403771/1059183841190592101457136585816187555253015024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 573062405365121794412660350531848779972303462263345153161411545657211203423398415314898915575451498660312599019058545421102356056432304202830828100647523412330084487422103136625857063978277443616498797989075253344457697562352160962967865254771287253039162688317638105866993485345855643/1059183841190592101457136585816187555253015024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vlo_a2 :
    (573062405365114268458818425983822785854887889670665689680149315554051954427434751956825470361559398965996328772072407681304212699702787804165356104427783364596178770697277179384651365703855232231969139376361238641434779598238818382580890870799266142867188260589002059319795079349403771 / 1059183841190592101457136585816187555253015024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (343559 / 200000) ∧
      Real.log (343559 / 200000) ≤ (573062405365121794412660350531848779972303462263345153161411545657211203423398415314898915575451498660312599019058545421102356056432304202830828100647523412330084487422103136625857063978277443616498797989075253344457697562352160962967865254771287253039162688317638105866993485345855643 / 1059183841190592101457136585816187555253015024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p6_vlo_a0
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p6_vlo_a1
  have hfold : Real.log (343559 / 200000) = Real.log (3 / 2) + Real.log (343559 / 300000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((343559 / 300000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p6_vlo_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (3266267 / 3150000)`.
    Route: the order-48 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [754233488250115505187712739210106773814537020098426116693394526282521240418528116445332347088677602976936150415476870069664070389660973469365298908725725627356626525476298305560150408090626479006123517717221701430126599942246414613646874474746352432963432371562693573679546350489300687124684892956240549729065241840270957616362950683/20809144954081051327855283243085987933037479401785856394744230461511138806506100237153652147491370945400292782778706168755888938903808593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 107747641178587929312530391315729539116362431442632302384770646611789129406825482096248819183913648529108614992346108376190529746508713138254878186125855113447588334176178196731280500299328928997529555876612525568112125477982740237923995874289548540139378917723073288210132226657607827422580685418097537962890620307347310875689432877/2972734993440150189693611891869426847576782771683693770677747208787305543786585748164807449641624420771470397539815166965126991271972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vlo_a3 :
    (754233488250115505187712739210106773814537020098426116693394526282521240418528116445332347088677602976936150415476870069664070389660973469365298908725725627356626525476298305560150408090626479006123517717221701430126599942246414613646874474746352432963432371562693573679546350489300687124684892956240549729065241840270957616362950683 / 20809144954081051327855283243085987933037479401785856394744230461511138806506100237153652147491370945400292782778706168755888938903808593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (3266267 / 3150000) ∧
      Real.log (3266267 / 3150000) ≤ (107747641178587929312530391315729539116362431442632302384770646611789129406825482096248819183913648529108614992346108376190529746508713138254878186125855113447588334176178196731280500299328928997529555876612525568112125477982740237923995874289548540139378917723073288210132226657607827422580685418097537962890620307347310875689432877 / 2972734993440150189693611891869426847576782771683693770677747208787305543786585748164807449641624420771470397539815166965126991271972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(116267 / 3150000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 48
  rw [show (1 : ℝ) - (-(116267 / 3150000)) = (3266267 / 3150000) by norm_num] at h
  generalize Real.log (3266267 / 3150000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p6_vlo_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (3266267 / 1400000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [299692964387377284698663686384858956785393084502091439223599302469805039886436660913975110460417115563204961103949303566304320810964321483634000175095149068439955440099284938716762241996134400143104099801192768924312152199018189048431996866070687991360378350316565790752552287958318111681119643180256089345394109111284606279478170161611/353755464219377872573539815132461794861637149830359558710651917845689359710603704031612086507353306071804977307238004868850111961364746093750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 42813280626768901695167202400658945139170650737398161371155420323996287574705564704642604923785152582802693799149039791574810301711187399371001256214120653622863980619256076350085149852744841792958002449902412934657906133125706584044707929862922325182369441601292245899572247853179333066183871652107658145369140545224904284886720358909/50536494888482553224791402161780256408805307118622794101521702549384194244371957718801726643907615153114996758176857838407158851623535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vlo_a4 :
    (299692964387377284698663686384858956785393084502091439223599302469805039886436660913975110460417115563204961103949303566304320810964321483634000175095149068439955440099284938716762241996134400143104099801192768924312152199018189048431996866070687991360378350316565790752552287958318111681119643180256089345394109111284606279478170161611 / 353755464219377872573539815132461794861637149830359558710651917845689359710603704031612086507353306071804977307238004868850111961364746093750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (3266267 / 1400000) ∧
      Real.log (3266267 / 1400000) ≤ (42813280626768901695167202400658945139170650737398161371155420323996287574705564704642604923785152582802693799149039791574810301711187399371001256214120653622863980619256076350085149852744841792958002449902412934657906133125706584044707929862922325182369441601292245899572247853179333066183871652107658145369140545224904284886720358909 / 50536494888482553224791402161780256408805307118622794101521702549384194244371957718801726643907615153114996758176857838407158851623535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p6_vlo_a0
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p6_vlo_a3
  have hfold : Real.log (3266267 / 1400000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (3266267 / 3150000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((3266267 / 3150000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p6_vlo_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (750677 / 720000)`.
    Route: the order-48 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [4015026704853837276064263290659233140016771430087235864603996552175562839927924514787977771590227106311499769081595699724155944495966566746246262589855265075827066169221331605427739471501964228382828414743056100688578200927944897311425515554969702584276587260063318901339676918938704589944395661420856867/96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 4015026704853837276064263290659233140016771430087235864603996552189616151833629535187994759945492689630217161592558889343747928869142565277216127660619990162143458584843266929228376224369727332383135157722552252973987639042589146752022585837164432446675905511103262277008254920493371103956422864849779011/96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vlo_a5 :
    (4015026704853837276064263290659233140016771430087235864603996552175562839927924514787977771590227106311499769081595699724155944495966566746246262589855265075827066169221331605427739471501964228382828414743056100688578200927944897311425515554969702584276587260063318901339676918938704589944395661420856867 / 96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (750677 / 720000) ∧
      Real.log (750677 / 720000) ≤ (4015026704853837276064263290659233140016771430087235864603996552189616151833629535187994759945492689630217161592558889343747928869142565277216127660619990162143458584843266929228376224369727332383135157722552252973987639042589146752022585837164432446675905511103262277008254920493371103956422864849779011 / 96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(30677 / 720000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 48
  rw [show (1 : ℝ) - (-(30677 / 720000)) = (750677 / 720000) by norm_num] at h
  generalize Real.log (750677 / 720000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p6_vlo_a6` -- a certified RATIONAL ENCLOSURE of `Real.log (750677 / 320000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [82048931676956064109353818619949523243242800445960489930249060669079325268145680360103084563681744581453938800357115699724155944495966566746246262589855265075827066169221331605427739471501964228382828414743056100688578200927944897311425515554969702584276587260063318901339676918938704589944395661420856867/96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 82048931676957431586436609439484778034522699248838439911415732671893892899433077809219593439164246154267284020580078889343747928869142565277216127660619990162143458584843266929228376224369727332383135157722552252973987639042589146752022585837164432446675905511103262277008254920493371103956422864849779011/96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vlo_a6 :
    (82048931676956064109353818619949523243242800445960489930249060669079325268145680360103084563681744581453938800357115699724155944495966566746246262589855265075827066169221331605427739471501964228382828414743056100688578200927944897311425515554969702584276587260063318901339676918938704589944395661420856867 / 96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (750677 / 320000) ∧
      Real.log (750677 / 320000) ≤ (82048931676957431586436609439484778034522699248838439911415732671893892899433077809219593439164246154267284020580078889343747928869142565277216127660619990162143458584843266929228376224369727332383135157722552252973987639042589146752022585837164432446675905511103262277008254920493371103956422864849779011 / 96227645007725433863491544260138443576866384030468951032289914455128841718069838820179406907409821115392110624768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p6_vlo_a0
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p6_vlo_a5
  have hfold : Real.log (750677 / 320000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (750677 / 720000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((750677 / 720000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p6_vhi_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (2863 / 2500)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [30546368685108024760786745109091159424827456837956049809578218374662439273868110022788057541165444285287712933641443172627/225302608749568256119033549111918546259403228759765625000000000000000000000000000000000000000000000000000000000000000000000, 30546368685108024760786745225726467970678001128353167190631628592077015980440782949933692988329084298227759175597429949139/225302608749568256119033549111918546259403228759765625000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vhi_a0 :
    (30546368685108024760786745109091159424827456837956049809578218374662439273868110022788057541165444285287712933641443172627 / 225302608749568256119033549111918546259403228759765625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (2863 / 2500) ∧
      Real.log (2863 / 2500) ≤ (30546368685108024760786745225726467970678001128353167190631628592077015980440782949933692988329084298227759175597429949139 / 225302608749568256119033549111918546259403228759765625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(363 / 2500)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(363 / 2500)) = (2863 / 2500) by norm_num] at h
  generalize Real.log (2863 / 2500) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p6_vhi_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (8589 / 5000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [36203918428005765972249626123574020803663558133089968805194578222810714775950719469614732777226136952730450741291508622270219/66914874798621772067352964086239808239042758941650390625000000000000000000000000000000000000000000000000000000000000000000000, 36203918459165432711012040272463163915355122811935173275542461082028917637591011336789486505033738036573644475152436694894283/66914874798621772067352964086239808239042758941650390625000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vhi_a1 :
    (36203918428005765972249626123574020803663558133089968805194578222810714775950719469614732777226136952730450741291508622270219 / 66914874798621772067352964086239808239042758941650390625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (8589 / 5000) ∧
      Real.log (8589 / 5000) ≤ (36203918459165432711012040272463163915355122811935173275542461082028917637591011336789486505033738036573644475152436694894283 / 66914874798621772067352964086239808239042758941650390625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p6_vhi_a0
  have hfold : Real.log (8589 / 5000) = Real.log (3 / 2) + Real.log (2863 / 2500) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((2863 / 2500) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p6_vhi_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (9073 / 8750)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [362615201405633498902109636866923942135553306623589011510891785006053271284332704188622858936311953383261044455860381642999764829041332223/10003379467408877599380308616170539620383736297434825163172157982960364108748763101175427436828613281250000000000000000000000000000000000000, 362615201405633498902109636866923942135553306731964055201134890217713297637175909979351410650763093027176387055882274893437867906196597311/10003379467408877599380308616170539620383736297434825163172157982960364108748763101175427436828613281250000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vhi_a2 :
    (362615201405633498902109636866923942135553306623589011510891785006053271284332704188622858936311953383261044455860381642999764829041332223 / 10003379467408877599380308616170539620383736297434825163172157982960364108748763101175427436828613281250000000000000000000000000000000000000 : ℝ) ≤ Real.log (9073 / 8750) ∧
      Real.log (9073 / 8750) ≤ (362615201405633498902109636866923942135553306731964055201134890217713297637175909979351410650763093027176387055882274893437867906196597311 / 10003379467408877599380308616170539620383736297434825163172157982960364108748763101175427436828613281250000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(323 / 8750)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(323 / 8750)) = (9073 / 8750) by norm_num] at h
  generalize Real.log (9073 / 8750) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p6_vhi_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (81657 / 35000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [210562653258863988203324102947098631258560367218777320776703455459611452522614849992473848831475029649524103615371420439828838510802101766483/248545505228697497276910744847929561337226678774726809823431309884322892855834652436897158622741699218750000000000000000000000000000000000000, 210562653490340028042019533401813548694736869681363659049658285282469858424519594802033457595421702078640269704955695406805426624457094122131/248545505228697497276910744847929561337226678774726809823431309884322892855834652436897158622741699218750000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vhi_a3 :
    (210562653258863988203324102947098631258560367218777320776703455459611452522614849992473848831475029649524103615371420439828838510802101766483 / 248545505228697497276910744847929561337226678774726809823431309884322892855834652436897158622741699218750000000000000000000000000000000000000 : ℝ) ≤ Real.log (81657 / 35000) ∧
      Real.log (81657 / 35000) ≤ (210562653490340028042019533401813548694736869681363659049658285282469858424519594802033457595421702078640269704955695406805426624457094122131 / 248545505228697497276910744847929561337226678774726809823431309884322892855834652436897158622741699218750000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p6_vhi_a2
  have hfold : Real.log (81657 / 35000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (9073 / 8750) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((9073 / 8750) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `arm_ladder_p6_vhi_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (18767 / 18000)`.
    Route: the order-32 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [835017725641272083374133799674576099579897024735826607181882883603299860691330177793591295613558769505845032188280109034591636576248428268574580189/20010849181966043832896998790344998744101430522544128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 278339241880424027791377933224858699859965683197852335207643426505131630968399492507426958049800449713766249222459302604787229388690741378346756191/6670283060655347944298999596781666248033810174181376000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vhi_a4 :
    (835017725641272083374133799674576099579897024735826607181882883603299860691330177793591295613558769505845032188280109034591636576248428268574580189 / 20010849181966043832896998790344998744101430522544128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (18767 / 18000) ∧
      Real.log (18767 / 18000) ≤ (278339241880424027791377933224858699859965683197852335207643426505131630968399492507426958049800449713766249222459302604787229388690741378346756191 / 6670283060655347944298999596781666248033810174181376000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(767 / 18000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  rw [show (1 : ℝ) - (-(767 / 18000)) = (18767 / 18000) by norm_num] at h
  generalize Real.log (18767 / 18000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `arm_ladder_p6_vhi_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (18767 / 8000)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [2439926055714575843618837635079997348671159511369030579787009252355271880078860215424483555272738904039335839602924055591946604030403525242406164967027/2861551433021144268104270827019334820406504564723810304000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 813308686126534430538233913218886146351902936323116974254693009990233823228481127428562055001121464309068573638811680272484573802582776017103586135313/953850477673714756034756942339778273468834854907936768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem arm_ladder_p6_vhi_a5 :
    (2439926055714575843618837635079997348671159511369030579787009252355271880078860215424483555272738904039335839602924055591946604030403525242406164967027 / 2861551433021144268104270827019334820406504564723810304000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (18767 / 8000) ∧
      Real.log (18767 / 8000) ≤ (813308686126534430538233913218886146351902936323116974254693009990233823228481127428562055001121464309068573638811680272484573802582776017103586135313 / 953850477673714756034756942339778273468834854907936768000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := arm_ladder_p3_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := arm_ladder_p6_vhi_a4
  have hfold : Real.log (18767 / 8000) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (18767 / 18000) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((18767 / 18000) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

theorem arm_ladder_p6_vlo : 0 < arm_ladder_F 6 (143559 / 100000 : ℝ) - arm_ladder_F 7 (143559 / 100000 : ℝ) := by
  have h0 := arm_ladder_p6_vlo_a0
  have h1 := arm_ladder_p6_vlo_a1
  have h2 := arm_ladder_p6_vlo_a2
  have h3 := arm_ladder_p6_vlo_a3
  have h4 := arm_ladder_p6_vlo_a4
  have h5 := arm_ladder_p6_vlo_a5
  have h6 := arm_ladder_p6_vlo_a6
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

theorem arm_ladder_p6_vhi : arm_ladder_F 6 (3589 / 2500 : ℝ) - arm_ladder_F 7 (3589 / 2500 : ℝ) < 0 := by
  have h0 := arm_ladder_p3_vlo_a1
  have h1 := arm_ladder_p6_vhi_a0
  have h2 := arm_ladder_p6_vhi_a1
  have h3 := arm_ladder_p6_vhi_a2
  have h4 := arm_ladder_p6_vhi_a3
  have h5 := arm_ladder_p6_vhi_a4
  have h6 := arm_ladder_p6_vhi_a5
  simp only [arm_ladder_F, arm_ladder_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

/-- (a) `F 6` and `F 7` cross EXACTLY ONCE on `S ∩ (0, oo)`, at a point of
`(143559/100000, 3589/2500)`: `F 6` is ahead before it, `F 7` after it. -/
theorem arm_ladder_p6_cross : ∃ c ∈ Set.Ioo ((143559 / 100000 : ℝ)) ((3589 / 2500 : ℝ)),
    arm_ladder_F 6 c = arm_ladder_F 7 c ∧ ∀ x ∈ arm_ladder_S, 0 < x →
      (x < c → arm_ladder_F 7 x < arm_ladder_F 6 x) ∧ (c < x → arm_ladder_F 6 x < arm_ladder_F 7 x) := by
  have hD0 : arm_ladder_F 6 0 - arm_ladder_F 7 0 = 0 := by simp [arm_ladder_F, logSum_zero]
  have hd : ∀ x ∈ arm_ladder_S, HasDerivAt (fun y => arm_ladder_F 6 y - arm_ladder_F 7 y)
      (logSumDeriv (arm_ladder_terms 6) x - logSumDeriv (arm_ladder_terms 7) x) x :=
    fun x hx => (hasDerivAt_logSum _ x (arm_ladder_argpos 6 (by norm_num) x hx)).sub
      (hasDerivAt_logSum _ x (arm_ladder_argpos 7 (by norm_num) x hx))
  obtain ⟨s, hs, hNp, hNn⟩ := arm_ladder_p6_sign
  obtain ⟨c, hc, hDc, hsg⟩ := single_crossing_core (S := arm_ladder_S)
    (P := fun x => (1 + (1 / 2 : ℝ) * x) * (1 + (13 / 14 : ℝ) * x) * (1 + (15 / 16 : ℝ) * x)) (Set.self_mem_Ici) hD0 hd arm_ladder_p6_fac arm_ladder_p6_P_pos
    hs hNp hNn (by norm_num) (by norm_num) (Set.mem_Ici.mpr (by norm_num)) arm_ladder_p6_vlo arm_ladder_p6_vhi
  refine ⟨c, hc, by linarith, fun x hx hx0 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := (hsg x hx hx0).1 h; linarith
  · have := (hsg x hx hx0).2 h; linarith

/-- (b) the brackets increase, so the breakpoints do. -/
theorem arm_ladder_brackets_increasing : (43051 / 100000 : ℝ) < (87247 / 100000 : ℝ) ∧ (5453 / 6250 : ℝ) < (119239 / 100000 : ℝ) ∧ (2981 / 2500 : ℝ) < (143559 / 100000 : ℝ) := by norm_num

/-- (c) THE LADDER over members 1..7: the breakpoints `Λ j` (0 for a
dominated pair, the unique crossing in its bracket otherwise) and, on
`(Λ (j-1), Λ j)`, `F j` is the UNIQUE maximum of `F 1, ..., F 7`. -/
theorem arm_ladder : ∃ Λ : ℕ → ℝ,
    Λ 1 = 0 ∧
    Λ 2 = 0 ∧
    ((861 / 2000 : ℝ) < Λ 3 ∧ Λ 3 < (43051 / 100000 : ℝ) ∧ arm_ladder_F 3 (Λ 3) = arm_ladder_F 4 (Λ 3)) ∧
    ((87247 / 100000 : ℝ) < Λ 4 ∧ Λ 4 < (5453 / 6250 : ℝ) ∧ arm_ladder_F 4 (Λ 4) = arm_ladder_F 5 (Λ 4)) ∧
    ((119239 / 100000 : ℝ) < Λ 5 ∧ Λ 5 < (2981 / 2500 : ℝ) ∧ arm_ladder_F 5 (Λ 5) = arm_ladder_F 6 (Λ 5)) ∧
    ((143559 / 100000 : ℝ) < Λ 6 ∧ Λ 6 < (3589 / 2500 : ℝ) ∧ arm_ladder_F 6 (Λ 6) = arm_ladder_F 7 (Λ 6)) ∧
    (∀ j, 1 ≤ j → j < 6 → Λ j ≤ Λ (j + 1)) ∧
    (∀ j, 1 ≤ j → j ≤ 7 → ∀ x ∈ arm_ladder_S, 0 < x →
      (j = 1 ∨ Λ (j - 1) < x) → (j = 7 ∨ x < Λ j) →
      ∀ k, 1 ≤ k → k ≤ 7 → k ≠ j → arm_ladder_F k x < arm_ladder_F j x) := by
  obtain ⟨c3, hc3, hz3, hs3⟩ := arm_ladder_p3_cross
  obtain ⟨c4, hc4, hz4, hs4⟩ := arm_ladder_p4_cross
  obtain ⟨c5, hc5, hz5, hs5⟩ := arm_ladder_p5_cross
  obtain ⟨c6, hc6, hz6, hs6⟩ := arm_ladder_p6_cross
  have hcross : ∀ j, 1 ≤ j → j ≤ 6 → ∀ x ∈ arm_ladder_S, 0 < x →
      (x < (fun j : ℕ => if j = 3 then c3 else if j = 4 then c4 else if j = 5 then c5 else if j = 6 then c6 else 0) j → arm_ladder_F (j + 1) x < arm_ladder_F j x) ∧
      ((fun j : ℕ => if j = 3 then c3 else if j = 4 then c4 else if j = 5 then c5 else if j = 6 then c6 else 0) j < x → arm_ladder_F j x < arm_ladder_F (j + 1) x) := by
    intro j hja hjJ x hx hx0
    interval_cases j
    · refine ⟨fun h => ?_, fun _ => by simpa using arm_ladder_p1_dom x hx hx0⟩
      simp at h; linarith
    · refine ⟨fun h => ?_, fun _ => by simpa using arm_ladder_p2_dom x hx hx0⟩
      simp at h; linarith
    · simpa using hs3 x hx hx0
    · simpa using hs4 x hx hx0
    · simpa using hs5 x hx hx0
    · simpa using hs6 x hx hx0
  have hmono : ∀ j, 1 ≤ j → j < 6 → (fun j : ℕ => if j = 3 then c3 else if j = 4 then c4 else if j = 5 then c5 else if j = 6 then c6 else 0) j ≤
      (fun j : ℕ => if j = 3 then c3 else if j = 4 then c4 else if j = 5 then c5 else if j = 6 then c6 else 0) (j + 1) := by
    intro j hja hjJ
    interval_cases j <;> simp <;> linarith [hc3.1, hc3.2, hc4.1, hc4.2, hc5.1, hc5.2, hc6.1, hc6.2]
  refine ⟨fun j : ℕ => if j = 3 then c3 else if j = 4 then c4 else if j = 5 then c5 else if j = 6 then c6 else 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
    exact ⟨hc3.1, hc3.2, hz3⟩
  · simp
    exact ⟨hc4.1, hc4.2, hz4⟩
  · simp
    exact ⟨hc5.1, hc5.2, hz5⟩
  · simp
    exact ⟨hc6.1, hc6.2, hz6⟩
  · exact hmono
  · exact ladder_core (a := 1) (J := 6) hcross hmono

/-- On `x ≤ (861 / 2000 : ℝ)`, member 3 is the UNIQUE maximum of members 1..7. -/
theorem arm_ladder_best_3 : ∀ x ∈ arm_ladder_S, 0 < x → x ≤ (861 / 2000 : ℝ) →
    ∀ k, 1 ≤ k → k ≤ 7 → k ≠ 3 → arm_ladder_F k x < arm_ladder_F 3 x := by
  obtain ⟨Λ, hL1, hL2, hL3, hL4, hL5, hL6, hmono, hlad⟩ := arm_ladder
  intro x hx hx0 hb
  exact hlad 3 (by norm_num) (by norm_num) x hx hx0
    (Or.inr (by norm_num; linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))
    (Or.inr (by linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))

/-- On `(43051 / 100000 : ℝ) ≤ x ∧ x ≤ (87247 / 100000 : ℝ)`, member 4 is the UNIQUE maximum of members 1..7. -/
theorem arm_ladder_best_4 : ∀ x ∈ arm_ladder_S, 0 < x → (43051 / 100000 : ℝ) ≤ x ∧ x ≤ (87247 / 100000 : ℝ) →
    ∀ k, 1 ≤ k → k ≤ 7 → k ≠ 4 → arm_ladder_F k x < arm_ladder_F 4 x := by
  obtain ⟨Λ, hL1, hL2, hL3, hL4, hL5, hL6, hmono, hlad⟩ := arm_ladder
  intro x hx hx0 hb
  obtain ⟨hb1, hb2⟩ := hb
  exact hlad 4 (by norm_num) (by norm_num) x hx hx0
    (Or.inr (by norm_num; linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))
    (Or.inr (by linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))

/-- On `(5453 / 6250 : ℝ) ≤ x ∧ x ≤ (119239 / 100000 : ℝ)`, member 5 is the UNIQUE maximum of members 1..7. -/
theorem arm_ladder_best_5 : ∀ x ∈ arm_ladder_S, 0 < x → (5453 / 6250 : ℝ) ≤ x ∧ x ≤ (119239 / 100000 : ℝ) →
    ∀ k, 1 ≤ k → k ≤ 7 → k ≠ 5 → arm_ladder_F k x < arm_ladder_F 5 x := by
  obtain ⟨Λ, hL1, hL2, hL3, hL4, hL5, hL6, hmono, hlad⟩ := arm_ladder
  intro x hx hx0 hb
  obtain ⟨hb1, hb2⟩ := hb
  exact hlad 5 (by norm_num) (by norm_num) x hx hx0
    (Or.inr (by norm_num; linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))
    (Or.inr (by linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))

/-- On `(2981 / 2500 : ℝ) ≤ x ∧ x ≤ (143559 / 100000 : ℝ)`, member 6 is the UNIQUE maximum of members 1..7. -/
theorem arm_ladder_best_6 : ∀ x ∈ arm_ladder_S, 0 < x → (2981 / 2500 : ℝ) ≤ x ∧ x ≤ (143559 / 100000 : ℝ) →
    ∀ k, 1 ≤ k → k ≤ 7 → k ≠ 6 → arm_ladder_F k x < arm_ladder_F 6 x := by
  obtain ⟨Λ, hL1, hL2, hL3, hL4, hL5, hL6, hmono, hlad⟩ := arm_ladder
  intro x hx hx0 hb
  obtain ⟨hb1, hb2⟩ := hb
  exact hlad 6 (by norm_num) (by norm_num) x hx hx0
    (Or.inr (by norm_num; linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))
    (Or.inr (by linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))

/-- On `(3589 / 2500 : ℝ) ≤ x`, member 7 is the UNIQUE maximum of members 1..7. -/
theorem arm_ladder_best_7 : ∀ x ∈ arm_ladder_S, 0 < x → (3589 / 2500 : ℝ) ≤ x →
    ∀ k, 1 ≤ k → k ≤ 7 → k ≠ 7 → arm_ladder_F k x < arm_ladder_F 7 x := by
  obtain ⟨Λ, hL1, hL2, hL3, hL4, hL5, hL6, hmono, hlad⟩ := arm_ladder
  intro x hx hx0 hb
  exact hlad 7 (by norm_num) (by norm_num) x hx hx0
    (Or.inr (by norm_num; linarith [hL1, hL2, hL3.1, hL3.2.1, hL4.1, hL4.2.1, hL5.1, hL5.2.1, hL6.1, hL6.2.1]))
    (Or.inl rfl)

/-! ## Instance `double_dip_bounded`

Family `F_j(x) = (j) log(1 + (1) x) + (-3*j/2) log(1 + (1/10) x) + (-j/2) log(1 + (2) x)` on `S = Icc 0 (2)`, members j = 0..1.
Pairs: 0 dominated, 1 crossing (brackets 0: (97/100, 49/50)).
conjecture1_proved = False. -/

noncomputable def double_dip_bounded_terms (j : ℕ) : List (ℝ × ℝ) :=
  [(((j : ℝ)), ((1 : ℝ))), (((-3 : ℝ) * (j : ℝ)) / ((2 : ℝ)), ((1 : ℝ)) / ((10 : ℝ))), (((-1 : ℝ) * (j : ℝ)) / ((2 : ℝ)), ((2 : ℝ)))]

noncomputable def double_dip_bounded_F (j : ℕ) (x : ℝ) : ℝ := logSum (double_dip_bounded_terms j) x

/-- The domain `S`. -/
abbrev double_dip_bounded_S : Set ℝ := Set.Icc (0 : ℝ) (2 : ℝ)

theorem double_dip_bounded_argpos (j : ℕ) (hj : 0 ≤ j ∧ j ≤ 1) :
    ∀ x ∈ double_dip_bounded_S, ∀ p ∈ double_dip_bounded_terms j, 0 < 1 + p.2 * x := by
  obtain ⟨hj1, hj2⟩ := hj
  intro x hx p hp
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hxX : x ≤ (2 : ℝ) := hx.2
  interval_cases j <;>
  · simp only [double_dip_bounded_terms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num <;> nlinarith

/-! ### Pair j = 0: `D = F 0 - F 1`, `D' * P = N`,
`N = x**2/5 - 11*x/20 + 3/20` -/

theorem double_dip_bounded_p0_P_pos (x : ℝ) (hx : x ∈ double_dip_bounded_S) (hx0 : 0 < x) :
    0 < (1 + (1 / 10 : ℝ) * x) * (1 + (1 : ℝ) * x) * (1 + (2 : ℝ) * x) := by
  have hxX : x ≤ (2 : ℝ) := hx.2
  have hpos0 : 0 < 1 + (1 / 10 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (1 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (2 : ℝ) * x := by nlinarith
  positivity

theorem double_dip_bounded_p0_fac (x : ℝ) (hx : x ∈ double_dip_bounded_S) (hx0 : 0 < x) :
    (logSumDeriv (double_dip_bounded_terms 0) x - logSumDeriv (double_dip_bounded_terms 1) x) *
      ((1 + (1 / 10 : ℝ) * x) * (1 + (1 : ℝ) * x) * (1 + (2 : ℝ) * x)) = polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x := by
  have hxX : x ≤ (2 : ℝ) := hx.2
  have hpos0 : 0 < 1 + (1 / 10 : ℝ) * x := by nlinarith
  have hpos1 : 0 < 1 + (1 : ℝ) * x := by nlinarith
  have hpos2 : 0 < 1 + (2 : ℝ) * x := by nlinarith
  have hne0 : 1 + (1 / 10 : ℝ) * x ≠ 0 := by nlinarith [hpos0]
  have hne1 : 1 + (1 : ℝ) * x ≠ 0 := by nlinarith [hpos1]
  have hne2 : 1 + (2 : ℝ) * x ≠ 0 := by nlinarith [hpos2]
  simp only [logSumDeriv, double_dip_bounded_terms, polyEval]
  norm_num at hne0 hne1 hne2 ⊢
  field_simp
  ring

theorem double_dip_bounded_p0_L0 (x : ℝ) (hs : 0 ≤ x - (0 : ℝ)) (ht : 0 ≤ (1 / 4 : ℝ) - x) :
    0 < polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x := by
  simp only [polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem double_dip_bounded_p0_R0 (x : ℝ) (hs : 0 ≤ x - (3 / 8 : ℝ)) (ht : 0 ≤ (2 : ℝ) - x) :
    polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x < 0 := by
  simp only [polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem double_dip_bounded_p0_C (x : ℝ) (hs : 0 ≤ x - (1 / 4 : ℝ)) (ht : 0 ≤ (3 / 8 : ℝ) - x) :
    polyDeriv [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x < 0 := by
  simp only [polyDeriv, polyEval]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem double_dip_bounded_p0_sign : ∃ s, 0 < s ∧
    (∀ x ∈ double_dip_bounded_S, 0 < x → x < s → 0 < polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x) ∧
    (∀ x ∈ double_dip_bounded_S, s < x → polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x < 0) := by
  have hleft : ∀ x ∈ double_dip_bounded_S, 0 < x → x ≤ (1 / 4 : ℝ) → 0 < polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x := by
    intro x hx hx0 hxa
    exact double_dip_bounded_p0_L0 x (by linarith) (by linarith)
  have hright : ∀ x ∈ double_dip_bounded_S, (3 / 8 : ℝ) ≤ x → polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x < 0 := by
    intro x hx hxb
    have hxX : x ≤ (2 : ℝ) := hx.2
    exact double_dip_bounded_p0_R0 x (by linarith) (by linarith)
  exact sign_change_of_cell (S := double_dip_bounded_S) (N' := polyDeriv [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)])
    (by norm_num) (by norm_num) (⟨by norm_num, by norm_num⟩)
    (fun x _ => hasDerivAt_polyEval [(3 / 20 : ℝ), (-11 / 20 : ℝ), (1 / 5 : ℝ)] x)
    (fun x hx => double_dip_bounded_p0_C x (by linarith [hx.1]) (by linarith [hx.2]))
    hleft hright (Set.left_mem_Icc.mpr (by norm_num))

/-- `double_dip_bounded_p0_vlo_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (1097 / 1000)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [27681396656036518041676214727398622883933233057748865343949935688684138382613079/299002392000000000000000000000000000000000000000000000000000000000000000000000000, 7750791063690225051669348782682707402986219621746370822706478783497926381050169/83720669760000000000000000000000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vlo_a0 :
    (27681396656036518041676214727398622883933233057748865343949935688684138382613079 / 299002392000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (1097 / 1000) ∧
      Real.log (1097 / 1000) ≤ (7750791063690225051669348782682707402986219621746370822706478783497926381050169 / 83720669760000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(97 / 1000)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (-(97 / 1000)) = (1097 / 1000) by norm_num] at h
  generalize Real.log (1097 / 1000) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `double_dip_bounded_p0_vlo_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (3 / 2)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [6070423640075591/14971509072199680, 6070425424818551/14971509072199680], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vlo_a1 :
    (6070423640075591 / 14971509072199680 : ℝ) ≤ Real.log (3 / 2) ∧
      Real.log (3 / 2) ≤ (6070425424818551 / 14971509072199680 : ℝ) := by
  have hx : |((-(1 / 2)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (-(1 / 2)) = (3 / 2) by norm_num] at h
  generalize Real.log (3 / 2) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `double_dip_bounded_p0_vlo_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (197 / 225)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-23645495629850046689510448795448099641886258732654309507439511476/177923908951887069986827587960210195205945638008415699005126953125, -945819825194001867580032980458126660059286396498499889821363156/7116956358075482799473103518408407808237825520336627960205078125], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vlo_a2 :
    (-(23645495629850046689510448795448099641886258732654309507439511476 / 177923908951887069986827587960210195205945638008415699005126953125) : ℝ) ≤ Real.log (197 / 225) ∧
      Real.log (197 / 225) ≤ (-(945819825194001867580032980458126660059286396498499889821363156 / 7116956358075482799473103518408407808237825520336627960205078125) : ℝ) := by
  have hx : |((28 / 225) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (28 / 225) = (197 / 225) by norm_num] at h
  generalize Real.log (197 / 225) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `double_dip_bounded_p0_vlo_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (197 / 100)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [56671321571747172889865923890769623691324946444975090193280214061654971527/83581899857404003461731460743088483810424804687500000000000000000000000000, 2266853659968999020048891341552778745941044420810169464672908441004055887/3343275994296160138469258429723539352416992187500000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vlo_a3 :
    (56671321571747172889865923890769623691324946444975090193280214061654971527 / 83581899857404003461731460743088483810424804687500000000000000000000000000 : ℝ) ≤ Real.log (197 / 100) ∧
      Real.log (197 / 100) ≤ (2266853659968999020048891341552778745941044420810169464672908441004055887 / 3343275994296160138469258429723539352416992187500000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := double_dip_bounded_p0_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := double_dip_bounded_p0_vlo_a2
  have hfold : Real.log (197 / 100) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (197 / 225) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((197 / 225) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `double_dip_bounded_p0_vlo_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (196 / 225)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-97705354372208110710889896934327979943000509374301075700411110497/708082967605479506952653954115760370768839493393898010253906250000, -3908214174888324428431893441234608112255315935947528787202164833/28323318704219180278106158164630414830753579735755920410156250000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vlo_a4 :
    (-(97705354372208110710889896934327979943000509374301075700411110497 / 708082967605479506952653954115760370768839493393898010253906250000) : ℝ) ≤ Real.log (196 / 225) ∧
      Real.log (196 / 225) ≤ (-(3908214174888324428431893441234608112255315935947528787202164833 / 28323318704219180278106158164630414830753579735755920410156250000) : ℝ) := by
  have hx : |((29 / 225) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (29 / 225) = (196 / 225) by norm_num] at h
  generalize Real.log (196 / 225) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `double_dip_bounded_p0_vlo_a5` -- a certified RATIONAL ENCLOSURE of `Real.log (147 / 50)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [6405568988867476287506684547420401935328415725880885972397008366279966199/5939830446719066235859088580727100372314453125000000000000000000000000000, 256222844524655164157839274500701574503999024670811198520250157376686911/237593217868762649434363543229084014892578125000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vlo_a5 :
    (6405568988867476287506684547420401935328415725880885972397008366279966199 / 5939830446719066235859088580727100372314453125000000000000000000000000000 : ℝ) ≤ Real.log (147 / 50) ∧
      Real.log (147 / 50) ≤ (256222844524655164157839274500701574503999024670811198520250157376686911 / 237593217868762649434363543229084014892578125000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := double_dip_bounded_p0_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := double_dip_bounded_p0_vlo_a4
  have hfold : Real.log (147 / 50) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (3 / 2) + Real.log (196 / 225) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((196 / 225) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `double_dip_bounded_p0_vhi_a0` -- a certified RATIONAL ENCLOSURE of `Real.log (549 / 500)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [5825166615228672224635992343691464272379645744781850734400776762642006021/62307682514190673828125000000000000000000000000000000000000000000000000000, 233006664609146888985440027233146744512701767353157775670479459570399613/2492307300567626953125000000000000000000000000000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vhi_a0 :
    (5825166615228672224635992343691464272379645744781850734400776762642006021 / 62307682514190673828125000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (549 / 500) ∧
      Real.log (549 / 500) ≤ (233006664609146888985440027233146744512701767353157775670479459570399613 / 2492307300567626953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  have hx : |((-(49 / 500)) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (-(49 / 500)) = (549 / 500) by norm_num] at h
  generalize Real.log (549 / 500) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `double_dip_bounded_p0_vhi_a1` -- a certified RATIONAL ENCLOSURE of `Real.log (22 / 25)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-54036706334493477766709736134785305993057/422712048475659685209393501281738281250000, -39299422788722529284873142787256347791/307426944345934316515922546386718750000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vhi_a1 :
    (-(54036706334493477766709736134785305993057 / 422712048475659685209393501281738281250000) : ℝ) ≤ Real.log (22 / 25) ∧
      Real.log (22 / 25) ≤ (-(39299422788722529284873142787256347791 / 307426944345934316515922546386718750000) : ℝ) := by
  have hx : |((3 / 25) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (3 / 25) = (22 / 25) by norm_num] at h
  generalize Real.log (22 / 25) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `double_dip_bounded_p0_vhi_a2` -- a certified RATIONAL ENCLOSURE of `Real.log (99 / 50)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [3633356299865322177706843341106896057181789204891/5318948507308959960937500000000000000000000000000, 29066860544011740837488114313506693570151713063/42551588058471679687500000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vhi_a2 :
    (3633356299865322177706843341106896057181789204891 / 5318948507308959960937500000000000000000000000000 : ℝ) ≤ Real.log (99 / 50) ∧
      Real.log (99 / 50) ≤ (29066860544011740837488114313506693570151713063 / 42551588058471679687500000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := double_dip_bounded_p0_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := double_dip_bounded_p0_vhi_a1
  have hfold : Real.log (99 / 50) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (22 / 25) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((22 / 25) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

/-- `double_dip_bounded_p0_vhi_a3` -- a certified RATIONAL ENCLOSURE of `Real.log (592 / 675)`.
    Route: the order-24 Taylor estimate Real.abs_log_sub_add_sum_range_le (exact rational S and radius).
    Exact fold [-34673033150992269196861419706504265603266909547512104472374234925248770983783/264263969294412181360791125133111557790183766769587236922234296798706054687500, -2773842652079381535748067327865658441587983009143599785857554909312224247857/21141117543552974508863290010648924623214701341566978953778743743896484375000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vhi_a3 :
    (-(34673033150992269196861419706504265603266909547512104472374234925248770983783 / 264263969294412181360791125133111557790183766769587236922234296798706054687500) : ℝ) ≤ Real.log (592 / 675) ∧
      Real.log (592 / 675) ≤ (-(2773842652079381535748067327865658441587983009143599785857554909312224247857 / 21141117543552974508863290010648924623214701341566978953778743743896484375000) : ℝ) := by
  have hx : |((83 / 675) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [show (1 : ℝ) - (83 / 675) = (592 / 675) by norm_num] at h
  generalize Real.log (592 / 675) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `double_dip_bounded_p0_vhi_a4` -- a certified RATIONAL ENCLOSURE of `Real.log (74 / 25)`.
    Route: the multiplicative fold log (prod f^c) = sum c log f (Real.log_mul, backwards).
    Exact fold [740201414928208769095902344918661840271528958327837348267056383050773291388590455913/682094414441495501495564098037114054944983959197998046875000000000000000000000000000, 29608066354567217019056190017993349514906781803110549924897244899040336616661204001/27283776577659820059822563921484562197799358367919921875000000000000000000000000000], inside the stated bracket with slack (0, 0).
    The generator REFUSES a bracket the fold does not imply rather than
    widening it.  A finite arithmetic fact about real constants; nothing
    about RH.  conjecture1_proved = False. -/
theorem double_dip_bounded_p0_vhi_a4 :
    (740201414928208769095902344918661840271528958327837348267056383050773291388590455913 / 682094414441495501495564098037114054944983959197998046875000000000000000000000000000 : ℝ) ≤ Real.log (74 / 25) ∧
      Real.log (74 / 25) ≤ (29608066354567217019056190017993349514906781803110549924897244899040336616661204001 / 27283776577659820059822563921484562197799358367919921875000000000000000000000000000 : ℝ) := by
  obtain ⟨h0lo, h0hi⟩ := double_dip_bounded_p0_vlo_a1
  obtain ⟨h1lo, h1hi⟩ := double_dip_bounded_p0_vhi_a3
  have hfold : Real.log (74 / 25) = Real.log (3 / 2) + Real.log (3 / 2) + Real.log (3 / 2) + Real.log (592 / 675) := by
    rw [← Real.log_mul (by norm_num : ((3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((3 / 2) : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((3 / 2) * (3 / 2) * (3 / 2) : ℝ) ≠ 0) (by norm_num : ((592 / 675) : ℝ) ≠ 0)]
    norm_num
  rw [hfold]
  constructor <;> linarith

theorem double_dip_bounded_p0_vlo : 0 < double_dip_bounded_F 0 (97 / 100 : ℝ) - double_dip_bounded_F 1 (97 / 100 : ℝ) := by
  have h0 := double_dip_bounded_p0_vlo_a0
  have h1 := double_dip_bounded_p0_vlo_a1
  have h2 := double_dip_bounded_p0_vlo_a2
  have h3 := double_dip_bounded_p0_vlo_a3
  have h4 := double_dip_bounded_p0_vlo_a4
  have h5 := double_dip_bounded_p0_vlo_a5
  simp only [double_dip_bounded_F, double_dip_bounded_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

theorem double_dip_bounded_p0_vhi : double_dip_bounded_F 0 (49 / 50 : ℝ) - double_dip_bounded_F 1 (49 / 50 : ℝ) < 0 := by
  have h0 := double_dip_bounded_p0_vhi_a0
  have h1 := double_dip_bounded_p0_vlo_a1
  have h2 := double_dip_bounded_p0_vhi_a1
  have h3 := double_dip_bounded_p0_vhi_a2
  have h4 := double_dip_bounded_p0_vhi_a3
  have h5 := double_dip_bounded_p0_vhi_a4
  simp only [double_dip_bounded_F, double_dip_bounded_terms, logSum]
  norm_num at h0 h1 h2 h3 h4 h5 ⊢
  linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

/-- (a) `F 0` and `F 1` cross EXACTLY ONCE on `S ∩ (0, oo)`, at a point of
`(97/100, 49/50)`: `F 0` is ahead before it, `F 1` after it. -/
theorem double_dip_bounded_p0_cross : ∃ c ∈ Set.Ioo ((97 / 100 : ℝ)) ((49 / 50 : ℝ)),
    double_dip_bounded_F 0 c = double_dip_bounded_F 1 c ∧ ∀ x ∈ double_dip_bounded_S, 0 < x →
      (x < c → double_dip_bounded_F 1 x < double_dip_bounded_F 0 x) ∧ (c < x → double_dip_bounded_F 0 x < double_dip_bounded_F 1 x) := by
  have hD0 : double_dip_bounded_F 0 0 - double_dip_bounded_F 1 0 = 0 := by simp [double_dip_bounded_F, logSum_zero]
  have hd : ∀ x ∈ double_dip_bounded_S, HasDerivAt (fun y => double_dip_bounded_F 0 y - double_dip_bounded_F 1 y)
      (logSumDeriv (double_dip_bounded_terms 0) x - logSumDeriv (double_dip_bounded_terms 1) x) x :=
    fun x hx => (hasDerivAt_logSum _ x (double_dip_bounded_argpos 0 (by norm_num) x hx)).sub
      (hasDerivAt_logSum _ x (double_dip_bounded_argpos 1 (by norm_num) x hx))
  obtain ⟨s, hs, hNp, hNn⟩ := double_dip_bounded_p0_sign
  obtain ⟨c, hc, hDc, hsg⟩ := single_crossing_core (S := double_dip_bounded_S)
    (P := fun x => (1 + (1 / 10 : ℝ) * x) * (1 + (1 : ℝ) * x) * (1 + (2 : ℝ) * x)) (Set.left_mem_Icc.mpr (by norm_num)) hD0 hd double_dip_bounded_p0_fac double_dip_bounded_p0_P_pos
    hs hNp hNn (by norm_num) (by norm_num) (⟨by norm_num, by norm_num⟩) double_dip_bounded_p0_vlo double_dip_bounded_p0_vhi
  refine ⟨c, hc, by linarith, fun x hx hx0 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := (hsg x hx hx0).1 h; linarith
  · have := (hsg x hx hx0).2 h; linarith

/-- (c) THE LADDER over members 0..1: the breakpoints `Λ j` (0 for a
dominated pair, the unique crossing in its bracket otherwise) and, on
`(Λ (j-1), Λ j)`, `F j` is the UNIQUE maximum of `F 0, ..., F 1`. -/
theorem double_dip_bounded : ∃ Λ : ℕ → ℝ,
    ((97 / 100 : ℝ) < Λ 0 ∧ Λ 0 < (49 / 50 : ℝ) ∧ double_dip_bounded_F 0 (Λ 0) = double_dip_bounded_F 1 (Λ 0)) ∧
    (∀ j, 0 ≤ j → j < 0 → Λ j ≤ Λ (j + 1)) ∧
    (∀ j, 0 ≤ j → j ≤ 1 → ∀ x ∈ double_dip_bounded_S, 0 < x →
      (j = 0 ∨ Λ (j - 1) < x) → (j = 1 ∨ x < Λ j) →
      ∀ k, 0 ≤ k → k ≤ 1 → k ≠ j → double_dip_bounded_F k x < double_dip_bounded_F j x) := by
  obtain ⟨c0, hc0, hz0, hs0⟩ := double_dip_bounded_p0_cross
  have hcross : ∀ j, 0 ≤ j → j ≤ 0 → ∀ x ∈ double_dip_bounded_S, 0 < x →
      (x < (fun j : ℕ => if j = 0 then c0 else 0) j → double_dip_bounded_F (j + 1) x < double_dip_bounded_F j x) ∧
      ((fun j : ℕ => if j = 0 then c0 else 0) j < x → double_dip_bounded_F j x < double_dip_bounded_F (j + 1) x) := by
    intro j hja hjJ x hx hx0
    interval_cases j
    · simpa using hs0 x hx hx0
  have hmono : ∀ j, 0 ≤ j → j < 0 → (fun j : ℕ => if j = 0 then c0 else 0) j ≤
      (fun j : ℕ => if j = 0 then c0 else 0) (j + 1) := by
    intro j hja hjJ
    omega
  refine ⟨fun j : ℕ => if j = 0 then c0 else 0, ?_, ?_, ?_⟩
  · simp
    exact ⟨hc0.1, hc0.2, hz0⟩
  · exact hmono
  · exact ladder_core (a := 0) (J := 0) hcross hmono

/-- On `x ≤ (97 / 100 : ℝ)`, member 0 is the UNIQUE maximum of members 0..1. -/
theorem double_dip_bounded_best_0 : ∀ x ∈ double_dip_bounded_S, 0 < x → x ≤ (97 / 100 : ℝ) →
    ∀ k, 0 ≤ k → k ≤ 1 → k ≠ 0 → double_dip_bounded_F k x < double_dip_bounded_F 0 x := by
  obtain ⟨Λ, hL0, hmono, hlad⟩ := double_dip_bounded
  intro x hx hx0 hb
  exact hlad 0 (by norm_num) (by norm_num) x hx hx0
    (Or.inl rfl)
    (Or.inr (by linarith [hL0.1, hL0.2.1]))

/-- On `(49 / 50 : ℝ) ≤ x`, member 1 is the UNIQUE maximum of members 0..1. -/
theorem double_dip_bounded_best_1 : ∀ x ∈ double_dip_bounded_S, 0 < x → (49 / 50 : ℝ) ≤ x →
    ∀ k, 0 ≤ k → k ≤ 1 → k ≠ 1 → double_dip_bounded_F k x < double_dip_bounded_F 1 x := by
  obtain ⟨Λ, hL0, hmono, hlad⟩ := double_dip_bounded
  intro x hx hx0 hb
  exact hlad 1 (by norm_num) (by norm_num) x hx hx0
    (Or.inr (by norm_num; linarith [hL0.1, hL0.2.1]))
    (Or.inl rfl)

end SingleCrossingLadder
