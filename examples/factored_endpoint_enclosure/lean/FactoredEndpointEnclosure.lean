/- telperion 0.1.6 | family FactoredEndpointEnclosure | input-hash 9e4cd8dbf5ba4b0a
   53 theorems, 7 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace FactoredEndpointEnclosure

set_option linter.unusedVariables false

/-! ## Generic factored endpoint enclosure (emitted once per file)

`factored_endpoint_core`: on a box (any predicate), if `0 <= t`, `0 < D`, the lower bound
`Q <= D * F`, the factorization `Q = t^k * H`, and `0 <= H`, then `0 <= F`.  The box may
contain the endpoint `t = 0`, where `F / t^k` is undefined: only `H` (a polynomial) is
evaluated there.  conjecture1_proved = False. -/

theorem factored_endpoint_core {α : Type*} {Box : α → Prop} {F D Q H t : α → ℝ} (k : ℕ)
    (ht : ∀ p, Box p → 0 ≤ t p) (hD : ∀ p, Box p → 0 < D p)
    (hlow : ∀ p, Box p → Q p ≤ D p * F p)
    (hfac : ∀ p, Q p = t p ^ k * H p)
    (hH : ∀ p, Box p → 0 ≤ H p) :
    ∀ p, Box p → 0 ≤ F p := by
  intro p hp
  have h1 := hlow p hp
  rw [hfac] at h1
  have h2 := mul_nonneg (pow_nonneg (ht p hp) k) (hH p hp)
  have h3 : 0 ≤ D p * F p := le_trans h2 h1
  exact (mul_nonneg_iff_of_pos_left (hD p hp)).mp h3

/-- The quotient corollary: off the endpoint, `0 <= F / t^k`. -/
theorem factored_endpoint_quot {F t : ℝ} (k : ℕ) (hF : 0 ≤ F) (ht : 0 ≤ t) :
    0 ≤ F / t ^ k :=
  div_nonneg hF (pow_nonneg ht k)

/-! ## `log (1 + u)` Taylor bounds for all `u >= 0`, with signed remainder

`T n u = sum_{j < n} (-1)^j u^(j+1) / (j+1)`.  For every `u >= 0`: `log (1 + u) <= T n u`
when `n` is odd, `T n u <= log (1 + u)` when `n` is even.  Generic proof: `T n - log (1 + .)`
vanishes at `0` and has derivative `-(-t)^n / (1 + t)` (geometric sum), then the mean value
theorem.  Emitted by `transcendental_enclosure` (face `log_taylor`). -/

namespace FEELogTaylor

noncomputable def T (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * u ^ (j + 1) / ((j : ℝ) + 1)

theorem hasDerivAt_T (n : ℕ) (t : ℝ) :
    HasDerivAt (T n) (∑ j ∈ Finset.range n, (-t) ^ j) t := by
  have h : ∀ j ∈ Finset.range n, HasDerivAt
      (fun u : ℝ => (-1 : ℝ) ^ j * u ^ (j + 1) / ((j : ℝ) + 1)) ((-t) ^ j) t := by
    intro j _
    have h1 := ((hasDerivAt_pow (j + 1) t).const_mul ((-1 : ℝ) ^ j)).div_const ((j : ℝ) + 1)
    refine h1.congr_deriv ?_
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, neg_pow t j]
    push_cast
    field_simp
  exact HasDerivAt.fun_sum h

theorem nonneg_of_deriv_nonneg {g g' : ℝ → ℝ} (h0 : g 0 = 0)
    (hd : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t) (hp : ∀ t, 0 ≤ t → 0 ≤ g' t) :
    ∀ u, 0 ≤ u → 0 ≤ g u := by
  intro u hu
  rcases hu.eq_or_lt with h | h
  · rw [← h, h0]
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' h
      (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
      (fun x hx => hd x hx.1.le)
    have := hp c hc.1.le
    rw [hcs, h0, sub_zero, sub_zero] at this
    exact (div_nonneg_iff.mp this).elim (fun h' => h'.1) (fun h' => by linarith [h'.2])

/-- The remainder's derivative: `(T n)' - 1/(1+t) = -(-t)^n / (1 + t)`. -/
theorem deriv_gap (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range n, (-t) ^ j) - 1 / (1 + t) = -(-t) ^ n / (1 + t) := by
  have h1 : (1 + t) ≠ 0 := by positivity
  have hg := geom_sum_mul_neg (-t) n
  rw [sub_neg_eq_add, add_comm] at hg
  field_simp
  linarith [hg]

theorem hasDerivAt_log1 (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 t := (hasDerivAt_id t).const_add 1
  have := h1.log (by positivity)
  simpa using this

/-- Odd order: the Taylor polynomial is an UPPER bound for every `u >= 0`. -/
theorem log_le_T (n : ℕ) (hn : Odd n) (u : ℝ) (hu : 0 ≤ u) : Real.log (1 + u) ≤ T n u := by
  have key := nonneg_of_deriv_nonneg (g := fun v => T n v - Real.log (1 + v))
    (g' := fun t => (∑ j ∈ Finset.range n, (-t) ^ j) - 1 / (1 + t))
    (by simp [T])
    (fun t ht => (hasDerivAt_T n t).sub (hasDerivAt_log1 t ht))
    (fun t ht => by
      rw [deriv_gap n t ht, hn.neg_pow]
      have : 0 ≤ t ^ n := pow_nonneg ht n
      have : 0 < 1 + t := by linarith
      rw [neg_neg]; positivity)
    u hu
  have key' : 0 ≤ T n u - Real.log (1 + u) := key
  linarith

/-- Even order: the Taylor polynomial is a LOWER bound for every `u >= 0`. -/
theorem T_le_log (n : ℕ) (hn : Even n) (u : ℝ) (hu : 0 ≤ u) : T n u ≤ Real.log (1 + u) := by
  have key := nonneg_of_deriv_nonneg (g := fun v => Real.log (1 + v) - T n v)
    (g' := fun t => 1 / (1 + t) - (∑ j ∈ Finset.range n, (-t) ^ j))
    (by simp [T])
    (fun t ht => (hasDerivAt_log1 t ht).sub (hasDerivAt_T n t))
    (fun t ht => by
      have e : 1 / (1 + t) - (∑ j ∈ Finset.range n, (-t) ^ j) = (-t) ^ n / (1 + t) := by
        have := deriv_gap n t ht; rw [neg_div] at this; linarith
      rw [e, hn.neg_pow]
      have : 0 ≤ t ^ n := pow_nonneg ht n
      positivity)
    u hu
  have key' : 0 ≤ Real.log (1 + u) - T n u := key
  linarith

theorem upper_3 (u : ℝ) (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  have h := log_le_T 3 (by decide) u hu
  simp only [T, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

theorem upper_5 (u : ℝ) (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 := by
  have h := log_le_T 5 (by decide) u hu
  simp only [T, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

end FEELogTaylor

/-! ## Instance `log_exp`

`0 <= F` with `F = l - log(l + 1)` on the closed box l ∈ [0, 1/10], endpoint `l = 0` (right side) included.
Factorization `Q = l^1 * H` with `H = -l**2/3 + l/2`.
Log atoms: log(1 + l) with coefficient -1, Taylor order 3 (upper bound).  Boxes: 1.
conjecture1_proved = False. -/

noncomputable def log_exp_F (l : ℝ) : ℝ :=
  (l + ((-1 : ℝ) * Real.log (1 + (l))))

noncomputable def log_exp_D (l : ℝ) : ℝ :=
  (1 : ℝ)

noncomputable def log_exp_Q (l : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * l ^ 2 + (-1 / 3 : ℝ) * l ^ 3)

noncomputable def log_exp_H (l : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * l + (-1 / 3 : ℝ) * l ^ 2)

/-- The factorization `Q = l^1 * H` (exact polynomial identity). -/
theorem log_exp_fac (l : ℝ) :
    log_exp_Q l = l ^ 1 * log_exp_H l := by
  simp only [log_exp_Q, log_exp_H]
  ring

theorem log_exp_b0_H (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    0 ≤ log_exp_H l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 10) - l := by linarith
  simp only [log_exp_H]
  linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)]

theorem log_exp_b0_D (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    0 < log_exp_D l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 10) - l := by linarith
  simp only [log_exp_D]
  exact (by norm_num)

theorem log_exp_b0_low (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    log_exp_Q l ≤ log_exp_D l * log_exp_F l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 10) - l := by linarith
  have e : log_exp_D l * log_exp_F l = (l) + ((-1 : ℝ)) * Real.log (1 + (l)) := by
    simp only [log_exp_D, log_exp_F]
    ring
  have hu0 : 0 ≤ (l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  have hT0 := FEELogTaylor.upper_3 (l) hu0
  have hk0 : 0 ≤ ((1 : ℝ)) := by norm_num
  have hp0 := mul_nonneg hk0 (sub_nonneg.2 hT0)
  simp only [log_exp_Q]
  linarith [e, hp0]

theorem log_exp_b0 (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    0 ≤ log_exp_F l :=
  factored_endpoint_core (Box := fun p : ℝ => (0 : ℝ) ≤ p ∧ p ≤ (1 / 10 : ℝ))
    (F := log_exp_F) (D := log_exp_D) (Q := log_exp_Q)
    (H := log_exp_H) (t := fun p => p) 1
    (fun p hp => by linarith [hp.1, hp.2])
    (fun p hp => log_exp_b0_D p hp.1 hp.2)
    (fun p hp => log_exp_b0_low p hp.1 hp.2)
    (fun p => log_exp_fac p)
    (fun p hp => log_exp_b0_H p hp.1 hp.2)
    l ⟨h1, h2⟩

/-- `0 <= F` on the CLOSED box, endpoint `l = 0` included. -/
theorem log_exp :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ), 0 ≤ log_exp_F l := by
  intro l hl
  obtain ⟨hl1, hl2⟩ := hl
  exact log_exp_b0 l (by linarith) (by linarith)

/-- The quotient `F / l^1` (the quantity of interest) is `>= 0` off the endpoint. -/
theorem log_exp_quot :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ), l ≠ (0 : ℝ) → 0 ≤ log_exp_F l / l ^ 1 := by
  intro l hl hne
  exact factored_endpoint_quot 1 (log_exp l hl) (by linarith [hl.1, hl.2])

/-! ## Instance `log_sharp`

`0 <= F` with `F = -117*l**2/250 + l - log(l + 1)` on the closed box l ∈ [0, 1/10], endpoint `l = 0` (right side) included.
Factorization `Q = l^2 * H` with `H = -l**3/5 + l**2/4 - l/3 + 4/125`.
Log atoms: log(1 + l) with coefficient -1, Taylor order 5 (upper bound).  Boxes: 1.
conjecture1_proved = False. -/

noncomputable def log_sharp_F (l : ℝ) : ℝ :=
  (l + ((-1 : ℝ) * Real.log (1 + (l))) + (((-117 : ℝ) * (l ^ 2)) / (250 : ℝ)))

noncomputable def log_sharp_D (l : ℝ) : ℝ :=
  (1 : ℝ)

noncomputable def log_sharp_Q (l : ℝ) : ℝ :=
  ((4 / 125 : ℝ) * l ^ 2 + (-1 / 3 : ℝ) * l ^ 3 + (1 / 4 : ℝ) * l ^ 4 + (-1 / 5 : ℝ) * l ^ 5)

noncomputable def log_sharp_H (l : ℝ) : ℝ :=
  ((4 / 125 : ℝ) + (-1 / 3 : ℝ) * l + (1 / 4 : ℝ) * l ^ 2 + (-1 / 5 : ℝ) * l ^ 3)

/-- The factorization `Q = l^2 * H` (exact polynomial identity). -/
theorem log_sharp_fac (l : ℝ) :
    log_sharp_Q l = l ^ 2 * log_sharp_H l := by
  simp only [log_sharp_Q, log_sharp_H]
  ring

theorem log_sharp_b0_H (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    0 ≤ log_sharp_H l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 10) - l := by linarith
  simp only [log_sharp_H]
  linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 3), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 2), mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 3) (pow_nonneg hr 0)]

theorem log_sharp_b0_D (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    0 < log_sharp_D l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 10) - l := by linarith
  simp only [log_sharp_D]
  exact (by norm_num)

theorem log_sharp_b0_low (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    log_sharp_Q l ≤ log_sharp_D l * log_sharp_F l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 10) - l := by linarith
  have e : log_sharp_D l * log_sharp_F l = (l + (-117 / 250 : ℝ) * l ^ 2) + ((-1 : ℝ)) * Real.log (1 + (l)) := by
    simp only [log_sharp_D, log_sharp_F]
    ring
  have hu0 : 0 ≤ (l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  have hT0 := FEELogTaylor.upper_5 (l) hu0
  have hk0 : 0 ≤ ((1 : ℝ)) := by norm_num
  have hp0 := mul_nonneg hk0 (sub_nonneg.2 hT0)
  simp only [log_sharp_Q]
  linarith [e, hp0]

theorem log_sharp_b0 (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 10 : ℝ)) :
    0 ≤ log_sharp_F l :=
  factored_endpoint_core (Box := fun p : ℝ => (0 : ℝ) ≤ p ∧ p ≤ (1 / 10 : ℝ))
    (F := log_sharp_F) (D := log_sharp_D) (Q := log_sharp_Q)
    (H := log_sharp_H) (t := fun p => p) 2
    (fun p hp => by linarith [hp.1, hp.2])
    (fun p hp => log_sharp_b0_D p hp.1 hp.2)
    (fun p hp => log_sharp_b0_low p hp.1 hp.2)
    (fun p => log_sharp_fac p)
    (fun p hp => log_sharp_b0_H p hp.1 hp.2)
    l ⟨h1, h2⟩

/-- `0 <= F` on the CLOSED box, endpoint `l = 0` included. -/
theorem log_sharp :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ), 0 ≤ log_sharp_F l := by
  intro l hl
  obtain ⟨hl1, hl2⟩ := hl
  exact log_sharp_b0 l (by linarith) (by linarith)

/-- The quotient `F / l^2` (the quantity of interest) is `>= 0` off the endpoint. -/
theorem log_sharp_quot :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ), l ≠ (0 : ℝ) → 0 ≤ log_sharp_F l / l ^ 2 := by
  intro l hl hne
  exact factored_endpoint_quot 2 (log_sharp l hl) (by linarith [hl.1, hl.2])

/-! ## Instance `rational`

`0 <= F` with `F = 4*l**3 - 3*l**2 + 2*l - 1 + (l + 1)**(-2)` on the closed box l ∈ [0, 1], endpoint `l = 0` (right side) included.
Factorization `Q = l^4 * H` with `H = 4*l + 5`.
Log atoms: none (closed form).  Boxes: 1.
conjecture1_proved = False. -/

noncomputable def rational_F (l : ℝ) : ℝ :=
  ((-1 : ℝ) + (1 / ((1 : ℝ) + l) ^ 2) + ((-3 : ℝ) * (l ^ 2)) + ((2 : ℝ) * l) + ((4 : ℝ) * (l ^ 3)))

noncomputable def rational_D (l : ℝ) : ℝ :=
  (1 : ℝ) * ((1 : ℝ) + l) ^ 2

noncomputable def rational_Q (l : ℝ) : ℝ :=
  ((5 : ℝ) * l ^ 4 + (4 : ℝ) * l ^ 5)

noncomputable def rational_H (l : ℝ) : ℝ :=
  ((5 : ℝ) + (4 : ℝ) * l)

/-- The factorization `Q = l^4 * H` (exact polynomial identity). -/
theorem rational_fac (l : ℝ) :
    rational_Q l = l ^ 4 * rational_H l := by
  simp only [rational_Q, rational_H]
  ring

theorem rational_b0_H (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 : ℝ)) :
    0 ≤ rational_H l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ 1 - l := by linarith
  simp only [rational_H]
  linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]

theorem rational_b0_D (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 : ℝ)) :
    0 < rational_D l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ 1 - l := by linarith
  have hf0 : 0 < ((1 : ℝ) + l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  simp only [rational_D]
  exact (mul_pos (by norm_num) (pow_pos hf0 2))

theorem rational_b0_low (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 : ℝ)) :
    rational_Q l ≤ rational_D l * rational_F l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ 1 - l := by linarith
  have hf0 : 0 < ((1 : ℝ) + l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  have hf0' := hf0.ne'
  have e : rational_D l * rational_F l = ((5 : ℝ) * l ^ 4 + (4 : ℝ) * l ^ 5) := by
    simp only [rational_D, rational_F]
    field_simp
    ring
  simp only [rational_Q]
  linarith [e]

theorem rational_b0 (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 : ℝ)) :
    0 ≤ rational_F l :=
  factored_endpoint_core (Box := fun p : ℝ => (0 : ℝ) ≤ p ∧ p ≤ (1 : ℝ))
    (F := rational_F) (D := rational_D) (Q := rational_Q)
    (H := rational_H) (t := fun p => p) 4
    (fun p hp => by linarith [hp.1, hp.2])
    (fun p hp => rational_b0_D p hp.1 hp.2)
    (fun p hp => rational_b0_low p hp.1 hp.2)
    (fun p => rational_fac p)
    (fun p hp => rational_b0_H p hp.1 hp.2)
    l ⟨h1, h2⟩

/-- `0 <= F` on the CLOSED box, endpoint `l = 0` included. -/
theorem rational :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 : ℝ), 0 ≤ rational_F l := by
  intro l hl
  obtain ⟨hl1, hl2⟩ := hl
  exact rational_b0 l (by linarith) (by linarith)

/-- The quotient `F / l^4` (the quantity of interest) is `>= 0` off the endpoint. -/
theorem rational_quot :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 : ℝ), l ≠ (0 : ℝ) → 0 ≤ rational_F l / l ^ 4 := by
  intro l hl hne
  exact factored_endpoint_quot 4 (rational l hl) (by linarith [hl.1, hl.2])

/-! ## Instance `synth2`

`0 <= F` with `F = l**2*x + l*(-l + x)**2` on the closed box l ∈ [0, 1/2], x ∈ [1/8, 1], endpoint `l = 0` (right side) included.
Factorization `Q = l^1 * H` with `H = l**2 - l*x + x**2`.
Log atoms: none (closed form).  Boxes: 3.
conjecture1_proved = False. -/

noncomputable def synth2_F (l x : ℝ) : ℝ :=
  ((l * ((x + ((-1 : ℝ) * l)) ^ 2)) + (x * (l ^ 2)))

noncomputable def synth2_D (l x : ℝ) : ℝ :=
  (1 : ℝ)

noncomputable def synth2_Q (l x : ℝ) : ℝ :=
  (l * x ^ 2 + (-1 : ℝ) * l ^ 2 * x + l ^ 3)

noncomputable def synth2_H (l x : ℝ) : ℝ :=
  (x ^ 2 + (-1 : ℝ) * l * x + l ^ 2)

/-- The factorization `Q = l^1 * H` (exact polynomial identity). -/
theorem synth2_fac (l x : ℝ) :
    synth2_Q l x = l ^ 1 * synth2_H l x := by
  simp only [synth2_Q, synth2_H]
  ring

theorem synth2_b0_H (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 4 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    0 ≤ synth2_H l x := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 4) - l := by linarith
  have hc : 0 ≤ x - (1 / 8) := by linarith
  have hd : 0 ≤ (9 / 16) - x := by linarith
  simp only [synth2_H]
  linarith [mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0))]

theorem synth2_b0_D (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 4 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    0 < synth2_D l x := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 4) - l := by linarith
  have hc : 0 ≤ x - (1 / 8) := by linarith
  have hd : 0 ≤ (9 / 16) - x := by linarith
  simp only [synth2_D]
  exact (by norm_num)

theorem synth2_b0_low (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 4 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    synth2_Q l x ≤ synth2_D l x * synth2_F l x := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 4) - l := by linarith
  have hc : 0 ≤ x - (1 / 8) := by linarith
  have hd : 0 ≤ (9 / 16) - x := by linarith
  have e : synth2_D l x * synth2_F l x = (l * x ^ 2 + (-1 : ℝ) * l ^ 2 * x + l ^ 3) := by
    simp only [synth2_D, synth2_F]
    ring
  simp only [synth2_Q]
  linarith [e]

theorem synth2_b0 (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 4 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    0 ≤ synth2_F l x :=
  factored_endpoint_core (Box := fun p : ℝ × ℝ => (0 : ℝ) ≤ p.1 ∧ p.1 ≤ (1 / 4 : ℝ) ∧ (1 / 8 : ℝ) ≤ p.2 ∧ p.2 ≤ (9 / 16 : ℝ))
    (F := fun p => synth2_F p.1 p.2) (D := fun p => synth2_D p.1 p.2) (Q := fun p => synth2_Q p.1 p.2)
    (H := fun p => synth2_H p.1 p.2) (t := fun p => p.1) 1
    (fun p hp => by linarith [hp.1, hp.2.1])
    (fun p hp => synth2_b0_D p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (fun p hp => synth2_b0_low p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (fun p => synth2_fac p.1 p.2)
    (fun p hp => synth2_b0_H p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (l, x) ⟨h1, h2, h3, h4⟩

theorem synth2_b1_H (l x : ℝ) (h1 : (1 / 4 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    0 ≤ synth2_H l x := by
  have hl : 0 ≤ l - (1 / 4) := by linarith
  have hr : 0 ≤ (1 / 2) - l := by linarith
  have hc : 0 ≤ x - (1 / 8) := by linarith
  have hd : 0 ≤ (9 / 16) - x := by linarith
  simp only [synth2_H]
  linarith [mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0))]

theorem synth2_b1_D (l x : ℝ) (h1 : (1 / 4 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    0 < synth2_D l x := by
  have hl : 0 ≤ l - (1 / 4) := by linarith
  have hr : 0 ≤ (1 / 2) - l := by linarith
  have hc : 0 ≤ x - (1 / 8) := by linarith
  have hd : 0 ≤ (9 / 16) - x := by linarith
  simp only [synth2_D]
  exact (by norm_num)

theorem synth2_b1_low (l x : ℝ) (h1 : (1 / 4 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    synth2_Q l x ≤ synth2_D l x * synth2_F l x := by
  have hl : 0 ≤ l - (1 / 4) := by linarith
  have hr : 0 ≤ (1 / 2) - l := by linarith
  have hc : 0 ≤ x - (1 / 8) := by linarith
  have hd : 0 ≤ (9 / 16) - x := by linarith
  have e : synth2_D l x * synth2_F l x = (l * x ^ 2 + (-1 : ℝ) * l ^ 2 * x + l ^ 3) := by
    simp only [synth2_D, synth2_F]
    ring
  simp only [synth2_Q]
  linarith [e]

theorem synth2_b1 (l x : ℝ) (h1 : (1 / 4 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (1 / 8 : ℝ) ≤ x) (h4 : x ≤ (9 / 16 : ℝ)) :
    0 ≤ synth2_F l x :=
  factored_endpoint_core (Box := fun p : ℝ × ℝ => (1 / 4 : ℝ) ≤ p.1 ∧ p.1 ≤ (1 / 2 : ℝ) ∧ (1 / 8 : ℝ) ≤ p.2 ∧ p.2 ≤ (9 / 16 : ℝ))
    (F := fun p => synth2_F p.1 p.2) (D := fun p => synth2_D p.1 p.2) (Q := fun p => synth2_Q p.1 p.2)
    (H := fun p => synth2_H p.1 p.2) (t := fun p => p.1) 1
    (fun p hp => by linarith [hp.1, hp.2.1])
    (fun p hp => synth2_b1_D p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (fun p hp => synth2_b1_low p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (fun p => synth2_fac p.1 p.2)
    (fun p hp => synth2_b1_H p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (l, x) ⟨h1, h2, h3, h4⟩

theorem synth2_b2_H (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (9 / 16 : ℝ) ≤ x) (h4 : x ≤ (1 : ℝ)) :
    0 ≤ synth2_H l x := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 2) - l := by linarith
  have hc : 0 ≤ x - (9 / 16) := by linarith
  have hd : 0 ≤ 1 - x := by linarith
  simp only [synth2_H]
  linarith [mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 0) (pow_nonneg hd 2)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 1) (pow_nonneg hd 1)), mul_nonneg (mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)) (mul_nonneg (pow_nonneg hc 2) (pow_nonneg hd 0))]

theorem synth2_b2_D (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (9 / 16 : ℝ) ≤ x) (h4 : x ≤ (1 : ℝ)) :
    0 < synth2_D l x := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 2) - l := by linarith
  have hc : 0 ≤ x - (9 / 16) := by linarith
  have hd : 0 ≤ 1 - x := by linarith
  simp only [synth2_D]
  exact (by norm_num)

theorem synth2_b2_low (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (9 / 16 : ℝ) ≤ x) (h4 : x ≤ (1 : ℝ)) :
    synth2_Q l x ≤ synth2_D l x * synth2_F l x := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 2) - l := by linarith
  have hc : 0 ≤ x - (9 / 16) := by linarith
  have hd : 0 ≤ 1 - x := by linarith
  have e : synth2_D l x * synth2_F l x = (l * x ^ 2 + (-1 : ℝ) * l ^ 2 * x + l ^ 3) := by
    simp only [synth2_D, synth2_F]
    ring
  simp only [synth2_Q]
  linarith [e]

theorem synth2_b2 (l x : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 2 : ℝ)) (h3 : (9 / 16 : ℝ) ≤ x) (h4 : x ≤ (1 : ℝ)) :
    0 ≤ synth2_F l x :=
  factored_endpoint_core (Box := fun p : ℝ × ℝ => (0 : ℝ) ≤ p.1 ∧ p.1 ≤ (1 / 2 : ℝ) ∧ (9 / 16 : ℝ) ≤ p.2 ∧ p.2 ≤ (1 : ℝ))
    (F := fun p => synth2_F p.1 p.2) (D := fun p => synth2_D p.1 p.2) (Q := fun p => synth2_Q p.1 p.2)
    (H := fun p => synth2_H p.1 p.2) (t := fun p => p.1) 1
    (fun p hp => by linarith [hp.1, hp.2.1])
    (fun p hp => synth2_b2_D p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (fun p hp => synth2_b2_low p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (fun p => synth2_fac p.1 p.2)
    (fun p hp => synth2_b2_H p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (l, x) ⟨h1, h2, h3, h4⟩

/-- `0 <= F` on the CLOSED box, endpoint `l = 0` included. -/
theorem synth2 :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ), ∀ x ∈ Set.Icc (1 / 8 : ℝ) (1 : ℝ), 0 ≤ synth2_F l x := by
  intro l hl x hx
  obtain ⟨hl1, hl2⟩ := hl
  obtain ⟨hx1, hx2⟩ := hx
  rcases le_total x (9 / 16 : ℝ) with h | h
  · rcases le_total l (1 / 4 : ℝ) with h | h
    · exact synth2_b0 l x (by linarith) (by linarith) (by linarith) (by linarith)
    · exact synth2_b1 l x (by linarith) (by linarith) (by linarith) (by linarith)
  · exact synth2_b2 l x (by linarith) (by linarith) (by linarith) (by linarith)

/-- The quotient `F / l^1` (the quantity of interest) is `>= 0` off the endpoint. -/
theorem synth2_quot :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ), l ≠ (0 : ℝ) → ∀ x ∈ Set.Icc (1 / 8 : ℝ) (1 : ℝ),
      0 ≤ synth2_F l x / l ^ 1 := by
  intro l hl hne x hx
  exact factored_endpoint_quot 1 (synth2 l hl x hx) (by linarith [hl.1, hl.2])

/-! ## Instance `pade`

`0 <= F` with `F = l*(l + 6)/(4*l + 6) - log(l + 1)` on the closed box l ∈ [0, 1/3], endpoint `l = 0` (right side) included.
Factorization `Q = l^4 * H` with `H = -2*l**2/5 - l/10 + 1/12`.
Log atoms: log(1 + l) with coefficient -2*l - 3, Taylor order 5 (upper bound).  Boxes: 1.
conjecture1_proved = False. -/

noncomputable def pade_F (l : ℝ) : ℝ :=
  (((-1 : ℝ) * Real.log (1 + (l))) + ((l * ((6 : ℝ) + l)) / ((6 : ℝ) + ((4 : ℝ) * l))))

noncomputable def pade_D (l : ℝ) : ℝ :=
  (1 : ℝ) * ((3 : ℝ) + (2 : ℝ) * l) ^ 1

noncomputable def pade_Q (l : ℝ) : ℝ :=
  ((1 / 12 : ℝ) * l ^ 4 + (-1 / 10 : ℝ) * l ^ 5 + (-2 / 5 : ℝ) * l ^ 6)

noncomputable def pade_H (l : ℝ) : ℝ :=
  ((1 / 12 : ℝ) + (-1 / 10 : ℝ) * l + (-2 / 5 : ℝ) * l ^ 2)

/-- The factorization `Q = l^4 * H` (exact polynomial identity). -/
theorem pade_fac (l : ℝ) :
    pade_Q l = l ^ 4 * pade_H l := by
  simp only [pade_Q, pade_H]
  ring

theorem pade_b0_H (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 3 : ℝ)) :
    0 ≤ pade_H l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 3) - l := by linarith
  simp only [pade_H]
  linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 2), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 2) (pow_nonneg hr 0)]

theorem pade_b0_D (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 3 : ℝ)) :
    0 < pade_D l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 3) - l := by linarith
  have hf0 : 0 < ((3 : ℝ) + (2 : ℝ) * l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  simp only [pade_D]
  exact (mul_pos (by norm_num) (pow_pos hf0 1))

theorem pade_b0_low (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 3 : ℝ)) :
    pade_Q l ≤ pade_D l * pade_F l := by
  have hl : 0 ≤ l - 0 := by linarith
  have hr : 0 ≤ (1 / 3) - l := by linarith
  have hf0 : 0 < ((3 : ℝ) + (2 : ℝ) * l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  have hf0' := hf0.ne'
  have e : pade_D l * pade_F l = ((3 : ℝ) * l + (1 / 2 : ℝ) * l ^ 2) + ((-3 : ℝ) + (-2 : ℝ) * l) * Real.log (1 + (l)) := by
    simp only [pade_D, pade_F]
    field_simp
    ring
  have hu0 : 0 ≤ (l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  have hT0 := FEELogTaylor.upper_5 (l) hu0
  have hk0 : 0 ≤ ((3 : ℝ) + (2 : ℝ) * l) := by linarith [mul_nonneg (pow_nonneg hl 0) (pow_nonneg hr 1), mul_nonneg (pow_nonneg hl 1) (pow_nonneg hr 0)]
  have hp0 := mul_nonneg hk0 (sub_nonneg.2 hT0)
  simp only [pade_Q]
  linarith [e, hp0]

theorem pade_b0 (l : ℝ) (h1 : (0 : ℝ) ≤ l) (h2 : l ≤ (1 / 3 : ℝ)) :
    0 ≤ pade_F l :=
  factored_endpoint_core (Box := fun p : ℝ => (0 : ℝ) ≤ p ∧ p ≤ (1 / 3 : ℝ))
    (F := pade_F) (D := pade_D) (Q := pade_Q)
    (H := pade_H) (t := fun p => p) 4
    (fun p hp => by linarith [hp.1, hp.2])
    (fun p hp => pade_b0_D p hp.1 hp.2)
    (fun p hp => pade_b0_low p hp.1 hp.2)
    (fun p => pade_fac p)
    (fun p hp => pade_b0_H p hp.1 hp.2)
    l ⟨h1, h2⟩

/-- `0 <= F` on the CLOSED box, endpoint `l = 0` included. -/
theorem pade :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 3 : ℝ), 0 ≤ pade_F l := by
  intro l hl
  obtain ⟨hl1, hl2⟩ := hl
  exact pade_b0 l (by linarith) (by linarith)

/-- The quotient `F / l^4` (the quantity of interest) is `>= 0` off the endpoint. -/
theorem pade_quot :
    ∀ l ∈ Set.Icc (0 : ℝ) (1 / 3 : ℝ), l ≠ (0 : ℝ) → 0 ≤ pade_F l / l ^ 4 := by
  intro l hl hne
  exact factored_endpoint_quot 4 (pade l hl) (by linarith [hl.1, hl.2])

end FactoredEndpointEnclosure
