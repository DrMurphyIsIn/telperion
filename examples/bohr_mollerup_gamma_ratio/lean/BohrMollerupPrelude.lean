import Mathlib

/-!
# BohrMollerupPrelude -- Bohr-Mollerup brackets for `Real.Gamma` at rational points

The once-proved part of Telperion's `bohr_mollerup_gamma_ratio` emitter.  Ported from the
hand-built CN-1 modules `GammaBounds.lean`, `GammaRatio.lean` and `RpowBounds.lean`
(github.com/DrMurphyIsIn/tenth-discriminant, Lean v4.34.1 / Mathlib d13f23b) to Lean v4.32.0 /
Mathlib v4.32.0.  Mathlib only.

Mathlib has `Real.convexOn_log_Gamma` (log-convexity of `Γ` on `(0, ∞)`) and the Bohr-Mollerup
inequality `Real.BohrMollerup.f_add_nat_le`.  From these, for `n ≥ 1` and `0 < x < 1`:

* `Gamma_add_le`:  `Γ(n + x) ≤ Γ(n) n^x`                     (two-point convexity at `n`, `n+1`);
* `Gamma_add_ge`:  `Γ(n+1) (n+x)^(x-1) ≤ Γ(n + x)`            (three-point convexity at `n+x`, `n+1+x`);
* `Gamma_add_nat_eq`: `Γ(n + x) = Γ(x) ∏_{k<n} (x + k)`;
* `Gamma_ratio_bounds`: for `0 < x₁, x₂ < 1`,
  `n (n+x₁)^(x₁-1) / n^x₂ · P ≤ Γ(x₁)/Γ(x₂) ≤ n^x₁ / (n (n+x₂)^(x₂-1)) · P`,
  `P = ∏_{k<n} (x₂+k)/(x₁+k)`; the two sides differ by the factor `(1+x₁/n)^(1-x₁) (1+x₂/n)^(1-x₂)`.

The kernel decides integer inequalities; two lemmas transport them to real `rpow` bounds:

* `rpow_div_upper`: `m^p S^q ≤ U^q` gives `m^(p/q) ≤ U/S`;
* `rpow_rat_neg_div_lower`: `L^q a^p ≤ b^p S^q` gives `L/S ≤ (a/b)^(-p/q)`.

These two are a minimal inline copy of the general root-bracket prelude of the
`nat_root_bracket_table` kind; once that kind lands this module should import it instead.

`prod_range_chunk` splits a range product into `C` blocks of `K`, so that each kernel
evaluation stays shallow.

Nothing here is about class numbers or about RH.  conjecture1_proved = False.
-/

set_option autoImplicit false

namespace BohrMollerupPrelude

open Real

/-- `Γ(n + x) = Γ(x) ∏_{k<n} (x + k)` for `x > 0`. -/
lemma Gamma_add_nat_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Gamma ((n : ℝ) + x) = Gamma x * ∏ k ∈ Finset.range n, (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, Nat.cast_succ,
      show (n : ℝ) + 1 + x = ((n : ℝ) + x) + 1 by ring, Gamma_add_one (by positivity)]
    ring

lemma log_Gamma_add_one {y : ℝ} (hy : 0 < y) :
    log (Gamma (y + 1)) = log (Gamma y) + log y := by
  rw [Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm]

/-- Upper bound: `Γ(n + x) ≤ Γ(n) n^x` for `n ≠ 0`, `0 < x ≤ 1`. -/
lemma Gamma_add_le (n : ℕ) (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Gamma ((n : ℝ) + x) ≤ Gamma n * (n : ℝ) ^ x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h := Real.BohrMollerup.f_add_nat_le (f := log ∘ Gamma) convexOn_log_Gamma
    (fun {y} hy => log_Gamma_add_one hy) hn hx hx1
  simp only [Function.comp_apply] at h
  have hG : 0 < Gamma ((n : ℝ) + x) := Gamma_pos_of_pos (by positivity)
  have hGn : 0 < Gamma n := Gamma_pos_of_pos hn'
  rw [← exp_log hG, ← exp_log (by positivity : 0 < Gamma n * (n : ℝ) ^ x)]
  apply exp_le_exp.mpr
  rw [log_mul hGn.ne' (rpow_pos_of_pos hn' x).ne', log_rpow hn']
  linarith

/-- Lower bound: `Γ(n+1) (n + x)^(x - 1) ≤ Γ(n + x)` for `0 < x < 1`. -/
lemma Gamma_add_ge (n : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Gamma ((n : ℝ) + 1) * ((n : ℝ) + x) ^ (x - 1) ≤ Gamma ((n : ℝ) + x) := by
  have hnx : (0 : ℝ) < n + x := by positivity
  have hnx1 : (0 : ℝ) < n + 1 + x := by positivity
  have hc := convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hnx) (Set.mem_Ioi.mpr hnx1) hx.le
    (by linarith : 0 ≤ 1 - x) (by ring : x + (1 - x) = 1)
  simp only [Function.comp_apply, smul_eq_mul] at hc
  rw [show x * ((n : ℝ) + x) + (1 - x) * ((n : ℝ) + 1 + x) = n + 1 by ring] at hc
  have h2 : log (Gamma ((n : ℝ) + 1 + x)) = log (Gamma (n + x)) + log (n + x) := by
    rw [show (n : ℝ) + 1 + x = (n + x) + 1 by ring]
    exact log_Gamma_add_one hnx
  rw [h2] at hc
  have hG := Gamma_pos_of_pos hnx
  have hG1 : 0 < Gamma ((n : ℝ) + 1) := Gamma_pos_of_pos (by positivity)
  rw [← exp_log hG, ← exp_log (by positivity : 0 < Gamma ((n : ℝ) + 1) * ((n : ℝ) + x) ^ (x - 1))]
  apply exp_le_exp.mpr
  rw [log_mul hG1.ne' (rpow_pos_of_pos hnx _).ne', log_rpow hnx]
  linarith

/-- The ratio `Γ(x₁)/Γ(x₂)` enclosed by elementary functions of `n` times the exact rational
`P = ∏_{k<n} (x₂+k)/(x₁+k)`. -/
theorem Gamma_ratio_bounds (n : ℕ) (hn : n ≠ 0) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁' : x₁ < 1)
    (hx₂ : 0 < x₂) (hx₂' : x₂ < 1) :
    (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) / (n : ℝ) ^ x₂ * (∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k))
        ≤ Gamma x₁ / Gamma x₂ ∧
    Gamma x₁ / Gamma x₂ ≤ (n : ℝ) ^ x₁ / ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1))
        * (∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hP1 : 0 < ∏ k ∈ Finset.range n, (x₁ + k) := Finset.prod_pos fun k _ => by positivity
  have hP2 : 0 < ∏ k ∈ Finset.range n, (x₂ + k) := Finset.prod_pos fun k _ => by positivity
  have hP : 0 < ∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k) := Finset.prod_pos fun k _ => by positivity
  have hG2 := Gamma_pos_of_pos hx₂
  have hGn := Gamma_pos_of_pos hn'
  have hGn1 : 0 < Gamma ((n : ℝ) + x₁) := Gamma_pos_of_pos (by positivity)
  have hGn2 : 0 < Gamma ((n : ℝ) + x₂) := Gamma_pos_of_pos (by positivity)
  have e1 := Gamma_add_nat_eq hx₁ n
  have e2 := Gamma_add_nat_eq hx₂ n
  have hratio : Gamma x₁ / Gamma x₂
      = Gamma ((n : ℝ) + x₁) / Gamma ((n : ℝ) + x₂) * ∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k) := by
    rw [Finset.prod_div_distrib, e1, e2]
    field_simp
    try ring
  have hA := Gamma_add_ge n hx₁ hx₁'
  rw [Gamma_add_one hn'.ne'] at hA
  have hB := Gamma_add_le n hn hx₂ hx₂'.le
  have hC := Gamma_add_le n hn hx₁ hx₁'.le
  have hD := Gamma_add_ge n hx₂ hx₂'
  rw [Gamma_add_one hn'.ne'] at hD
  rw [hratio]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hP.le
    rw [div_le_div_iff₀ (by positivity) hGn2]
    calc (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) * Gamma ((n : ℝ) + x₂)
        ≤ (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) * (Gamma n * (n : ℝ) ^ x₂) := by gcongr
      _ = ((n : ℝ) * Gamma n * ((n : ℝ) + x₁) ^ (x₁ - 1)) * (n : ℝ) ^ x₂ := by ring
      _ ≤ Gamma ((n : ℝ) + x₁) * (n : ℝ) ^ x₂ := by gcongr
  · apply mul_le_mul_of_nonneg_right _ hP.le
    rw [div_le_div_iff₀ hGn2 (by positivity)]
    calc Gamma ((n : ℝ) + x₁) * ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1))
        ≤ (Gamma n * (n : ℝ) ^ x₁) * ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1)) := by gcongr
      _ = (n : ℝ) ^ x₁ * ((n : ℝ) * Gamma n * ((n : ℝ) + x₂) ^ (x₂ - 1)) := by ring
      _ ≤ (n : ℝ) ^ x₁ * Gamma ((n : ℝ) + x₂) := by gcongr

/-! ### Root brackets (a minimal copy of the `nat_root_bracket_table` prelude) -/

/-- `m^p S^q ≤ U^q` gives `m^(p/q) ≤ U/S`. -/
lemma rpow_div_upper (m p q U S : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hU : m ^ p * S ^ q ≤ U ^ q) : (m : ℝ) ^ ((p : ℝ) / q) ≤ (U : ℝ) / S := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ ((p : ℝ) / q) := Real.rpow_nonneg hm _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ ((p : ℝ) / q)) ^ q = (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast hU

/-- `L^q a^p ≤ b^p S^q` gives `L/S ≤ (a/b)^(-p/q)`. -/
lemma rpow_rat_neg_div_lower (a b p q L S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * a ^ p ≤ b ^ p * S ^ q) : (L : ℝ) / S ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ (-((p : ℝ) / q))) ^ q = (b : ℝ) ^ p / (a : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hab.le, Real.rpow_natCast, div_pow, inv_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hL

/-! ### Chunking -/

/-- A range product over `C * K` terms as `C` blocks of `K`. -/
lemma prod_range_chunk {M : Type*} [CommMonoid M] (f : ℕ → M) (C K : ℕ) :
    ∏ i ∈ Finset.range (C * K), f i
      = ∏ c ∈ Finset.range C, ∏ n ∈ Finset.range K, f (K * c + n) := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [Finset.prod_range_succ, ← ih, show (C + 1) * K = C * K + K by ring, Finset.prod_range_add,
      mul_comm K C]

end BohrMollerupPrelude
