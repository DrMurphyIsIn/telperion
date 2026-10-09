/-
ScaledInterval -- the fixed-scale integer interval kernel behind Telperion's
`scaled_interval_eval` emitter.

Adapted from OpenAI's `openai/math` Lean library (Apache-2.0),
https://github.com/openai/math, file
`lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean`
(namespace `AtomicTriangular.Interval`: `RI`, `RI.Mem`, `add/neg/sub/mul/divNat/widen`,
their `mem_*` lemmas, `CI.taylor`, `CI.square`, `CI.exp`, `RI.mem_of_subset`).
Changes from the source: the scale `S` is a parameter rather than the constant `10^60`;
real intervals only; `exp` closes its Taylor remainder with Mathlib's `Real.exp_bound`
against an emitter-chosen widen `r` (checked by `decide`); Bool checks
(`subset`, `lowerOK`, `upperOK`, `expSmallOK`, `expRemOK`) so per-node facts are
decided by the kernel and lifted to `ℝ` by a once-proved soundness lemma.

Every operation is computable `ℤ` arithmetic with floor division and a one-ulp
outward round, so `decide +kernel` evaluates it on literal boxes.

conjecture1_proved = False.
-/
import Mathlib

namespace ScaledInterval

/-- A real interval at scale `S`: `(lo, hi)` encloses `x` when `lo ≤ S·x ≤ hi`. -/
structure RI where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

/-- `a` encloses `x` at scale `S`. -/
def RI.Mem (S : ℤ) (a : RI) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (S : ℝ) * x ∧ (S : ℝ) * x ≤ a.hi

/-! ### Operations (computable, kernel-reducible) -/

/-- The box of every `x ∈ [p₁/q₁, p₂/q₂]` (floor below, floor + 1 above). -/
def RI.ofRange (S p₁ : ℤ) (q₁ : ℕ) (p₂ : ℤ) (q₂ : ℕ) : RI :=
  ⟨S * p₁ / (q₁ : ℤ), S * p₂ / (q₂ : ℤ) + 1⟩

/-- The box of the rational `p / q`. -/
def RI.ofFrac (S p : ℤ) (q : ℕ) : RI := RI.ofRange S p q p q

def RI.add (a b : RI) : RI := ⟨a.lo + b.lo, a.hi + b.hi⟩
def RI.neg (a : RI) : RI := ⟨-a.hi, -a.lo⟩
def RI.sub (a b : RI) : RI := a.add b.neg

def imin4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def imax4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

/-- Product at scale `S`: the four corner products, floor-divided by `S`, plus one ulp. -/
def RI.mul (S : ℤ) (a b : RI) : RI :=
  ⟨imin4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi) / S,
   imax4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi) / S + 1⟩

def RI.divNat (a : RI) (n : ℕ) : RI := ⟨a.lo / (n : ℤ), a.hi / (n : ℤ) + 1⟩
def RI.widen (a : RI) (r : ℤ) : RI := ⟨a.lo - r, a.hi + r⟩

/-- `k` repeated squarings. -/
def RI.square (S : ℤ) (a : RI) : ℕ → RI
  | 0 => a
  | k + 1 => RI.square S (RI.mul S a a) k

/-- `(x^n / n!, ∑_{j ≤ n} x^j / j!)` enclosures. -/
def RI.taylor (S : ℤ) (a : RI) : ℕ → RI × RI
  | 0 => (⟨S, S⟩, ⟨S, S⟩)
  | n + 1 =>
    let p := RI.taylor S a n
    let t := (RI.mul S p.1 a).divNat (n + 1)
    (t, p.2.add t)

/-- `exp` by argument reduction `x / 2^k`, the order-`n` Taylor sum, an `r`-ulp
remainder widen, and `k` squarings. -/
def RI.expR (S : ℤ) (a : RI) (k n : ℕ) (r : ℤ) : RI :=
  RI.square S (((a.divNat (2 ^ k)).taylor S n).2.widen r) k

/-! ### Bool checks (decided per instance by `decide +kernel`) -/

def RI.subset (a b : RI) : Bool := decide (b.lo ≤ a.lo) && decide (a.hi ≤ b.hi)
def RI.lowerOK (S : ℤ) (a : RI) (p : ℤ) (q : ℕ) : Bool := decide (S * p ≤ a.lo * (q : ℤ))
def RI.upperOK (S : ℤ) (a : RI) (p : ℤ) (q : ℕ) : Bool := decide (a.hi * (q : ℤ) ≤ S * p)
/-- The reduced argument lies in `[-1, 1]`. -/
def RI.expSmallOK (S : ℤ) (a : RI) (k : ℕ) : Bool :=
  decide (-S ≤ (a.divNat (2 ^ k)).lo) && decide ((a.divNat (2 ^ k)).hi ≤ S)
/-- `r / S` dominates the `Real.exp_bound` remainder of the order-`(n+1)` partial sum. -/
def RI.expRemOK (S : ℤ) (n : ℕ) (r : ℤ) : Bool :=
  decide (S * ((n + 2 : ℕ) : ℤ) ≤ r * (((n + 1).factorial * (n + 1) : ℕ) : ℤ))

/-! ### Soundness (`mem_*`), each proved once -/

section
variable {S : ℤ}

lemma div_floor_bounds (a n : ℤ) (hn : 0 < n) :
    ((a / n : ℤ) : ℝ) * (n : ℝ) ≤ a ∧ (a : ℝ) ≤ ((a / n + 1 : ℤ) : ℝ) * (n : ℝ) := by
  constructor
  · exact_mod_cast Int.ediv_mul_le a (ne_of_gt hn)
  · exact_mod_cast (Int.lt_ediv_add_one_mul_self a hn).le

theorem RI.mem_ofRange (hS : 0 < S) {p₁ p₂ : ℤ} {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    {l u x : ℝ} (hl : l = (p₁ : ℝ) / (q₁ : ℝ)) (hu : u = (p₂ : ℝ) / (q₂ : ℝ))
    (h₁ : l ≤ x) (h₂ : x ≤ u) : (RI.ofRange S p₁ q₁ p₂ q₂).Mem S x := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hq₁' : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂' : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have A := (div_floor_bounds (S * p₁) q₁ (by exact_mod_cast hq₁)).1
  have B := (div_floor_bounds (S * p₂) q₂ (by exact_mod_cast hq₂)).2
  push_cast at A B
  subst hl hu
  constructor
  · show ((S * p₁ / (q₁ : ℤ) : ℤ) : ℝ) ≤ (S : ℝ) * x
    have h1 : ((S * p₁ / (q₁ : ℤ) : ℤ) : ℝ) ≤ (S : ℝ) * p₁ / q₁ := by
      rw [le_div_iff₀ hq₁']; exact A
    calc _ ≤ (S : ℝ) * p₁ / q₁ := h1
      _ = (S : ℝ) * ((p₁ : ℝ) / q₁) := by ring
      _ ≤ (S : ℝ) * x := by gcongr
  · show (S : ℝ) * x ≤ ((S * p₂ / (q₂ : ℤ) + 1 : ℤ) : ℝ)
    have h1 : (S : ℝ) * p₂ / q₂ ≤ ((S * p₂ / (q₂ : ℤ) + 1 : ℤ) : ℝ) := by
      rw [div_le_iff₀ hq₂']; push_cast; exact B
    calc (S : ℝ) * x ≤ (S : ℝ) * ((p₂ : ℝ) / q₂) := by gcongr
      _ = (S : ℝ) * p₂ / q₂ := by ring
      _ ≤ _ := h1

theorem RI.mem_ofFrac (hS : 0 < S) {p : ℤ} {q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : x = (p : ℝ) / (q : ℝ)) : (RI.ofFrac S p q).Mem S x :=
  RI.mem_ofRange hS hq hq hx hx le_rfl le_rfl

theorem RI.mem_add {a b : RI} {x y : ℝ} (hx : a.Mem S x) (hy : b.Mem S y) :
    (a.add b).Mem S (x + y) := by
  rcases hx with ⟨hx₀, hx₁⟩; rcases hy with ⟨hy₀, hy₁⟩
  constructor <;> simp only [RI.add, Int.cast_add] <;> linarith

theorem RI.mem_neg {a : RI} {x : ℝ} (hx : a.Mem S x) : a.neg.Mem S (-x) := by
  rcases hx with ⟨hx₀, hx₁⟩
  constructor <;> simp only [RI.neg, Int.cast_neg] <;> linarith

theorem RI.mem_sub {a b : RI} {x y : ℝ} (hx : a.Mem S x) (hy : b.Mem S y) :
    (a.sub b).Mem S (x - y) := by
  simpa [RI.sub, sub_eq_add_neg] using RI.mem_add hx (RI.mem_neg hy)

lemma mul_bounds {a b x t : ℝ} (h : a ≤ x ∧ x ≤ b) :
    min (a * t) (b * t) ≤ x * t ∧ x * t ≤ max (a * t) (b * t) := by
  rcases le_total 0 t with ht | ht
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h.1 ht),
      (mul_le_mul_of_nonneg_right h.2 ht).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h.2 ht),
      (mul_le_mul_of_nonpos_right h.1 ht).trans (le_max_left _ _)⟩

lemma four_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hxy := mul_bounds (t := y) hx
  have ha := mul_bounds (t := a) hy
  have hb := mul_bounds (t := b) hy
  simp only [mul_comm c, mul_comm d, mul_comm y] at ha hb
  constructor
  · apply le_trans _ hxy.1
    exact le_min ((min_le_left _ _).trans ha.1) ((min_le_right _ _).trans hb.1)
  · apply le_trans hxy.2
    exact max_le (ha.2.trans (le_max_left _ _)) (hb.2.trans (le_max_right _ _))

theorem RI.mem_mul (hS : 0 < S) {a b : RI} {x y : ℝ} (hx : a.Mem S x) (hy : b.Mem S y) :
    (RI.mul S a b).Mem S (x * y) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hh := four_bounds hx hy
  have hl := (div_floor_bounds (imin4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi))
    S hS).1
  have hu := (div_floor_bounds (imax4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi))
    S hS).2
  simp only [imin4, imax4, Int.cast_min, Int.cast_max, Int.cast_mul] at hl hu
  have e : ((S : ℝ) * x) * ((S : ℝ) * y) = (S : ℝ) * ((S : ℝ) * (x * y)) := by ring
  constructor
  · apply (mul_le_mul_iff_right₀ hS').mp
    dsimp only [RI.mul, imin4, imax4]
    rw [← e, mul_comm]
    exact hl.trans hh.1
  · apply (mul_le_mul_iff_right₀ hS').mp
    dsimp only [RI.mul, imin4, imax4]
    rw [← e, mul_comm (S : ℝ) (((_ : ℤ) : ℝ))]
    exact hh.2.trans hu

theorem RI.mem_divNat {a : RI} {x : ℝ} (hx : a.Mem S x) {n : ℕ} (hn : 0 < n) :
    (a.divNat n).Mem S (x / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnl : (0 : ℤ) < n := by exact_mod_cast hn
  have hl := (div_floor_bounds a.lo n hnl).1
  have hu := (div_floor_bounds a.hi n hnl).2
  push_cast at hl hu
  constructor
  · show ((a.lo / (n : ℤ) : ℤ) : ℝ) ≤ (S : ℝ) * (x / n)
    rw [← mul_div_assoc, le_div_iff₀ hn']
    exact hl.trans hx.1
  · show (S : ℝ) * (x / n) ≤ ((a.hi / (n : ℤ) + 1 : ℤ) : ℝ)
    rw [← mul_div_assoc, div_le_iff₀ hn']
    push_cast
    exact hx.2.trans hu

theorem RI.mem_widen (hS : 0 < S) {a : RI} {x y : ℝ} {r : ℤ} (hx : a.Mem S x)
    (hxy : |y - x| ≤ (r : ℝ) / (S : ℝ)) : (a.widen r).Mem S y := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hh := abs_le.mp hxy
  have hl := (div_le_iff₀ hS').mp
    (show -(r : ℝ) / (S : ℝ) ≤ y - x by simpa only [neg_div] using hh.1)
  have hu := (le_div_iff₀ hS').mp hh.2
  rcases hx with ⟨hx₀, hx₁⟩
  constructor <;> simp only [RI.widen, Int.cast_sub, Int.cast_add] <;> nlinarith

theorem RI.mem_square (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) (k : ℕ) :
    (RI.square S a k).Mem S (x ^ (2 ^ k)) := by
  induction k generalizing a x with
  | zero => simpa [RI.square] using hx
  | succ k ih =>
    have h := ih (RI.mem_mul hS hx hx)
    rw [RI.square]
    have e : (x * x) ^ (2 ^ k) = x ^ (2 ^ (k + 1)) := by
      rw [← pow_two, ← pow_mul, pow_succ, mul_comm (2 ^ k) 2]
    rwa [e] at h

theorem RI.mem_one : (⟨S, S⟩ : RI).Mem S 1 := by
  constructor <;> simp

theorem RI.mem_taylor (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) (n : ℕ) :
    (RI.taylor S a n).1.Mem S (x ^ n / (n.factorial : ℝ)) ∧
    (RI.taylor S a n).2.Mem S (∑ j ∈ Finset.range (n + 1), x ^ j / (j.factorial : ℝ)) := by
  induction n with
  | zero => simpa [RI.taylor] using And.intro (RI.mem_one (S := S)) (RI.mem_one (S := S))
  | succ n ih =>
    have hf : x ^ (n + 1) / ((n + 1).factorial : ℝ) =
        (x ^ n / (n.factorial : ℝ)) * x / ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      field_simp
    have ht := RI.mem_divNat (RI.mem_mul hS ih.1 hx) (Nat.succ_pos n)
    constructor
    · rw [hf]; exact ht
    · rw [Finset.sum_range_succ, hf]
      exact RI.mem_add ih.2 ht

theorem RI.mem_of_subset {a b : RI} {x : ℝ} (hx : a.Mem S x) (h : RI.subset a b = true) :
    b.Mem S x := by
  simp only [RI.subset, Bool.and_eq_true, decide_eq_true_eq] at h
  have hl' : (b.lo : ℝ) ≤ a.lo := by exact_mod_cast h.1
  have hu' : (a.hi : ℝ) ≤ b.hi := by exact_mod_cast h.2
  exact ⟨hl'.trans hx.1, hx.2.trans hu'⟩

theorem RI.le_of_mem (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) {p : ℤ} {q : ℕ}
    (hq : 0 < q) {l : ℝ} (hl : l = (p : ℝ) / (q : ℝ)) (h : RI.lowerOK S a p q = true) :
    l ≤ x := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [RI.lowerOK, decide_eq_true_eq] at h
  have h' : (S : ℝ) * p ≤ (a.lo : ℝ) * q := by exact_mod_cast h
  subst hl
  rw [div_le_iff₀ hq']
  have : (S : ℝ) * (p : ℝ) ≤ (S : ℝ) * (x * q) := by nlinarith [hx.1]
  exact le_of_mul_le_mul_left this hS'

theorem RI.ge_of_mem (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) {p : ℤ} {q : ℕ}
    (hq : 0 < q) {u : ℝ} (hu : u = (p : ℝ) / (q : ℝ)) (h : RI.upperOK S a p q = true) :
    x ≤ u := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [RI.upperOK, decide_eq_true_eq] at h
  have h' : (a.hi : ℝ) * q ≤ (S : ℝ) * p := by exact_mod_cast h
  subst hu
  rw [le_div_iff₀ hq']
  have : (S : ℝ) * (x * q) ≤ (S : ℝ) * (p : ℝ) := by nlinarith [hx.2]
  exact le_of_mul_le_mul_left this hS'

theorem RI.mem_expR (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) {k n : ℕ} {r : ℤ}
    (hsmall : RI.expSmallOK S a k = true) (hrem : RI.expRemOK S n r = true) :
    (RI.expR S a k n r).Mem S (Real.exp x) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hd := RI.mem_divNat hx (show 0 < 2 ^ k from Nat.two_pow_pos k)
  set y : ℝ := x / ((2 ^ k : ℕ) : ℝ) with hy_def
  -- the reduced argument is in [-1, 1]
  have hy : |y| ≤ 1 := by
    simp only [RI.expSmallOK, Bool.and_eq_true, decide_eq_true_eq] at hsmall
    have h1 : (-(S : ℝ)) ≤ ((a.divNat (2 ^ k)).lo : ℝ) := by exact_mod_cast hsmall.1
    have h2 : ((a.divNat (2 ^ k)).hi : ℝ) ≤ (S : ℝ) := by exact_mod_cast hsmall.2
    rw [abs_le]
    constructor <;> nlinarith [hd.1, hd.2]
  have ht := (RI.mem_taylor hS hd n).2
  have hb := Real.exp_bound hy (n := n + 1) (Nat.succ_pos n)
  have hr : (S : ℝ) * ((n + 2 : ℕ) : ℝ) ≤ (r : ℝ) * (((n + 1).factorial * (n + 1) : ℕ) : ℝ) := by
    simp only [RI.expRemOK, decide_eq_true_eq] at hrem
    exact_mod_cast hrem
  have hF : (0 : ℝ) < (((n + 1).factorial * (n + 1) : ℕ) : ℝ) := by positivity
  have herr : |Real.exp y - ∑ j ∈ Finset.range (n + 1), y ^ j / (j.factorial : ℝ)| ≤
      (r : ℝ) / (S : ℝ) := by
    refine hb.trans ?_
    have hpow : |y| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
    have hq : (((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ)) ≤
        (r : ℝ) / (S : ℝ) := by
      rw [div_le_div_iff₀ (by push_cast; positivity) hS']
      have e1 : (((n + 1).succ : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
      have e2 : (((n + 1).factorial : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) =
          (((n + 1).factorial * (n + 1) : ℕ) : ℝ) := by push_cast; ring
      rw [e1, e2]; linarith
    have hnn : (0 : ℝ) ≤ (((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ)) := by
      positivity
    calc |y| ^ (n + 1) * ((((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ)))
        ≤ 1 * ((((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ))) := by
          gcongr
      _ ≤ (r : ℝ) / (S : ℝ) := by rw [one_mul]; exact hq
  have hw := RI.mem_widen hS ht herr
  have hsq := RI.mem_square hS hw k
  have hpow : Real.exp y ^ (2 ^ k) = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hy_def]
    field_simp
  rw [hpow] at hsq
  exact hsq

end

end ScaledInterval
