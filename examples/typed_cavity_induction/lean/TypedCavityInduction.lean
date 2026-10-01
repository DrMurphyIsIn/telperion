/- telperion 0.1.6 | family TypedCavityInduction | input-hash 140e74a3fe64c914
   585 theorems, 392 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace TypedCavityInduction

/-! ## Generic typed cavity induction (emitted once per file)

A finite type table with per-type bounds is an inductive invariant of a branching recursion
over every finite rooted tree.  conjecture1_proved = False. -/

namespace TypedCavity

/-- Finite rooted trees; an internal node has `m + 1 ≥ 1` children. -/
inductive PTree : Type
  | leaf : PTree
  | node (m : ℕ) (cs : Fin (m + 1) → PTree) : PTree

namespace PTree

/-- Number of vertices. -/
def size : PTree → ℕ
  | leaf => 1
  | node _ cs => (∑ i, size (cs i)) + 1

/-- The message: `y0` at a leaf, `h (#children) (sum of the children's messages)`. -/
def msg (h : ℕ → ℝ → ℝ) (y0 : ℝ) : PTree → ℝ
  | leaf => y0
  | node m cs => h (m + 1) (∑ i, msg h y0 (cs i))

/-- The value: `l0` at a leaf, the children's values plus `g (#children) (sum)`. -/
def ell (g h : ℕ → ℝ → ℝ) (l0 y0 : ℝ) : PTree → ℝ
  | leaf => l0
  | node m cs => (∑ i, ell g h l0 y0 (cs i)) + g (m + 1) (∑ i, msg h y0 (cs i))

/-- The type of a tree: `tp 0 0` at a leaf, `tp (#children) (sum of the children's messages)`. -/
def typ {T : Type} (tp : ℕ → ℝ → T) (h : ℕ → ℝ → ℝ) (y0 : ℝ) : PTree → T
  | leaf => tp 0 0
  | node m cs => tp (m + 1) (∑ i, msg h y0 (cs i))

/-- Every internal node's child count satisfies `ok`. -/
def AllDeg (ok : ℕ → Prop) : PTree → Prop
  | leaf => True
  | node m cs => ok (m + 1) ∧ ∀ i, AllDeg ok (cs i)

theorem allDeg_true (b : PTree) : b.AllDeg (fun _ => True) := by
  induction b with
  | leaf => trivial
  | node m cs ih => exact ⟨trivial, ih⟩

end PTree

/-- The invariant of one tree of type `t` with value `l` and message `y`. -/
abbrev Inv {T : Type} (B ylo yhi : T → ℝ) (t : T) (l y : ℝ) : Prop :=
  l ≤ B t ∧ ylo t ≤ y ∧ y ≤ yhi t

/-- THE TYPED INDUCTION.  If the leaf satisfies the invariant of its type and every admissible
parent step preserves it (children of any types satisfying theirs), every tree satisfies the
invariant of its own type. -/
theorem typed_induction_core {T : Type} (ok : ℕ → Prop) (h g : ℕ → ℝ → ℝ) (y0 l0 : ℝ)
    (tp : ℕ → ℝ → T) (B ylo yhi : T → ℝ)
    (hbase : Inv B ylo yhi (tp 0 0) l0 y0)
    (hstep : ∀ k : ℕ, 1 ≤ k → ok k → ∀ (τ : Fin k → T) (y l : Fin k → ℝ),
      (∀ i, Inv B ylo yhi (τ i) (l i) (y i)) →
      Inv B ylo yhi (tp k (∑ i, y i)) ((∑ i, l i) + g k (∑ i, y i)) (h k (∑ i, y i))) :
    ∀ b : PTree, b.AllDeg ok →
      Inv B ylo yhi (b.typ tp h y0) (b.ell g h l0 y0) (b.msg h y0) := by
  intro b
  induction b with
  | leaf => intro _; simpa [PTree.typ, PTree.ell, PTree.msg] using hbase
  | node m cs ih =>
    intro hdeg
    obtain ⟨hok, hcs⟩ := hdeg
    simp only [PTree.typ, PTree.ell, PTree.msg]
    exact hstep (m + 1) (Nat.le_add_left 1 m) hok (fun i => (cs i).typ tp h y0)
      (fun i => (cs i).msg h y0) (fun i => (cs i).ell g h l0 y0) (fun i => ih i (hcs i))

/-- A sum over children is a sum over types weighted by the child counts. -/
theorem sum_by_type {n k : ℕ} (τ : Fin k → Fin n) (F : Fin n → ℝ) :
    ∑ i, F (τ i) = ∑ t, ((Finset.univ.filter (fun i => τ i = t)).card : ℝ) * F t := by
  rw [← Finset.sum_fiberwise Finset.univ τ (fun i => F (τ i))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem count_sum {n k : ℕ} (τ : Fin k → Fin n) :
    ∑ t, (Finset.univ.filter (fun i => τ i = t)).card = k := by
  rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (τ i))]
  simp

/-- ENUMERATION reduces to child-type COUNTS: a step stated for every count vector `c` with
`∑ c = k` gives the step for every assignment of child types. -/
theorem step_of_counts {n k : ℕ} (G H : ℝ → ℝ) (tpk : ℝ → Fin n) (B ylo yhi : Fin n → ℝ)
    (hc : ∀ c : Fin n → ℕ, ∑ t, c t = k → ∀ R : ℝ,
      ∑ t, (c t : ℝ) * ylo t ≤ R → R ≤ ∑ t, (c t : ℝ) * yhi t →
      Inv B ylo yhi (tpk R) ((∑ t, (c t : ℝ) * B t) + G R) (H R))
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    Inv B ylo yhi (tpk (∑ i, y i)) ((∑ i, l i) + G (∑ i, y i)) (H (∑ i, y i)) := by
  set c : Fin n → ℕ := fun t => (Finset.univ.filter (fun i => τ i = t)).card
  have h1 : ∑ t, (c t : ℝ) * ylo t ≤ ∑ i, y i := by
    rw [← sum_by_type τ ylo]; exact Finset.sum_le_sum fun i _ => (hch i).2.1
  have h2 : ∑ i, y i ≤ ∑ t, (c t : ℝ) * yhi t := by
    rw [← sum_by_type τ yhi]; exact Finset.sum_le_sum fun i _ => (hch i).2.2
  have hl : ∑ i, l i ≤ ∑ t, (c t : ℝ) * B t := by
    rw [← sum_by_type τ B]; exact Finset.sum_le_sum fun i _ => (hch i).1
  obtain ⟨a1, a2, a3⟩ := hc c (count_sum τ) _ h1 h2
  exact ⟨by linarith, a2, a3⟩

/-- The JOIN version of `step_of_counts` (a root closing `k` trees; value only). -/
theorem join_of_counts {n k : ℕ} (G : ℝ → ℝ) (C : ℝ) (B ylo yhi : Fin n → ℝ)
    (hc : ∀ c : Fin n → ℕ, ∑ t, c t = k → ∀ R : ℝ,
      ∑ t, (c t : ℝ) * ylo t ≤ R → R ≤ ∑ t, (c t : ℝ) * yhi t →
      (∑ t, (c t : ℝ) * B t) + G R ≤ C)
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    (∑ i, l i) + G (∑ i, y i) ≤ C := by
  set c : Fin n → ℕ := fun t => (Finset.univ.filter (fun i => τ i = t)).card
  have h1 : ∑ t, (c t : ℝ) * ylo t ≤ ∑ i, y i := by
    rw [← sum_by_type τ ylo]; exact Finset.sum_le_sum fun i _ => (hch i).2.1
  have h2 : ∑ i, y i ≤ ∑ t, (c t : ℝ) * yhi t := by
    rw [← sum_by_type τ yhi]; exact Finset.sum_le_sum fun i _ => (hch i).2.2
  have hl : ∑ i, l i ≤ ∑ t, (c t : ℝ) * B t := by
    rw [← sum_by_type τ B]; exact Finset.sum_le_sum fun i _ => (hch i).1
  have := hc c (count_sum τ) _ h1 h2
  linarith

/-- SEPARABLE (tangent) bound: with a per-type cap `B t + s y ≤ μ`, the children's values plus
`s` times their message sum are at most `k μ`. -/
theorem separable_bound {n k : ℕ} (B ylo yhi : Fin n → ℝ) (s μ : ℝ)
    (hμ : ∀ t y, ylo t ≤ y → y ≤ yhi t → B t + s * y ≤ μ)
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    (∑ i, l i) + s * ∑ i, y i ≤ (k : ℝ) * μ := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have : ∑ i, (l i + s * y i) ≤ ∑ _i : Fin k, μ :=
    Finset.sum_le_sum fun i _ => by
      have := hμ (τ i) (y i) (hch i).2.1 (hch i).2.2
      linarith [(hch i).1]
  simpa using this

/-- The children's message sum lies in `[k ymin, k ymax]`. -/
theorem msg_sum_range {n k : ℕ} (B ylo yhi : Fin n → ℝ) (ymin ymax : ℝ)
    (hmin : ∀ t, ymin ≤ ylo t) (hmax : ∀ t, yhi t ≤ ymax)
    (τ : Fin k → Fin n) (y l : Fin k → ℝ) (hch : ∀ i, Inv B ylo yhi (τ i) (l i) (y i)) :
    (k : ℝ) * ymin ≤ ∑ i, y i ∧ ∑ i, y i ≤ (k : ℝ) * ymax := by
  constructor
  · have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      le_trans (hmin (τ i)) (hch i).2.1
    simpa using this
  · have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      le_trans (hch i).2.2 (hmax (τ i))
    simpa using this

end TypedCavity

open TypedCavity

/-! ## Instance `bbg3`

Claim: on every finite rooted tree of child count at most 2, `ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ yhi[type b]`, for
  h(m, R) = 1/(m+1),  g(m, R) = R/(m+1) - 7/27  (m = number of children),
  leaf (y, l) = (1, -7/27), and the type table
  0 `deg1`: 0 ≤ k ≤ 0, any R, EXACT (l, y) = (-7/27, 1)
  1 `deg2`: 1 ≤ k ≤ 1, any R, B = -1/54, y in [1/2, 1/2]
  2 `deg3`: 2 ≤ k, any R, B = 1/27, y in [1/3, 1/3]
Devices: enumeration k = 1..2.
conjecture1_proved = False. -/

noncomputable def bbg3_h : ℕ → ℝ → ℝ := fun m _ => ((1 : ℝ)) / ((1 : ℝ) + (m : ℝ))
noncomputable def bbg3_g : ℕ → ℝ → ℝ := fun m R => ((-7 : ℝ) + (27 : ℝ) * R + (-7 : ℝ) * (m : ℝ)) / ((27 : ℝ) + (27 : ℝ) * (m : ℝ))
noncomputable def bbg3_B : Fin 3 → ℝ := ![(-7 / 27 : ℝ), (-1 / 54 : ℝ), (1 / 27 : ℝ)]
theorem bbg3_B_0 : bbg3_B 0 = (-7 / 27 : ℝ) := rfl
theorem bbg3_B_1 : bbg3_B 1 = (-1 / 54 : ℝ) := rfl
theorem bbg3_B_2 : bbg3_B 2 = (1 / 27 : ℝ) := rfl
noncomputable def bbg3_ylo : Fin 3 → ℝ := ![(1 : ℝ), (1 / 2 : ℝ), (1 / 3 : ℝ)]
theorem bbg3_ylo_0 : bbg3_ylo 0 = (1 : ℝ) := rfl
theorem bbg3_ylo_1 : bbg3_ylo 1 = (1 / 2 : ℝ) := rfl
theorem bbg3_ylo_2 : bbg3_ylo 2 = (1 / 3 : ℝ) := rfl
noncomputable def bbg3_yhi : Fin 3 → ℝ := ![(1 : ℝ), (1 / 2 : ℝ), (1 / 3 : ℝ)]
theorem bbg3_yhi_0 : bbg3_yhi 0 = (1 : ℝ) := rfl
theorem bbg3_yhi_1 : bbg3_yhi 1 = (1 / 2 : ℝ) := rfl
theorem bbg3_yhi_2 : bbg3_yhi 2 = (1 / 3 : ℝ) := rfl

/-- The type map: degree groups, then bins of the message sum. -/
noncomputable def bbg3_tp (k : ℕ) (_ : ℝ) : Fin 3 :=
  if k ≤ 0 then 0 else if k ≤ 1 then 1 else 2

theorem bbg3_tp_0_0 (k : ℕ) (hk2 : k ≤ 0) (R : ℝ) :
    bbg3_tp k R = 0 := by
  unfold bbg3_tp
  rw [if_pos (show k ≤ 0 by omega)]

theorem bbg3_tp_1_0 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 1) (R : ℝ) :
    bbg3_tp k R = 1 := by
  unfold bbg3_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_pos (show k ≤ 1 by omega)]

theorem bbg3_tp_2_0 (k : ℕ) (hk1 : 2 ≤ k) (R : ℝ) :
    bbg3_tp k R = 2 := by
  unfold bbg3_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega)]

theorem bbg3_base : Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 0 0) (-7 / 27 : ℝ) (1 : ℝ) := by
  rw [bbg3_tp_0_0 (0) (by omega) (0)]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [bbg3_B_0, bbg3_ylo_0, bbg3_yhi_0]

theorem bbg3_ymin : ∀ t, (1 / 3 : ℝ) ≤ bbg3_ylo t := by
  intro t; fin_cases t <;> norm_num [bbg3_ylo]

theorem bbg3_ymax : ∀ t, bbg3_yhi t ≤ (1 : ℝ) := by
  intro t; fin_cases t <;> norm_num [bbg3_yhi]

theorem bbg3_Bmax : ∀ t, bbg3_B t ≤ (1 / 27 : ℝ) := by
  intro t; fin_cases t <;> norm_num [bbg3_B]

theorem bbg3_e1_0_0_1_b0_val (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    (1 / 27 : ℝ) + bbg3_g 1 R ≤ (-1 / 54 : ℝ) := by
  obtain rfl : R = (1 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e1_0_0_1_b0_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    (1 / 2 : ℝ) ≤ bbg3_h 1 R := by
  obtain rfl : R = (1 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e1_0_0_1_b0_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    bbg3_h 1 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e1_0_0_1 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 1 R) ((1 / 27 : ℝ) + bbg3_g 1 R) (bbg3_h 1 R) := by
  rw [bbg3_tp_1_0 (1) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_1]; exact bbg3_e1_0_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_1]; exact bbg3_e1_0_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_1]; exact bbg3_e1_0_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg3_e1_0_1_0_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 54 : ℝ) + bbg3_g 1 R ≤ (-1 / 54 : ℝ) := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e1_0_1_0_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ bbg3_h 1 R := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e1_0_1_0_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    bbg3_h 1 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e1_0_1_0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 1 R) ((-1 / 54 : ℝ) + bbg3_g 1 R) (bbg3_h 1 R) := by
  rw [bbg3_tp_1_0 (1) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_1]; exact bbg3_e1_0_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_1]; exact bbg3_e1_0_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_1]; exact bbg3_e1_0_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg3_e1_1_0_0_b0_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 27 : ℝ) + bbg3_g 1 R ≤ (-1 / 54 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e1_1_0_0_b0_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ bbg3_h 1 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e1_1_0_0_b0_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    bbg3_h 1 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e1_1_0_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 1 R) ((-7 / 27 : ℝ) + bbg3_g 1 R) (bbg3_h 1 R) := by
  rw [bbg3_tp_1_0 (1) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_1]; exact bbg3_e1_1_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_1]; exact bbg3_e1_1_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_1]; exact bbg3_e1_1_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg3_cnt1 (c : Fin 3 → ℕ) (hc : ∑ t, c t = 1) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * bbg3_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * bbg3_yhi t) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 1 R)
      ((∑ t, (c t : ℝ) * bbg3_B t) + bbg3_g 1 R) (bbg3_h 1 R) := by
  simp only [Fin.sum_univ_three, bbg3_B_0, bbg3_B_1, bbg3_B_2, bbg3_ylo_0, bbg3_ylo_1, bbg3_ylo_2, bbg3_yhi_0, bbg3_yhi_1, bbg3_yhi_2] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  have b0 : c0 ≤ 1 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · obtain rfl : c2 = 1 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e1_0_0_1 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e1_0_1_0 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e1_1_0_0 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩

theorem bbg3_e2_0_0_2_b0_val (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    (2 / 27 : ℝ) + bbg3_g 2 R ≤ (1 / 27 : ℝ) := by
  obtain rfl : R = (2 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e2_0_0_2_b0_lo (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg3_h 2 R := by
  obtain rfl : R = (2 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_0_0_2_b0_hi (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    bbg3_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (2 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_0_0_2 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 2 R) ((2 / 27 : ℝ) + bbg3_g 2 R) (bbg3_h 2 R) := by
  rw [bbg3_tp_2_0 (2) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_2]; exact bbg3_e2_0_0_2_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_2]; exact bbg3_e2_0_0_2_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_2]; exact bbg3_e2_0_0_2_b0_hi R (by linarith) (by linarith)

theorem bbg3_e2_0_1_1_b0_val (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    (1 / 54 : ℝ) + bbg3_g 2 R ≤ (1 / 27 : ℝ) := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e2_0_1_1_b0_lo (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg3_h 2 R := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_0_1_1_b0_hi (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    bbg3_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_0_1_1 (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 2 R) ((1 / 54 : ℝ) + bbg3_g 2 R) (bbg3_h 2 R) := by
  rw [bbg3_tp_2_0 (2) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_2]; exact bbg3_e2_0_1_1_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_2]; exact bbg3_e2_0_1_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_2]; exact bbg3_e2_0_1_1_b0_hi R (by linarith) (by linarith)

theorem bbg3_e2_0_2_0_b0_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 27 : ℝ) + bbg3_g 2 R ≤ (1 / 27 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e2_0_2_0_b0_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg3_h 2 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_0_2_0_b0_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    bbg3_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_0_2_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 2 R) ((-1 / 27 : ℝ) + bbg3_g 2 R) (bbg3_h 2 R) := by
  rw [bbg3_tp_2_0 (2) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_2]; exact bbg3_e2_0_2_0_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_2]; exact bbg3_e2_0_2_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_2]; exact bbg3_e2_0_2_0_b0_hi R (by linarith) (by linarith)

theorem bbg3_e2_1_0_1_b0_val (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (-2 / 9 : ℝ) + bbg3_g 2 R ≤ (1 / 27 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e2_1_0_1_b0_lo (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg3_h 2 R := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_1_0_1_b0_hi (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    bbg3_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_1_0_1 (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 2 R) ((-2 / 9 : ℝ) + bbg3_g 2 R) (bbg3_h 2 R) := by
  rw [bbg3_tp_2_0 (2) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_2]; exact bbg3_e2_1_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_2]; exact bbg3_e2_1_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_2]; exact bbg3_e2_1_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg3_e2_1_1_0_b0_val (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-5 / 18 : ℝ) + bbg3_g 2 R ≤ (1 / 27 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e2_1_1_0_b0_lo (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg3_h 2 R := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_1_1_0_b0_hi (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    bbg3_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_1_1_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 2 R) ((-5 / 18 : ℝ) + bbg3_g 2 R) (bbg3_h 2 R) := by
  rw [bbg3_tp_2_0 (2) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_2]; exact bbg3_e2_1_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_2]; exact bbg3_e2_1_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_2]; exact bbg3_e2_1_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg3_e2_2_0_0_b0_val (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-14 / 27 : ℝ) + bbg3_g 2 R ≤ (1 / 27 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_g]

theorem bbg3_e2_2_0_0_b0_lo (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg3_h 2 R := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_2_0_0_b0_hi (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    bbg3_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_h]

theorem bbg3_e2_2_0_0 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 2 R) ((-14 / 27 : ℝ) + bbg3_g 2 R) (bbg3_h 2 R) := by
  rw [bbg3_tp_2_0 (2) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg3_B_2]; exact bbg3_e2_2_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg3_ylo_2]; exact bbg3_e2_2_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg3_yhi_2]; exact bbg3_e2_2_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg3_cnt2 (c : Fin 3 → ℕ) (hc : ∑ t, c t = 2) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * bbg3_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * bbg3_yhi t) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp 2 R)
      ((∑ t, (c t : ℝ) * bbg3_B t) + bbg3_g 2 R) (bbg3_h 2 R) := by
  simp only [Fin.sum_univ_three, bbg3_B_0, bbg3_B_1, bbg3_B_2, bbg3_ylo_0, bbg3_ylo_1, bbg3_ylo_2, bbg3_yhi_0, bbg3_yhi_1, bbg3_yhi_2] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  have b0 : c0 ≤ 2 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 2 := by omega
    interval_cases c1
    · obtain rfl : c2 = 2 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e2_0_0_2 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · obtain rfl : c2 = 1 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e2_0_1_1 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e2_0_2_0 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · obtain rfl : c2 = 1 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e2_1_0_1 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e2_1_1_0 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      have hob := bbg3_e2_2_0_0 R (by linarith) (by linarith)
      exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩

theorem bbg3_hstep : ∀ k : ℕ, 1 ≤ k → k ≤ 2 → ∀ (τ : Fin k → Fin 3) (y l : Fin k → ℝ),
    (∀ i, Inv bbg3_B bbg3_ylo bbg3_yhi (τ i) (l i) (y i)) →
    Inv bbg3_B bbg3_ylo bbg3_yhi (bbg3_tp k (∑ i, y i))
      ((∑ i, l i) + bbg3_g k (∑ i, y i)) (bbg3_h k (∑ i, y i)) := by
  intro k hk hok τ y l hch
  interval_cases k
  · exact step_of_counts (bbg3_g 1) (bbg3_h 1) (bbg3_tp 1) bbg3_B bbg3_ylo bbg3_yhi bbg3_cnt1 τ y l hch
  · exact step_of_counts (bbg3_g 2) (bbg3_h 2) (bbg3_tp 2) bbg3_B bbg3_ylo bbg3_yhi bbg3_cnt2 τ y l hch

/-- MAIN.  The type table is an inductive invariant on every tree of child count at most 2:
`ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ yhi[type b]`. -/
theorem bbg3 (b : PTree) (hb : b.AllDeg (fun k => k ≤ 2)) :
    Inv bbg3_B bbg3_ylo bbg3_yhi (b.typ bbg3_tp bbg3_h (1 : ℝ))
      (b.ell bbg3_g bbg3_h (-7 / 27 : ℝ) (1 : ℝ)) (b.msg bbg3_h (1 : ℝ)) :=
  typed_induction_core (fun k => k ≤ 2) bbg3_h bbg3_g (1 : ℝ) (-7 / 27 : ℝ) bbg3_tp bbg3_B bbg3_ylo bbg3_yhi
    bbg3_base bbg3_hstep b hb

/-- Uniform corollary: `ell b ≤ max_t B_t = 1/27`. -/
theorem bbg3_uniform (b : PTree) (hb : b.AllDeg (fun k => k ≤ 2)) :
    b.ell bbg3_g bbg3_h (-7 / 27 : ℝ) (1 : ℝ) ≤ (1 / 27 : ℝ) :=
  le_trans (bbg3 b hb).1 (bbg3_Bmax _)

/-- The join (root) function, `gJ(R)` at root child count 3. -/
noncomputable def bbg3_gJ : ℝ → ℝ := fun R => ((-7 / 27 : ℝ) + (1 / 3 : ℝ) * R)

theorem bbg3_j_0_0_3 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 9 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_0_1_2 (R : ℝ) (h1 : (7 / 6 : ℝ) ≤ R) (h2 : R ≤ (7 / 6 : ℝ)) :
    (1 / 18 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (7 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_0_2_1 (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (0 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_0_3_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-1 / 18 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_1_0_2 (R : ℝ) (h1 : (5 / 3 : ℝ) ≤ R) (h2 : R ≤ (5 / 3 : ℝ)) :
    (-5 / 27 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (5 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_1_1_1 (R : ℝ) (h1 : (11 / 6 : ℝ) ≤ R) (h2 : R ≤ (11 / 6 : ℝ)) :
    (-13 / 54 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (11 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_1_2_0 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-8 / 27 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_2_0_1 (R : ℝ) (h1 : (7 / 3 : ℝ) ≤ R) (h2 : R ≤ (7 / 3 : ℝ)) :
    (-13 / 27 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (7 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_2_1_0 (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    (-29 / 54 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (5 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_j_3_0_0 (R : ℝ) (h1 : (3 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (-7 / 9 : ℝ) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  obtain rfl : R = (3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg3_gJ]

theorem bbg3_jcnt (c : Fin 3 → ℕ) (hc : ∑ t, c t = 3) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * bbg3_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * bbg3_yhi t) :
    (∑ t, (c t : ℝ) * bbg3_B t) + bbg3_gJ R ≤ (5 / 27 : ℝ) := by
  simp only [Fin.sum_univ_three, bbg3_B_0, bbg3_B_1, bbg3_B_2, bbg3_ylo_0, bbg3_ylo_1, bbg3_ylo_2, bbg3_yhi_0, bbg3_yhi_1, bbg3_yhi_2] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  have b0 : c0 ≤ 3 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 3 := by omega
    interval_cases c1
    · obtain rfl : c2 = 3 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_0_0_3 R (by linarith) (by linarith)]
    · obtain rfl : c2 = 2 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_0_1_2 R (by linarith) (by linarith)]
    · obtain rfl : c2 = 1 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_0_2_1 R (by linarith) (by linarith)]
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_0_3_0 R (by linarith) (by linarith)]
  · have b1 : c1 ≤ 2 := by omega
    interval_cases c1
    · obtain rfl : c2 = 2 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_1_0_2 R (by linarith) (by linarith)]
    · obtain rfl : c2 = 1 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_1_1_1 R (by linarith) (by linarith)]
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_1_2_0 R (by linarith) (by linarith)]
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · obtain rfl : c2 = 1 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_2_0_1 R (by linarith) (by linarith)]
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_2_1_0 R (by linarith) (by linarith)]
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · obtain rfl : c2 = 0 := by omega
      push_cast at h1 h2 ⊢
      linarith [bbg3_j_3_0_0 R (by linarith) (by linarith)]

/-- JOIN.  A root with 3 children closing any 3 trees: `∑ ell + gJ(∑ msg) ≤ 5/27`. -/
theorem bbg3_join (b : Fin 3 → PTree) (hb : ∀ i, (b i).AllDeg (fun k => k ≤ 2)) :
    (∑ i, (b i).ell bbg3_g bbg3_h (-7 / 27 : ℝ) (1 : ℝ)) +
      bbg3_gJ (∑ i, (b i).msg bbg3_h (1 : ℝ)) ≤ (5 / 27 : ℝ) :=
  join_of_counts bbg3_gJ (5 / 27 : ℝ) bbg3_B bbg3_ylo bbg3_yhi bbg3_jcnt
    (fun i => (b i).typ bbg3_tp bbg3_h (1 : ℝ))
    (fun i => (b i).msg bbg3_h (1 : ℝ))
    (fun i => (b i).ell bbg3_g bbg3_h (-7 / 27 : ℝ) (1 : ℝ))
    (fun i => bbg3 (b i) (hb i))

/-! ## Instance `bbg4`

Claim: on every finite rooted tree of child count at most 3, `ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ yhi[type b]`, for
  h(m, R) = 1/(m+1),  g(m, R) = R/(m+1) - 139/528  (m = number of children),
  leaf (y, l) = (1, -139/528), and the type table
  0 `deg1`: 0 ≤ k ≤ 0, any R, EXACT (l, y) = (-139/528, 1)
  1 `deg2`: 1 ≤ k ≤ 1, any R, B = -7/264, y in [1/2, 1/2]
  2 `deg3`: 2 ≤ k ≤ 2, any R, B = 3/176, y in [1/3, 1/3]
  3 `deg4`: 3 ≤ k, any R, B = 5/132, y in [1/4, 1/4]
Devices: enumeration k = 1..3.
conjecture1_proved = False. -/

noncomputable def bbg4_h : ℕ → ℝ → ℝ := fun m _ => ((1 : ℝ)) / ((1 : ℝ) + (m : ℝ))
noncomputable def bbg4_g : ℕ → ℝ → ℝ := fun m R => ((-139 : ℝ) + (528 : ℝ) * R + (-139 : ℝ) * (m : ℝ)) / ((528 : ℝ) + (528 : ℝ) * (m : ℝ))
noncomputable def bbg4_B : Fin 4 → ℝ := ![(-139 / 528 : ℝ), (-7 / 264 : ℝ), (3 / 176 : ℝ), (5 / 132 : ℝ)]
theorem bbg4_B_0 : bbg4_B 0 = (-139 / 528 : ℝ) := rfl
theorem bbg4_B_1 : bbg4_B 1 = (-7 / 264 : ℝ) := rfl
theorem bbg4_B_2 : bbg4_B 2 = (3 / 176 : ℝ) := rfl
theorem bbg4_B_3 : bbg4_B 3 = (5 / 132 : ℝ) := rfl
noncomputable def bbg4_ylo : Fin 4 → ℝ := ![(1 : ℝ), (1 / 2 : ℝ), (1 / 3 : ℝ), (1 / 4 : ℝ)]
theorem bbg4_ylo_0 : bbg4_ylo 0 = (1 : ℝ) := rfl
theorem bbg4_ylo_1 : bbg4_ylo 1 = (1 / 2 : ℝ) := rfl
theorem bbg4_ylo_2 : bbg4_ylo 2 = (1 / 3 : ℝ) := rfl
theorem bbg4_ylo_3 : bbg4_ylo 3 = (1 / 4 : ℝ) := rfl
noncomputable def bbg4_yhi : Fin 4 → ℝ := ![(1 : ℝ), (1 / 2 : ℝ), (1 / 3 : ℝ), (1 / 4 : ℝ)]
theorem bbg4_yhi_0 : bbg4_yhi 0 = (1 : ℝ) := rfl
theorem bbg4_yhi_1 : bbg4_yhi 1 = (1 / 2 : ℝ) := rfl
theorem bbg4_yhi_2 : bbg4_yhi 2 = (1 / 3 : ℝ) := rfl
theorem bbg4_yhi_3 : bbg4_yhi 3 = (1 / 4 : ℝ) := rfl

/-- The type map: degree groups, then bins of the message sum. -/
noncomputable def bbg4_tp (k : ℕ) (_ : ℝ) : Fin 4 :=
  if k ≤ 0 then 0 else if k ≤ 1 then 1 else if k ≤ 2 then 2 else 3

theorem bbg4_tp_0_0 (k : ℕ) (hk2 : k ≤ 0) (R : ℝ) :
    bbg4_tp k R = 0 := by
  unfold bbg4_tp
  rw [if_pos (show k ≤ 0 by omega)]

theorem bbg4_tp_1_0 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 1) (R : ℝ) :
    bbg4_tp k R = 1 := by
  unfold bbg4_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_pos (show k ≤ 1 by omega)]

theorem bbg4_tp_2_0 (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k ≤ 2) (R : ℝ) :
    bbg4_tp k R = 2 := by
  unfold bbg4_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega), if_pos (show k ≤ 2 by omega)]

theorem bbg4_tp_3_0 (k : ℕ) (hk1 : 3 ≤ k) (R : ℝ) :
    bbg4_tp k R = 3 := by
  unfold bbg4_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega), if_neg (show ¬ (k ≤ 2) by omega)]

theorem bbg4_base : Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 0 0) (-139 / 528 : ℝ) (1 : ℝ) := by
  rw [bbg4_tp_0_0 (0) (by omega) (0)]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [bbg4_B_0, bbg4_ylo_0, bbg4_yhi_0]

theorem bbg4_ymin : ∀ t, (1 / 4 : ℝ) ≤ bbg4_ylo t := by
  intro t; fin_cases t <;> norm_num [bbg4_ylo]

theorem bbg4_ymax : ∀ t, bbg4_yhi t ≤ (1 : ℝ) := by
  intro t; fin_cases t <;> norm_num [bbg4_yhi]

theorem bbg4_Bmax : ∀ t, bbg4_B t ≤ (5 / 132 : ℝ) := by
  intro t; fin_cases t <;> norm_num [bbg4_B]

theorem bbg4_e1_0_0_0_1_b0_val (R : ℝ) (h1 : (1 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 / 4 : ℝ)) :
    (5 / 132 : ℝ) + bbg4_g 1 R ≤ (-7 / 264 : ℝ) := by
  obtain rfl : R = (1 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e1_0_0_0_1_b0_lo (R : ℝ) (h1 : (1 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 / 4 : ℝ)) :
    (1 / 2 : ℝ) ≤ bbg4_h 1 R := by
  obtain rfl : R = (1 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_0_0_0_1_b0_hi (R : ℝ) (h1 : (1 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 / 4 : ℝ)) :
    bbg4_h 1 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_0_0_0_1 (R : ℝ) (h1 : (1 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 / 4 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 1 R) ((5 / 132 : ℝ) + bbg4_g 1 R) (bbg4_h 1 R) := by
  rw [bbg4_tp_1_0 (1) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_1]; exact bbg4_e1_0_0_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_1]; exact bbg4_e1_0_0_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_1]; exact bbg4_e1_0_0_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e1_0_0_1_0_b0_val (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    (3 / 176 : ℝ) + bbg4_g 1 R ≤ (-7 / 264 : ℝ) := by
  obtain rfl : R = (1 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e1_0_0_1_0_b0_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    (1 / 2 : ℝ) ≤ bbg4_h 1 R := by
  obtain rfl : R = (1 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_0_0_1_0_b0_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    bbg4_h 1 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_0_0_1_0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 3 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 1 R) ((3 / 176 : ℝ) + bbg4_g 1 R) (bbg4_h 1 R) := by
  rw [bbg4_tp_1_0 (1) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_1]; exact bbg4_e1_0_0_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_1]; exact bbg4_e1_0_0_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_1]; exact bbg4_e1_0_0_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e1_0_1_0_0_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-7 / 264 : ℝ) + bbg4_g 1 R ≤ (-7 / 264 : ℝ) := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e1_0_1_0_0_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ bbg4_h 1 R := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_0_1_0_0_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    bbg4_h 1 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_0_1_0_0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 1 R) ((-7 / 264 : ℝ) + bbg4_g 1 R) (bbg4_h 1 R) := by
  rw [bbg4_tp_1_0 (1) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_1]; exact bbg4_e1_0_1_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_1]; exact bbg4_e1_0_1_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_1]; exact bbg4_e1_0_1_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e1_1_0_0_0_b0_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-139 / 528 : ℝ) + bbg4_g 1 R ≤ (-7 / 264 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e1_1_0_0_0_b0_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ bbg4_h 1 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_1_0_0_0_b0_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    bbg4_h 1 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e1_1_0_0_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 1 R) ((-139 / 528 : ℝ) + bbg4_g 1 R) (bbg4_h 1 R) := by
  rw [bbg4_tp_1_0 (1) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_1]; exact bbg4_e1_1_0_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_1]; exact bbg4_e1_1_0_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_1]; exact bbg4_e1_1_0_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_cnt1 (c : Fin 4 → ℕ) (hc : ∑ t, c t = 1) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * bbg4_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * bbg4_yhi t) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 1 R)
      ((∑ t, (c t : ℝ) * bbg4_B t) + bbg4_g 1 R) (bbg4_h 1 R) := by
  simp only [Fin.sum_univ_four, bbg4_B_0, bbg4_B_1, bbg4_B_2, bbg4_B_3, bbg4_ylo_0, bbg4_ylo_1, bbg4_ylo_2, bbg4_ylo_3, bbg4_yhi_0, bbg4_yhi_1, bbg4_yhi_2, bbg4_yhi_3] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  generalize c 3 = c3 at hc h1 h2 ⊢
  have b0 : c0 ≤ 1 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e1_0_0_0_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e1_0_0_1_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e1_0_1_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e1_1_0_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩

theorem bbg4_e2_0_0_0_2_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (5 / 66 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_0_0_0_2_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_0_0_2_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (1 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_0_0_2 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((5 / 66 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_0_0_0_2_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_0_0_0_2_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_0_0_0_2_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_0_0_1_1_b0_val (R : ℝ) (h1 : (7 / 12 : ℝ) ≤ R) (h2 : R ≤ (7 / 12 : ℝ)) :
    (29 / 528 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (7 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_0_0_1_1_b0_lo (R : ℝ) (h1 : (7 / 12 : ℝ) ≤ R) (h2 : R ≤ (7 / 12 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (7 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_0_1_1_b0_hi (R : ℝ) (h1 : (7 / 12 : ℝ) ≤ R) (h2 : R ≤ (7 / 12 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (7 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_0_1_1 (R : ℝ) (h1 : (7 / 12 : ℝ) ≤ R) (h2 : R ≤ (7 / 12 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((29 / 528 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_0_0_1_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_0_0_1_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_0_0_1_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_0_0_2_0_b0_val (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    (3 / 88 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (2 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_0_0_2_0_b0_lo (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (2 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_0_2_0_b0_hi (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (2 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_0_2_0 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (2 / 3 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((3 / 88 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_0_0_2_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_0_0_2_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_0_0_2_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_0_1_0_1_b0_val (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 88 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (3 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_0_1_0_1_b0_lo (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (3 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_1_0_1_b0_hi (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (3 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_1_0_1 (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((1 / 88 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_0_1_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_0_1_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_0_1_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_0_1_1_0_b0_val (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    (-5 / 528 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_0_1_1_0_b0_lo (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_1_1_0_b0_hi (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_1_1_0 (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((-5 / 528 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_0_1_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_0_1_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_0_1_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_0_2_0_0_b0_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 132 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_0_2_0_0_b0_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_2_0_0_b0_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_0_2_0_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((-7 / 132 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_0_2_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_0_2_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_0_2_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_1_0_0_1_b0_val (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    (-119 / 528 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_1_0_0_1_b0_lo (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_1_0_0_1_b0_hi (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_1_0_0_1 (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((-119 / 528 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_1_0_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_1_0_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_1_0_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_1_0_1_0_b0_val (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (-65 / 264 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_1_0_1_0_b0_lo (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_1_0_1_0_b0_hi (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_1_0_1_0 (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((-65 / 264 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_1_0_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_1_0_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_1_0_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_1_1_0_0_b0_val (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-51 / 176 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_1_1_0_0_b0_lo (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_1_1_0_0_b0_hi (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_1_1_0_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((-51 / 176 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_1_1_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_1_1_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_1_1_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e2_2_0_0_0_b0_val (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-139 / 264 : ℝ) + bbg4_g 2 R ≤ (3 / 176 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e2_2_0_0_0_b0_lo (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ bbg4_h 2 R := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_2_0_0_0_b0_hi (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    bbg4_h 2 R ≤ (1 / 3 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e2_2_0_0_0 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R) ((-139 / 264 : ℝ) + bbg4_g 2 R) (bbg4_h 2 R) := by
  rw [bbg4_tp_2_0 (2) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_2]; exact bbg4_e2_2_0_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_2]; exact bbg4_e2_2_0_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_2]; exact bbg4_e2_2_0_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_cnt2 (c : Fin 4 → ℕ) (hc : ∑ t, c t = 2) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * bbg4_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * bbg4_yhi t) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 2 R)
      ((∑ t, (c t : ℝ) * bbg4_B t) + bbg4_g 2 R) (bbg4_h 2 R) := by
  simp only [Fin.sum_univ_four, bbg4_B_0, bbg4_B_1, bbg4_B_2, bbg4_B_3, bbg4_ylo_0, bbg4_ylo_1, bbg4_ylo_2, bbg4_ylo_3, bbg4_yhi_0, bbg4_yhi_1, bbg4_yhi_2, bbg4_yhi_3] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  generalize c 3 = c3 at hc h1 h2 ⊢
  have b0 : c0 ≤ 2 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 2 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 2 := by omega
      interval_cases c2
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_0_0_0_2 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_0_0_1_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_0_0_2_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_0_1_0_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_0_1_1_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_0_2_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_1_0_0_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_1_0_1_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_1_1_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e2_2_0_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩

theorem bbg4_e3_0_0_0_3_b0_val (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (5 / 44 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (3 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_0_0_3_b0_lo (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (3 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_0_3_b0_hi (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (3 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_0_3 (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((5 / 44 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_0_0_3_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_0_0_3_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_0_0_3_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_0_1_2_b0_val (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    (49 / 528 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_0_1_2_b0_lo (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_1_2_b0_hi (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (5 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_1_2 (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (5 / 6 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((49 / 528 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_0_1_2_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_0_1_2_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_0_1_2_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_0_2_1_b0_val (R : ℝ) (h1 : (11 / 12 : ℝ) ≤ R) (h2 : R ≤ (11 / 12 : ℝ)) :
    (19 / 264 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (11 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_0_2_1_b0_lo (R : ℝ) (h1 : (11 / 12 : ℝ) ≤ R) (h2 : R ≤ (11 / 12 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (11 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_2_1_b0_hi (R : ℝ) (h1 : (11 / 12 : ℝ) ≤ R) (h2 : R ≤ (11 / 12 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (11 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_2_1 (R : ℝ) (h1 : (11 / 12 : ℝ) ≤ R) (h2 : R ≤ (11 / 12 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((19 / 264 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_0_2_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_0_2_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_0_2_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_0_3_0_b0_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (9 / 176 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_0_3_0_b0_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_3_0_b0_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_0_3_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((9 / 176 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_0_3_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_0_3_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_0_3_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_1_0_2_b0_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (13 / 264 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_1_0_2_b0_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_1_0_2_b0_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_1_0_2 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((13 / 264 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_1_0_2_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_1_0_2_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_1_0_2_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_1_1_1_b0_val (R : ℝ) (h1 : (13 / 12 : ℝ) ≤ R) (h2 : R ≤ (13 / 12 : ℝ)) :
    (5 / 176 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (13 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_1_1_1_b0_lo (R : ℝ) (h1 : (13 / 12 : ℝ) ≤ R) (h2 : R ≤ (13 / 12 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (13 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_1_1_1_b0_hi (R : ℝ) (h1 : (13 / 12 : ℝ) ≤ R) (h2 : R ≤ (13 / 12 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (13 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_1_1_1 (R : ℝ) (h1 : (13 / 12 : ℝ) ≤ R) (h2 : R ≤ (13 / 12 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((5 / 176 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_1_1_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_1_1_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_1_1_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_1_2_0_b0_val (R : ℝ) (h1 : (7 / 6 : ℝ) ≤ R) (h2 : R ≤ (7 / 6 : ℝ)) :
    (1 / 132 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (7 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_1_2_0_b0_lo (R : ℝ) (h1 : (7 / 6 : ℝ) ≤ R) (h2 : R ≤ (7 / 6 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (7 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_1_2_0_b0_hi (R : ℝ) (h1 : (7 / 6 : ℝ) ≤ R) (h2 : R ≤ (7 / 6 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (7 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_1_2_0 (R : ℝ) (h1 : (7 / 6 : ℝ) ≤ R) (h2 : R ≤ (7 / 6 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((1 / 132 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_1_2_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_1_2_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_1_2_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_2_0_1_b0_val (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    (-1 / 66 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_2_0_1_b0_lo (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_2_0_1_b0_hi (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_2_0_1 (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-1 / 66 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_2_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_2_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_2_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_2_1_0_b0_val (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (-19 / 528 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_2_1_0_b0_lo (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_2_1_0_b0_hi (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_2_1_0 (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-19 / 528 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_2_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_2_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_2_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_0_3_0_0_b0_val (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-7 / 88 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_0_3_0_0_b0_lo (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_3_0_0_b0_hi (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_0_3_0_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-7 / 88 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_0_3_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_0_3_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_0_3_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_1_0_0_2_b0_val (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-3 / 16 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_1_0_0_2_b0_lo (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_0_0_2_b0_hi (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_0_0_2 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-3 / 16 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_1_0_0_2_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_1_0_0_2_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_1_0_0_2_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_1_0_1_1_b0_val (R : ℝ) (h1 : (19 / 12 : ℝ) ≤ R) (h2 : R ≤ (19 / 12 : ℝ)) :
    (-5 / 24 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (19 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_1_0_1_1_b0_lo (R : ℝ) (h1 : (19 / 12 : ℝ) ≤ R) (h2 : R ≤ (19 / 12 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (19 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_0_1_1_b0_hi (R : ℝ) (h1 : (19 / 12 : ℝ) ≤ R) (h2 : R ≤ (19 / 12 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (19 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_0_1_1 (R : ℝ) (h1 : (19 / 12 : ℝ) ≤ R) (h2 : R ≤ (19 / 12 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-5 / 24 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_1_0_1_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_1_0_1_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_1_0_1_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_1_0_2_0_b0_val (R : ℝ) (h1 : (5 / 3 : ℝ) ≤ R) (h2 : R ≤ (5 / 3 : ℝ)) :
    (-11 / 48 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (5 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_1_0_2_0_b0_lo (R : ℝ) (h1 : (5 / 3 : ℝ) ≤ R) (h2 : R ≤ (5 / 3 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (5 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_0_2_0_b0_hi (R : ℝ) (h1 : (5 / 3 : ℝ) ≤ R) (h2 : R ≤ (5 / 3 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (5 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_0_2_0 (R : ℝ) (h1 : (5 / 3 : ℝ) ≤ R) (h2 : R ≤ (5 / 3 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-11 / 48 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_1_0_2_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_1_0_2_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_1_0_2_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_1_1_0_1_b0_val (R : ℝ) (h1 : (7 / 4 : ℝ) ≤ R) (h2 : R ≤ (7 / 4 : ℝ)) :
    (-133 / 528 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (7 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_1_1_0_1_b0_lo (R : ℝ) (h1 : (7 / 4 : ℝ) ≤ R) (h2 : R ≤ (7 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (7 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_1_0_1_b0_hi (R : ℝ) (h1 : (7 / 4 : ℝ) ≤ R) (h2 : R ≤ (7 / 4 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (7 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_1_0_1 (R : ℝ) (h1 : (7 / 4 : ℝ) ≤ R) (h2 : R ≤ (7 / 4 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-133 / 528 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_1_1_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_1_1_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_1_1_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_1_1_1_0_b0_val (R : ℝ) (h1 : (11 / 6 : ℝ) ≤ R) (h2 : R ≤ (11 / 6 : ℝ)) :
    (-3 / 11 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (11 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_1_1_1_0_b0_lo (R : ℝ) (h1 : (11 / 6 : ℝ) ≤ R) (h2 : R ≤ (11 / 6 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (11 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_1_1_0_b0_hi (R : ℝ) (h1 : (11 / 6 : ℝ) ≤ R) (h2 : R ≤ (11 / 6 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (11 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_1_1_0 (R : ℝ) (h1 : (11 / 6 : ℝ) ≤ R) (h2 : R ≤ (11 / 6 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-3 / 11 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_1_1_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_1_1_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_1_1_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_1_2_0_0_b0_val (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-167 / 528 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_1_2_0_0_b0_lo (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_2_0_0_b0_hi (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_1_2_0_0 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-167 / 528 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_1_2_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_1_2_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_1_2_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_2_0_0_1_b0_val (R : ℝ) (h1 : (9 / 4 : ℝ) ≤ R) (h2 : R ≤ (9 / 4 : ℝ)) :
    (-43 / 88 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (9 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_2_0_0_1_b0_lo (R : ℝ) (h1 : (9 / 4 : ℝ) ≤ R) (h2 : R ≤ (9 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (9 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_2_0_0_1_b0_hi (R : ℝ) (h1 : (9 / 4 : ℝ) ≤ R) (h2 : R ≤ (9 / 4 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (9 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_2_0_0_1 (R : ℝ) (h1 : (9 / 4 : ℝ) ≤ R) (h2 : R ≤ (9 / 4 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-43 / 88 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_2_0_0_1_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_2_0_0_1_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_2_0_0_1_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_2_0_1_0_b0_val (R : ℝ) (h1 : (7 / 3 : ℝ) ≤ R) (h2 : R ≤ (7 / 3 : ℝ)) :
    (-269 / 528 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (7 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_2_0_1_0_b0_lo (R : ℝ) (h1 : (7 / 3 : ℝ) ≤ R) (h2 : R ≤ (7 / 3 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (7 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_2_0_1_0_b0_hi (R : ℝ) (h1 : (7 / 3 : ℝ) ≤ R) (h2 : R ≤ (7 / 3 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (7 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_2_0_1_0 (R : ℝ) (h1 : (7 / 3 : ℝ) ≤ R) (h2 : R ≤ (7 / 3 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-269 / 528 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_2_0_1_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_2_0_1_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_2_0_1_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_2_1_0_0_b0_val (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    (-73 / 132 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (5 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_2_1_0_0_b0_lo (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (5 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_2_1_0_0_b0_hi (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (5 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_2_1_0_0 (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-73 / 132 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_2_1_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_2_1_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_2_1_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_e3_3_0_0_0_b0_val (R : ℝ) (h1 : (3 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (-139 / 176 : ℝ) + bbg4_g 3 R ≤ (5 / 132 : ℝ) := by
  obtain rfl : R = (3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_g]

theorem bbg4_e3_3_0_0_0_b0_lo (R : ℝ) (h1 : (3 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (1 / 4 : ℝ) ≤ bbg4_h 3 R := by
  obtain rfl : R = (3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_3_0_0_0_b0_hi (R : ℝ) (h1 : (3 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    bbg4_h 3 R ≤ (1 / 4 : ℝ) := by
  obtain rfl : R = (3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_h]

theorem bbg4_e3_3_0_0_0 (R : ℝ) (h1 : (3 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R) ((-139 / 176 : ℝ) + bbg4_g 3 R) (bbg4_h 3 R) := by
  rw [bbg4_tp_3_0 (3) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [bbg4_B_3]; exact bbg4_e3_3_0_0_0_b0_val R (by linarith) (by linarith)
  · rw [bbg4_ylo_3]; exact bbg4_e3_3_0_0_0_b0_lo R (by linarith) (by linarith)
  · rw [bbg4_yhi_3]; exact bbg4_e3_3_0_0_0_b0_hi R (by linarith) (by linarith)

theorem bbg4_cnt3 (c : Fin 4 → ℕ) (hc : ∑ t, c t = 3) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * bbg4_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * bbg4_yhi t) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp 3 R)
      ((∑ t, (c t : ℝ) * bbg4_B t) + bbg4_g 3 R) (bbg4_h 3 R) := by
  simp only [Fin.sum_univ_four, bbg4_B_0, bbg4_B_1, bbg4_B_2, bbg4_B_3, bbg4_ylo_0, bbg4_ylo_1, bbg4_ylo_2, bbg4_ylo_3, bbg4_yhi_0, bbg4_yhi_1, bbg4_yhi_2, bbg4_yhi_3] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  generalize c 3 = c3 at hc h1 h2 ⊢
  have b0 : c0 ≤ 3 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 3 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 3 := by omega
      interval_cases c2
      · obtain rfl : c3 = 3 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_0_0_3 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_0_1_2 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_0_2_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_0_3_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 2 := by omega
      interval_cases c2
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_1_0_2 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_1_1_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_1_2_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_2_0_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_2_1_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_0_3_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 2 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 2 := by omega
      interval_cases c2
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_1_0_0_2 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_1_0_1_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_1_0_2_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_1_1_0_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_1_1_1_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_1_2_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_2_0_0_1 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_2_0_1_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_2_1_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        have hob := bbg4_e3_3_0_0_0 R (by linarith) (by linarith)
        exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩

theorem bbg4_hstep : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ (τ : Fin k → Fin 4) (y l : Fin k → ℝ),
    (∀ i, Inv bbg4_B bbg4_ylo bbg4_yhi (τ i) (l i) (y i)) →
    Inv bbg4_B bbg4_ylo bbg4_yhi (bbg4_tp k (∑ i, y i))
      ((∑ i, l i) + bbg4_g k (∑ i, y i)) (bbg4_h k (∑ i, y i)) := by
  intro k hk hok τ y l hch
  interval_cases k
  · exact step_of_counts (bbg4_g 1) (bbg4_h 1) (bbg4_tp 1) bbg4_B bbg4_ylo bbg4_yhi bbg4_cnt1 τ y l hch
  · exact step_of_counts (bbg4_g 2) (bbg4_h 2) (bbg4_tp 2) bbg4_B bbg4_ylo bbg4_yhi bbg4_cnt2 τ y l hch
  · exact step_of_counts (bbg4_g 3) (bbg4_h 3) (bbg4_tp 3) bbg4_B bbg4_ylo bbg4_yhi bbg4_cnt3 τ y l hch

/-- MAIN.  The type table is an inductive invariant on every tree of child count at most 3:
`ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ yhi[type b]`. -/
theorem bbg4 (b : PTree) (hb : b.AllDeg (fun k => k ≤ 3)) :
    Inv bbg4_B bbg4_ylo bbg4_yhi (b.typ bbg4_tp bbg4_h (1 : ℝ))
      (b.ell bbg4_g bbg4_h (-139 / 528 : ℝ) (1 : ℝ)) (b.msg bbg4_h (1 : ℝ)) :=
  typed_induction_core (fun k => k ≤ 3) bbg4_h bbg4_g (1 : ℝ) (-139 / 528 : ℝ) bbg4_tp bbg4_B bbg4_ylo bbg4_yhi
    bbg4_base bbg4_hstep b hb

/-- Uniform corollary: `ell b ≤ max_t B_t = 5/132`. -/
theorem bbg4_uniform (b : PTree) (hb : b.AllDeg (fun k => k ≤ 3)) :
    b.ell bbg4_g bbg4_h (-139 / 528 : ℝ) (1 : ℝ) ≤ (5 / 132 : ℝ) :=
  le_trans (bbg4 b hb).1 (bbg4_Bmax _)

/-- The join (root) function, `gJ(R)` at root child count 4. -/
noncomputable def bbg4_gJ : ℝ → ℝ := fun R => ((-139 / 528 : ℝ) + (1 / 4 : ℝ) * R)

theorem bbg4_j_0_0_0_4 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (5 / 33 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_0_1_3 (R : ℝ) (h1 : (13 / 12 : ℝ) ≤ R) (h2 : R ≤ (13 / 12 : ℝ)) :
    (23 / 176 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (13 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_0_2_2 (R : ℝ) (h1 : (7 / 6 : ℝ) ≤ R) (h2 : R ≤ (7 / 6 : ℝ)) :
    (29 / 264 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (7 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_0_3_1 (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    (47 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_0_4_0 (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (3 / 44 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_1_0_3 (R : ℝ) (h1 : (5 / 4 : ℝ) ≤ R) (h2 : R ≤ (5 / 4 : ℝ)) :
    (23 / 264 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (5 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_1_1_2 (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (4 / 3 : ℝ)) :
    (35 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (4 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_1_2_1 (R : ℝ) (h1 : (17 / 12 : ℝ) ≤ R) (h2 : R ≤ (17 / 12 : ℝ)) :
    (1 / 22 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (17 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_1_3_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (13 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_2_0_2 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 44 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (3 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_2_1_1 (R : ℝ) (h1 : (19 / 12 : ℝ) ≤ R) (h2 : R ≤ (19 / 12 : ℝ)) :
    (1 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (19 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_2_2_0 (R : ℝ) (h1 : (5 / 3 : ℝ) ≤ R) (h2 : R ≤ (5 / 3 : ℝ)) :
    (-5 / 264 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (5 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_3_0_1 (R : ℝ) (h1 : (7 / 4 : ℝ) ≤ R) (h2 : R ≤ (7 / 4 : ℝ)) :
    (-1 / 24 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (7 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_3_1_0 (R : ℝ) (h1 : (11 / 6 : ℝ) ≤ R) (h2 : R ≤ (11 / 6 : ℝ)) :
    (-1 / 16 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (11 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_0_4_0_0 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 66 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_0_0_3 (R : ℝ) (h1 : (7 / 4 : ℝ) ≤ R) (h2 : R ≤ (7 / 4 : ℝ)) :
    (-79 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (7 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_0_1_2 (R : ℝ) (h1 : (11 / 6 : ℝ) ≤ R) (h2 : R ≤ (11 / 6 : ℝ)) :
    (-15 / 88 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (11 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_0_2_1 (R : ℝ) (h1 : (23 / 12 : ℝ) ≤ R) (h2 : R ≤ (23 / 12 : ℝ)) :
    (-101 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (23 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_0_3_0 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 33 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_1_0_2 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-113 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_1_1_1 (R : ℝ) (h1 : (25 / 12 : ℝ) ≤ R) (h2 : R ≤ (25 / 12 : ℝ)) :
    (-31 / 132 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (25 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_1_2_0 (R : ℝ) (h1 : (13 / 6 : ℝ) ≤ R) (h2 : R ≤ (13 / 6 : ℝ)) :
    (-45 / 176 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (13 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_2_0_1 (R : ℝ) (h1 : (9 / 4 : ℝ) ≤ R) (h2 : R ≤ (9 / 4 : ℝ)) :
    (-49 / 176 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (9 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_2_1_0 (R : ℝ) (h1 : (7 / 3 : ℝ) ≤ R) (h2 : R ≤ (7 / 3 : ℝ)) :
    (-79 / 264 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (7 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_1_3_0_0 (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    (-181 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (5 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_2_0_0_2 (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    (-119 / 264 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (5 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_2_0_1_1 (R : ℝ) (h1 : (31 / 12 : ℝ) ≤ R) (h2 : R ≤ (31 / 12 : ℝ)) :
    (-83 / 176 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (31 / 12 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_2_0_2_0 (R : ℝ) (h1 : (8 / 3 : ℝ) ≤ R) (h2 : R ≤ (8 / 3 : ℝ)) :
    (-65 / 132 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (8 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_2_1_0_1 (R : ℝ) (h1 : (11 / 4 : ℝ) ≤ R) (h2 : R ≤ (11 / 4 : ℝ)) :
    (-17 / 33 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (11 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_2_1_1_0 (R : ℝ) (h1 : (17 / 6 : ℝ) ≤ R) (h2 : R ≤ (17 / 6 : ℝ)) :
    (-283 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (17 / 6 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_2_2_0_0 (R : ℝ) (h1 : (3 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (-51 / 88 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_3_0_0_1 (R : ℝ) (h1 : (13 / 4 : ℝ) ≤ R) (h2 : R ≤ (13 / 4 : ℝ)) :
    (-397 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (13 / 4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_3_0_1_0 (R : ℝ) (h1 : (10 / 3 : ℝ) ≤ R) (h2 : R ≤ (10 / 3 : ℝ)) :
    (-17 / 22 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (10 / 3 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_3_1_0_0 (R : ℝ) (h1 : (7 / 2 : ℝ) ≤ R) (h2 : R ≤ (7 / 2 : ℝ)) :
    (-431 / 528 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (7 / 2 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_j_4_0_0_0 (R : ℝ) (h1 : (4 : ℝ) ≤ R) (h2 : R ≤ (4 : ℝ)) :
    (-139 / 132 : ℝ) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  obtain rfl : R = (4 : ℝ) := le_antisymm h2 h1
  norm_num [bbg4_gJ]

theorem bbg4_jcnt (c : Fin 4 → ℕ) (hc : ∑ t, c t = 4) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * bbg4_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * bbg4_yhi t) :
    (∑ t, (c t : ℝ) * bbg4_B t) + bbg4_gJ R ≤ (73 / 528 : ℝ) := by
  simp only [Fin.sum_univ_four, bbg4_B_0, bbg4_B_1, bbg4_B_2, bbg4_B_3, bbg4_ylo_0, bbg4_ylo_1, bbg4_ylo_2, bbg4_ylo_3, bbg4_yhi_0, bbg4_yhi_1, bbg4_yhi_2, bbg4_yhi_3] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  generalize c 3 = c3 at hc h1 h2 ⊢
  have b0 : c0 ≤ 4 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 4 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 4 := by omega
      interval_cases c2
      · obtain rfl : c3 = 4 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_0_0_4 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 3 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_0_1_3 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_0_2_2 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_0_3_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_0_4_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 3 := by omega
      interval_cases c2
      · obtain rfl : c3 = 3 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_1_0_3 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_1_1_2 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_1_2_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_1_3_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 2 := by omega
      interval_cases c2
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_2_0_2 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_2_1_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_2_2_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_3_0_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_3_1_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_0_4_0_0 R (by linarith) (by linarith)]
  · have b1 : c1 ≤ 3 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 3 := by omega
      interval_cases c2
      · obtain rfl : c3 = 3 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_0_0_3 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_0_1_2 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_0_2_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_0_3_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 2 := by omega
      interval_cases c2
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_1_0_2 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_1_1_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_1_2_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_2_0_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_2_1_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_1_3_0_0 R (by linarith) (by linarith)]
  · have b1 : c1 ≤ 2 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 2 := by omega
      interval_cases c2
      · obtain rfl : c3 = 2 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_2_0_0_2 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_2_0_1_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_2_0_2_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_2_1_0_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_2_1_1_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_2_2_0_0 R (by linarith) (by linarith)]
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · obtain rfl : c3 = 1 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_3_0_0_1 R (by linarith) (by linarith)]
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_3_0_1_0 R (by linarith) (by linarith)]
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_3_1_0_0 R (by linarith) (by linarith)]
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · obtain rfl : c3 = 0 := by omega
        push_cast at h1 h2 ⊢
        linarith [bbg4_j_4_0_0_0 R (by linarith) (by linarith)]

/-- JOIN.  A root with 4 children closing any 4 trees: `∑ ell + gJ(∑ msg) ≤ 73/528`. -/
theorem bbg4_join (b : Fin 4 → PTree) (hb : ∀ i, (b i).AllDeg (fun k => k ≤ 3)) :
    (∑ i, (b i).ell bbg4_g bbg4_h (-139 / 528 : ℝ) (1 : ℝ)) +
      bbg4_gJ (∑ i, (b i).msg bbg4_h (1 : ℝ)) ≤ (73 / 528 : ℝ) :=
  join_of_counts bbg4_gJ (73 / 528 : ℝ) bbg4_B bbg4_ylo bbg4_yhi bbg4_jcnt
    (fun i => (b i).typ bbg4_tp bbg4_h (1 : ℝ))
    (fun i => (b i).msg bbg4_h (1 : ℝ))
    (fun i => (b i).ell bbg4_g bbg4_h (-139 / 528 : ℝ) (1 : ℝ))
    (fun i => bbg4 (b i) (hb i))

/-! ## Instance `synth`

Claim: on every finite rooted tree, `ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ yhi[type b]`, for
  h(m, R) = 1/(1+R),  g(m, R) = R/(1+R) + 1/(4*(m+1)) - 3/5  (m = number of children),
  leaf (y, l) = (1, -3/5), and the type table
  0 `leaf`: 0 ≤ k ≤ 0, any R, EXACT (l, y) = (-3/5, 1)
  1 `m1lo`: 1 ≤ k ≤ 1, R < 3/4, B = -17/25, y in [4/7, 1]
  2 `m1hi`: 1 ≤ k ≤ 1, 3/4 ≤ R, B = -23/40, y in [1/2, 4/7]
  3 `m2lo`: 2 ≤ k ≤ 2, R < 1, B = -41/25, y in [1/2, 1]
  4 `m2hi`: 2 ≤ k ≤ 2, 1 ≤ R, B = -21/20, y in [1/3, 1/2]
  5 `band`: 3 ≤ k ≤ 4, any R, B = -29/20, y in [1/5, 1]
  6 `tail_lo`: 5 ≤ k, R < 1, B = -13/5, y in [1/2, 1]
  7 `tail_hi`: 5 ≤ k, 1 ≤ R, B = -13/5, y in [0, 1/2]
Devices: enumeration k = 1..2, tangent band k = 3..4, analytic tail k ≥ 5.
conjecture1_proved = False. -/

noncomputable def synth_h : ℕ → ℝ → ℝ := fun _ R => ((1 : ℝ)) / ((1 : ℝ) + R)
noncomputable def synth_g : ℕ → ℝ → ℝ := fun m R => ((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (m : ℝ) + (8 : ℝ) * (m : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (m : ℝ) + (20 : ℝ) * (m : ℝ) * R)
noncomputable def synth_B : Fin 8 → ℝ := ![(-3 / 5 : ℝ), (-17 / 25 : ℝ), (-23 / 40 : ℝ), (-41 / 25 : ℝ), (-21 / 20 : ℝ), (-29 / 20 : ℝ), (-13 / 5 : ℝ), (-13 / 5 : ℝ)]
theorem synth_B_0 : synth_B 0 = (-3 / 5 : ℝ) := rfl
theorem synth_B_1 : synth_B 1 = (-17 / 25 : ℝ) := rfl
theorem synth_B_2 : synth_B 2 = (-23 / 40 : ℝ) := rfl
theorem synth_B_3 : synth_B 3 = (-41 / 25 : ℝ) := rfl
theorem synth_B_4 : synth_B 4 = (-21 / 20 : ℝ) := rfl
theorem synth_B_5 : synth_B 5 = (-29 / 20 : ℝ) := rfl
theorem synth_B_6 : synth_B 6 = (-13 / 5 : ℝ) := rfl
theorem synth_B_7 : synth_B 7 = (-13 / 5 : ℝ) := rfl
noncomputable def synth_ylo : Fin 8 → ℝ := ![(1 : ℝ), (4 / 7 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 3 : ℝ), (1 / 5 : ℝ), (1 / 2 : ℝ), (0 : ℝ)]
theorem synth_ylo_0 : synth_ylo 0 = (1 : ℝ) := rfl
theorem synth_ylo_1 : synth_ylo 1 = (4 / 7 : ℝ) := rfl
theorem synth_ylo_2 : synth_ylo 2 = (1 / 2 : ℝ) := rfl
theorem synth_ylo_3 : synth_ylo 3 = (1 / 2 : ℝ) := rfl
theorem synth_ylo_4 : synth_ylo 4 = (1 / 3 : ℝ) := rfl
theorem synth_ylo_5 : synth_ylo 5 = (1 / 5 : ℝ) := rfl
theorem synth_ylo_6 : synth_ylo 6 = (1 / 2 : ℝ) := rfl
theorem synth_ylo_7 : synth_ylo 7 = (0 : ℝ) := rfl
noncomputable def synth_yhi : Fin 8 → ℝ := ![(1 : ℝ), (1 : ℝ), (4 / 7 : ℝ), (1 : ℝ), (1 / 2 : ℝ), (1 : ℝ), (1 : ℝ), (1 / 2 : ℝ)]
theorem synth_yhi_0 : synth_yhi 0 = (1 : ℝ) := rfl
theorem synth_yhi_1 : synth_yhi 1 = (1 : ℝ) := rfl
theorem synth_yhi_2 : synth_yhi 2 = (4 / 7 : ℝ) := rfl
theorem synth_yhi_3 : synth_yhi 3 = (1 : ℝ) := rfl
theorem synth_yhi_4 : synth_yhi 4 = (1 / 2 : ℝ) := rfl
theorem synth_yhi_5 : synth_yhi 5 = (1 : ℝ) := rfl
theorem synth_yhi_6 : synth_yhi 6 = (1 : ℝ) := rfl
theorem synth_yhi_7 : synth_yhi 7 = (1 / 2 : ℝ) := rfl

/-- The type map: degree groups, then bins of the message sum. -/
noncomputable def synth_tp (k : ℕ) (R : ℝ) : Fin 8 :=
  if k ≤ 0 then 0 else if k ≤ 1 then (if R < (3 / 4 : ℝ) then 1 else 2) else if k ≤ 2 then (if R < (1 : ℝ) then 3 else 4) else if k ≤ 4 then 5 else (if R < (1 : ℝ) then 6 else 7)

theorem synth_tp_0_0 (k : ℕ) (hk2 : k ≤ 0) (R : ℝ) :
    synth_tp k R = 0 := by
  unfold synth_tp
  rw [if_pos (show k ≤ 0 by omega)]

theorem synth_tp_1_0 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 1) (R : ℝ) (hr2 : R < (3 / 4 : ℝ)) :
    synth_tp k R = 1 := by
  unfold synth_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_pos (show k ≤ 1 by omega), if_pos hr2]

theorem synth_tp_1_1 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 1) (R : ℝ) (hr1 : (3 / 4 : ℝ) ≤ R) :
    synth_tp k R = 2 := by
  unfold synth_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_pos (show k ≤ 1 by omega), if_neg (show ¬ (R < (3 / 4 : ℝ)) from not_lt.mpr (by linarith))]

theorem synth_tp_2_0 (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k ≤ 2) (R : ℝ) (hr2 : R < (1 : ℝ)) :
    synth_tp k R = 3 := by
  unfold synth_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega), if_pos (show k ≤ 2 by omega), if_pos hr2]

theorem synth_tp_2_1 (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k ≤ 2) (R : ℝ) (hr1 : (1 : ℝ) ≤ R) :
    synth_tp k R = 4 := by
  unfold synth_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega), if_pos (show k ≤ 2 by omega), if_neg (show ¬ (R < (1 : ℝ)) from not_lt.mpr (by linarith))]

theorem synth_tp_3_0 (k : ℕ) (hk1 : 3 ≤ k) (hk2 : k ≤ 4) (R : ℝ) :
    synth_tp k R = 5 := by
  unfold synth_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega), if_neg (show ¬ (k ≤ 2) by omega), if_pos (show k ≤ 4 by omega)]

theorem synth_tp_4_0 (k : ℕ) (hk1 : 5 ≤ k) (R : ℝ) (hr2 : R < (1 : ℝ)) :
    synth_tp k R = 6 := by
  unfold synth_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega), if_neg (show ¬ (k ≤ 2) by omega), if_neg (show ¬ (k ≤ 4) by omega), if_pos hr2]

theorem synth_tp_4_1 (k : ℕ) (hk1 : 5 ≤ k) (R : ℝ) (hr1 : (1 : ℝ) ≤ R) :
    synth_tp k R = 7 := by
  unfold synth_tp
  rw [if_neg (show ¬ (k ≤ 0) by omega), if_neg (show ¬ (k ≤ 1) by omega), if_neg (show ¬ (k ≤ 2) by omega), if_neg (show ¬ (k ≤ 4) by omega), if_neg (show ¬ (R < (1 : ℝ)) from not_lt.mpr (by linarith))]

theorem synth_base : Inv synth_B synth_ylo synth_yhi (synth_tp 0 0) (-3 / 5 : ℝ) (1 : ℝ) := by
  rw [synth_tp_0_0 (0) (by omega) (0)]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [synth_B_0, synth_ylo_0, synth_yhi_0]

theorem synth_ymin : ∀ t, (0 : ℝ) ≤ synth_ylo t := by
  intro t; fin_cases t <;> norm_num [synth_ylo]

theorem synth_ymax : ∀ t, synth_yhi t ≤ (1 : ℝ) := by
  intro t; fin_cases t <;> norm_num [synth_yhi]

theorem synth_Bmax : ∀ t, synth_B t ≤ (-23 / 40 : ℝ) := by
  intro t; fin_cases t <;> norm_num [synth_B]

theorem synth_e1_0_0_0_0_0_0_0_1_b0_val (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-13 / 5 : ℝ) + synth_g 1 R ≤ (-17 / 25 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((479 / 5 : ℝ) + (279 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-17 / 25 : ℝ)) - ((-13 / 5 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((479 / 5 : ℝ) + (279 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_0_1_b0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (4 / 7 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((4 / 7 : ℝ)) = ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_0_1_b0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    synth_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_0_1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-13 / 5 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · rw [synth_tp_1_0 (1) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_1]; exact synth_e1_0_0_0_0_0_0_0_1_b0_val R h1 h2
    · rw [synth_ylo_1]; exact synth_e1_0_0_0_0_0_0_0_1_b0_lo R h1 h2
    · rw [synth_yhi_1]; exact synth_e1_0_0_0_0_0_0_0_1_b0_hi R h1 h2
  exfalso; linarith

theorem synth_e1_0_0_0_0_0_0_1_0_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (-13 / 5 : ℝ) + synth_g 1 R ≤ (-17 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((479 / 5 : ℝ) + (279 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-17 / 25 : ℝ)) - ((-13 / 5 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((479 / 5 : ℝ) + (279 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_1_0_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (4 / 7 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((4 / 7 : ℝ)) = ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_1_0_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    synth_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_1_0_b1_val (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-13 / 5 : ℝ) + synth_g 1 R ≤ (-23 / 40 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((100 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-23 / 40 : ℝ)) - ((-13 / 5 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((100 : ℝ) + (60 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_1_0_b1_lo (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_1_0_b1_hi (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 1 R ≤ (4 / 7 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((4 / 7 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_0_1_0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-13 / 5 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · rw [synth_tp_1_0 (1) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_1]; exact synth_e1_0_0_0_0_0_0_1_0_b0_val R h1 hb0.le
    · rw [synth_ylo_1]; exact synth_e1_0_0_0_0_0_0_1_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_1]; exact synth_e1_0_0_0_0_0_0_1_0_b0_hi R h1 hb0.le
  rw [synth_tp_1_1 (1) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_2]; exact synth_e1_0_0_0_0_0_0_1_0_b1_val R hb0 h2
  · rw [synth_ylo_2]; exact synth_e1_0_0_0_0_0_0_1_0_b1_lo R hb0 h2
  · rw [synth_yhi_2]; exact synth_e1_0_0_0_0_0_0_1_0_b1_hi R hb0 h2

theorem synth_e1_0_0_0_0_0_1_0_0_b0_val (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (-29 / 20 : ℝ) + synth_g 1 R ≤ (-17 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((249 / 5 : ℝ) + (49 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-17 / 25 : ℝ)) - ((-29 / 20 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((249 / 5 : ℝ) + (49 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_1_0_0_b0_lo (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (4 / 7 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (1 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((4 / 7 : ℝ)) = ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_1_0_0_b0_hi (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    synth_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_1_0_0_b1_val (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-29 / 20 : ℝ) + synth_g 1 R ≤ (-23 / 40 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((54 : ℝ) + (14 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-23 / 40 : ℝ)) - ((-29 / 20 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((54 : ℝ) + (14 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_1_0_0_b1_lo (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_1_0_0_b1_hi (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 1 R ≤ (4 / 7 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((4 / 7 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_0_1_0_0 (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-29 / 20 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · rw [synth_tp_1_0 (1) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_1]; exact synth_e1_0_0_0_0_0_1_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_1]; exact synth_e1_0_0_0_0_0_1_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_1]; exact synth_e1_0_0_0_0_0_1_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_1_1 (1) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_2]; exact synth_e1_0_0_0_0_0_1_0_0_b1_val R hb0 h2
  · rw [synth_ylo_2]; exact synth_e1_0_0_0_0_0_1_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_2]; exact synth_e1_0_0_0_0_0_1_0_0_b1_hi R hb0 h2

theorem synth_e1_0_0_0_0_1_0_0_0_b0_val (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-21 / 20 : ℝ) + synth_g 1 R ≤ (-17 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((169 / 5 : ℝ) + (-31 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-17 / 25 : ℝ)) - ((-21 / 20 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((169 / 5 : ℝ) + (-31 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_1_0_0_0_b0_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (4 / 7 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((4 / 7 : ℝ)) = ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_1_0_0_0_b0_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    synth_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_0_1_0_0_0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-21 / 20 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · rw [synth_tp_1_0 (1) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_1]; exact synth_e1_0_0_0_0_1_0_0_0_b0_val R h1 h2
    · rw [synth_ylo_1]; exact synth_e1_0_0_0_0_1_0_0_0_b0_lo R h1 h2
    · rw [synth_yhi_1]; exact synth_e1_0_0_0_0_1_0_0_0_b0_hi R h1 h2
  exfalso; linarith

theorem synth_e1_0_0_0_1_0_0_0_0_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (-41 / 25 : ℝ) + synth_g 1 R ≤ (-17 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((287 / 5 : ℝ) + (87 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-17 / 25 : ℝ)) - ((-41 / 25 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((287 / 5 : ℝ) + (87 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_1_0_0_0_0_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (4 / 7 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((4 / 7 : ℝ)) = ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_1_0_0_0_0_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    synth_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_1_0_0_0_0_b1_val (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-41 / 25 : ℝ) + synth_g 1 R ≤ (-23 / 40 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((308 / 5 : ℝ) + (108 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-23 / 40 : ℝ)) - ((-41 / 25 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((308 / 5 : ℝ) + (108 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_1_0_0_0_0_b1_lo (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_1_0_0_0_0_b1_hi (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 1 R ≤ (4 / 7 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((4 / 7 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_0_1_0_0_0_0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-41 / 25 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · rw [synth_tp_1_0 (1) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_1]; exact synth_e1_0_0_0_1_0_0_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_1]; exact synth_e1_0_0_0_1_0_0_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_1]; exact synth_e1_0_0_0_1_0_0_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_1_1 (1) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_2]; exact synth_e1_0_0_0_1_0_0_0_0_b1_val R hb0 h2
  · rw [synth_ylo_2]; exact synth_e1_0_0_0_1_0_0_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_2]; exact synth_e1_0_0_0_1_0_0_0_0_b1_hi R hb0 h2

theorem synth_e1_0_0_1_0_0_0_0_0_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (4 / 7 : ℝ)) :
    (-23 / 40 : ℝ) + synth_g 1 R ≤ (-17 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (4 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((74 / 5 : ℝ) + (-126 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-17 / 25 : ℝ)) - ((-23 / 40 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((74 / 5 : ℝ) + (-126 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_1_0_0_0_0_0_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (4 / 7 : ℝ)) :
    (4 / 7 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (4 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((4 / 7 : ℝ)) = ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_1_0_0_0_0_0_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (4 / 7 : ℝ)) :
    synth_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (4 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_0_1_0_0_0_0_0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (4 / 7 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-23 / 40 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · rw [synth_tp_1_0 (1) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_1]; exact synth_e1_0_0_1_0_0_0_0_0_b0_val R h1 h2
    · rw [synth_ylo_1]; exact synth_e1_0_0_1_0_0_0_0_0_b0_lo R h1 h2
    · rw [synth_yhi_1]; exact synth_e1_0_0_1_0_0_0_0_0_b0_hi R h1 h2
  exfalso; linarith

theorem synth_e1_0_1_0_0_0_0_0_0_b0_val (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (-17 / 25 : ℝ) + synth_g 1 R ≤ (-17 / 25 : ℝ) := by
  have hs : 0 ≤ R - (4 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((19 : ℝ) + (-21 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-17 / 25 : ℝ)) - ((-17 / 25 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((19 : ℝ) + (-21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_1_0_0_0_0_0_0_b0_lo (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (4 / 7 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (4 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((4 / 7 : ℝ)) = ((3 / 7 : ℝ) + (-4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_1_0_0_0_0_0_0_b0_hi (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    synth_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (4 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_1_0_0_0_0_0_0_b1_val (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-17 / 25 : ℝ) + synth_g 1 R ≤ (-23 / 40 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((40 : ℝ) + (40 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 1 R = (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((116 / 5 : ℝ) + (-84 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-23 / 40 : ℝ)) - ((-17 / 25 : ℝ) + (((-19 : ℝ) + (21 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R))) = ((116 / 5 : ℝ) + (-84 / 5 : ℝ) * R) / ((40 : ℝ) + (40 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_1_0_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 1 R := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_1_0_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (3 / 4 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 1 R ≤ (4 / 7 : ℝ) := by
  have hs : 0 ≤ R - (3 / 4 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((4 / 7 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-3 / 7 : ℝ) + (4 / 7 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e1_0_1_0_0_0_0_0_0 (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-17 / 25 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · rw [synth_tp_1_0 (1) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_1]; exact synth_e1_0_1_0_0_0_0_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_1]; exact synth_e1_0_1_0_0_0_0_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_1]; exact synth_e1_0_1_0_0_0_0_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_1_1 (1) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_2]; exact synth_e1_0_1_0_0_0_0_0_0_b1_val R hb0 h2
  · rw [synth_ylo_2]; exact synth_e1_0_1_0_0_0_0_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_2]; exact synth_e1_0_1_0_0_0_0_0_0_b1_hi R hb0 h2

theorem synth_e1_1_0_0_0_0_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-3 / 5 : ℝ) + synth_g 1 R ≤ (-23 / 40 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_g]

theorem synth_e1_1_0_0_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 1 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e1_1_0_0_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 1 R ≤ (4 / 7 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e1_1_0_0_0_0_0_0_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R) ((-3 / 5 : ℝ) + synth_g 1 R) (synth_h 1 R) := by
  rcases lt_or_ge (R) (3 / 4 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_1_1 (1) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_2]; exact synth_e1_1_0_0_0_0_0_0_0_b1_val R (by linarith) (by linarith)
  · rw [synth_ylo_2]; exact synth_e1_1_0_0_0_0_0_0_0_b1_lo R (by linarith) (by linarith)
  · rw [synth_yhi_2]; exact synth_e1_1_0_0_0_0_0_0_0_b1_hi R (by linarith) (by linarith)

theorem synth_cnt1 (c : Fin 8 → ℕ) (hc : ∑ t, c t = 1) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * synth_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * synth_yhi t) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 1 R)
      ((∑ t, (c t : ℝ) * synth_B t) + synth_g 1 R) (synth_h 1 R) := by
  simp only [Fin.sum_univ_eight, synth_B_0, synth_B_1, synth_B_2, synth_B_3, synth_B_4, synth_B_5, synth_B_6, synth_B_7, synth_ylo_0, synth_ylo_1, synth_ylo_2, synth_ylo_3, synth_ylo_4, synth_ylo_5, synth_ylo_6, synth_ylo_7, synth_yhi_0, synth_yhi_1, synth_yhi_2, synth_yhi_3, synth_yhi_4, synth_yhi_5, synth_yhi_6, synth_yhi_7] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  generalize c 3 = c3 at hc h1 h2 ⊢
  generalize c 4 = c4 at hc h1 h2 ⊢
  generalize c 5 = c5 at hc h1 h2 ⊢
  generalize c 6 = c6 at hc h1 h2 ⊢
  generalize c 7 = c7 at hc h1 h2 ⊢
  have b0 : c0 ≤ 1 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 1 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 1 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 1 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 1 := by omega
              interval_cases c6
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_0_0_0_0_0_0_0_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_0_0_0_0_0_0_1_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_0_0_0_0_0_1_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_0_0_0_0_1_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_0_0_0_1_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_0_0_1_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_0_1_0_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e1_1_0_0_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩

theorem synth_e2_0_0_0_0_0_0_0_2_b0_val (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-26 / 5 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((1223 / 5 : ℝ) + (923 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-26 / 5 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((1223 / 5 : ℝ) + (923 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_0_2_b0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_0_2_b0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_0_2_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-26 / 5 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_g]

theorem synth_e2_0_0_0_0_0_0_0_2_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_0_0_0_0_0_0_0_2_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_0_0_0_0_0_0_0_2 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-26 / 5 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_0_0_0_2_b0_val R h1 h2
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_0_0_0_2_b0_lo R h1 h2
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_0_0_0_2_b0_hi R h1 h2
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_0_0_0_2_b1_val R (by linarith) (by linarith)
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_0_0_0_2_b1_lo R (by linarith) (by linarith)
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_0_0_0_2_b1_hi R (by linarith) (by linarith)

theorem synth_e2_0_0_0_0_0_0_1_1_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-26 / 5 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((1223 / 5 : ℝ) + (923 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-26 / 5 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((1223 / 5 : ℝ) + (923 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_1_1_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_1_1_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_1_1_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-26 / 5 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((280 : ℝ) + (220 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-26 / 5 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((280 : ℝ) + (220 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_1_1_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_1_1_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_1_1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-26 / 5 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_0_0_1_1_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_0_0_1_1_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_0_0_1_1_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_0_0_1_1_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_0_0_1_1_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_0_0_1_1_b1_hi R hb0 h2

theorem synth_e2_0_0_0_0_0_0_2_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-26 / 5 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((280 : ℝ) + (220 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-26 / 5 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((280 : ℝ) + (220 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_2_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_2_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_0_2_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-26 / 5 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_0_0_2_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_0_0_2_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_0_0_2_0_b1_hi R h1 h2

theorem synth_e2_0_0_0_0_0_1_0_1_b0_val (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-81 / 20 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((878 / 5 : ℝ) + (578 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-81 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((878 / 5 : ℝ) + (578 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_0_1_b0_lo (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_0_1_b0_hi (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_0_1_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-81 / 20 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((211 : ℝ) + (151 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-81 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((211 : ℝ) + (151 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_0_1_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_0_1_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_0_1 (R : ℝ) (h1 : (1 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-81 / 20 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_0_1_0_1_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_0_1_0_1_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_0_1_0_1_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_0_1_0_1_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_0_1_0_1_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_0_1_0_1_b1_hi R hb0 h2

theorem synth_e2_0_0_0_0_0_1_1_0_b0_val (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-81 / 20 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((878 / 5 : ℝ) + (578 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-81 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((878 / 5 : ℝ) + (578 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_1_0_b0_lo (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_1_0_b0_hi (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_1_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-81 / 20 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((211 : ℝ) + (151 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-81 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((211 : ℝ) + (151 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_1_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_1_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_1_1_0 (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-81 / 20 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_0_1_1_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_0_1_1_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_0_1_1_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_0_1_1_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_0_1_1_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_0_1_1_0_b1_hi R hb0 h2

theorem synth_e2_0_0_0_0_0_2_0_0_b0_val (R : ℝ) (h1 : (2 / 5 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-29 / 10 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (2 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((533 / 5 : ℝ) + (233 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-29 / 10 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((533 / 5 : ℝ) + (233 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_2_0_0_b0_lo (R : ℝ) (h1 : (2 / 5 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (2 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_2_0_0_b0_hi (R : ℝ) (h1 : (2 / 5 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (2 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_2_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-29 / 10 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((142 : ℝ) + (82 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-29 / 10 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((142 : ℝ) + (82 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_2_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_2_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_0_2_0_0 (R : ℝ) (h1 : (2 / 5 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-29 / 10 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_0_2_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_0_2_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_0_2_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_0_2_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_0_2_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_0_2_0_0_b1_hi R hb0 h2

theorem synth_e2_0_0_0_0_1_0_0_1_b0_val (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-73 / 20 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((758 / 5 : ℝ) + (458 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-73 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((758 / 5 : ℝ) + (458 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_0_1_b0_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_0_1_b0_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_0_1_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-73 / 20 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_g]

theorem synth_e2_0_0_0_0_1_0_0_1_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_0_0_0_0_1_0_0_1_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_0_0_0_0_1_0_0_1 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-73 / 20 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_1_0_0_1_b0_val R h1 h2
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_1_0_0_1_b0_lo R h1 h2
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_1_0_0_1_b0_hi R h1 h2
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_1_0_0_1_b1_val R (by linarith) (by linarith)
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_1_0_0_1_b1_lo R (by linarith) (by linarith)
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_1_0_0_1_b1_hi R (by linarith) (by linarith)

theorem synth_e2_0_0_0_0_1_0_1_0_b0_val (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-73 / 20 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((758 / 5 : ℝ) + (458 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-73 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((758 / 5 : ℝ) + (458 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_1_0_b0_lo (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_1_0_b0_hi (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_1_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-73 / 20 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((187 : ℝ) + (127 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-73 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((187 : ℝ) + (127 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_1_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_1_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_0_1_0 (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-73 / 20 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_1_0_1_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_1_0_1_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_1_0_1_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_1_0_1_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_1_0_1_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_1_0_1_0_b1_hi R hb0 h2

theorem synth_e2_0_0_0_0_1_1_0_0_b0_val (R : ℝ) (h1 : (8 / 15 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-5 / 2 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (8 / 15 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((413 / 5 : ℝ) + (113 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-5 / 2 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((413 / 5 : ℝ) + (113 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_1_0_0_b0_lo (R : ℝ) (h1 : (8 / 15 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (8 / 15 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_1_0_0_b0_hi (R : ℝ) (h1 : (8 / 15 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (8 / 15 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_1_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-5 / 2 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((118 : ℝ) + (58 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-5 / 2 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((118 : ℝ) + (58 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_1_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_1_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_1_1_0_0 (R : ℝ) (h1 : (8 / 15 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-5 / 2 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_1_1_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_1_1_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_1_1_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_1_1_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_1_1_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_1_1_0_0_b1_hi R hb0 h2

theorem synth_e2_0_0_0_0_2_0_0_0_b0_val (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-21 / 10 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((293 / 5 : ℝ) + (-7 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-21 / 10 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((293 / 5 : ℝ) + (-7 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_2_0_0_0_b0_lo (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_2_0_0_0_b0_hi (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_0_2_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-21 / 10 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_g]

theorem synth_e2_0_0_0_0_2_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_0_0_0_0_2_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (1 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_0_0_0_0_2_0_0_0 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-21 / 10 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_0_2_0_0_0_b0_val R h1 h2
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_0_2_0_0_0_b0_lo R h1 h2
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_0_2_0_0_0_b0_hi R h1 h2
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_0_2_0_0_0_b1_val R (by linarith) (by linarith)
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_0_2_0_0_0_b1_lo R (by linarith) (by linarith)
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_0_2_0_0_0_b1_hi R (by linarith) (by linarith)

theorem synth_e2_0_0_0_1_0_0_0_1_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-106 / 25 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((187 : ℝ) + (127 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-106 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((187 : ℝ) + (127 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_0_1_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_0_1_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_0_1_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-106 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((1112 / 5 : ℝ) + (812 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-106 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((1112 / 5 : ℝ) + (812 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_0_1_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_0_1_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_0_1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-106 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_1_0_0_0_1_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_1_0_0_0_1_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_1_0_0_0_1_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_1_0_0_0_1_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_1_0_0_0_1_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_1_0_0_0_1_b1_hi R hb0 h2

theorem synth_e2_0_0_0_1_0_0_1_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-106 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((1112 / 5 : ℝ) + (812 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-106 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((1112 / 5 : ℝ) + (812 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_1_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_1_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_0_1_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-106 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_1_0_0_1_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_1_0_0_1_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_1_0_0_1_0_b1_hi R h1 h2

theorem synth_e2_0_0_0_1_0_1_0_0_b0_val (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-309 / 100 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((118 : ℝ) + (58 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-309 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((118 : ℝ) + (58 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_1_0_0_b0_lo (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_1_0_0_b0_hi (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_1_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-309 / 100 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((767 / 5 : ℝ) + (467 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-309 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((767 / 5 : ℝ) + (467 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_1_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_1_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_0_1_0_0 (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-309 / 100 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_1_0_1_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_1_0_1_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_1_0_1_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_1_0_1_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_1_0_1_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_1_0_1_0_0_b1_hi R hb0 h2

theorem synth_e2_0_0_0_1_1_0_0_0_b0_val (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-269 / 100 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((94 : ℝ) + (34 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-269 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((94 : ℝ) + (34 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_1_0_0_0_b0_lo (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_1_0_0_0_b0_hi (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_1_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-269 / 100 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((647 / 5 : ℝ) + (347 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-269 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((647 / 5 : ℝ) + (347 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_1_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_1_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_1_1_0_0_0 (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-269 / 100 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_0_1_1_0_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_0_1_1_0_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_0_1_1_0_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_1_1_0_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_1_1_0_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_1_1_0_0_0_b1_hi R hb0 h2

theorem synth_e2_0_0_0_2_0_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-82 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((824 / 5 : ℝ) + (524 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-82 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((824 / 5 : ℝ) + (524 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_2_0_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_2_0_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_0_2_0_0_0_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-82 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_0_2_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_0_2_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_0_2_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_0_0_1_0_0_0_0_1_b0_val (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-127 / 40 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((1231 / 10 : ℝ) + (631 / 10 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-127 / 40 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((1231 / 10 : ℝ) + (631 / 10 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_0_1_b0_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_0_1_b0_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_0_1_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    (-127 / 40 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (15 / 14 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((317 / 2 : ℝ) + (197 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-127 / 40 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((317 / 2 : ℝ) + (197 / 2 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_0_1_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (15 / 14 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_0_1_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (15 / 14 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_0_1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-127 / 40 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_1_0_0_0_0_1_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_1_0_0_0_0_1_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_1_0_0_0_0_1_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_1_0_0_0_0_1_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_1_0_0_0_0_1_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_1_0_0_0_0_1_b1_hi R hb0 h2

theorem synth_e2_0_0_1_0_0_0_1_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (-127 / 40 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((317 / 2 : ℝ) + (197 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-127 / 40 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((317 / 2 : ℝ) + (197 / 2 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_1_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_1_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_0_1_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-127 / 40 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_1_0_0_0_1_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_1_0_0_0_1_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_1_0_0_0_1_0_b1_hi R h1 h2

theorem synth_e2_0_0_1_0_0_1_0_0_b0_val (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-81 / 40 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((541 / 10 : ℝ) + (-59 / 10 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-81 / 40 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((541 / 10 : ℝ) + (-59 / 10 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_1_0_0_b0_lo (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_1_0_0_b0_hi (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (7 / 10 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_1_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (-81 / 40 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((179 / 2 : ℝ) + (59 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-81 / 40 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((179 / 2 : ℝ) + (59 / 2 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_1_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_1_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_0_1_0_0 (R : ℝ) (h1 : (7 / 10 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-81 / 40 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_1_0_0_1_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_1_0_0_1_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_1_0_0_1_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_1_0_0_1_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_1_0_0_1_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_1_0_0_1_0_0_b1_hi R hb0 h2

theorem synth_e2_0_0_1_0_1_0_0_0_b0_val (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-13 / 8 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((301 / 10 : ℝ) + (-299 / 10 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-13 / 8 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((301 / 10 : ℝ) + (-299 / 10 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_1_0_0_0_b0_lo (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_1_0_0_0_b0_hi (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (5 / 6 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_1_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    (-13 / 8 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (15 / 14 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((131 / 2 : ℝ) + (11 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-13 / 8 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((131 / 2 : ℝ) + (11 / 2 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_1_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (15 / 14 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_1_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (15 / 14 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_0_1_0_0_0 (R : ℝ) (h1 : (5 / 6 : ℝ) ≤ R) (h2 : R ≤ (15 / 14 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-13 / 8 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_0_1_0_1_0_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_0_1_0_1_0_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_0_1_0_1_0_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_1_0_1_0_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_1_0_1_0_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_1_0_1_0_0_0_b1_hi R hb0 h2

theorem synth_e2_0_0_1_1_0_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (-443 / 200 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((1009 / 10 : ℝ) + (409 / 10 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-443 / 200 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((1009 / 10 : ℝ) + (409 / 10 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_1_0_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_1_0_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_1_1_0_0_0_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-443 / 200 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_1_1_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_1_1_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_1_1_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_0_0_2_0_0_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (8 / 7 : ℝ)) :
    (-23 / 20 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (8 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((37 : ℝ) + (-23 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-23 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((37 : ℝ) + (-23 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_2_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (8 / 7 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (8 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_2_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (8 / 7 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (8 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_0_2_0_0_0_0_0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (8 / 7 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-23 / 20 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_0_2_0_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_0_2_0_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_0_2_0_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_0_1_0_0_0_0_0_1_b0_val (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-82 / 25 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (4 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((647 / 5 : ℝ) + (347 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-82 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((647 / 5 : ℝ) + (347 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_0_1_b0_lo (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (4 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_0_1_b0_hi (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (4 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_0_1_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-82 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((824 / 5 : ℝ) + (524 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-82 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((824 / 5 : ℝ) + (524 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_0_1_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_0_1_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_0_1 (R : ℝ) (h1 : (4 / 7 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-82 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_1_0_0_0_0_0_1_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_1_0_0_0_0_0_1_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_1_0_0_0_0_0_1_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_1_0_0_0_0_0_1_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_1_0_0_0_0_0_1_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_1_0_0_0_0_0_1_b1_hi R hb0 h2

theorem synth_e2_0_1_0_0_0_0_1_0_b1_val (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-82 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((824 / 5 : ℝ) + (524 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-82 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((824 / 5 : ℝ) + (524 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_1_0_b1_lo (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_1_0_b1_hi (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_0_1_0 (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-82 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_1_0_0_0_0_1_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_1_0_0_0_0_1_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_1_0_0_0_0_1_0_b1_hi R h1 h2

theorem synth_e2_0_1_0_0_0_1_0_0_b0_val (R : ℝ) (h1 : (27 / 35 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-213 / 100 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (27 / 35 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((302 / 5 : ℝ) + (2 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-213 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((302 / 5 : ℝ) + (2 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_1_0_0_b0_lo (R : ℝ) (h1 : (27 / 35 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (27 / 35 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_1_0_0_b0_hi (R : ℝ) (h1 : (27 / 35 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (27 / 35 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_1_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-213 / 100 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((479 / 5 : ℝ) + (179 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-213 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((479 / 5 : ℝ) + (179 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_1_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_1_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_0_1_0_0 (R : ℝ) (h1 : (27 / 35 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-213 / 100 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_1_0_0_0_1_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_1_0_0_0_1_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_1_0_0_0_1_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_1_0_0_0_1_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_1_0_0_0_1_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_1_0_0_0_1_0_0_b1_hi R hb0 h2

theorem synth_e2_0_1_0_0_1_0_0_0_b0_val (R : ℝ) (h1 : (19 / 21 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-173 / 100 : ℝ) + synth_g 2 R ≤ (-41 / 25 : ℝ) := by
  have hs : 0 ≤ R - (19 / 21 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((182 / 5 : ℝ) + (-118 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-41 / 25 : ℝ)) - ((-173 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((182 / 5 : ℝ) + (-118 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_1_0_0_0_b0_lo (R : ℝ) (h1 : (19 / 21 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (19 / 21 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_1_0_0_0_b0_hi (R : ℝ) (h1 : (19 / 21 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (19 / 21 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_1_0_0_0_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-173 / 100 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((359 / 5 : ℝ) + (59 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-173 / 100 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((359 / 5 : ℝ) + (59 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_1_0_0_0_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_1_0_0_0_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_0_1_0_0_0 (R : ℝ) (h1 : (19 / 21 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-173 / 100 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_2_0 (2) (by omega) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_3]; exact synth_e2_0_1_0_0_1_0_0_0_b0_val R h1 hb0.le
    · rw [synth_ylo_3]; exact synth_e2_0_1_0_0_1_0_0_0_b0_lo R h1 hb0.le
    · rw [synth_yhi_3]; exact synth_e2_0_1_0_0_1_0_0_0_b0_hi R h1 hb0.le
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_1_0_0_1_0_0_0_b1_val R hb0 h2
  · rw [synth_ylo_4]; exact synth_e2_0_1_0_0_1_0_0_0_b1_lo R hb0 h2
  · rw [synth_yhi_4]; exact synth_e2_0_1_0_0_1_0_0_0_b1_hi R hb0 h2

theorem synth_e2_0_1_0_1_0_0_0_0_b1_val (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-58 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((536 / 5 : ℝ) + (236 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-58 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((536 / 5 : ℝ) + (236 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_1_0_0_0_0_b1_lo (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_1_0_0_0_0_b1_hi (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_0_1_0_0_0_0 (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-58 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_1_0_1_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_1_0_1_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_1_0_1_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_0_1_1_0_0_0_0_0_b1_val (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (-251 / 200 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((433 / 10 : ℝ) + (-167 / 10 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-251 / 200 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((433 / 10 : ℝ) + (-167 / 10 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_1_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_1_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (15 / 14 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_1_1_0_0_0_0_0 (R : ℝ) (h1 : (15 / 14 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-251 / 200 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_1_1_0_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_1_1_0_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_1_1_0_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_0_2_0_0_0_0_0_0_b1_val (R : ℝ) (h1 : (8 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-34 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (8 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((248 / 5 : ℝ) + (-52 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-34 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((248 / 5 : ℝ) + (-52 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_2_0_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (8 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (8 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_2_0_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (8 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (8 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_0_2_0_0_0_0_0_0 (R : ℝ) (h1 : (8 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-34 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_0_2_0_0_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_0_2_0_0_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_0_2_0_0_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_1_0_0_0_0_0_0_1_b1_val (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-16 / 5 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((160 : ℝ) + (100 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-16 / 5 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((160 : ℝ) + (100 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_0_0_1_b1_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_0_0_1_b1_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_0_0_1 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-16 / 5 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_1_0_0_0_0_0_0_1_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_1_0_0_0_0_0_0_1_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_1_0_0_0_0_0_0_1_b1_hi R h1 h2

theorem synth_e2_1_0_0_0_0_0_1_0_b1_val (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-16 / 5 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((160 : ℝ) + (100 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-16 / 5 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((160 : ℝ) + (100 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_0_1_0_b1_lo (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_0_1_0_b1_hi (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_0_1_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-16 / 5 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_1_0_0_0_0_0_1_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_1_0_0_0_0_0_1_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_1_0_0_0_0_0_1_0_b1_hi R h1 h2

theorem synth_e2_1_0_0_0_0_1_0_0_b1_val (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-41 / 20 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (6 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((91 : ℝ) + (31 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-41 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((91 : ℝ) + (31 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_1_0_0_b1_lo (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (6 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_1_0_0_b1_hi (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (6 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_0_1_0_0 (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-41 / 20 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_1_0_0_0_0_1_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_1_0_0_0_0_1_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_1_0_0_0_0_1_0_0_b1_hi R h1 h2

theorem synth_e2_1_0_0_0_1_0_0_0_b1_val (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (-33 / 20 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (4 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((67 : ℝ) + (7 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-33 / 20 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((67 : ℝ) + (7 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_1_0_0_0_b1_lo (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (4 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_1_0_0_0_b1_hi (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (4 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_0_1_0_0_0 (R : ℝ) (h1 : (4 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-33 / 20 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_1_0_0_0_1_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_1_0_0_0_1_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_1_0_0_0_1_0_0_0_b1_hi R h1 h2

theorem synth_e2_1_0_0_1_0_0_0_0_b1_val (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-56 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((512 / 5 : ℝ) + (212 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-56 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((512 / 5 : ℝ) + (212 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_1_0_0_0_0_b1_lo (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_1_0_0_0_0_b1_hi (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_0_1_0_0_0_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-56 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_1_0_0_1_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_1_0_0_1_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_1_0_0_1_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_1_0_1_0_0_0_0_0_b1_val (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (-47 / 40 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((77 / 2 : ℝ) + (-43 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-47 / 40 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((77 / 2 : ℝ) + (-43 / 2 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_1_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_1_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (11 / 7 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_0_1_0_0_0_0_0 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (11 / 7 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-47 / 40 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_1_0_1_0_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_1_0_1_0_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_1_0_1_0_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_1_1_0_0_0_0_0_0_b1_val (R : ℝ) (h1 : (11 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-32 / 25 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  have hs : 0 ≤ R - (11 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((60 : ℝ) + (60 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 2 R = (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((224 / 5 : ℝ) + (-76 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((-21 / 20 : ℝ)) - ((-32 / 25 : ℝ) + (((-31 : ℝ) + (29 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R))) = ((224 / 5 : ℝ) + (-76 / 5 : ℝ) * R) / ((60 : ℝ) + (60 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_1_0_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (11 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  have hs : 0 ≤ R - (11 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_1_0_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (11 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (11 / 7 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_e2_1_1_0_0_0_0_0_0 (R : ℝ) (h1 : (11 / 7 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-32 / 25 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_1_1_0_0_0_0_0_0_b1_val R h1 h2
  · rw [synth_ylo_4]; exact synth_e2_1_1_0_0_0_0_0_0_b1_lo R h1 h2
  · rw [synth_yhi_4]; exact synth_e2_1_1_0_0_0_0_0_0_b1_hi R h1 h2

theorem synth_e2_2_0_0_0_0_0_0_0_b1_val (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-6 / 5 : ℝ) + synth_g 2 R ≤ (-21 / 20 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [synth_g]

theorem synth_e2_2_0_0_0_0_0_0_0_b1_lo (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (1 / 3 : ℝ) ≤ synth_h 2 R := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_2_0_0_0_0_0_0_0_b1_hi (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_h 2 R ≤ (1 / 2 : ℝ) := by
  obtain rfl : R = (2 : ℝ) := le_antisymm h2 h1
  norm_num [synth_h]

theorem synth_e2_2_0_0_0_0_0_0_0 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R) ((-6 / 5 : ℝ) + synth_g 2 R) (synth_h 2 R) := by
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · exfalso; linarith
  rw [synth_tp_2_1 (2) (by omega) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_4]; exact synth_e2_2_0_0_0_0_0_0_0_b1_val R (by linarith) (by linarith)
  · rw [synth_ylo_4]; exact synth_e2_2_0_0_0_0_0_0_0_b1_lo R (by linarith) (by linarith)
  · rw [synth_yhi_4]; exact synth_e2_2_0_0_0_0_0_0_0_b1_hi R (by linarith) (by linarith)

theorem synth_cnt2 (c : Fin 8 → ℕ) (hc : ∑ t, c t = 2) (R : ℝ)
    (h1 : ∑ t, (c t : ℝ) * synth_ylo t ≤ R) (h2 : R ≤ ∑ t, (c t : ℝ) * synth_yhi t) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 2 R)
      ((∑ t, (c t : ℝ) * synth_B t) + synth_g 2 R) (synth_h 2 R) := by
  simp only [Fin.sum_univ_eight, synth_B_0, synth_B_1, synth_B_2, synth_B_3, synth_B_4, synth_B_5, synth_B_6, synth_B_7, synth_ylo_0, synth_ylo_1, synth_ylo_2, synth_ylo_3, synth_ylo_4, synth_ylo_5, synth_ylo_6, synth_ylo_7, synth_yhi_0, synth_yhi_1, synth_yhi_2, synth_yhi_3, synth_yhi_4, synth_yhi_5, synth_yhi_6, synth_yhi_7] at hc h1 h2 ⊢
  generalize c 0 = c0 at hc h1 h2 ⊢
  generalize c 1 = c1 at hc h1 h2 ⊢
  generalize c 2 = c2 at hc h1 h2 ⊢
  generalize c 3 = c3 at hc h1 h2 ⊢
  generalize c 4 = c4 at hc h1 h2 ⊢
  generalize c 5 = c5 at hc h1 h2 ⊢
  generalize c 6 = c6 at hc h1 h2 ⊢
  generalize c 7 = c7 at hc h1 h2 ⊢
  have b0 : c0 ≤ 2 := by omega
  interval_cases c0
  · have b1 : c1 ≤ 2 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 2 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 2 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 2 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 2 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 2 := by omega
              interval_cases c6
              · obtain rfl : c7 = 2 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_0_0_0_2 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_0_0_1_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_0_0_2_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 1 := by omega
              interval_cases c6
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_0_1_0_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_0_1_1_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_0_2_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
          · have b5 : c5 ≤ 1 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 1 := by omega
              interval_cases c6
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_1_0_0_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_1_0_1_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_1_1_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_0_2_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
        · have b4 : c4 ≤ 1 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 1 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 1 := by omega
              interval_cases c6
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_1_0_0_0_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_1_0_0_1_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_1_0_1_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_1_1_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_0_2_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · have b3 : c3 ≤ 1 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 1 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 1 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 1 := by omega
              interval_cases c6
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_1_0_0_0_0_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_1_0_0_0_1_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_1_0_0_1_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_1_0_1_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_1_1_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_0_2_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 1 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 1 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 1 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 1 := by omega
              interval_cases c6
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_1_0_0_0_0_0_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_1_0_0_0_0_1_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_1_0_0_0_1_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_1_0_0_1_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_1_0_1_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_1_1_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_0_2_0_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 1 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 1 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 1 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 1 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 1 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 1 := by omega
              interval_cases c6
              · obtain rfl : c7 = 1 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_1_0_0_0_0_0_0_1 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_1_0_0_0_0_0_1_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_1_0_0_0_0_1_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_1_0_0_0_1_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_1_0_0_1_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_1_0_1_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_1_1_0_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩
  · have b1 : c1 ≤ 0 := by omega
    interval_cases c1
    · have b2 : c2 ≤ 0 := by omega
      interval_cases c2
      · have b3 : c3 ≤ 0 := by omega
        interval_cases c3
        · have b4 : c4 ≤ 0 := by omega
          interval_cases c4
          · have b5 : c5 ≤ 0 := by omega
            interval_cases c5
            · have b6 : c6 ≤ 0 := by omega
              interval_cases c6
              · obtain rfl : c7 = 0 := by omega
                push_cast at h1 h2 ⊢
                have hob := synth_e2_2_0_0_0_0_0_0_0 R (by linarith) (by linarith)
                exact ⟨by linarith [hob.1], hob.2.1, hob.2.2⟩

theorem synth_band3_tan_c0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    synth_g 3 R ≤ (-71 / 400 : ℝ) + (4 / 25 : ℝ) * R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((80 : ℝ) + (80 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 3 R = (((-43 : ℝ) + (37 : ℝ) * R) / ((80 : ℝ) + (80 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((144 / 5 : ℝ) + (-192 / 5 : ℝ) * R + (64 / 5 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-71 / 400 : ℝ) + (4 / 25 : ℝ) * R) - ((((-43 : ℝ) + (37 : ℝ) * R) / ((80 : ℝ) + (80 : ℝ) * R))) = ((144 / 5 : ℝ) + (-192 / 5 : ℝ) * R + (64 / 5 : ℝ) * R ^ 2) / ((80 : ℝ) + (80 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band3_tan_c1 (R : ℝ) (h1 : (3 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    synth_g 3 R ≤ (-71 / 400 : ℝ) + (4 / 25 : ℝ) * R := by
  have hs : 0 ≤ R - (3 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 : ℝ) - R := by linarith
  have hD0 : 0 < ((80 : ℝ) + (80 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 3 R = (((-43 : ℝ) + (37 : ℝ) * R) / ((80 : ℝ) + (80 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((144 / 5 : ℝ) + (-192 / 5 : ℝ) * R + (64 / 5 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-71 / 400 : ℝ) + (4 / 25 : ℝ) * R) - ((((-43 : ℝ) + (37 : ℝ) * R) / ((80 : ℝ) + (80 : ℝ) * R))) = ((144 / 5 : ℝ) + (-192 / 5 : ℝ) * R + (64 / 5 : ℝ) * R ^ 2) / ((80 : ℝ) + (80 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band3_tan (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    synth_g 3 R ≤ (-71 / 400 : ℝ) + (4 / 25 : ℝ) * R := by
  rcases le_or_gt R (3 / 2 : ℝ) with h_0 | h_0
  · exact synth_band3_tan_c0 R h1 h_0
  exact synth_band3_tan_c1 R h_0.le h2

theorem synth_band3_mu : ∀ t y, synth_ylo t ≤ y → y ≤ synth_yhi t →
    synth_B t + (4 / 25 : ℝ) * y ≤ (-11 / 25 : ℝ) := by
  intro t y h1 h2
  fin_cases t <;> norm_num [synth_B, synth_ylo, synth_yhi] at h1 h2 ⊢ <;> linarith

theorem synth_band3_b0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (1 / 5 : ℝ) ≤ synth_h 3 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (3 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 3 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((4 / 5 : ℝ) + (-1 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 5 : ℝ)) = ((4 / 5 : ℝ) + (-1 / 5 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band3_b0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    synth_h 3 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (3 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 3 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band3 (τ : Fin 3 → Fin 8) (y l : Fin 3 → ℝ)
    (hch : ∀ i, Inv synth_B synth_ylo synth_yhi (τ i) (l i) (y i)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 3 (∑ i, y i))
      ((∑ i, l i) + synth_g 3 (∑ i, y i)) (synth_h 3 (∑ i, y i)) := by
  have hsep := separable_bound synth_B synth_ylo synth_yhi (4 / 25 : ℝ) (-11 / 25 : ℝ) synth_band3_mu τ y l hch
  have hR := msg_sum_range synth_B synth_ylo synth_yhi (0 : ℝ) (1 : ℝ) synth_ymin synth_ymax τ y l hch
  generalize ∑ i, y i = R at hsep hR ⊢
  generalize ∑ i, l i = L at hsep ⊢
  push_cast at hsep hR
  obtain ⟨hR1, hR2⟩ := hR
  have ht := synth_band3_tan R (by linarith) (by linarith)
  rw [synth_tp_3_0 (3) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_5]; linarith
  · rw [synth_ylo_5]; exact synth_band3_b0_lo R (by linarith) (by linarith)
  · rw [synth_yhi_5]; exact synth_band3_b0_hi R (by linarith) (by linarith)

theorem synth_band4_tan_c0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_g 4 R ≤ (-19 / 180 : ℝ) + (1 / 9 : ℝ) * R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD0 : 0 < ((100 : ℝ) + (100 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 4 R = (((-55 : ℝ) + (45 : ℝ) * R) / ((100 : ℝ) + (100 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((400 / 9 : ℝ) + (-400 / 9 : ℝ) * R + (100 / 9 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-19 / 180 : ℝ) + (1 / 9 : ℝ) * R) - ((((-55 : ℝ) + (45 : ℝ) * R) / ((100 : ℝ) + (100 : ℝ) * R))) = ((400 / 9 : ℝ) + (-400 / 9 : ℝ) * R + (100 / 9 : ℝ) * R ^ 2) / ((100 : ℝ) + (100 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band4_tan_c1 (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (4 : ℝ)) :
    synth_g 4 R ≤ (-19 / 180 : ℝ) + (1 / 9 : ℝ) * R := by
  have hs : 0 ≤ R - (2 : ℝ) := by linarith
  have ht : 0 ≤ (4 : ℝ) - R := by linarith
  have hD0 : 0 < ((100 : ℝ) + (100 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_g 4 R = (((-55 : ℝ) + (45 : ℝ) * R) / ((100 : ℝ) + (100 : ℝ) * R)) := by simp only [synth_g]; ring
  have key : 0 ≤ ((400 / 9 : ℝ) + (-400 / 9 : ℝ) * R + (100 / 9 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-19 / 180 : ℝ) + (1 / 9 : ℝ) * R) - ((((-55 : ℝ) + (45 : ℝ) * R) / ((100 : ℝ) + (100 : ℝ) * R))) = ((400 / 9 : ℝ) + (-400 / 9 : ℝ) * R + (100 / 9 : ℝ) * R ^ 2) / ((100 : ℝ) + (100 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band4_tan (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (4 : ℝ)) :
    synth_g 4 R ≤ (-19 / 180 : ℝ) + (1 / 9 : ℝ) * R := by
  rcases le_or_gt R (2 : ℝ) with h_0 | h_0
  · exact synth_band4_tan_c0 R h1 h_0
  exact synth_band4_tan_c1 R h_0.le h2

theorem synth_band4_mu : ∀ t y, synth_ylo t ≤ y → y ≤ synth_yhi t →
    synth_B t + (1 / 9 : ℝ) * y ≤ (-22 / 45 : ℝ) := by
  intro t y h1 h2
  fin_cases t <;> norm_num [synth_B, synth_ylo, synth_yhi] at h1 h2 ⊢ <;> linarith

theorem synth_band4_b0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (4 : ℝ)) :
    (1 / 5 : ℝ) ≤ synth_h 4 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 4 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((4 / 5 : ℝ) + (-1 / 5 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 5 : ℝ)) = ((4 / 5 : ℝ) + (-1 / 5 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band4_b0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (4 : ℝ)) :
    synth_h 4 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (4 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have ef : synth_h 4 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_band4 (τ : Fin 4 → Fin 8) (y l : Fin 4 → ℝ)
    (hch : ∀ i, Inv synth_B synth_ylo synth_yhi (τ i) (l i) (y i)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp 4 (∑ i, y i))
      ((∑ i, l i) + synth_g 4 (∑ i, y i)) (synth_h 4 (∑ i, y i)) := by
  have hsep := separable_bound synth_B synth_ylo synth_yhi (1 / 9 : ℝ) (-22 / 45 : ℝ) synth_band4_mu τ y l hch
  have hR := msg_sum_range synth_B synth_ylo synth_yhi (0 : ℝ) (1 : ℝ) synth_ymin synth_ymax τ y l hch
  generalize ∑ i, y i = R at hsep hR ⊢
  generalize ∑ i, l i = L at hsep ⊢
  push_cast at hsep hR
  obtain ⟨hR1, hR2⟩ := hR
  have ht := synth_band4_tan R (by linarith) (by linarith)
  rw [synth_tp_3_0 (4) (by omega) (by omega) (R)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_5]; linarith
  · rw [synth_ylo_5]; exact synth_band4_b0_lo R (by linarith) (by linarith)
  · rw [synth_yhi_5]; exact synth_band4_b0_hi R (by linarith) (by linarith)

theorem synth_tail_tan_c0 (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synth_g k R ≤ (-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have ef : synth_g k R = (((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R)) := by simp only [synth_g]
  have key : 0 ≤ ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0))]
  have e : ((-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R) - ((((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R))) = ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_tan_c1 (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (2 : ℝ) ≤ R) (h2 : R ≤ (5 / 2 : ℝ)) :
    synth_g k R ≤ (-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R := by
  have hs : 0 ≤ R - (2 : ℝ) := by linarith
  have ht : 0 ≤ (5 / 2 : ℝ) - R := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have ef : synth_g k R = (((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R)) := by simp only [synth_g]
  have key : 0 ≤ ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0))]
  have e : ((-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R) - ((((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R))) = ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_tan_c2 (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (5 / 2 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    synth_g k R ≤ (-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R := by
  have hs : 0 ≤ R - (5 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (3 : ℝ) - R := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have ef : synth_g k R = (((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R)) := by simp only [synth_g]
  have key : 0 ≤ ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0))]
  have e : ((-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R) - ((((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R))) = ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_tan_c3 (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (3 : ℝ) ≤ R) (h2 : R ≤ (4 : ℝ)) :
    synth_g k R ≤ (-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R := by
  have hs : 0 ≤ R - (3 : ℝ) := by linarith
  have ht : 0 ≤ (4 : ℝ) - R := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have ef : synth_g k R = (((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R)) := by simp only [synth_g]
  have key : 0 ≤ ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 1) (mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0))]
  have e : ((-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R) - ((((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R))) = ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_tan_c4 (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (4 : ℝ) ≤ R) :
    synth_g k R ≤ (-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R := by
  have hs : 0 ≤ R - (4 : ℝ) := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 0), mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 1), mul_nonneg (pow_nonneg hu 1) (pow_nonneg hs 0), mul_nonneg (pow_nonneg hu 1) (pow_nonneg hs 1)]
  have ef : synth_g k R = (((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R)) := by simp only [synth_g]
  have key : 0 ≤ ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 0), mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 1), mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 2), mul_nonneg (pow_nonneg hu 1) (pow_nonneg hs 0), mul_nonneg (pow_nonneg hu 1) (pow_nonneg hs 1), mul_nonneg (pow_nonneg hu 1) (pow_nonneg hs 2)]
  have e : ((-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R) - ((((-7 : ℝ) + (13 : ℝ) * R + (-12 : ℝ) * (k : ℝ) + (8 : ℝ) * (k : ℝ) * R) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R))) = ((1775 / 294 : ℝ) + (-3625 / 294 : ℝ) * R + (80 / 49 : ℝ) * R ^ 2 + (3245 / 294 : ℝ) * (k : ℝ) + (-2155 / 294 : ℝ) * (k : ℝ) * R + (80 / 49 : ℝ) * (k : ℝ) * R ^ 2) / ((20 : ℝ) + (20 : ℝ) * R + (20 : ℝ) * (k : ℝ) + (20 : ℝ) * (k : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_tan (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (0 : ℝ) ≤ R) :
    synth_g k R ≤ (-283 / 5880 : ℝ) + (4 / 49 : ℝ) * R := by
  rcases le_or_gt R (2 : ℝ) with h_0 | h_0
  · exact synth_tail_tan_c0 k hk R h1 h_0
  rcases le_or_gt R (5 / 2 : ℝ) with h_1 | h_1
  · exact synth_tail_tan_c1 k hk R h_0.le h_1
  rcases le_or_gt R (3 : ℝ) with h_2 | h_2
  · exact synth_tail_tan_c2 k hk R h_1.le h_2
  rcases le_or_gt R (4 : ℝ) with h_3 | h_3
  · exact synth_tail_tan_c3 k hk R h_2.le h_3
  exact synth_tail_tan_c4 k hk R h_3.le

theorem synth_tail_mu : ∀ t y, synth_ylo t ≤ y → y ≤ synth_yhi t →
    synth_B t + (4 / 49 : ℝ) * y ≤ (-127 / 245 : ℝ) := by
  intro t y h1 h2
  fin_cases t <;> norm_num [synth_B, synth_ylo, synth_yhi] at h1 h2 ⊢ <;> linarith

theorem synth_tail_b0_lo (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ synth_h k R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have ef : synth_h k R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_b0_hi (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synth_h k R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have ef : synth_h k R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1)), mul_nonneg (pow_nonneg hu 0) (mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0))]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_b1_lo (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (0 : ℝ) ≤ synth_h k R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 0), mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 1)]
  have ef : synth_h k R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail_b1_hi (k : ℕ) (hk : 5 ≤ k) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    synth_h k R ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hk' : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ (k : ℝ) - 5 := by linarith
  have hD0 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 0), mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 1)]
  have ef : synth_h k R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synth_h]
  have key : 0 ≤ ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 0), mul_nonneg (pow_nonneg hu 0) (pow_nonneg hs 1)]
  have e : ((1 / 2 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 2 : ℝ) + (1 / 2 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hD0.le
  rw [ef]
  linarith

theorem synth_tail (k : ℕ) (hk : 4 < k) (τ : Fin k → Fin 8) (y l : Fin k → ℝ)
    (hch : ∀ i, Inv synth_B synth_ylo synth_yhi (τ i) (l i) (y i)) :
    Inv synth_B synth_ylo synth_yhi (synth_tp k (∑ i, y i))
      ((∑ i, l i) + synth_g k (∑ i, y i)) (synth_h k (∑ i, y i)) := by
  have hk' : 5 ≤ k := hk
  have hsep := separable_bound synth_B synth_ylo synth_yhi (4 / 49 : ℝ) (-127 / 245 : ℝ) synth_tail_mu τ y l hch
  have hR := msg_sum_range synth_B synth_ylo synth_yhi (0 : ℝ) (1 : ℝ) synth_ymin synth_ymax τ y l hch
  generalize ∑ i, y i = R at hsep hR ⊢
  generalize ∑ i, l i = L at hsep ⊢
  have hkr : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'
  have hmu : (k : ℝ) * (-127 / 245 : ℝ) ≤ (5 : ℝ) * (-127 / 245 : ℝ) :=
    mul_le_mul_of_nonpos_right hkr (by norm_num)
  have hR0 : (5 : ℝ) * (0 : ℝ) ≤ R :=
    le_trans (mul_le_mul_of_nonneg_right hkr (by norm_num)) hR.1
  have ht := synth_tail_tan k hk' R (by linarith)
  rcases lt_or_ge (R) (1 : ℝ) with hb0 | hb0
  · rw [synth_tp_4_0 (k) (by omega) (R) (by linarith)]
    refine ⟨?_, ?_, ?_⟩
    · rw [synth_B_6]; linarith
    · rw [synth_ylo_6]; exact synth_tail_b0_lo k hk' R (by linarith) hb0.le
    · rw [synth_yhi_6]; exact synth_tail_b0_hi k hk' R (by linarith) hb0.le
  rw [synth_tp_4_1 (k) (by omega) (R) (by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_B_7]; linarith
  · rw [synth_ylo_7]; exact synth_tail_b1_lo k hk' R (by linarith)
  · rw [synth_yhi_7]; exact synth_tail_b1_hi k hk' R (by linarith)

theorem synth_hstep : ∀ k : ℕ, 1 ≤ k → True → ∀ (τ : Fin k → Fin 8) (y l : Fin k → ℝ),
    (∀ i, Inv synth_B synth_ylo synth_yhi (τ i) (l i) (y i)) →
    Inv synth_B synth_ylo synth_yhi (synth_tp k (∑ i, y i))
      ((∑ i, l i) + synth_g k (∑ i, y i)) (synth_h k (∑ i, y i)) := by
  intro k hk hok τ y l hch
  rcases Nat.lt_or_ge 4 k with hK | hK
  · exact synth_tail k hK τ y l hch
  interval_cases k
  · exact step_of_counts (synth_g 1) (synth_h 1) (synth_tp 1) synth_B synth_ylo synth_yhi synth_cnt1 τ y l hch
  · exact step_of_counts (synth_g 2) (synth_h 2) (synth_tp 2) synth_B synth_ylo synth_yhi synth_cnt2 τ y l hch
  · exact synth_band3 τ y l hch
  · exact synth_band4 τ y l hch

/-- MAIN.  The type table is an inductive invariant on every finite rooted tree:
`ell b ≤ B[type b]` and `ylo[type b] ≤ msg b ≤ yhi[type b]`. -/
theorem synth (b : PTree) :
    Inv synth_B synth_ylo synth_yhi (b.typ synth_tp synth_h (1 : ℝ))
      (b.ell synth_g synth_h (-3 / 5 : ℝ) (1 : ℝ)) (b.msg synth_h (1 : ℝ)) :=
  typed_induction_core (fun _ => True) synth_h synth_g (1 : ℝ) (-3 / 5 : ℝ) synth_tp synth_B synth_ylo synth_yhi
    synth_base synth_hstep b (PTree.allDeg_true b)

/-- Uniform corollary: `ell b ≤ max_t B_t = -23/40`. -/
theorem synth_uniform (b : PTree) :
    b.ell synth_g synth_h (-3 / 5 : ℝ) (1 : ℝ) ≤ (-23 / 40 : ℝ) :=
  le_trans (synth b).1 (synth_Bmax _)

end TypedCavityInduction
