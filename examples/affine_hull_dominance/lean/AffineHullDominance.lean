/- telperion 0.1.6 | family AffineHullDominance | input-hash c9fc6c2f8fe14673
   182 theorems, 2529 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace AffineHullDominance

/-! ## Generic affine hull dominance (emitted once per file)

A positive multilinear tree recursion, domination by convex combinations in dual form, the
exchange induction, the exact maximum and the maximizer structure theorem.
conjecture1_proved = False. -/

namespace HullDom

/-- States of a branch or a bundle: vectors of rationals. -/
abbrev Vec (D : ℕ) := Fin D → ℚ

/-- A positive multilinear tree recursion of dimension `D`. -/
structure Rec (D : ℕ) where
  /-- the value of the empty bundle -/
  e : Vec D
  /-- adding a child: `(x ⊗ z) i = ∑ j l, T i j l * x j * z l` -/
  T : Fin D → Fin D → Fin D → ℚ
  /-- planting a bundle of `c` children: `(P c x) i = ∑ j, P c i j * x j` -/
  P : ℕ → Fin D → Fin D → ℚ
  /-- the root functional for a root with `k` children -/
  F : ℕ → Fin D → ℚ

/-- Finite rooted trees; the children form a list. -/
inductive RTree : Type
  | node : List RTree → RTree

variable {D : ℕ}

def dot (a x : Vec D) : ℚ := ∑ i, a i * x i

namespace Rec

def mul (R : Rec D) (x z : Vec D) : Vec D := fun i => ∑ j, ∑ l, R.T i j l * x j * z l

def plant (R : Rec D) (c : ℕ) (x : Vec D) : Vec D := fun i => ∑ j, R.P c i j * x j

def root (R : Rec D) (k : ℕ) (x : Vec D) : ℚ := dot (R.F k) x

end Rec

mutual
/-- Number of vertices of a tree. -/
def RTree.size : RTree → ℕ
  | .node l => RTree.sizeL l + 1
/-- Total number of vertices of a list of trees. -/
def RTree.sizeL : List RTree → ℕ
  | [] => 0
  | t :: l => t.size + RTree.sizeL l
end

mutual
/-- The value of a planted branch. -/
def Rec.branch (R : Rec D) : RTree → Vec D
  | .node l => R.plant l.length (R.bundle l)
/-- The value of a bundle of branches. -/
def Rec.bundle (R : Rec D) : List RTree → Vec D
  | [] => R.e
  | t :: l => R.mul (R.bundle l) (R.branch t)
end

/-- The quantity: the root functional applied to the bundle of the root's children. -/
def Rec.pi (R : Rec D) : RTree → ℚ
  | .node l => R.root l.length (R.bundle l)

theorem RTree.length_le_sizeL : ∀ l : List RTree, l.length ≤ RTree.sizeL l
  | [] => le_rfl
  | t :: l => by
    have := RTree.length_le_sizeL l
    simp only [List.length_cons, RTree.sizeL]
    cases t with
    | node l' => simp only [RTree.size]; omega

/-! ### Domination by a convex combination, in dual form -/

/-- `x` is weakly dominated by the convex hull of `K`: every nonnegative covector is at least
as large at some point of `K`. -/
def Dom (K : List (Vec D)) (x : Vec D) : Prop :=
  ∀ a : Vec D, (∀ i, 0 ≤ a i) → ∃ p ∈ K, dot a x ≤ dot a p

/-- `x` is strictly dominated: every strictly positive covector is strictly larger at some
point of `K`. -/
def SDom (K : List (Vec D)) (x : Vec D) : Prop :=
  ∀ a : Vec D, (∀ i, 0 < a i) → ∃ p ∈ K, dot a x < dot a p

/-- A convex combination `∑ w_k K_k`. -/
def combo : List ℚ → List (Vec D) → Vec D
  | c :: w, p :: K => fun i => c * p i + combo w K i
  | _, _ => fun _ => 0

/-- A witness for one candidate: it is a kept point (by index), or it is dominated by a convex
combination of the kept points, strictly in at least one coordinate. -/
inductive Wit : Type
  | kept (i : ℕ)
  | dom (w : List ℚ)

def WitOK (K : List (Vec D)) (x : Vec D) : Wit → Prop
  | .kept i => i < K.length ∧ ∀ j, K.getD i 0 j = x j
  | .dom w => w.length = K.length ∧ (∀ c ∈ w, 0 ≤ c) ∧ w.sum = 1 ∧
      (∀ j, x j ≤ combo w K j) ∧ ∃ j, x j < combo w K j

instance (K : List (Vec D)) (x : Vec D) : (w : Wit) → Decidable (WitOK K x w)
  | .kept i => inferInstanceAs (Decidable (i < K.length ∧ ∀ j, K.getD i 0 j = x j))
  | .dom w => inferInstanceAs (Decidable (w.length = K.length ∧ (∀ c ∈ w, 0 ≤ c) ∧
      w.sum = 1 ∧ (∀ j, x j ≤ combo w K j) ∧ ∃ j, x j < combo w K j))

theorem dot_add (a u v : Vec D) : dot a (fun i => u i + v i) = dot a u + dot a v := by
  simp only [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul (a u : Vec D) (c : ℚ) : dot a (fun i => c * u i) = c * dot a u := by
  simp only [dot, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_zero (a : Vec D) : dot a (fun _ => 0) = 0 := by simp [dot]

theorem dot_combo (a : Vec D) :
    ∀ (w : List ℚ) (K : List (Vec D)), w.length = K.length →
      dot a (combo w K) = (List.zipWith (fun c p => c * dot a p) w K).sum
  | [], [], _ => by simp [combo, dot_zero]
  | c :: w, p :: K, h => by
    have ih := dot_combo a w K (by simpa using h)
    simp only [combo, List.zipWith_cons_cons, List.sum_cons]
    rw [dot_add, dot_smul, ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem zip_le (f : Vec D → ℚ) (M : ℚ) :
    ∀ (w : List ℚ) (K : List (Vec D)), w.length = K.length → (∀ c ∈ w, 0 ≤ c) →
      (∀ p ∈ K, f p ≤ M) → (List.zipWith (fun c p => c * f p) w K).sum ≤ w.sum * M
  | [], [], _, _, _ => by simp
  | c :: w, p :: K, h, hw, hK => by
    have ih := zip_le f M w K (by simpa using h) (fun c hc => hw c (by simp [hc]))
      (fun p hp => hK p (by simp [hp]))
    have h1 : c * f p ≤ c * M :=
      mul_le_mul_of_nonneg_left (hK p (by simp)) (hw c (by simp))
    simp only [List.zipWith_cons_cons, List.sum_cons]
    nlinarith
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

/-- A convex combination is below the best point of `K` for any covector. -/
theorem exists_ge_combo (a : Vec D) (w : List ℚ) (K : List (Vec D)) (hl : w.length = K.length)
    (hw : ∀ c ∈ w, 0 ≤ c) (hs : w.sum = 1) : ∃ p ∈ K, dot a (combo w K) ≤ dot a p := by
  classical
  have hne : K ≠ [] := by
    rintro rfl
    have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this; simp at hs
  obtain ⟨p, hp, hmax⟩ := K.toFinset.exists_max_image (fun p => dot a p)
    (by simpa [List.toFinset_nonempty_iff] using hne)
  refine ⟨p, by simpa using hp, ?_⟩
  rw [dot_combo a w K hl]
  have := zip_le (fun q => dot a q) (dot a p) w K hl hw (fun q hq => hmax q (by simpa using hq))
  simpa [hs] using this

theorem dom_of_mem {K : List (Vec D)} {x : Vec D} (h : x ∈ K) : Dom K x :=
  fun _ _ => ⟨x, h, le_rfl⟩

theorem dot_le_dot {a x y : Vec D} (ha : ∀ i, 0 ≤ a i) (h : ∀ i, x i ≤ y i) :
    dot a x ≤ dot a y :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (ha i)

theorem dot_lt_dot {a x y : Vec D} (ha : ∀ i, 0 < a i) (h : ∀ i, x i ≤ y i)
    (hj : ∃ j, x j < y j) : dot a x < dot a y := by
  obtain ⟨j, hj⟩ := hj
  exact Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (ha i).le)
    ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (ha j)⟩

/-- A checked witness makes the candidate kept, or strictly dominated; in both cases weakly
dominated. -/
theorem witOK_sound {K : List (Vec D)} {x : Vec D} {w : Wit} (h : WitOK K x w) :
    (x ∈ K ∨ SDom K x) ∧ Dom K x := by
  cases w with
  | kept i =>
    obtain ⟨hi, he⟩ := h
    have hx : x = K.getD i 0 := funext fun j => (he j).symm
    have hm : x ∈ K := by
      rw [hx, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact ⟨Or.inl hm, dom_of_mem hm⟩
  | dom w =>
    obtain ⟨hl, hw, hs, hle, hlt⟩ := h
    refine ⟨Or.inr fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨p, hp, hp'⟩ := exists_ge_combo a w K hl hw hs
      exact ⟨p, hp, lt_of_lt_of_le (dot_lt_dot ha hle hlt) hp'⟩
    · obtain ⟨p, hp, hp'⟩ := exists_ge_combo a w K hl hw hs
      exact ⟨p, hp, le_trans (dot_le_dot ha hle) hp'⟩

theorem forall2_exists {α β : Type} {Rl : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Rl l₁ l₂ → ∀ x ∈ l₁, ∃ y, Rl x y
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons (a := a) (b := b) h t, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, h⟩
    · exact forall2_exists t x hx

/-! ### Pulling covectors back through the recursion -/

namespace Rec

variable (R : Rec D)

theorem dot_mul_left (a x z : Vec D) :
    dot a (R.mul x z) = dot (fun j => ∑ i, ∑ l, a i * R.T i j l * z l) x := by
  simp only [dot, mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem dot_mul_right (a x z : Vec D) :
    dot a (R.mul x z) = dot (fun l => ∑ i, ∑ j, a i * R.T i j l * x j) z := by
  simp only [dot, mul, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ i, ∑ l, ∑ j, a i * (R.T i j l * x j * z l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, a i * (R.T i j l * x j * z l) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring

theorem dot_plant (a : Vec D) (c : ℕ) (x : Vec D) :
    dot a (R.plant c x) = dot (fun j => ∑ i, a i * R.P c i j) x := by
  simp only [dot, plant, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- Sign conditions on the recursion (checked per instance by `decide`), for child counts
below `N`: nonnegative coefficients, a positive `0`-th coordinate that propagates, and every
column reached from coordinate `0`, so strictly positive covectors pull back to strictly
positive covectors. -/
structure Signs (R : Rec D) (N : ℕ) (z0 : Fin D) : Prop where
  e_nn : ∀ i, 0 ≤ R.e i
  e_pos : 0 < R.e z0
  T_nn : ∀ i j l, 0 ≤ R.T i j l
  T_pos : 0 < R.T z0 z0 z0
  T_left : ∀ j, ∃ i, 0 < R.T i j z0
  T_right : ∀ l, ∃ i, 0 < R.T i z0 l
  P_nn : ∀ c < N, ∀ i j, 0 ≤ R.P c i j
  P_pos : ∀ c < N, 0 < R.P c z0 z0
  P_col : ∀ c < N, ∀ j, ∃ i, 0 < R.P c i j

end Rec

/-! ### Pulled-back covectors keep their sign -/

section Pull

variable {R : Rec D} {N : ℕ} {z0 : Fin D}

theorem pullL_nn (hT : ∀ i j l, 0 ≤ R.T i j l) {a z : Vec D} (ha : ∀ i, 0 ≤ a i)
    (hz : ∀ i, 0 ≤ z i) (j : Fin D) : 0 ≤ ∑ i, ∑ l, a i * R.T i j l * z l :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (ha i) (hT i j l)) (hz l)

theorem pullR_nn (hT : ∀ i j l, 0 ≤ R.T i j l) {a x : Vec D} (ha : ∀ i, 0 ≤ a i)
    (hx : ∀ i, 0 ≤ x i) (l : Fin D) : 0 ≤ ∑ i, ∑ j, a i * R.T i j l * x j :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (ha i) (hT i j l)) (hx j)

theorem pullP_nn {c : ℕ} (hP : ∀ i j, 0 ≤ R.P c i j) {a : Vec D} (ha : ∀ i, 0 ≤ a i)
    (j : Fin D) : 0 ≤ ∑ i, a i * R.P c i j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hP i j)

theorem pullL_pos (hS : R.Signs N z0) {a z : Vec D} (ha : ∀ i, 0 < a i)
    (hz : ∀ i, 0 ≤ z i) (hz0 : 0 < z z0) (j : Fin D) :
    0 < ∑ i, ∑ l, a i * R.T i j l * z l := by
  obtain ⟨i, hi⟩ := hS.T_left j
  have hnn : ∀ i l, 0 ≤ a i * R.T i j l * z l := fun i l =>
    mul_nonneg (mul_nonneg (ha i).le (hS.T_nn i j l)) (hz l)
  have h1 : 0 < a i * R.T i j z0 * z z0 := mul_pos (mul_pos (ha i) hi) hz0
  have h2 : a i * R.T i j z0 * z z0 ≤ ∑ l, a i * R.T i j l * z l :=
    Finset.single_le_sum (fun l _ => hnn i l) (Finset.mem_univ z0)
  have h3 : ∑ l, a i * R.T i j l * z l ≤ ∑ i, ∑ l, a i * R.T i j l * z l :=
    Finset.single_le_sum (f := fun i => ∑ l, a i * R.T i j l * z l)
      (fun i _ => Finset.sum_nonneg fun l _ => hnn i l) (Finset.mem_univ i)
  linarith

theorem pullR_pos (hS : R.Signs N z0) {a x : Vec D} (ha : ∀ i, 0 < a i)
    (hx : ∀ i, 0 ≤ x i) (hx0 : 0 < x z0) (l : Fin D) :
    0 < ∑ i, ∑ j, a i * R.T i j l * x j := by
  obtain ⟨i, hi⟩ := hS.T_right l
  have hnn : ∀ i j, 0 ≤ a i * R.T i j l * x j := fun i j =>
    mul_nonneg (mul_nonneg (ha i).le (hS.T_nn i j l)) (hx j)
  have h1 : 0 < a i * R.T i z0 l * x z0 := mul_pos (mul_pos (ha i) hi) hx0
  have h2 : a i * R.T i z0 l * x z0 ≤ ∑ j, a i * R.T i j l * x j :=
    Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ z0)
  have h3 : ∑ j, a i * R.T i j l * x j ≤ ∑ i, ∑ j, a i * R.T i j l * x j :=
    Finset.single_le_sum (f := fun i => ∑ j, a i * R.T i j l * x j)
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_univ i)
  linarith

theorem pullP_pos (hS : R.Signs N z0) {c : ℕ} (hc : c < N) {a : Vec D}
    (ha : ∀ i, 0 < a i) (j : Fin D) : 0 < ∑ i, a i * R.P c i j := by
  obtain ⟨i, hi⟩ := hS.P_col c hc j
  have h1 : 0 < a i * R.P c i j := mul_pos (ha i) hi
  have h2 : a i * R.P c i j ≤ ∑ i, a i * R.P c i j :=
    Finset.single_le_sum (f := fun i => a i * R.P c i j)
      (fun i _ => mul_nonneg (ha i).le (hS.P_nn c hc i j)) (Finset.mem_univ i)
  linarith

/-! ### One step of the recursion transports domination -/

/-- Adding a child: weak domination (the exchange argument). -/
theorem mul_dom (hS : R.Signs N z0) {K1 K2 K : List (Vec D)} {x z : Vec D}
    (hx : Dom K1 x) (hz : Dom K2 z) (hz0 : ∀ i, 0 ≤ z i) (hK1 : ∀ p ∈ K1, ∀ i, 0 ≤ p i)
    (hc : ∀ p ∈ K1, ∀ q ∈ K2, Dom K (R.mul p q)) : Dom K (R.mul x z) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullL_nn hS.T_nn ha hz0)
  obtain ⟨q, hq, h2⟩ := hz _ (pullR_nn hS.T_nn ha (hK1 p hp))
  obtain ⟨r, hr, h3⟩ := hc p hp q hq a ha
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_mul_left a x z
  have e2 := R.dot_mul_left a p z
  have e3 := R.dot_mul_right a p z
  have e4 := R.dot_mul_right a p q
  linarith

/-- Adding a child to a strictly dominated bundle. -/
theorem mul_sdom_left (hS : R.Signs N z0) {K1 K2 K : List (Vec D)} {x z : Vec D}
    (hx : SDom K1 x) (hz : Dom K2 z) (hz0 : ∀ i, 0 ≤ z i) (hzp : 0 < z z0)
    (hK1 : ∀ p ∈ K1, ∀ i, 0 ≤ p i)
    (hc : ∀ p ∈ K1, ∀ q ∈ K2, Dom K (R.mul p q)) : SDom K (R.mul x z) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullL_pos hS ha hz0 hzp)
  obtain ⟨q, hq, h2⟩ := hz _ (pullR_nn hS.T_nn (fun i => (ha i).le) (hK1 p hp))
  obtain ⟨r, hr, h3⟩ := hc p hp q hq a (fun i => (ha i).le)
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_mul_left a x z
  have e2 := R.dot_mul_left a p z
  have e3 := R.dot_mul_right a p z
  have e4 := R.dot_mul_right a p q
  linarith

/-- Adding a strictly dominated child to a kept bundle. -/
theorem mul_sdom_right (hS : R.Signs N z0) {K1 K2 K : List (Vec D)} {x z : Vec D}
    (hx : x ∈ K1) (hx0 : ∀ i, 0 ≤ x i) (hxp : 0 < x z0) (hz : SDom K2 z)
    (hc : ∀ p ∈ K1, ∀ q ∈ K2, Dom K (R.mul p q)) : SDom K (R.mul x z) := by
  intro a ha
  obtain ⟨q, hq, h2⟩ := hz _ (pullR_pos hS ha hx0 hxp)
  obtain ⟨r, hr, h3⟩ := hc x hx q hq a (fun i => (ha i).le)
  refine ⟨r, hr, ?_⟩
  have e3 := R.dot_mul_right a x z
  have e4 := R.dot_mul_right a x q
  linarith

/-- Planting: weak domination. -/
theorem plant_dom (hS : R.Signs N z0) {c : ℕ} (hcN : c < N) {K1 K : List (Vec D)}
    {x : Vec D} (hx : Dom K1 x) (hc : ∀ p ∈ K1, Dom K (R.plant c p)) :
    Dom K (R.plant c x) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullP_nn (hS.P_nn c hcN) ha)
  obtain ⟨r, hr, h3⟩ := hc p hp a ha
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_plant a c x
  have e2 := R.dot_plant a c p
  linarith

/-- Planting a strictly dominated bundle. -/
theorem plant_sdom (hS : R.Signs N z0) {c : ℕ} (hcN : c < N) {K1 K : List (Vec D)}
    {x : Vec D} (hx : SDom K1 x) (hc : ∀ p ∈ K1, Dom K (R.plant c p)) :
    SDom K (R.plant c x) := by
  intro a ha
  obtain ⟨p, hp, h1⟩ := hx _ (pullP_pos hS hcN ha)
  obtain ⟨r, hr, h3⟩ := hc p hp a (fun i => (ha i).le)
  refine ⟨r, hr, ?_⟩
  have e1 := R.dot_plant a c x
  have e2 := R.dot_plant a c p
  linarith

theorem mul_nn (hT : ∀ i j l, 0 ≤ R.T i j l) {x z : Vec D} (hx : ∀ i, 0 ≤ x i)
    (hz : ∀ i, 0 ≤ z i) (i : Fin D) : 0 ≤ R.mul x z i :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (hT i j l) (hx j)) (hz l)

theorem mul_pos0 (hS : R.Signs N z0) {x z : Vec D} (hx : ∀ i, 0 ≤ x i)
    (hz : ∀ i, 0 ≤ z i) (hxp : 0 < x z0) (hzp : 0 < z z0) : 0 < R.mul x z z0 := by
  have hnn : ∀ j l, 0 ≤ R.T z0 j l * x j * z l := fun j l =>
    mul_nonneg (mul_nonneg (hS.T_nn z0 j l) (hx j)) (hz l)
  have h1 : 0 < R.T z0 z0 z0 * x z0 * z z0 := mul_pos (mul_pos hS.T_pos hxp) hzp
  have h2 : R.T z0 z0 z0 * x z0 * z z0 ≤ ∑ l, R.T z0 z0 l * x z0 * z l :=
    Finset.single_le_sum (f := fun l => R.T z0 z0 l * x z0 * z l)
      (fun l _ => hnn z0 l) (Finset.mem_univ z0)
  have h3 : ∑ l, R.T z0 z0 l * x z0 * z l ≤ ∑ j, ∑ l, R.T z0 j l * x j * z l :=
    Finset.single_le_sum (f := fun j => ∑ l, R.T z0 j l * x j * z l)
      (fun j _ => Finset.sum_nonneg fun l _ => hnn j l) (Finset.mem_univ z0)
  show 0 < ∑ j, ∑ l, R.T z0 j l * x j * z l
  linarith

theorem plant_nn {c : ℕ} (hP : ∀ i j, 0 ≤ R.P c i j) {x : Vec D} (hx : ∀ i, 0 ≤ x i)
    (i : Fin D) : 0 ≤ R.plant c x i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hx j)

theorem plant_pos0 (hS : R.Signs N z0) {c : ℕ} (hc : c < N) {x : Vec D}
    (hx : ∀ i, 0 ≤ x i) (hxp : 0 < x z0) : 0 < R.plant c x z0 := by
  have h1 : 0 < R.P c z0 z0 * x z0 := mul_pos (hS.P_pos c hc) hxp
  have h2 : R.P c z0 z0 * x z0 ≤ ∑ j, R.P c z0 j * x j :=
    Finset.single_le_sum (f := fun j => R.P c z0 j * x j)
      (fun j _ => mul_nonneg (hS.P_nn c hc z0 j) (hx j)) (Finset.mem_univ z0)
  show 0 < ∑ j, R.P c z0 j * x j
  linarith

end Pull

/-! ### The certificate -/

/-- Kept hull points per class, and one witness per candidate.  `KB s c`: bundles of `c`
branches with `s` vertices in total; `KH m`: planted branches on `m` vertices. -/
structure Cert (D : ℕ) where
  KB : ℕ → ℕ → List (Vec D)
  KH : ℕ → List (Vec D)
  WB : ℕ → ℕ → List Wit
  WH : ℕ → List Wit

/-- Every candidate of the bundle class `(s, c)`: a kept bundle of `(s - j, c - 1)` joined with
a kept branch on `j` vertices, for every `j = 1..s`. -/
def candB (R : Rec D) (C : Cert D) (s c : ℕ) : List (Vec D) :=
  if c = 0 then (if s = 0 then [R.e] else [])
  else (List.range s).flatMap fun j' =>
    (C.KB (s - (j' + 1)) (c - 1)).flatMap fun p => (C.KH (j' + 1)).map fun q => R.mul p q

/-- Every candidate of the branch class `m`: a kept bundle of `(m - 1, c)`, planted. -/
def candH (R : Rec D) (C : Cert D) (m : ℕ) : List (Vec D) :=
  (List.range m).flatMap fun c => (C.KB (m - 1) c).map fun p => R.plant c p

/-- The decidable certificate: every candidate of every class below `N` carries a checked
witness, and every kept point is nonnegative with a positive `z0` coordinate. -/
abbrev Cert.Valid (R : Rec D) (C : Cert D) (N : ℕ) (z0 : Fin D) : Prop :=
  (∀ s < N, ∀ c ≤ s, List.Forall₂ (WitOK (C.KB s c)) (candB R C s c) (C.WB s c)) ∧
  (∀ m < N, 1 ≤ m → List.Forall₂ (WitOK (C.KH m)) (candH R C m) (C.WH m)) ∧
  (∀ s < N, ∀ c ≤ s, ∀ p ∈ C.KB s c, (∀ i, 0 ≤ p i) ∧ 0 < p z0) ∧
  (∀ m < N, 1 ≤ m → ∀ p ∈ C.KH m, (∀ i, 0 ≤ p i) ∧ 0 < p z0)

section Main

variable {R : Rec D} {C : Cert D} {N : ℕ} {z0 : Fin D}

theorem candB_sound (hC : C.Valid R N z0) {s c : ℕ} (hs : s < N) (hc : c ≤ s) :
    ∀ x ∈ candB R C s c, (x ∈ C.KB s c ∨ SDom (C.KB s c) x) ∧ Dom (C.KB s c) x := by
  intro x hx
  obtain ⟨w, hw⟩ := forall2_exists (hC.1 s hs c hc) x hx
  exact witOK_sound hw

theorem candH_sound (hC : C.Valid R N z0) {m : ℕ} (hm : m < N) (hm1 : 1 ≤ m) :
    ∀ x ∈ candH R C m, (x ∈ C.KH m ∨ SDom (C.KH m) x) ∧ Dom (C.KH m) x := by
  intro x hx
  obtain ⟨w, hw⟩ := forall2_exists (hC.2.1 m hm hm1) x hx
  exact witOK_sound hw

theorem mem_candB {s c j : ℕ} (hc : 1 ≤ c) (hj : 1 ≤ j) (hjs : j ≤ s) {p q : Vec D}
    (hp : p ∈ C.KB (s - j) (c - 1)) (hq : q ∈ C.KH j) : R.mul p q ∈ candB R C s c := by
  unfold candB
  rw [if_neg (by omega)]
  refine List.mem_flatMap.2 ⟨j - 1, List.mem_range.2 (by omega), ?_⟩
  have e : j - 1 + 1 = j := by omega
  rw [e]
  exact List.mem_flatMap.2 ⟨p, hp, List.mem_map.2 ⟨q, hq, rfl⟩⟩

theorem mem_candH {m c : ℕ} (hc : c < m) {p : Vec D} (hp : p ∈ C.KB (m - 1) c) :
    R.plant c p ∈ candH R C m :=
  List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, List.mem_map.2 ⟨p, hp, rfl⟩⟩

theorem RTree.size_pos (t : RTree) : 1 ≤ t.size := by
  cases t; simp [RTree.size]

/-- The value invariant of a class: nonnegative, positive `z0` coordinate, weakly dominated. -/
def Inv (z0 : Fin D) (K : List (Vec D)) (x : Vec D) : Prop :=
  (∀ i, 0 ≤ x i) ∧ 0 < x z0 ∧ Dom K x

mutual
/-- THE INDUCTION (weak part), branches. -/
theorem inv_branch (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ t : RTree, t.size < N → Inv z0 (C.KH t.size) (R.branch t)
  | .node l, h => by
    have hl : RTree.sizeL l < N := by simp only [RTree.size] at h; omega
    obtain ⟨h1, h2, h3⟩ := inv_bundle hS hC l hl
    have hlen := RTree.length_le_sizeL l
    have hcN : l.length < N := by omega
    simp only [Rec.branch, RTree.size]
    refine ⟨plant_nn (hS.P_nn _ hcN) h1, plant_pos0 hS hcN h1 h2, ?_⟩
    refine plant_dom hS hcN h3 fun p hp => ?_
    have hm := mem_candH (R := R) (m := RTree.sizeL l + 1) (c := l.length) (by omega)
      (by simpa using hp)
    exact (candH_sound hC (by simp only [RTree.size] at h; omega) (by omega) _ hm).2

/-- THE INDUCTION (weak part), bundles. -/
theorem inv_bundle (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ l : List RTree, RTree.sizeL l < N →
      Inv z0 (C.KB (RTree.sizeL l) l.length) (R.bundle l)
  | [], h => by
    simp only [Rec.bundle, RTree.sizeL, List.length_nil]
    refine ⟨hS.e_nn, hS.e_pos, ?_⟩
    exact (candB_sound (s := 0) (c := 0) hC (by simpa [RTree.sizeL] using h) le_rfl R.e
      (by simp [candB])).2
  | t :: l, h => by
    have ht0 := RTree.size_pos t
    have ht : t.size < N := by simp only [RTree.sizeL] at h; omega
    have hl : RTree.sizeL l < N := by simp only [RTree.sizeL] at h; omega
    obtain ⟨x1, x2, x3⟩ := inv_bundle hS hC l hl
    obtain ⟨z1, z2, z3⟩ := inv_branch hS hC t ht
    have hlen := RTree.length_le_sizeL l
    simp only [Rec.bundle, RTree.sizeL, List.length_cons]
    refine ⟨mul_nn hS.T_nn x1 z1, mul_pos0 hS x1 z1 x2 z2, ?_⟩
    refine mul_dom hS x3 z3 z1 (fun p hp => (hC.2.2.1 _ hl _ hlen p hp).1) fun p hp q hq => ?_
    have hm := mem_candB (R := R) (C := C) (s := t.size + RTree.sizeL l)
      (c := l.length + 1) (j := t.size) (by omega) ht0 (by omega)
      (by simpa using hp) hq
    exact (candB_sound hC (by simpa [RTree.sizeL] using h) (by omega) _ hm).2
end

mutual
/-- A tree whose every branch value and every partial bundle value is a KEPT hull point. -/
def KeptT (R : Rec D) (C : Cert D) : RTree → Prop
  | .node l => KeptL R C l ∧ R.branch (.node l) ∈ C.KH (RTree.sizeL l + 1)
/-- The same for a list of children (all partial bundles kept). -/
def KeptL (R : Rec D) (C : Cert D) : List RTree → Prop
  | [] => R.e ∈ C.KB 0 0
  | t :: l => KeptT R C t ∧ KeptL R C l ∧
      R.bundle (t :: l) ∈ C.KB (t.size + RTree.sizeL l) (l.length + 1)
end

theorem keptL_mem {l : List RTree} (h : KeptL R C l) :
    R.bundle l ∈ C.KB (RTree.sizeL l) l.length := by
  cases l with
  | nil => simpa [Rec.bundle, RTree.sizeL, KeptL] using h
  | cons t l => simpa [RTree.sizeL, KeptL] using h.2.2

theorem keptT_mem {t : RTree} (h : KeptT R C t) : R.branch t ∈ C.KH t.size := by
  cases t with
  | node l => simpa [RTree.size, KeptT] using h.2

mutual
/-- THE INDUCTION (strict part), branches: a branch is kept all the way down, or its value
is strictly dominated in its class. -/
theorem kept_branch (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ t : RTree, t.size < N → KeptT R C t ∨ SDom (C.KH t.size) (R.branch t)
  | .node l, h => by
    have hl : RTree.sizeL l < N := by simp only [RTree.size] at h; omega
    have hlen := RTree.length_le_sizeL l
    have hcN : l.length < N := by omega
    have hmN : RTree.sizeL l + 1 < N := by simp only [RTree.size] at h; omega
    have hcand : ∀ p ∈ C.KB (RTree.sizeL l) l.length,
        (R.plant l.length p ∈ C.KH (RTree.sizeL l + 1) ∨
          SDom (C.KH (RTree.sizeL l + 1)) (R.plant l.length p)) ∧
        Dom (C.KH (RTree.sizeL l + 1)) (R.plant l.length p) := fun p hp =>
      candH_sound hC hmN (by omega) _
        (mem_candH (R := R) (m := RTree.sizeL l + 1) (c := l.length) (by omega)
          (by simpa using hp))
    simp only [RTree.size]
    rcases kept_bundle hS hC l hl with hk | hsd
    · rcases (hcand _ (keptL_mem hk)).1 with hm | hsd'
      · exact Or.inl ⟨hk, hm⟩
      · exact Or.inr hsd'
    · exact Or.inr (plant_sdom hS hcN hsd fun p hp => (hcand p hp).2)

/-- THE INDUCTION (strict part), bundles. -/
theorem kept_bundle (hS : R.Signs N z0) (hC : C.Valid R N z0) :
    ∀ l : List RTree, RTree.sizeL l < N →
      KeptL R C l ∨ SDom (C.KB (RTree.sizeL l) l.length) (R.bundle l)
  | [], h => by
    simp only [Rec.bundle, RTree.sizeL, List.length_nil, KeptL]
    exact (candB_sound (s := 0) (c := 0) hC (by simpa [RTree.sizeL] using h) le_rfl R.e
      (by simp [candB])).1
  | t :: l, h => by
    have ht0 := RTree.size_pos t
    have ht : t.size < N := by simp only [RTree.sizeL] at h; omega
    have hl : RTree.sizeL l < N := by simp only [RTree.sizeL] at h; omega
    have hlen := RTree.length_le_sizeL l
    obtain ⟨x1, x2, x3⟩ := inv_bundle hS hC l hl
    obtain ⟨z1, z2, z3⟩ := inv_branch hS hC t ht
    have hsN : t.size + RTree.sizeL l < N := by simpa [RTree.sizeL] using h
    have hcand : ∀ p ∈ C.KB (RTree.sizeL l) l.length, ∀ q ∈ C.KH t.size,
        (R.mul p q ∈ C.KB (t.size + RTree.sizeL l) (l.length + 1) ∨
          SDom (C.KB (t.size + RTree.sizeL l) (l.length + 1)) (R.mul p q)) ∧
        Dom (C.KB (t.size + RTree.sizeL l) (l.length + 1)) (R.mul p q) := fun p hp q hq =>
      candB_sound hC hsN (by omega) _
        (mem_candB (R := R) (C := C) (s := t.size + RTree.sizeL l) (c := l.length + 1)
          (j := t.size) (by omega) ht0 (by omega) (by simpa using hp) hq)
    have hK1 : ∀ p ∈ C.KB (RTree.sizeL l) l.length, ∀ i, 0 ≤ p i :=
      fun p hp => (hC.2.2.1 _ hl _ hlen p hp).1
    simp only [Rec.bundle, RTree.sizeL, List.length_cons, KeptL]
    rcases kept_bundle hS hC l hl with hk | hsd
    · have hxm := keptL_mem hk
      rcases kept_branch hS hC t ht with hkt | hsdt
      · rcases (hcand _ hxm _ (keptT_mem hkt)).1 with hm | hsd'
        · exact Or.inl ⟨hkt, hk, hm⟩
        · exact Or.inr hsd'
      · exact Or.inr (mul_sdom_right hS hxm x1 x2 hsdt fun p hp q hq => (hcand p hp q hq).2)
    · exact Or.inr (mul_sdom_left hS hsd z3 z1 z2 hK1 fun p hp q hq => (hcand p hp q hq).2)
end

/-- UPPER BOUND.  Every tree on `n ≤ N` vertices has `pi ≤ v`, as soon as every kept root
bundle has root value at most `v`. -/
theorem pi_le (hS : R.Signs N z0) (hC : C.Valid R N z0) {n : ℕ} (hn : n ≤ N) (hn2 : 2 ≤ n)
    {v : ℚ} (hF : ∀ k, 1 ≤ k → k < n → ∀ i, 0 ≤ R.F k i)
    (hV : ∀ k, 1 ≤ k → k < n → ∀ p ∈ C.KB (n - 1) k, R.root k p ≤ v) :
    ∀ T : RTree, T.size = n → R.pi T ≤ v
  | .node l, h => by
    simp only [RTree.size] at h
    have hl : RTree.sizeL l < N := by omega
    have hlen := RTree.length_le_sizeL l
    have hk1 : 1 ≤ l.length := by
      cases l with
      | nil => simp [RTree.sizeL] at h; omega
      | cons _ _ => simp
    obtain ⟨_, _, h3⟩ := inv_bundle hS hC l hl
    obtain ⟨p, hp, hle⟩ := h3 (R.F l.length) (hF _ hk1 (by omega))
    have hs : RTree.sizeL l = n - 1 := by omega
    rw [hs] at hp
    have := hV _ hk1 (by omega) p hp
    simp only [Rec.pi, Rec.root] at this ⊢
    linarith

/-- MAXIMIZERS.  If the root functionals are strictly positive, a tree attaining `v` has every
branch value and every partial bundle value on the kept hull points. -/
theorem kept_of_pi_eq (hS : R.Signs N z0) (hC : C.Valid R N z0) {n : ℕ} (hn : n ≤ N)
    (hn2 : 2 ≤ n) {v : ℚ} (hF : ∀ k, 1 ≤ k → k < n → ∀ i, 0 < R.F k i)
    (hV : ∀ k, 1 ≤ k → k < n → ∀ p ∈ C.KB (n - 1) k, R.root k p ≤ v) :
    ∀ l : List RTree, (RTree.node l).size = n → R.pi (.node l) = v →
      KeptL R C l ∧ R.bundle l ∈ C.KB (n - 1) l.length := by
  intro l h hpi
  simp only [RTree.size] at h
  have hl : RTree.sizeL l < N := by omega
  have hlen := RTree.length_le_sizeL l
  have hk1 : 1 ≤ l.length := by
    cases l with
    | nil => simp [RTree.sizeL] at h; omega
    | cons _ _ => simp
  have hs : RTree.sizeL l = n - 1 := by omega
  rcases kept_bundle hS hC l hl with hk | hsd
  · exact ⟨hk, hs ▸ keptL_mem hk⟩
  · exfalso
    obtain ⟨p, hp, hlt⟩ := hsd (R.F l.length) (hF _ hk1 (by omega))
    rw [hs] at hp
    have := hV _ hk1 (by omega) p hp
    simp only [Rec.pi, Rec.root] at hpi this
    linarith

/-- EXACT MAXIMUM: the upper bound together with one tree attaining it. -/
theorem isGreatest_pi (hS : R.Signs N z0) (hC : C.Valid R N z0) {n : ℕ} (hn : n ≤ N)
    (hn2 : 2 ≤ n) {v : ℚ} (hF : ∀ k, 1 ≤ k → k < n → ∀ i, 0 ≤ R.F k i)
    (hV : ∀ k, 1 ≤ k → k < n → ∀ p ∈ C.KB (n - 1) k, R.root k p ≤ v)
    (Tw : RTree) (hTw : Tw.size = n ∧ R.pi Tw = v) :
    IsGreatest {x | ∃ T : RTree, T.size = n ∧ R.pi T = x} v :=
  ⟨⟨Tw, hTw⟩, by
    rintro x ⟨T, hT, rfl⟩
    exact pi_le hS hC hn hn2 hF hV T hT⟩

end Main

end HullDom

open HullDom

/-! ## Instance `matching_sum`: the Randic-weighted matching sum

Dimension 2, trees on n = 2..14 vertices, 222 kept points, 1290 candidate witnesses.
Certified values: M_2 = 2, M_3 = 2, M_4 = 5/2, M_5 = 3, M_6 = 29/8, M_7 = 9/2, M_8 = 43/8, M_9 = 27/4, M_10 = 65/8, M_11 = 81/8, M_12 = 783/64, M_13 = 243/16, M_14 = 9477/512. -/

/-- The recursion. -/
def matching_sum_R : Rec 2 where
  e := ![1, 0]
  T := fun i j l => (![![![1, 0], ![0, 0]], ![![0, 1], ![1, 0]]] : Fin 2 → Fin 2 → Fin 2 → ℚ) i j l
  P := fun c => ![![1, ((1 + (c : ℚ)))⁻¹], ![((1 + (c : ℚ)))⁻¹, 0]]
  F := fun k => ![1, ((k : ℚ))⁻¹]

/-- Kept bundle points, indexed [s][c]. -/
def matching_sum_KBt : List (List (List (Vec 2))) := [
  [[![1, 0]]],
  [[], [![1, 1]]],
  [[], [![(3/2 : ℚ), (1/2 : ℚ)]], [![1, 2]]],
  [[], [![(7/4 : ℚ), (3/4 : ℚ)]], [![(3/2 : ℚ), 2]], [![1, 3]]],
  [[], [![(17/8 : ℚ), (7/8 : ℚ)], ![(13/6 : ℚ), (1/2 : ℚ)]], [![(7/4 : ℚ), (5/2 : ℚ)], ![(9/4 : ℚ), (3/2 : ℚ)]], [![(3/2 : ℚ), (7/2 : ℚ)]], [![1, 4]]],
  [[], [![(29/12 : ℚ), (13/12 : ℚ)], ![(41/16 : ℚ), (17/16 : ℚ)], ![(11/4 : ℚ), (3/4 : ℚ)]], [![(17/8 : ℚ), 3], ![(21/8 : ℚ), 2]], [![(7/4 : ℚ), (17/4 : ℚ)], ![(9/4 : ℚ), (15/4 : ℚ)]], [![(3/2 : ℚ), 5]], [![1, 5]]],
  [[], [![(25/8 : ℚ), (11/8 : ℚ)], ![(79/24 : ℚ), (7/8 : ℚ)]], [![(41/16 : ℚ), (29/8 : ℚ)], ![(11/4 : ℚ), (7/2 : ℚ)], ![(51/16 : ℚ), (19/8 : ℚ)], ![(13/4 : ℚ), (11/6 : ℚ)]], [![(17/8 : ℚ), (41/8 : ℚ)], ![(21/8 : ℚ), (37/8 : ℚ)], ![(27/8 : ℚ), (27/8 : ℚ)]], [![(9/4 : ℚ), 6]], [![(3/2 : ℚ), (13/2 : ℚ)]], [![1, 6]]],
  [[], [![(179/48 : ℚ), (79/48 : ℚ)], ![(61/16 : ℚ), (25/16 : ℚ)], ![(135/32 : ℚ), (27/32 : ℚ)]], [![(25/8 : ℚ), (9/2 : ℚ)], ![(79/24 : ℚ), (25/6 : ℚ)], ![(33/8 : ℚ), (5/2 : ℚ)]], [![(11/4 : ℚ), (25/4 : ℚ)], ![(51/16 : ℚ), (89/16 : ℚ)], ![(63/16 : ℚ), (69/16 : ℚ)]], [![(21/8 : ℚ), (29/4 : ℚ)], ![(27/8 : ℚ), (27/4 : ℚ)]], [![(9/4 : ℚ), (33/4 : ℚ)]], [![(3/2 : ℚ), 8]], [![1, 7]]],
  [[], [![(297/64 : ℚ), (135/64 : ℚ)], ![(119/24 : ℚ), (11/8 : ℚ)], ![(321/64 : ℚ), (63/64 : ℚ)]], [![(61/16 : ℚ), (43/8 : ℚ)], ![(135/32 : ℚ), (81/16 : ℚ)], ![(77/16 : ℚ), (27/8 : ℚ)], ![(79/16 : ℚ), (71/24 : ℚ)]], [![(25/8 : ℚ), (61/8 : ℚ)], ![(79/24 : ℚ), (179/24 : ℚ)], ![(33/8 : ℚ), (53/8 : ℚ)], ![(153/32 : ℚ), (165/32 : ℚ)], ![(39/8 : ℚ), (35/8 : ℚ)]], [![(11/4 : ℚ), 9], ![(51/16 : ℚ), (35/4 : ℚ)], ![(63/16 : ℚ), (33/4 : ℚ)], ![(81/16 : ℚ), (27/4 : ℚ)]], [![(27/8 : ℚ), (81/8 : ℚ)]], [![(9/4 : ℚ), (21/2 : ℚ)]], [![(3/2 : ℚ), (19/2 : ℚ)]], [![1, 8]]],
  [[], [![(705/128 : ℚ), (321/128 : ℚ)], ![(271/48 : ℚ), (119/48 : ℚ)], ![(513/80 : ℚ), (81/80 : ℚ)]], [![(297/64 : ℚ), (27/4 : ℚ)], ![(119/24 : ℚ), (19/3 : ℚ)], ![(405/64 : ℚ), (27/8 : ℚ)]], [![(135/32 : ℚ), (297/32 : ℚ)], ![(99/16 : ℚ), (93/16 : ℚ)]], [![(33/8 : ℚ), (43/4 : ℚ)], ![(153/32 : ℚ), (159/16 : ℚ)], ![(189/32 : ℚ), (135/16 : ℚ)]], [![(63/16 : ℚ), (195/16 : ℚ)], ![(81/16 : ℚ), (189/16 : ℚ)]], [![(27/8 : ℚ), (27/2 : ℚ)]], [![(9/4 : ℚ), (51/4 : ℚ)]], [![(3/2 : ℚ), 11]], [![1, 9]]],
  [[], [![(1107/160 : ℚ), (513/160 : ℚ)], ![(477/64 : ℚ), (135/64 : ℚ)], ![(489/64 : ℚ), (99/64 : ℚ)]], [![(271/48 : ℚ), (65/8 : ℚ)], ![(513/80 : ℚ), (297/40 : ℚ)], ![(119/16 : ℚ), (109/24 : ℚ)], ![(121/16 : ℚ), (33/8 : ℚ)]], [![(297/64 : ℚ), (729/64 : ℚ)], ![(119/24 : ℚ), (271/24 : ℚ)], ![(405/64 : ℚ), (621/64 : ℚ)], ![(231/32 : ℚ), (239/32 : ℚ)], ![(237/32 : ℚ), (221/32 : ℚ)]], [![(135/32 : ℚ), (27/2 : ℚ)], ![(99/16 : ℚ), 12], ![(459/64 : ℚ), (81/8 : ℚ)], ![(117/16 : ℚ), 9]], [![(33/8 : ℚ), (119/8 : ℚ)], ![(153/32 : ℚ), (471/32 : ℚ)], ![(189/32 : ℚ), (459/32 : ℚ)], ![(243/32 : ℚ), (405/32 : ℚ)]], [![(81/16 : ℚ), (135/8 : ℚ)]], [![(27/8 : ℚ), (135/8 : ℚ)]], [![(9/4 : ℚ), 15]], [![(3/2 : ℚ), (25/2 : ℚ)]], [![1, 10]]],
  [[], [![(1077/128 : ℚ), (489/128 : ℚ)], ![(1089/128 : ℚ), (477/128 : ℚ)], ![(621/64 : ℚ), (81/64 : ℚ)]], [![(1107/160 : ℚ), (81/8 : ℚ)], ![(477/64 : ℚ), (153/16 : ℚ)], ![(489/64 : ℚ), (147/16 : ℚ)], ![(1539/160 : ℚ), (189/40 : ℚ)]], [![(513/80 : ℚ), (1107/80 : ℚ)], ![(119/16 : ℚ), (575/48 : ℚ)], ![(1215/128 : ℚ), (1053/128 : ℚ)]], [![(119/24 : ℚ), (65/4 : ℚ)], ![(405/64 : ℚ), (513/32 : ℚ)], ![(297/32 : ℚ), (189/16 : ℚ)]], [![(99/16 : ℚ), (291/16 : ℚ)], ![(459/64 : ℚ), (1107/64 : ℚ)], ![(567/64 : ℚ), (999/64 : ℚ)]], [![(243/32 : ℚ), (81/4 : ℚ)]], [![(81/16 : ℚ), (351/16 : ℚ)]], [![(27/8 : ℚ), (81/4 : ℚ)]], [![(9/4 : ℚ), (69/4 : ℚ)]], [![(3/2 : ℚ), 14]], [![1, 11]]],
  [[], [![(1323/128 : ℚ), (621/128 : ℚ)], ![(1791/160 : ℚ), (513/160 : ℚ)], ![(5913/512 : ℚ), (1215/512 : ℚ)], ![(1863/160 : ℚ), (297/160 : ℚ)]], [![(1089/128 : ℚ), (783/64 : ℚ)], ![(621/64 : ℚ), (351/32 : ℚ)], ![(1467/128 : ℚ), (393/64 : ℚ)], ![(1485/128 : ℚ), (351/64 : ℚ)]], [![(1107/160 : ℚ), (2727/160 : ℚ)], ![(477/64 : ℚ), (1089/64 : ℚ)], ![(489/64 : ℚ), (1077/64 : ℚ)], ![(1539/160 : ℚ), (459/32 : ℚ)], ![(357/32 : ℚ), (337/32 : ℚ)], ![(363/32 : ℚ), (319/32 : ℚ)]], [![(513/80 : ℚ), (81/4 : ℚ)], ![(119/16 : ℚ), (233/12 : ℚ)], ![(1215/128 : ℚ), (567/32 : ℚ)], ![(693/64 : ℚ), (237/16 : ℚ)], ![(711/64 : ℚ), (225/16 : ℚ)]], [![(405/64 : ℚ), (1431/64 : ℚ)], ![(297/32 : ℚ), (675/32 : ℚ)], ![(1377/128 : ℚ), (2403/128 : ℚ)], ![(351/32 : ℚ), (549/32 : ℚ)]], [![(567/64 : ℚ), (783/32 : ℚ)], ![(729/64 : ℚ), (729/32 : ℚ)]], [![(243/32 : ℚ), (891/32 : ℚ)]], [![(81/16 : ℚ), 27]], [![(27/8 : ℚ), (189/8 : ℚ)]], [![(9/4 : ℚ), (39/2 : ℚ)]], [![(3/2 : ℚ), (31/2 : ℚ)]], [![1, 12]]],
  [[], [![(4023/320 : ℚ), (1863/320 : ℚ)], ![(13041/1024 : ℚ), (5913/1024 : ℚ)], ![(6561/448 : ℚ), (729/448 : ℚ)]], [![(1323/128 : ℚ), (243/16 : ℚ)], ![(1791/160 : ℚ), (72/5 : ℚ)], ![(5913/512 : ℚ), (891/64 : ℚ)], ![(1863/128 : ℚ), (27/4 : ℚ)]], [![(1089/128 : ℚ), (2655/128 : ℚ)], ![(621/64 : ℚ), (1323/64 : ℚ)], ![(1467/128 : ℚ), (2253/128 : ℚ)], ![(4617/320 : ℚ), (3807/320 : ℚ)]], [![(489/64 : ℚ), (783/32 : ℚ)], ![(1539/160 : ℚ), (1917/80 : ℚ)], ![(357/32 : ℚ), (347/16 : ℚ)], ![(3645/256 : ℚ), (2187/128 : ℚ)]], [![(1215/128 : ℚ), (3483/128 : ℚ)], ![(891/64 : ℚ), (1431/64 : ℚ)]], [![(297/32 : ℚ), (243/8 : ℚ)], ![(1377/128 : ℚ), (945/32 : ℚ)], ![(1701/128 : ℚ), (891/32 : ℚ)]], [![(729/64 : ℚ), (2187/64 : ℚ)]], [![(243/32 : ℚ), (567/16 : ℚ)]], [![(81/16 : ℚ), (513/16 : ℚ)]], [![(27/8 : ℚ), 27]], [![(9/4 : ℚ), (87/4 : ℚ)]], [![(3/2 : ℚ), 17]], [![1, 13]]]]

/-- Kept branch points, indexed [m]. -/
def matching_sum_KHt : List (List (Vec 2)) := [
  [],
  [![1, 1]],
  [![(3/2 : ℚ), (1/2 : ℚ)]],
  [![(7/4 : ℚ), (3/4 : ℚ)]],
  [![(17/8 : ℚ), (7/8 : ℚ)], ![(13/6 : ℚ), (1/2 : ℚ)]],
  [![(29/12 : ℚ), (13/12 : ℚ)], ![(41/16 : ℚ), (17/16 : ℚ)], ![(11/4 : ℚ), (3/4 : ℚ)]],
  [![(25/8 : ℚ), (11/8 : ℚ)], ![(79/24 : ℚ), (7/8 : ℚ)]],
  [![(179/48 : ℚ), (79/48 : ℚ)], ![(61/16 : ℚ), (25/16 : ℚ)], ![(135/32 : ℚ), (27/32 : ℚ)]],
  [![(297/64 : ℚ), (135/64 : ℚ)], ![(119/24 : ℚ), (11/8 : ℚ)], ![(321/64 : ℚ), (63/64 : ℚ)]],
  [![(705/128 : ℚ), (321/128 : ℚ)], ![(271/48 : ℚ), (119/48 : ℚ)], ![(513/80 : ℚ), (81/80 : ℚ)]],
  [![(1107/160 : ℚ), (513/160 : ℚ)], ![(477/64 : ℚ), (135/64 : ℚ)], ![(489/64 : ℚ), (99/64 : ℚ)]],
  [![(1077/128 : ℚ), (489/128 : ℚ)], ![(1089/128 : ℚ), (477/128 : ℚ)], ![(621/64 : ℚ), (81/64 : ℚ)]],
  [![(1323/128 : ℚ), (621/128 : ℚ)], ![(1791/160 : ℚ), (513/160 : ℚ)], ![(5913/512 : ℚ), (1215/512 : ℚ)], ![(1863/160 : ℚ), (297/160 : ℚ)]],
  [![(4023/320 : ℚ), (1863/320 : ℚ)], ![(13041/1024 : ℚ), (5913/1024 : ℚ)], ![(6561/448 : ℚ), (729/448 : ℚ)]]]

/-- Bundle candidate witnesses, in `candB` order. -/
def matching_sum_WBt : List (List (List Wit)) := [
  [[.kept 0]],
  [[], [.kept 0]],
  [[], [.kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1], [.kept 0, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .dom [(11/12 : ℚ), (1/12 : ℚ)], .kept 1, .kept 1, .kept 0, .dom [(11/12 : ℚ), (1/12 : ℚ)]], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1], [.dom [1, 0, 0, 0], .kept 0, .kept 1, .kept 2, .kept 3, .dom [0, (2/7 : ℚ), (5/7 : ℚ), 0], .kept 2, .kept 3, .dom [1, 0, 0, 0], .kept 0, .kept 1], [.kept 0, .kept 1, .kept 1, .kept 2, .kept 1, .kept 0, .dom [(11/12 : ℚ), (1/12 : ℚ), 0]], [.dom [1], .kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .dom [0, (3/5 : ℚ), (2/5 : ℚ)], .dom [0, (27/80 : ℚ), (53/80 : ℚ)], .kept 2, .dom [0, (39/80 : ℚ), (41/80 : ℚ)], .dom [0, 0, 1], .dom [0, (39/80 : ℚ), (41/80 : ℚ)], .dom [0, 0, 1], .dom [0, (3/5 : ℚ), (2/5 : ℚ)], .dom [0, (27/80 : ℚ), (53/80 : ℚ)], .kept 2, .kept 0, .kept 1], [.dom [1, 0, 0], .kept 0, .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .kept 1, .kept 2, .dom [(2/7 : ℚ), (5/7 : ℚ), 0], .kept 2, .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .kept 0], [.dom [1, 0], .kept 0, .kept 1, .kept 0, .kept 1, .kept 0, .dom [1, 0], .dom [1, 0]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.dom [1, 0, 0, 0], .kept 0, .kept 1, .dom [0, (4/19 : ℚ), (15/19 : ℚ), 0], .kept 3, .dom [0, (56/57 : ℚ), (1/57 : ℚ), 0], .dom [0, (21/38 : ℚ), (17/38 : ℚ), 0], .kept 2, .dom [0, (1/2 : ℚ), (1/2 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, (56/57 : ℚ), (1/57 : ℚ), 0], .dom [0, (21/38 : ℚ), (17/38 : ℚ), 0], .kept 2, .dom [0, (4/19 : ℚ), (15/19 : ℚ), 0], .kept 3, .dom [1, 0, 0, 0], .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .dom [0, (27/80 : ℚ), (53/80 : ℚ), 0, 0], .kept 2, .kept 3, .kept 4, .dom [0, (39/80 : ℚ), (41/80 : ℚ), 0, 0], .dom [0, 0, (2/7 : ℚ), (5/7 : ℚ), 0], .dom [0, (39/80 : ℚ), (41/80 : ℚ), 0, 0], .dom [0, 0, 1, 0, 0], .kept 3, .kept 4, .dom [0, 0, 1, 0, 0], .dom [0, (27/80 : ℚ), (53/80 : ℚ), 0, 0], .kept 2, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 3, .dom [0, 1, 0, 0], .kept 2, .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ), 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .kept 0], [.dom [1], .kept 0, .kept 0, .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .dom [0, (252/263 : ℚ), (11/263 : ℚ)], .dom [0, (141/263 : ℚ), (122/263 : ℚ)], .dom [0, (117/263 : ℚ), (146/263 : ℚ)], .kept 2, .dom [0, (165/263 : ℚ), (98/263 : ℚ)], .dom [0, (109/263 : ℚ), (154/263 : ℚ)], .dom [0, (229/263 : ℚ), (34/263 : ℚ)], .dom [0, (629/789 : ℚ), (160/789 : ℚ)], .dom [0, (339/526 : ℚ), (187/526 : ℚ)], .dom [0, (149/263 : ℚ), (114/263 : ℚ)], .dom [0, (93/263 : ℚ), (170/263 : ℚ)], .dom [0, 0, 1], .dom [0, (229/263 : ℚ), (34/263 : ℚ)], .dom [0, (339/526 : ℚ), (187/526 : ℚ)], .dom [0, (93/263 : ℚ), (170/263 : ℚ)], .dom [0, (629/789 : ℚ), (160/789 : ℚ)], .dom [0, (149/263 : ℚ), (114/263 : ℚ)], .dom [0, 0, 1], .dom [0, (165/263 : ℚ), (98/263 : ℚ)], .dom [0, (109/263 : ℚ), (154/263 : ℚ)], .dom [0, (141/263 : ℚ), (122/263 : ℚ)], .dom [0, (117/263 : ℚ), (146/263 : ℚ)], .kept 2, .kept 0, .kept 1, .dom [0, (252/263 : ℚ), (11/263 : ℚ)]], [.dom [1, 0], .kept 0, .dom [(44/63 : ℚ), (19/63 : ℚ)], .dom [(40/63 : ℚ), (23/63 : ℚ)], .dom [(16/21 : ℚ), (5/21 : ℚ)], .dom [(40/63 : ℚ), (23/63 : ℚ)], .kept 1, .dom [(109/126 : ℚ), (17/126 : ℚ)], .dom [(44/63 : ℚ), (19/63 : ℚ)], .dom [(13/42 : ℚ), (29/42 : ℚ)], .dom [0, 1], .dom [(107/126 : ℚ), (19/126 : ℚ)], .dom [(152/189 : ℚ), (37/189 : ℚ)], .dom [(13/42 : ℚ), (29/42 : ℚ)], .dom [0, 1], .dom [(188/189 : ℚ), (1/189 : ℚ)], .dom [(109/126 : ℚ), (17/126 : ℚ)], .dom [(44/63 : ℚ), (19/63 : ℚ)], .dom [(8/21 : ℚ), (13/21 : ℚ)], .dom [(3/14 : ℚ), (11/14 : ℚ)], .kept 1, .dom [(16/21 : ℚ), (5/21 : ℚ)], .dom [(40/63 : ℚ), (23/63 : ℚ)], .dom [1, 0], .dom [1, 0], .kept 0], [.dom [1, 0, 0], .dom [1, 0, 0], .kept 0, .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .kept 0, .kept 1, .kept 2, .dom [1, 0, 0], .dom [(2/7 : ℚ), (5/7 : ℚ), 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .kept 0, .dom [1, 0, 0], .dom [1, 0, 0]], [.dom [1, 0], .dom [1, 0], .kept 0, .kept 1, .kept 0, .kept 1, .kept 0, .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.dom [1, 0, 0, 0], .kept 0, .kept 1, .dom [0, (305/656 : ℚ), (351/656 : ℚ), 0], .kept 2, .dom [0, 0, 0, 1], .dom [0, (875/984 : ℚ), (109/984 : ℚ), 0], .dom [0, (245/328 : ℚ), (83/328 : ℚ), 0], .dom [0, (35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, (255/328 : ℚ), (73/328 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, (425/984 : ℚ), (559/984 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, (95/123 : ℚ), (28/123 : ℚ), 0], .dom [0, 1, 0, 0], .dom [0, (1115/1312 : ℚ), (197/1312 : ℚ), 0], .dom [0, (125/328 : ℚ), (203/328 : ℚ), 0], .dom [0, (95/123 : ℚ), (28/123 : ℚ), 0], .dom [0, (125/328 : ℚ), (203/328 : ℚ), 0], .kept 3, .dom [0, (255/328 : ℚ), (73/328 : ℚ), 0], .dom [0, (425/984 : ℚ), (559/984 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, (875/984 : ℚ), (109/984 : ℚ), 0], .dom [0, (245/328 : ℚ), (83/328 : ℚ), 0], .dom [0, (35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, (305/656 : ℚ), (351/656 : ℚ), 0], .kept 2, .dom [0, 0, 0, 1], .dom [1, 0, 0, 0], .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .dom [0, (117/263 : ℚ), (146/263 : ℚ), 0, 0], .kept 2, .kept 3, .kept 4, .dom [0, (165/263 : ℚ), (98/263 : ℚ), 0, 0], .dom [0, (109/263 : ℚ), (154/263 : ℚ), 0, 0], .kept 3, .dom [0, (339/526 : ℚ), (187/526 : ℚ), 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, (93/263 : ℚ), (170/263 : ℚ), 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, 0, (1/2 : ℚ), (1/2 : ℚ), 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 1, 0, 0], .dom [0, (339/526 : ℚ), (187/526 : ℚ), 0, 0], .dom [0, (93/263 : ℚ), (170/263 : ℚ), 0, 0], .dom [0, 0, (56/57 : ℚ), (1/57 : ℚ), 0], .dom [0, 0, (21/38 : ℚ), (17/38 : ℚ), 0], .kept 3, .dom [0, (165/263 : ℚ), (98/263 : ℚ), 0, 0], .dom [0, (109/263 : ℚ), (154/263 : ℚ), 0, 0], .dom [0, 0, (4/19 : ℚ), (15/19 : ℚ), 0], .kept 4, .dom [0, (141/263 : ℚ), (122/263 : ℚ), 0, 0], .dom [0, (117/263 : ℚ), (146/263 : ℚ), 0, 0], .kept 2, .kept 0, .kept 1, .dom [0, (252/263 : ℚ), (11/263 : ℚ), 0, 0]], [.kept 0, .kept 1, .dom [(16/21 : ℚ), (5/21 : ℚ), 0, 0], .dom [(40/63 : ℚ), (23/63 : ℚ), 0, 0], .kept 1, .kept 2, .kept 3, .dom [(44/63 : ℚ), (19/63 : ℚ), 0, 0], .dom [(13/42 : ℚ), (29/42 : ℚ), 0, 0], .dom [0, (2/7 : ℚ), (5/7 : ℚ), 0], .dom [(107/126 : ℚ), (19/126 : ℚ), 0, 0], .dom [(152/189 : ℚ), (37/189 : ℚ), 0, 0], .dom [(13/42 : ℚ), (29/42 : ℚ), 0, 0], .dom [0, 1, 0, 0], .kept 2, .kept 3, .dom [(188/189 : ℚ), (1/189 : ℚ), 0, 0], .dom [(109/126 : ℚ), (17/126 : ℚ), 0, 0], .dom [(44/63 : ℚ), (19/63 : ℚ), 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .kept 1, .dom [(16/21 : ℚ), (5/21 : ℚ), 0, 0], .dom [(40/63 : ℚ), (23/63 : ℚ), 0, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .kept 0], [.kept 0, .kept 1, .kept 2, .kept 0, .kept 1, .kept 2, .kept 3, .dom [0, 1, 0, 0], .kept 2, .kept 1, .dom [0, 0, 1, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .kept 0, .dom [1, 0, 0, 0], .dom [1, 0, 0, 0]], [.dom [1], .kept 0, .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .dom [0, 0, (579/844 : ℚ), (265/844 : ℚ)], .dom [0, 0, (368/633 : ℚ), (265/633 : ℚ)], .kept 3, .dom [0, 0, (639/844 : ℚ), (205/844 : ℚ)], .dom [0, 0, (904/1899 : ℚ), (995/1899 : ℚ)], .dom [0, 0, (359/844 : ℚ), (485/844 : ℚ)], .dom [0, 0, (3253/3798 : ℚ), (545/3798 : ℚ)], .dom [0, 0, (4432/5697 : ℚ), (1265/5697 : ℚ)], .dom [0, 0, (971/1266 : ℚ), (295/1266 : ℚ)], .dom [0, 0, (1304/1899 : ℚ), (595/1899 : ℚ)], .dom [0, 0, (279/844 : ℚ), (565/844 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, 1, 0], .dom [0, 0, (1031/1266 : ℚ), (235/1266 : ℚ)], .dom [0, 0, (328/633 : ℚ), (305/633 : ℚ)], .dom [0, 0, (4792/5697 : ℚ), (905/5697 : ℚ)], .dom [0, 0, (2273/3798 : ℚ), (1525/3798 : ℚ)], .dom [0, 0, (544/1899 : ℚ), (1355/1899 : ℚ)], .dom [0, 0, 1, 0], .dom [0, 0, (4792/5697 : ℚ), (905/5697 : ℚ)], .dom [0, 0, (1031/1266 : ℚ), (235/1266 : ℚ)], .dom [0, 0, (2273/3798 : ℚ), (1525/3798 : ℚ)], .dom [0, 0, (328/633 : ℚ), (305/633 : ℚ)], .dom [0, 0, (544/1899 : ℚ), (1355/1899 : ℚ)], .dom [0, 0, (3253/3798 : ℚ), (545/3798 : ℚ)], .dom [0, 0, (971/1266 : ℚ), (295/1266 : ℚ)], .dom [0, 0, (279/844 : ℚ), (565/844 : ℚ)], .dom [0, 0, (4432/5697 : ℚ), (1265/5697 : ℚ)], .dom [0, 0, (1304/1899 : ℚ), (595/1899 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, (639/844 : ℚ), (205/844 : ℚ)], .dom [0, 0, (904/1899 : ℚ), (995/1899 : ℚ)], .dom [0, 0, (359/844 : ℚ), (485/844 : ℚ)], .dom [0, 0, (579/844 : ℚ), (265/844 : ℚ)], .dom [0, 0, (368/633 : ℚ), (265/633 : ℚ)], .kept 3, .kept 0, .kept 1, .kept 2], [.dom [1, 0, 0], .kept 0, .kept 1, .dom [0, (247/263 : ℚ), (16/263 : ℚ)], .dom [(305/656 : ℚ), (351/656 : ℚ), 0], .kept 1, .kept 2, .dom [(245/328 : ℚ), (83/328 : ℚ), 0], .dom [(35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, (137/263 : ℚ), (126/263 : ℚ)], .dom [0, (109/263 : ℚ), (154/263 : ℚ)], .dom [(255/328 : ℚ), (73/328 : ℚ), 0], .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, (93/263 : ℚ), (170/263 : ℚ)], .dom [0, 0, 1], .dom [1, 0, 0], .dom [(1115/1312 : ℚ), (197/1312 : ℚ), 0], .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, (247/263 : ℚ), (16/263 : ℚ)], .dom [0, (229/263 : ℚ), (34/263 : ℚ)], .dom [0, (339/526 : ℚ), (187/526 : ℚ)], .dom [0, (93/263 : ℚ), (170/263 : ℚ)], .dom [0, 0, 1], .dom [0, 0, 1], .dom [0, 0, 1], .dom [(255/328 : ℚ), (73/328 : ℚ), 0], .dom [0, 1, 0], .dom [0, (165/263 : ℚ), (98/263 : ℚ)], .dom [0, (109/263 : ℚ), (154/263 : ℚ)], .dom [(875/984 : ℚ), (109/984 : ℚ), 0], .dom [(245/328 : ℚ), (83/328 : ℚ), 0], .dom [(35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, (141/263 : ℚ), (122/263 : ℚ)], .dom [0, (117/263 : ℚ), (146/263 : ℚ)], .kept 2, .dom [(305/656 : ℚ), (351/656 : ℚ), 0], .kept 1, .dom [0, (252/263 : ℚ), (11/263 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .kept 0], [.dom [1, 0, 0], .kept 0, .kept 1, .dom [0, (44/63 : ℚ), (19/63 : ℚ)], .dom [0, (40/63 : ℚ), (23/63 : ℚ)], .kept 1, .kept 2, .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, (44/63 : ℚ), (19/63 : ℚ)], .dom [0, (13/42 : ℚ), (29/42 : ℚ)], .dom [0, 0, 1], .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, (107/126 : ℚ), (19/126 : ℚ)], .dom [0, (152/189 : ℚ), (37/189 : ℚ)], .dom [0, (13/42 : ℚ), (29/42 : ℚ)], .dom [0, 0, 1], .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, (188/189 : ℚ), (1/189 : ℚ)], .dom [0, (109/126 : ℚ), (17/126 : ℚ)], .dom [0, (44/63 : ℚ), (19/63 : ℚ)], .dom [0, 0, 1], .dom [0, (3/14 : ℚ), (11/14 : ℚ)], .kept 2, .dom [0, 1, 0], .dom [0, 1, 0], .dom [0, (16/21 : ℚ), (5/21 : ℚ)], .dom [0, (40/63 : ℚ), (23/63 : ℚ)], .dom [0, 1, 0], .dom [0, 1, 0], .kept 1, .dom [1, 0, 0], .kept 0, .dom [0, 1, 0]], [.dom [1, 0, 0], .kept 0, .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .kept 0, .kept 1, .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [(2/7 : ℚ), (5/7 : ℚ), 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .kept 0, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]], [.dom [1], .dom [1], .dom [1], .kept 0, .dom [1], .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2, .kept 3], [.dom [1, 0, 0, 0], .kept 0, .kept 1, .dom [0, (77/125 : ℚ), (48/125 : ℚ), 0], .dom [0, (4/25 : ℚ), (21/25 : ℚ), 0], .kept 2, .dom [0, 1, 0, 0], .dom [0, (607/675 : ℚ), (68/675 : ℚ), 0], .dom [0, (17/125 : ℚ), (108/125 : ℚ), 0], .dom [0, (91/100 : ℚ), (9/100 : ℚ), 0], .dom [0, (4/5 : ℚ), (1/5 : ℚ), 0], .dom [0, (71/135 : ℚ), (64/135 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, (137/300 : ℚ), (163/300 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, (463/675 : ℚ), (212/675 : ℚ), 0], .dom [0, 1, 0, 0], .dom [0, (433/450 : ℚ), (17/450 : ℚ), 0], .dom [0, (5/9 : ℚ), (4/9 : ℚ), 0], .dom [0, (18/25 : ℚ), (7/25 : ℚ), 0], .dom [0, (37/100 : ℚ), (63/100 : ℚ), 0], .kept 3, .dom [0, (217/225 : ℚ), (8/225 : ℚ), 0], .dom [0, (451/675 : ℚ), (224/675 : ℚ), 0], .dom [0, (451/675 : ℚ), (224/675 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, (18/25 : ℚ), (7/25 : ℚ), 0], .dom [0, 1, 0, 0], .dom [0, (433/450 : ℚ), (17/450 : ℚ), 0], .dom [0, (37/100 : ℚ), (63/100 : ℚ), 0], .dom [0, (463/675 : ℚ), (212/675 : ℚ), 0], .dom [0, (5/9 : ℚ), (4/9 : ℚ), 0], .kept 3, .dom [0, (91/100 : ℚ), (9/100 : ℚ), 0], .dom [0, (71/135 : ℚ), (64/135 : ℚ), 0], .dom [0, (137/300 : ℚ), (163/300 : ℚ), 0], .dom [0, (4/5 : ℚ), (1/5 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, 1, 0, 0], .dom [0, (607/675 : ℚ), (68/675 : ℚ), 0], .dom [0, (17/125 : ℚ), (108/125 : ℚ), 0], .dom [0, (77/125 : ℚ), (48/125 : ℚ), 0], .dom [0, (4/25 : ℚ), (21/25 : ℚ), 0], .kept 2, .dom [1, 0, 0, 0], .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 3, .dom [0, 0, (368/633 : ℚ), (265/633 : ℚ), 0, 0], .kept 3, .kept 4, .kept 5, .dom [0, 0, (639/844 : ℚ), (205/844 : ℚ), 0, 0], .dom [0, 0, (904/1899 : ℚ), (995/1899 : ℚ), 0, 0], .dom [0, 0, 0, (35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, 0, (971/1266 : ℚ), (295/1266 : ℚ), 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, (279/844 : ℚ), (565/844 : ℚ), 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, 0, (595/984 : ℚ), (389/984 : ℚ), 0], .dom [0, 0, 0, 0, 1, 0], .dom [0, 0, 0, (425/984 : ℚ), (559/984 : ℚ), 0], .dom [0, 0, 0, 0, 1, 0], .dom [0, 0, 1, 0, 0, 0], .dom [0, 0, (1031/1266 : ℚ), (235/1266 : ℚ), 0, 0], .dom [0, 0, (328/633 : ℚ), (305/633 : ℚ), 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, 0, 0, 1, 0], .dom [0, 0, 0, (125/328 : ℚ), (203/328 : ℚ), 0], .kept 5, .dom [0, 0, (1031/1266 : ℚ), (235/1266 : ℚ), 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, (328/633 : ℚ), (305/633 : ℚ), 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, 0, (255/328 : ℚ), (73/328 : ℚ), 0], .dom [0, 0, 0, (425/984 : ℚ), (559/984 : ℚ), 0], .dom [0, 0, 0, 0, 1, 0], .dom [0, 0, 0, 0, 1, 0], .dom [0, 0, (3253/3798 : ℚ), (545/3798 : ℚ), 0, 0], .dom [0, 0, (971/1266 : ℚ), (295/1266 : ℚ), 0, 0], .dom [0, 0, (279/844 : ℚ), (565/844 : ℚ), 0, 0], .dom [0, 0, 0, (875/984 : ℚ), (109/984 : ℚ), 0], .dom [0, 0, 0, (245/328 : ℚ), (83/328 : ℚ), 0], .dom [0, 0, 0, (35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, 0, (639/844 : ℚ), (205/844 : ℚ), 0, 0], .dom [0, 0, (904/1899 : ℚ), (995/1899 : ℚ), 0, 0], .dom [0, 0, 0, 1, 0, 0], .dom [0, 0, 0, (305/656 : ℚ), (351/656 : ℚ), 0], .kept 4, .dom [0, 0, 0, 0, 0, 1], .dom [0, 0, (579/844 : ℚ), (265/844 : ℚ), 0, 0], .dom [0, 0, (368/633 : ℚ), (265/633 : ℚ), 0, 0], .kept 3, .kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .dom [0, 1, 0, 0, 0], .kept 1, .kept 2, .kept 3, .kept 4, .dom [0, 1, 0, 0, 0], .kept 3, .dom [0, 1, 0, 0, 0], .dom [0, 1, 0, 0, 0], .dom [0, 1, 0, 0, 0], .dom [0, 1, 0, 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, 0, (1/2 : ℚ), (1/2 : ℚ), 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, 1, 0], .dom [0, 1, 0, 0, 0], .dom [0, 1, 0, 0, 0], .dom [0, (247/263 : ℚ), (16/263 : ℚ), 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, (21/38 : ℚ), (17/38 : ℚ), 0], .kept 3, .dom [0, 1, 0, 0, 0], .dom [0, 1, 0, 0, 0], .dom [0, (165/263 : ℚ), (98/263 : ℚ), 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, 0, (4/19 : ℚ), (15/19 : ℚ), 0], .kept 4, .dom [0, 1, 0, 0, 0], .dom [0, 1, 0, 0, 0], .dom [0, 1, 0, 0, 0], .dom [0, 0, 1, 0, 0], .dom [0, (117/263 : ℚ), (146/263 : ℚ), 0, 0], .kept 2, .dom [0, 1, 0, 0, 0], .kept 1, .dom [0, (252/263 : ℚ), (11/263 : ℚ), 0, 0], .dom [1, 0, 0, 0, 0], .dom [1, 0, 0, 0, 0], .kept 0], [.dom [1, 0, 0, 0], .kept 0, .kept 1, .kept 0, .kept 1, .kept 2, .kept 3, .dom [(44/63 : ℚ), (19/63 : ℚ), 0, 0], .dom [0, 1, 0, 0], .dom [0, (2/7 : ℚ), (5/7 : ℚ), 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .dom [(107/126 : ℚ), (19/126 : ℚ), 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .kept 2, .kept 3, .dom [0, 1, 0, 0], .dom [(109/126 : ℚ), (17/126 : ℚ), 0, 0], .dom [(44/63 : ℚ), (19/63 : ℚ), 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .kept 1, .dom [(16/21 : ℚ), (5/21 : ℚ), 0, 0], .dom [(40/63 : ℚ), (23/63 : ℚ), 0, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .kept 0, .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0]], [.dom [1, 0], .dom [1, 0], .kept 0, .dom [1, 0], .dom [1, 0], .kept 0, .kept 1, .dom [1, 0], .kept 0, .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .dom [0, 0, (92/95 : ℚ), (3/95 : ℚ)], .dom [0, 0, (110/171 : ℚ), (61/171 : ℚ)], .dom [0, 0, (34/57 : ℚ), (23/57 : ℚ)], .kept 3, .dom [0, 0, (232/285 : ℚ), (53/285 : ℚ)], .dom [0, 0, (86/171 : ℚ), (85/171 : ℚ)], .dom [0, 0, (202/513 : ℚ), (311/513 : ℚ)], .dom [0, 0, (973/1026 : ℚ), (53/1026 : ℚ)], .dom [0, 0, (1342/1539 : ℚ), (197/1539 : ℚ)], .dom [0, 0, (3928/4617 : ℚ), (689/4617 : ℚ)], .dom [0, 0, (10700/13851 : ℚ), (3151/13851 : ℚ)], .dom [0, 0, (88/285 : ℚ), (197/285 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, 1, 0], .dom [0, 0, (101/114 : ℚ), (13/114 : ℚ)], .dom [0, 0, (34/57 : ℚ), (23/57 : ℚ)], .dom [0, 0, (11852/13851 : ℚ), (1999/13851 : ℚ)], .dom [0, 0, (2840/4617 : ℚ), (1777/4617 : ℚ)], .dom [0, 0, (1412/4617 : ℚ), (3205/4617 : ℚ)], .dom [0, 0, (1246/1539 : ℚ), (293/1539 : ℚ)], .dom [0, 0, (581/1026 : ℚ), (445/1026 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, (4456/4617 : ℚ), (161/4617 : ℚ)], .dom [0, 0, (10504/13851 : ℚ), (3347/13851 : ℚ)], .dom [0, 0, (1352/1539 : ℚ), (187/1539 : ℚ)], .dom [0, 0, (3080/4617 : ℚ), (1537/4617 : ℚ)], .dom [0, 0, (26/57 : ℚ), (31/57 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, (4456/4617 : ℚ), (161/4617 : ℚ)], .dom [0, 0, (1352/1539 : ℚ), (187/1539 : ℚ)], .dom [0, 0, (26/57 : ℚ), (31/57 : ℚ)], .dom [0, 0, (10504/13851 : ℚ), (3347/13851 : ℚ)], .dom [0, 0, (3080/4617 : ℚ), (1537/4617 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, 1, 0], .dom [0, 0, (11852/13851 : ℚ), (1999/13851 : ℚ)], .dom [0, 0, (1246/1539 : ℚ), (293/1539 : ℚ)], .dom [0, 0, (101/114 : ℚ), (13/114 : ℚ)], .dom [0, 0, (2840/4617 : ℚ), (1777/4617 : ℚ)], .dom [0, 0, (581/1026 : ℚ), (445/1026 : ℚ)], .dom [0, 0, (34/57 : ℚ), (23/57 : ℚ)], .dom [0, 0, (1412/4617 : ℚ), (3205/4617 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, (973/1026 : ℚ), (53/1026 : ℚ)], .dom [0, 0, (3928/4617 : ℚ), (689/4617 : ℚ)], .dom [0, 0, (88/285 : ℚ), (197/285 : ℚ)], .dom [0, 0, (1342/1539 : ℚ), (197/1539 : ℚ)], .dom [0, 0, (10700/13851 : ℚ), (3151/13851 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, (232/285 : ℚ), (53/285 : ℚ)], .dom [0, 0, (86/171 : ℚ), (85/171 : ℚ)], .dom [0, 0, (202/513 : ℚ), (311/513 : ℚ)], .dom [0, 0, (110/171 : ℚ), (61/171 : ℚ)], .dom [0, 0, (34/57 : ℚ), (23/57 : ℚ)], .kept 3, .kept 0, .kept 1, .kept 2, .dom [0, 0, (92/95 : ℚ), (3/95 : ℚ)]], [.kept 0, .kept 1, .kept 2, .dom [0, 0, (201/211 : ℚ), (10/211 : ℚ)], .dom [0, (77/125 : ℚ), (48/125 : ℚ), 0], .dom [0, (4/25 : ℚ), (21/25 : ℚ), 0], .kept 2, .kept 3, .dom [0, (607/675 : ℚ), (68/675 : ℚ), 0], .dom [0, (17/125 : ℚ), (108/125 : ℚ), 0], .dom [0, 0, (904/1899 : ℚ), (995/1899 : ℚ)], .dom [0, 0, (764/1899 : ℚ), (1135/1899 : ℚ)], .dom [0, (91/100 : ℚ), (9/100 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, (71/135 : ℚ), (64/135 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (279/844 : ℚ), (565/844 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 1, 0, 0], .dom [0, (433/450 : ℚ), (17/450 : ℚ), 0], .dom [0, (5/9 : ℚ), (4/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, 0, (201/211 : ℚ), (10/211 : ℚ)], .dom [0, 0, (5372/5697 : ℚ), (325/5697 : ℚ)], .dom [0, 0, (2683/3798 : ℚ), (1115/3798 : ℚ)], .dom [0, 0, (764/1899 : ℚ), (1135/1899 : ℚ)], .dom [0, 0, (4792/5697 : ℚ), (905/5697 : ℚ)], .dom [0, 0, (2273/3798 : ℚ), (1525/3798 : ℚ)], .dom [0, 0, 0, 1], .dom [0, (217/225 : ℚ), (8/225 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, 0, (328/633 : ℚ), (305/633 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 1, 0, 0], .dom [0, (433/450 : ℚ), (17/450 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, (5/9 : ℚ), (4/9 : ℚ), 0], .dom [0, 0, (201/211 : ℚ), (10/211 : ℚ)], .dom [0, 0, (3253/3798 : ℚ), (545/3798 : ℚ)], .dom [0, 0, (971/1266 : ℚ), (295/1266 : ℚ)], .dom [0, 0, (279/844 : ℚ), (565/844 : ℚ)], .dom [0, 0, (4432/5697 : ℚ), (1265/5697 : ℚ)], .dom [0, 0, (1304/1899 : ℚ), (595/1899 : ℚ)], .dom [0, 0, 0, 1], .dom [0, (91/100 : ℚ), (9/100 : ℚ), 0], .dom [0, (71/135 : ℚ), (64/135 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (639/844 : ℚ), (205/844 : ℚ)], .dom [0, 0, (904/1899 : ℚ), (995/1899 : ℚ)], .dom [0, 0, (359/844 : ℚ), (485/844 : ℚ)], .dom [0, 1, 0, 0], .dom [0, (607/675 : ℚ), (68/675 : ℚ), 0], .dom [0, (17/125 : ℚ), (108/125 : ℚ), 0], .dom [0, 0, (579/844 : ℚ), (265/844 : ℚ)], .dom [0, 0, (368/633 : ℚ), (265/633 : ℚ)], .kept 3, .dom [0, (77/125 : ℚ), (48/125 : ℚ), 0], .dom [0, (4/25 : ℚ), (21/25 : ℚ), 0], .kept 2, .dom [1, 0, 0, 0], .kept 0, .kept 1], [.dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .kept 0, .kept 1, .kept 2, .dom [0, 0, (247/263 : ℚ), (16/263 : ℚ)], .kept 1, .kept 2, .kept 3, .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, (35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, 0, (137/263 : ℚ), (126/263 : ℚ)], .dom [0, 0, (109/263 : ℚ), (154/263 : ℚ)], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 0, (93/263 : ℚ), (170/263 : ℚ)], .dom [0, 0, 0, 1], .dom [1, 0, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, 0, (247/263 : ℚ), (16/263 : ℚ)], .dom [0, 0, (229/263 : ℚ), (34/263 : ℚ)], .dom [0, 0, (339/526 : ℚ), (187/526 : ℚ)], .dom [0, 0, (93/263 : ℚ), (170/263 : ℚ)], .dom [0, 0, 0, 1], .dom [0, 0, 0, 1], .dom [0, 0, 0, 1], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, (255/328 : ℚ), (73/328 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (165/263 : ℚ), (98/263 : ℚ)], .dom [0, 0, (109/263 : ℚ), (154/263 : ℚ)], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 0, 1, 0], .dom [0, (245/328 : ℚ), (83/328 : ℚ), 0], .dom [0, (35/656 : ℚ), (621/656 : ℚ), 0], .dom [0, 0, (141/263 : ℚ), (122/263 : ℚ)], .dom [0, 0, (117/263 : ℚ), (146/263 : ℚ)], .kept 3, .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .dom [0, (305/656 : ℚ), (351/656 : ℚ), 0], .kept 2, .dom [0, 0, (252/263 : ℚ), (11/263 : ℚ)], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .kept 1, .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .kept 0], [.dom [1, 0], .dom [1, 0], .kept 0, .dom [(44/63 : ℚ), (19/63 : ℚ)], .dom [(40/63 : ℚ), (23/63 : ℚ)], .dom [1, 0], .kept 0, .kept 1, .dom [1, 0], .dom [(44/63 : ℚ), (19/63 : ℚ)], .dom [(13/42 : ℚ), (29/42 : ℚ)], .dom [0, 1], .dom [1, 0], .dom [1, 0], .dom [(107/126 : ℚ), (19/126 : ℚ)], .dom [(152/189 : ℚ), (37/189 : ℚ)], .dom [(13/42 : ℚ), (29/42 : ℚ)], .dom [0, 1], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [(188/189 : ℚ), (1/189 : ℚ)], .dom [(109/126 : ℚ), (17/126 : ℚ)], .dom [(44/63 : ℚ), (19/63 : ℚ)], .dom [0, 1], .dom [(3/14 : ℚ), (11/14 : ℚ)], .kept 1, .dom [1, 0], .dom [1, 0], .dom [(16/21 : ℚ), (5/21 : ℚ)], .dom [(40/63 : ℚ), (23/63 : ℚ)], .dom [1, 0], .dom [1, 0], .kept 0, .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0]], [.dom [1, 0, 0], .kept 0, .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .kept 0, .kept 1, .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 1, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .kept 1, .dom [0, (11/12 : ℚ), (1/12 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .kept 0, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]], [.dom [1], .kept 0, .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]]]

/-- Branch candidate witnesses, in `candH` order. -/
def matching_sum_WHt : List (List Wit) := [
  [],
  [.kept 0],
  [.kept 0],
  [.kept 0, .dom [1]],
  [.kept 0, .kept 1, .dom [1, 0]],
  [.kept 1, .kept 0, .dom [0, 0, 1], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [1, 0], .dom [1, 0], .kept 0, .dom [1, 0], .kept 1, .dom [1, 0], .dom [0, 1], .dom [1, 0], .dom [1, 0]],
  [.kept 1, .kept 0, .dom [0, 1, 0], .dom [0, (29/39 : ℚ), (10/39 : ℚ)], .dom [0, (23/39 : ℚ), (16/39 : ℚ)], .dom [0, (103/117 : ℚ), (14/117 : ℚ)], .dom [1, 0, 0], .dom [0, 1, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [1, 0, 0], .dom [1, 0, 0], .kept 0, .dom [1, 0, 0], .dom [0, 1, 0], .kept 1, .dom [1, 0, 0], .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [0, 1, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [0, (1377/1472 : ℚ), (95/1472 : ℚ)], .kept 1, .kept 0, .dom [0, 1, 0], .dom [0, (243/368 : ℚ), (125/368 : ℚ)], .dom [0, (57/92 : ℚ), (35/92 : ℚ)], .dom [0, (44/69 : ℚ), (25/69 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, (303/368 : ℚ), (65/368 : ℚ)], .dom [0, (657/1472 : ℚ), (815/1472 : ℚ)], .dom [0, (213/368 : ℚ), (155/368 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 1, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [1, 0, 0], .dom [1, 0, 0], .kept 0, .dom [1, 0, 0], .dom [0, 1, 0], .kept 1, .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 0, 1], .dom [1, 0, 0], .dom [0, 1, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [0, (84/85 : ℚ), (1/85 : ℚ)], .kept 1, .kept 0, .dom [1, 0, 0], .dom [0, (58/85 : ℚ), (27/85 : ℚ)], .dom [0, (866/1377 : ℚ), (511/1377 : ℚ)], .dom [0, (98/153 : ℚ), (55/153 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, (27/34 : ℚ), (7/34 : ℚ)], .dom [0, (79/153 : ℚ), (74/153 : ℚ)], .dom [0, (73/153 : ℚ), (80/153 : ℚ)], .dom [1, 0, 0], .dom [0, 0, 1], .dom [0, (36/85 : ℚ), (49/85 : ℚ)], .dom [0, (42/85 : ℚ), (43/85 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [1, 0, 0, 0], .dom [(117/122 : ℚ), (5/122 : ℚ), 0, 0], .kept 0, .dom [1, 0, 0, 0], .dom [0, 1, 0, 0], .dom [0, 1, 0, 0], .kept 1, .dom [1, 0, 0, 0], .dom [0, 1, 0, 0], .kept 2, .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .kept 3, .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .dom [0, 0, 1, 0], .dom [0, 1, 0, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0], .dom [1, 0, 0, 0]],
  [.dom [0, (500/507 : ℚ), (7/507 : ℚ)], .dom [0, (1472/1521 : ℚ), (49/1521 : ℚ)], .kept 1, .kept 0, .dom [0, 1, 0], .dom [0, (1024/1521 : ℚ), (497/1521 : ℚ)], .dom [0, (8152/13689 : ℚ), (5537/13689 : ℚ)], .dom [0, (968/1521 : ℚ), (553/1521 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, (1912/2535 : ℚ), (623/2535 : ℚ)], .dom [0, (472/1053 : ℚ), (581/1053 : ℚ)], .dom [0, (5800/13689 : ℚ), (7889/13689 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, (712/845 : ℚ), (133/845 : ℚ)], .dom [0, (10208/22815 : ℚ), (12607/22815 : ℚ)], .dom [0, (64/169 : ℚ), (105/169 : ℚ)], .dom [1, 0, 0], .dom [0, 0, 1], .dom [0, (604/1521 : ℚ), (917/1521 : ℚ)], .dom [0, (1952/4563 : ℚ), (2611/4563 : ℚ)], .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]]]

/-- The certificate. -/
def matching_sum_C : Cert 2 where
  KB s c := (matching_sum_KBt.getD s []).getD c []
  KH m := matching_sum_KHt.getD m []
  WB s c := (matching_sum_WBt.getD s []).getD c []
  WH m := matching_sum_WHt.getD m []

/-- The sign conditions (positive multilinear recursion). -/
theorem matching_sum_signs : matching_sum_R.Signs 14 (0 : Fin 2) where
  e_nn := by decide +kernel
  e_pos := by decide +kernel
  T_nn := by decide +kernel
  T_pos := by decide +kernel
  T_left := by decide +kernel
  T_right := by decide +kernel
  P_nn := by decide +kernel
  P_pos := by decide +kernel
  P_col := by decide +kernel

/-- The dominance certificate: every candidate of every class has a checked
witness (exact rational arithmetic, evaluated by the kernel). -/
theorem matching_sum_valid : matching_sum_C.Valid matching_sum_R 14 (0 : Fin 2) := by decide +kernel

theorem matching_sum_F_nn : ∀ k, 1 ≤ k → k < 14 → ∀ i, 0 ≤ matching_sum_R.F k i := by
  decide +kernel

theorem matching_sum_F_pos : ∀ k, 1 ≤ k → k < 14 → ∀ i, 0 < matching_sum_R.F k i := by
  decide +kernel

/-- n = 2: every kept root bundle has value at most M_2 = 2. -/
theorem matching_sum_hV_2 : ∀ k, 1 ≤ k → k < 2 → ∀ p ∈ matching_sum_C.KB 1 k,
    matching_sum_R.root k p ≤ (2 : ℚ) := by
  decide +kernel

/-- n = 2: the listed maximizers (one rooting per isomorphism class)
attain 2. -/
theorem matching_sum_listed_2 : ∀ T ∈ ([RTree.node [RTree.node []]] : List RTree),
    T.size = 2 ∧ matching_sum_R.pi T = (2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 2 vertices. -/
theorem matching_sum_max_2 :
    IsGreatest {x | ∃ T : RTree, T.size = 2 ∧ matching_sum_R.pi T = x} (2 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 2) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_2 _
    (matching_sum_listed_2 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 2 vertices: a tree attaining 2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_2 : ∀ l : List RTree, (RTree.node l).size = 2 →
    matching_sum_R.pi (.node l) = (2 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 1 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_2

/-- n = 3: every kept root bundle has value at most M_3 = 2. -/
theorem matching_sum_hV_3 : ∀ k, 1 ≤ k → k < 3 → ∀ p ∈ matching_sum_C.KB 2 k,
    matching_sum_R.root k p ≤ (2 : ℚ) := by
  decide +kernel

/-- n = 3: the listed maximizers (one rooting per isomorphism class)
attain 2. -/
theorem matching_sum_listed_3 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node []]] : List RTree),
    T.size = 3 ∧ matching_sum_R.pi T = (2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 3 vertices. -/
theorem matching_sum_max_3 :
    IsGreatest {x | ∃ T : RTree, T.size = 3 ∧ matching_sum_R.pi T = x} (2 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 3) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_3 _
    (matching_sum_listed_3 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 3 vertices: a tree attaining 2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_3 : ∀ l : List RTree, (RTree.node l).size = 3 →
    matching_sum_R.pi (.node l) = (2 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 2 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_3

/-- n = 4: every kept root bundle has value at most M_4 = 5/2. -/
theorem matching_sum_hV_4 : ∀ k, 1 ≤ k → k < 4 → ∀ p ∈ matching_sum_C.KB 3 k,
    matching_sum_R.root k p ≤ (5 / 2 : ℚ) := by
  decide +kernel

/-- n = 4: the listed maximizers (one rooting per isomorphism class)
attain 5/2. -/
theorem matching_sum_listed_4 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node []]]] : List RTree),
    T.size = 4 ∧ matching_sum_R.pi T = (5 / 2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 4 vertices. -/
theorem matching_sum_max_4 :
    IsGreatest {x | ∃ T : RTree, T.size = 4 ∧ matching_sum_R.pi T = x} (5 / 2 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 4) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_4 _
    (matching_sum_listed_4 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 4 vertices: a tree attaining 5/2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_4 : ∀ l : List RTree, (RTree.node l).size = 4 →
    matching_sum_R.pi (.node l) = (5 / 2 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 3 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_4

/-- n = 5: every kept root bundle has value at most M_5 = 3. -/
theorem matching_sum_hV_5 : ∀ k, 1 ≤ k → k < 5 → ∀ p ∈ matching_sum_C.KB 4 k,
    matching_sum_R.root k p ≤ (3 : ℚ) := by
  decide +kernel

/-- n = 5: the listed maximizers (one rooting per isomorphism class)
attain 3. -/
theorem matching_sum_listed_5 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []]]]] : List RTree),
    T.size = 5 ∧ matching_sum_R.pi T = (3 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 5 vertices. -/
theorem matching_sum_max_5 :
    IsGreatest {x | ∃ T : RTree, T.size = 5 ∧ matching_sum_R.pi T = x} (3 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 5) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_5 _
    (matching_sum_listed_5 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 5 vertices: a tree attaining 3 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_5 : ∀ l : List RTree, (RTree.node l).size = 5 →
    matching_sum_R.pi (.node l) = (3 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 4 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_5

/-- n = 6: every kept root bundle has value at most M_6 = 29/8. -/
theorem matching_sum_hV_6 : ∀ k, 1 ≤ k → k < 6 → ∀ p ∈ matching_sum_C.KB 5 k,
    matching_sum_R.root k p ≤ (29 / 8 : ℚ) := by
  decide +kernel

/-- n = 6: the listed maximizers (one rooting per isomorphism class)
attain 29/8. -/
theorem matching_sum_listed_6 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 6 ∧ matching_sum_R.pi T = (29 / 8 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 6 vertices. -/
theorem matching_sum_max_6 :
    IsGreatest {x | ∃ T : RTree, T.size = 6 ∧ matching_sum_R.pi T = x} (29 / 8 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 6) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_6 _
    (matching_sum_listed_6 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 6 vertices: a tree attaining 29/8 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_6 : ∀ l : List RTree, (RTree.node l).size = 6 →
    matching_sum_R.pi (.node l) = (29 / 8 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 5 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_6

/-- n = 7: every kept root bundle has value at most M_7 = 9/2. -/
theorem matching_sum_hV_7 : ∀ k, 1 ≤ k → k < 7 → ∀ p ∈ matching_sum_C.KB 6 k,
    matching_sum_R.root k p ≤ (9 / 2 : ℚ) := by
  decide +kernel

/-- n = 7: the listed maximizers (one rooting per isomorphism class)
attain 9/2. -/
theorem matching_sum_listed_7 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []]]]] : List RTree),
    T.size = 7 ∧ matching_sum_R.pi T = (9 / 2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 7 vertices. -/
theorem matching_sum_max_7 :
    IsGreatest {x | ∃ T : RTree, T.size = 7 ∧ matching_sum_R.pi T = x} (9 / 2 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 7) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_7 _
    (matching_sum_listed_7 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 7 vertices: a tree attaining 9/2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_7 : ∀ l : List RTree, (RTree.node l).size = 7 →
    matching_sum_R.pi (.node l) = (9 / 2 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 6 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_7

/-- n = 8: every kept root bundle has value at most M_8 = 43/8. -/
theorem matching_sum_hV_8 : ∀ k, 1 ≤ k → k < 8 → ∀ p ∈ matching_sum_C.KB 7 k,
    matching_sum_R.root k p ≤ (43 / 8 : ℚ) := by
  decide +kernel

/-- n = 8: the listed maximizers (one rooting per isomorphism class)
attain 43/8. -/
theorem matching_sum_listed_8 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 8 ∧ matching_sum_R.pi T = (43 / 8 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 8 vertices. -/
theorem matching_sum_max_8 :
    IsGreatest {x | ∃ T : RTree, T.size = 8 ∧ matching_sum_R.pi T = x} (43 / 8 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 8) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_8 _
    (matching_sum_listed_8 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 8 vertices: a tree attaining 43/8 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_8 : ∀ l : List RTree, (RTree.node l).size = 8 →
    matching_sum_R.pi (.node l) = (43 / 8 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 7 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_8

/-- n = 9: every kept root bundle has value at most M_9 = 27/4. -/
theorem matching_sum_hV_9 : ∀ k, 1 ≤ k → k < 9 → ∀ p ∈ matching_sum_C.KB 8 k,
    matching_sum_R.root k p ≤ (27 / 4 : ℚ) := by
  decide +kernel

/-- n = 9: the listed maximizers (one rooting per isomorphism class)
attain 27/4. -/
theorem matching_sum_listed_9 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []]]]] : List RTree),
    T.size = 9 ∧ matching_sum_R.pi T = (27 / 4 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 9 vertices. -/
theorem matching_sum_max_9 :
    IsGreatest {x | ∃ T : RTree, T.size = 9 ∧ matching_sum_R.pi T = x} (27 / 4 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 9) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_9 _
    (matching_sum_listed_9 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 9 vertices: a tree attaining 27/4 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_9 : ∀ l : List RTree, (RTree.node l).size = 9 →
    matching_sum_R.pi (.node l) = (27 / 4 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 8 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_9

/-- n = 10: every kept root bundle has value at most M_10 = 65/8. -/
theorem matching_sum_hV_10 : ∀ k, 1 ≤ k → k < 10 → ∀ p ∈ matching_sum_C.KB 9 k,
    matching_sum_R.root k p ≤ (65 / 8 : ℚ) := by
  decide +kernel

/-- n = 10: the listed maximizers (one rooting per isomorphism class)
attain 65/8. -/
theorem matching_sum_listed_10 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 10 ∧ matching_sum_R.pi T = (65 / 8 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 10 vertices. -/
theorem matching_sum_max_10 :
    IsGreatest {x | ∃ T : RTree, T.size = 10 ∧ matching_sum_R.pi T = x} (65 / 8 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 10) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_10 _
    (matching_sum_listed_10 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 10 vertices: a tree attaining 65/8 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_10 : ∀ l : List RTree, (RTree.node l).size = 10 →
    matching_sum_R.pi (.node l) = (65 / 8 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 9 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_10

/-- n = 11: every kept root bundle has value at most M_11 = 81/8. -/
theorem matching_sum_hV_11 : ∀ k, 1 ≤ k → k < 11 → ∀ p ∈ matching_sum_C.KB 10 k,
    matching_sum_R.root k p ≤ (81 / 8 : ℚ) := by
  decide +kernel

/-- n = 11: the listed maximizers (one rooting per isomorphism class)
attain 81/8. -/
theorem matching_sum_listed_11 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []]]]] : List RTree),
    T.size = 11 ∧ matching_sum_R.pi T = (81 / 8 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 11 vertices. -/
theorem matching_sum_max_11 :
    IsGreatest {x | ∃ T : RTree, T.size = 11 ∧ matching_sum_R.pi T = x} (81 / 8 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 11) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_11 _
    (matching_sum_listed_11 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 11 vertices: a tree attaining 81/8 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_11 : ∀ l : List RTree, (RTree.node l).size = 11 →
    matching_sum_R.pi (.node l) = (81 / 8 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 10 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_11

/-- n = 12: every kept root bundle has value at most M_12 = 783/64. -/
theorem matching_sum_hV_12 : ∀ k, 1 ≤ k → k < 12 → ∀ p ∈ matching_sum_C.KB 11 k,
    matching_sum_R.root k p ≤ (783 / 64 : ℚ) := by
  decide +kernel

/-- n = 12: the listed maximizers (one rooting per isomorphism class)
attain 783/64. -/
theorem matching_sum_listed_12 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 12 ∧ matching_sum_R.pi T = (783 / 64 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 12 vertices. -/
theorem matching_sum_max_12 :
    IsGreatest {x | ∃ T : RTree, T.size = 12 ∧ matching_sum_R.pi T = x} (783 / 64 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 12) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_12 _
    (matching_sum_listed_12 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 12 vertices: a tree attaining 783/64 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_12 : ∀ l : List RTree, (RTree.node l).size = 12 →
    matching_sum_R.pi (.node l) = (783 / 64 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 11 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_12

/-- n = 13: every kept root bundle has value at most M_13 = 243/16. -/
theorem matching_sum_hV_13 : ∀ k, 1 ≤ k → k < 13 → ∀ p ∈ matching_sum_C.KB 12 k,
    matching_sum_R.root k p ≤ (243 / 16 : ℚ) := by
  decide +kernel

/-- n = 13: the listed maximizers (one rooting per isomorphism class)
attain 243/16. -/
theorem matching_sum_listed_13 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []]]]] : List RTree),
    T.size = 13 ∧ matching_sum_R.pi T = (243 / 16 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 13 vertices. -/
theorem matching_sum_max_13 :
    IsGreatest {x | ∃ T : RTree, T.size = 13 ∧ matching_sum_R.pi T = x} (243 / 16 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 13) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_13 _
    (matching_sum_listed_13 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 13 vertices: a tree attaining 243/16 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_13 : ∀ l : List RTree, (RTree.node l).size = 13 →
    matching_sum_R.pi (.node l) = (243 / 16 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 12 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_13

/-- n = 14: every kept root bundle has value at most M_14 = 9477/512. -/
theorem matching_sum_hV_14 : ∀ k, 1 ≤ k → k < 14 → ∀ p ∈ matching_sum_C.KB 13 k,
    matching_sum_R.root k p ≤ (9477 / 512 : ℚ) := by
  decide +kernel

/-- n = 14: the listed maximizers (one rooting per isomorphism class)
attain 9477/512. -/
theorem matching_sum_listed_14 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 14 ∧ matching_sum_R.pi T = (9477 / 512 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 14 vertices. -/
theorem matching_sum_max_14 :
    IsGreatest {x | ∃ T : RTree, T.size = 14 ∧ matching_sum_R.pi T = x} (9477 / 512 : ℚ) :=
  isGreatest_pi matching_sum_signs matching_sum_valid (n := 14) (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_nn k h1 (by omega)) matching_sum_hV_14 _
    (matching_sum_listed_14 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 14 vertices: a tree attaining 9477/512 has every
branch state and every partial bundle state on the kept hull points. -/
theorem matching_sum_kept_14 : ∀ l : List RTree, (RTree.node l).size = 14 →
    matching_sum_R.pi (.node l) = (9477 / 512 : ℚ) →
      KeptL matching_sum_R matching_sum_C l ∧ matching_sum_R.bundle l ∈ matching_sum_C.KB 13 l.length :=
  kept_of_pi_eq matching_sum_signs matching_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => matching_sum_F_pos k h1 (by omega)) matching_sum_hV_14

/-- MAIN.  The exact maximum for every n = 2..14. -/
theorem matching_sum :
    IsGreatest {x | ∃ T : RTree, T.size = 2 ∧ matching_sum_R.pi T = x} (2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 3 ∧ matching_sum_R.pi T = x} (2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 4 ∧ matching_sum_R.pi T = x} (5 / 2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 5 ∧ matching_sum_R.pi T = x} (3 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 6 ∧ matching_sum_R.pi T = x} (29 / 8 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 7 ∧ matching_sum_R.pi T = x} (9 / 2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 8 ∧ matching_sum_R.pi T = x} (43 / 8 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 9 ∧ matching_sum_R.pi T = x} (27 / 4 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 10 ∧ matching_sum_R.pi T = x} (65 / 8 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 11 ∧ matching_sum_R.pi T = x} (81 / 8 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 12 ∧ matching_sum_R.pi T = x} (783 / 64 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 13 ∧ matching_sum_R.pi T = x} (243 / 16 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 14 ∧ matching_sum_R.pi T = x} (9477 / 512 : ℚ) :=
  ⟨matching_sum_max_2, matching_sum_max_3, matching_sum_max_4, matching_sum_max_5, matching_sum_max_6, matching_sum_max_7, matching_sum_max_8, matching_sum_max_9, matching_sum_max_10, matching_sum_max_11, matching_sum_max_12, matching_sum_max_13, matching_sum_max_14⟩

/-! ## Instance `randic_sum`: one plus the Randic-type edge sum

Dimension 3, trees on n = 2..12 vertices, 209 kept points, 700 candidate witnesses.
Certified values: M_2 = 2, M_3 = 2, M_4 = 9/4, M_5 = 5/2, M_6 = 11/4, M_7 = 3, M_8 = 13/4, M_9 = 7/2, M_10 = 34/9, M_11 = 145/36, M_12 = 103/24. -/

/-- The recursion. -/
def randic_sum_R : Rec 3 where
  e := ![1, 0, 0]
  T := fun i j l => (![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℚ) i j l
  P := fun c => ![![1, 0, 0], ![0, 1, ((1 + (c : ℚ)))⁻¹], ![((1 + (c : ℚ)))⁻¹, 0, 0]]
  F := fun k => ![1, 1, ((k : ℚ))⁻¹]

/-- Kept bundle points, indexed [s][c]. -/
def randic_sum_KBt : List (List (List (Vec 3))) := [
  [[![1, 0, 0]]],
  [[], [![1, 0, 1]]],
  [[], [![1, (1/2 : ℚ), (1/2 : ℚ)]], [![1, 0, 2]]],
  [[], [![1, (3/4 : ℚ), (1/2 : ℚ)]], [![1, (1/2 : ℚ), (3/2 : ℚ)]], [![1, 0, 3]]],
  [[], [![1, 1, (1/2 : ℚ)]], [![1, (3/4 : ℚ), (3/2 : ℚ)], ![1, 1, 1]], [![1, (1/2 : ℚ), (5/2 : ℚ)]], [![1, 0, 4]]],
  [[], [![1, (5/4 : ℚ), (1/2 : ℚ)], ![1, (4/3 : ℚ), (1/3 : ℚ)]], [![1, 1, (3/2 : ℚ)], ![1, (5/4 : ℚ), 1]], [![1, (3/4 : ℚ), (5/2 : ℚ)], ![1, 1, 2]], [![1, (1/2 : ℚ), (7/2 : ℚ)]], [![1, 0, 5]]],
  [[], [![1, (3/2 : ℚ), (1/2 : ℚ)], ![1, (19/12 : ℚ), (1/3 : ℚ)]], [![1, (5/4 : ℚ), (3/2 : ℚ)], ![1, (4/3 : ℚ), (4/3 : ℚ)], ![1, (3/2 : ℚ), 1]], [![1, 1, (5/2 : ℚ)], ![1, (5/4 : ℚ), 2], ![1, (3/2 : ℚ), (3/2 : ℚ)]], [![1, (3/4 : ℚ), (7/2 : ℚ)], ![1, 1, 3]], [![1, (1/2 : ℚ), (9/2 : ℚ)]], [![1, 0, 6]]],
  [[], [![1, (7/4 : ℚ), (1/2 : ℚ)], ![1, (11/6 : ℚ), (1/3 : ℚ)], ![1, (15/8 : ℚ), (1/4 : ℚ)]], [![1, (3/2 : ℚ), (3/2 : ℚ)], ![1, (19/12 : ℚ), (4/3 : ℚ)], ![1, (7/4 : ℚ), 1], ![1, (11/6 : ℚ), (5/6 : ℚ)]], [![1, (5/4 : ℚ), (5/2 : ℚ)], ![1, (4/3 : ℚ), (7/3 : ℚ)], ![1, (3/2 : ℚ), 2], ![1, (7/4 : ℚ), (3/2 : ℚ)]], [![1, 1, (7/2 : ℚ)], ![1, (5/4 : ℚ), 3], ![1, (3/2 : ℚ), (5/2 : ℚ)]], [![1, (3/4 : ℚ), (9/2 : ℚ)], ![1, 1, 4]], [![1, (1/2 : ℚ), (11/2 : ℚ)]], [![1, 0, 7]]],
  [[], [![1, 2, (1/2 : ℚ)], ![1, (19/9 : ℚ), (1/3 : ℚ)], ![1, (17/8 : ℚ), (1/4 : ℚ)]], [![1, (7/4 : ℚ), (3/2 : ℚ)], ![1, (11/6 : ℚ), (4/3 : ℚ)], ![1, (15/8 : ℚ), (5/4 : ℚ)], ![1, 2, 1], ![1, (25/12 : ℚ), (5/6 : ℚ)]], [![1, (3/2 : ℚ), (5/2 : ℚ)], ![1, (19/12 : ℚ), (7/3 : ℚ)], ![1, (7/4 : ℚ), 2], ![1, (11/6 : ℚ), (11/6 : ℚ)], ![1, 2, (3/2 : ℚ)]], [![1, (5/4 : ℚ), (7/2 : ℚ)], ![1, (4/3 : ℚ), (10/3 : ℚ)], ![1, (3/2 : ℚ), 3], ![1, (7/4 : ℚ), (5/2 : ℚ)], ![1, 2, 2]], [![1, 1, (9/2 : ℚ)], ![1, (5/4 : ℚ), 4], ![1, (3/2 : ℚ), (7/2 : ℚ)]], [![1, (3/4 : ℚ), (11/2 : ℚ)], ![1, 1, 5]], [![1, (1/2 : ℚ), (13/2 : ℚ)]], [![1, 0, 8]]],
  [[], [![1, (41/18 : ℚ), (1/2 : ℚ)], ![1, (85/36 : ℚ), (1/3 : ℚ)], ![1, (12/5 : ℚ), (1/5 : ℚ)]], [![1, 2, (3/2 : ℚ)], ![1, (19/9 : ℚ), (4/3 : ℚ)], ![1, (19/8 : ℚ), (3/4 : ℚ)]], [![1, (7/4 : ℚ), (5/2 : ℚ)], ![1, (11/6 : ℚ), (7/3 : ℚ)], ![1, (15/8 : ℚ), (9/4 : ℚ)], ![1, 2, 2], ![1, (25/12 : ℚ), (11/6 : ℚ)], ![1, (9/4 : ℚ), (3/2 : ℚ)], ![1, (7/3 : ℚ), (4/3 : ℚ)]], [![1, (3/2 : ℚ), (7/2 : ℚ)], ![1, (19/12 : ℚ), (10/3 : ℚ)], ![1, (7/4 : ℚ), 3], ![1, (11/6 : ℚ), (17/6 : ℚ)], ![1, 2, (5/2 : ℚ)], ![1, (9/4 : ℚ), 2]], [![1, (5/4 : ℚ), (9/2 : ℚ)], ![1, (4/3 : ℚ), (13/3 : ℚ)], ![1, (3/2 : ℚ), 4], ![1, (7/4 : ℚ), (7/2 : ℚ)], ![1, 2, 3]], [![1, 1, (11/2 : ℚ)], ![1, (5/4 : ℚ), 5], ![1, (3/2 : ℚ), (9/2 : ℚ)]], [![1, (3/4 : ℚ), (13/2 : ℚ)], ![1, 1, 6]], [![1, (1/2 : ℚ), (15/2 : ℚ)]], [![1, 0, 9]]],
  [[], [![1, (91/36 : ℚ), (1/2 : ℚ)], ![1, (21/8 : ℚ), (1/3 : ℚ)], ![1, (8/3 : ℚ), (1/4 : ℚ)]], [![1, (41/18 : ℚ), (3/2 : ℚ)], ![1, (85/36 : ℚ), (4/3 : ℚ)], ![1, (47/18 : ℚ), (5/6 : ℚ)], ![1, (8/3 : ℚ), (2/3 : ℚ)]], [![1, 2, (5/2 : ℚ)], ![1, (19/9 : ℚ), (7/3 : ℚ)], ![1, (31/12 : ℚ), (4/3 : ℚ)]], [![1, (7/4 : ℚ), (7/2 : ℚ)], ![1, (11/6 : ℚ), (10/3 : ℚ)], ![1, (15/8 : ℚ), (13/4 : ℚ)], ![1, 2, 3], ![1, (25/12 : ℚ), (17/6 : ℚ)], ![1, (9/4 : ℚ), (5/2 : ℚ)], ![1, (7/3 : ℚ), (7/3 : ℚ)], ![1, (5/2 : ℚ), 2]], [![1, (3/2 : ℚ), (9/2 : ℚ)], ![1, (19/12 : ℚ), (13/3 : ℚ)], ![1, (7/4 : ℚ), 4], ![1, (11/6 : ℚ), (23/6 : ℚ)], ![1, 2, (7/2 : ℚ)], ![1, (9/4 : ℚ), 3], ![1, (5/2 : ℚ), (5/2 : ℚ)]], [![1, (5/4 : ℚ), (11/2 : ℚ)], ![1, (4/3 : ℚ), (16/3 : ℚ)], ![1, (3/2 : ℚ), 5], ![1, (7/4 : ℚ), (9/2 : ℚ)], ![1, 2, 4]], [![1, 1, (13/2 : ℚ)], ![1, (5/4 : ℚ), 6], ![1, (3/2 : ℚ), (11/2 : ℚ)]], [![1, (3/4 : ℚ), (15/2 : ℚ)], ![1, 1, 7]], [![1, (1/2 : ℚ), (17/2 : ℚ)]], [![1, 0, 10]]],
  [[], [![1, (67/24 : ℚ), (1/2 : ℚ)], ![1, (26/9 : ℚ), (1/3 : ℚ)], ![1, (35/12 : ℚ), (1/4 : ℚ)]], [![1, (91/36 : ℚ), (3/2 : ℚ)], ![1, (21/8 : ℚ), (4/3 : ℚ)], ![1, (8/3 : ℚ), (5/4 : ℚ)], ![1, (103/36 : ℚ), (5/6 : ℚ)], ![1, (35/12 : ℚ), (2/3 : ℚ)]], [![1, (41/18 : ℚ), (5/2 : ℚ)], ![1, (85/36 : ℚ), (7/3 : ℚ)], ![1, (47/18 : ℚ), (11/6 : ℚ)], ![1, (23/8 : ℚ), (5/4 : ℚ)]], [![1, 2, (7/2 : ℚ)], ![1, (19/9 : ℚ), (10/3 : ℚ)], ![1, (17/6 : ℚ), (11/6 : ℚ)]], [![1, (7/4 : ℚ), (9/2 : ℚ)], ![1, (11/6 : ℚ), (13/3 : ℚ)], ![1, (15/8 : ℚ), (17/4 : ℚ)], ![1, 2, 4], ![1, (25/12 : ℚ), (23/6 : ℚ)], ![1, (9/4 : ℚ), (7/2 : ℚ)], ![1, (7/3 : ℚ), (10/3 : ℚ)], ![1, (5/2 : ℚ), 3], ![1, (11/4 : ℚ), (5/2 : ℚ)]], [![1, (3/2 : ℚ), (11/2 : ℚ)], ![1, (19/12 : ℚ), (16/3 : ℚ)], ![1, (7/4 : ℚ), 5], ![1, (11/6 : ℚ), (29/6 : ℚ)], ![1, 2, (9/2 : ℚ)], ![1, (9/4 : ℚ), 4], ![1, (5/2 : ℚ), (7/2 : ℚ)]], [![1, (5/4 : ℚ), (13/2 : ℚ)], ![1, (4/3 : ℚ), (19/3 : ℚ)], ![1, (3/2 : ℚ), 6], ![1, (7/4 : ℚ), (11/2 : ℚ)], ![1, 2, 5]], [![1, 1, (15/2 : ℚ)], ![1, (5/4 : ℚ), 7], ![1, (3/2 : ℚ), (13/2 : ℚ)]], [![1, (3/4 : ℚ), (17/2 : ℚ)], ![1, 1, 8]], [![1, (1/2 : ℚ), (19/2 : ℚ)]], [![1, 0, 11]]]]

/-- Kept branch points, indexed [m]. -/
def randic_sum_KHt : List (List (Vec 3)) := [
  [],
  [![1, 0, 1]],
  [![1, (1/2 : ℚ), (1/2 : ℚ)]],
  [![1, (3/4 : ℚ), (1/2 : ℚ)]],
  [![1, 1, (1/2 : ℚ)]],
  [![1, (5/4 : ℚ), (1/2 : ℚ)], ![1, (4/3 : ℚ), (1/3 : ℚ)]],
  [![1, (3/2 : ℚ), (1/2 : ℚ)], ![1, (19/12 : ℚ), (1/3 : ℚ)]],
  [![1, (7/4 : ℚ), (1/2 : ℚ)], ![1, (11/6 : ℚ), (1/3 : ℚ)], ![1, (15/8 : ℚ), (1/4 : ℚ)]],
  [![1, 2, (1/2 : ℚ)], ![1, (19/9 : ℚ), (1/3 : ℚ)], ![1, (17/8 : ℚ), (1/4 : ℚ)]],
  [![1, (41/18 : ℚ), (1/2 : ℚ)], ![1, (85/36 : ℚ), (1/3 : ℚ)], ![1, (12/5 : ℚ), (1/5 : ℚ)]],
  [![1, (91/36 : ℚ), (1/2 : ℚ)], ![1, (21/8 : ℚ), (1/3 : ℚ)], ![1, (8/3 : ℚ), (1/4 : ℚ)]],
  [![1, (67/24 : ℚ), (1/2 : ℚ)], ![1, (26/9 : ℚ), (1/3 : ℚ)], ![1, (35/12 : ℚ), (1/4 : ℚ)]]]

/-- Bundle candidate witnesses, in `candB` order. -/
def randic_sum_WBt : List (List (List Wit)) := [
  [[.kept 0]],
  [[], [.kept 0]],
  [[], [.kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 2, .kept 2, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 2, .kept 2, .kept 2, .kept 3, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 2, .kept 3, .kept 2, .kept 3, .kept 2, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 3, .kept 4, .kept 3, .kept 3, .kept 4, .kept 3, .kept 4, .kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 2, .kept 3, .kept 4, .kept 2, .kept 4, .kept 2, .kept 4, .kept 2, .kept 3, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 2, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .dom [0, (18/19 : ℚ), (1/19 : ℚ)], .dom [0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, (3/19 : ℚ), (16/19 : ℚ)], .kept 2, .dom [0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, (3/19 : ℚ), (16/19 : ℚ)], .kept 2, .kept 0, .kept 1, .dom [0, (18/19 : ℚ), (1/19 : ℚ)]], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 3, .kept 4, .kept 5, .kept 6, .kept 3, .kept 4, .kept 5, .kept 3, .kept 5, .kept 3, .kept 4, .kept 5, .kept 6, .kept 3, .kept 4, .kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 4, .kept 5, .kept 2, .kept 4, .kept 5, .kept 2, .kept 4, .kept 2, .kept 3, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 2, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .dom [0, (38/45 : ℚ), (7/45 : ℚ), 0], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .kept 2, .dom [0, 0, (3/4 : ℚ), (1/4 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (3/4 : ℚ), (1/4 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .kept 3, .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (3/4 : ℚ), (1/4 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .kept 2, .dom [0, 0, (3/4 : ℚ), (1/4 : ℚ)], .kept 0, .kept 1, .dom [0, (38/45 : ℚ), (7/45 : ℚ), 0]], [.kept 0, .kept 1, .dom [0, (15/34 : ℚ), (19/34 : ℚ)], .dom [0, (12/17 : ℚ), (5/17 : ℚ)], .dom [0, (9/17 : ℚ), (8/17 : ℚ)], .dom [0, (15/34 : ℚ), (19/34 : ℚ)], .dom [0, (3/17 : ℚ), (14/17 : ℚ)], .kept 2, .dom [0, (12/17 : ℚ), (5/17 : ℚ)], .dom [0, (9/17 : ℚ), (8/17 : ℚ)], .dom [0, (3/17 : ℚ), (14/17 : ℚ)], .kept 2, .dom [0, (12/17 : ℚ), (5/17 : ℚ)], .dom [0, (9/17 : ℚ), (8/17 : ℚ)], .dom [0, (3/17 : ℚ), (14/17 : ℚ)], .dom [0, (12/17 : ℚ), (5/17 : ℚ)], .dom [0, (9/17 : ℚ), (8/17 : ℚ)], .dom [0, (3/17 : ℚ), (14/17 : ℚ)], .kept 2, .dom [0, (12/17 : ℚ), (5/17 : ℚ)], .dom [0, (9/17 : ℚ), (8/17 : ℚ)], .dom [0, (3/17 : ℚ), (14/17 : ℚ)], .kept 2, .dom [0, (12/17 : ℚ), (5/17 : ℚ)], .dom [0, (9/17 : ℚ), (8/17 : ℚ)], .dom [0, (15/34 : ℚ), (19/34 : ℚ)], .kept 0, .kept 1, .dom [0, (33/34 : ℚ), (1/34 : ℚ)]], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 3, .kept 4, .kept 5, .kept 7, .kept 3, .kept 5, .kept 7, .kept 3, .kept 4, .kept 5, .kept 6, .kept 3, .kept 4, .kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 2, .kept 4, .kept 5, .kept 2, .kept 4, .kept 2, .kept 3, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 2, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .dom [0, 0, (3/7 : ℚ), (4/7 : ℚ), 0], .kept 3, .dom [0, 0, 0, (3/10 : ℚ), (7/10 : ℚ)], .dom [0, 0, (4/7 : ℚ), (3/7 : ℚ), 0], .kept 3, .dom [0, 0, 0, (3/4 : ℚ), (1/4 : ℚ)], .dom [0, 0, (4/7 : ℚ), (3/7 : ℚ), 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, (3/4 : ℚ), (1/4 : ℚ)], .dom [0, 0, (4/7 : ℚ), (3/7 : ℚ), 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, 1, 0], .kept 4, .dom [0, 0, (4/7 : ℚ), (3/7 : ℚ), 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, 1, 0], .kept 4, .dom [0, 0, (4/7 : ℚ), (3/7 : ℚ), 0], .dom [0, 0, 0, 1, 0], .dom [0, 0, 0, (3/4 : ℚ), (1/4 : ℚ)], .dom [0, 0, (4/7 : ℚ), (3/7 : ℚ), 0], .kept 3, .dom [0, 0, 0, (3/4 : ℚ), (1/4 : ℚ)], .dom [0, 0, (3/7 : ℚ), (4/7 : ℚ), 0], .kept 3, .dom [0, 0, 0, (3/10 : ℚ), (7/10 : ℚ)], .kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .dom [0, 0, (15/19 : ℚ), (4/19 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .kept 2, .kept 3, .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (18/19 : ℚ), (1/19 : ℚ)], .dom [0, 0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, 0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, 0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, 1, 0], .dom [0, 0, (15/19 : ℚ), (4/19 : ℚ)], .dom [0, 0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, 0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, 0, (3/19 : ℚ), (16/19 : ℚ)], .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .dom [0, 0, 1, 0], .dom [0, 0, (18/19 : ℚ), (1/19 : ℚ)], .dom [0, 0, (9/19 : ℚ), (10/19 : ℚ)], .dom [0, 0, (3/19 : ℚ), (16/19 : ℚ)], .kept 3, .dom [0, (4/9 : ℚ), (5/9 : ℚ), 0], .kept 2, .dom [0, 0, (18/19 : ℚ), (1/19 : ℚ)], .kept 0, .kept 1, .dom [0, (38/45 : ℚ), (7/45 : ℚ), 0]], [.kept 0, .kept 1, .dom [0, (9/26 : ℚ), (17/26 : ℚ)], .dom [0, (21/26 : ℚ), (5/26 : ℚ)], .dom [0, (9/13 : ℚ), (4/13 : ℚ)], .dom [0, (33/52 : ℚ), (19/52 : ℚ)], .dom [0, (6/13 : ℚ), (7/13 : ℚ)], .dom [0, (9/26 : ℚ), (17/26 : ℚ)], .dom [0, (3/26 : ℚ), (23/26 : ℚ)], .kept 2, .dom [0, (21/26 : ℚ), (5/26 : ℚ)], .dom [0, (9/13 : ℚ), (4/13 : ℚ)], .dom [0, (6/13 : ℚ), (7/13 : ℚ)], .dom [0, (9/26 : ℚ), (17/26 : ℚ)], .dom [0, (3/26 : ℚ), (23/26 : ℚ)], .dom [0, (21/26 : ℚ), (5/26 : ℚ)], .dom [0, (9/13 : ℚ), (4/13 : ℚ)], .dom [0, (6/13 : ℚ), (7/13 : ℚ)], .dom [0, (3/26 : ℚ), (23/26 : ℚ)], .dom [0, (21/26 : ℚ), (5/26 : ℚ)], .dom [0, (9/13 : ℚ), (4/13 : ℚ)], .dom [0, (6/13 : ℚ), (7/13 : ℚ)], .dom [0, (9/26 : ℚ), (17/26 : ℚ)], .dom [0, (3/26 : ℚ), (23/26 : ℚ)], .kept 2, .dom [0, (21/26 : ℚ), (5/26 : ℚ)], .dom [0, (9/13 : ℚ), (4/13 : ℚ)], .dom [0, (6/13 : ℚ), (7/13 : ℚ)], .dom [0, (9/26 : ℚ), (17/26 : ℚ)], .dom [0, (21/26 : ℚ), (5/26 : ℚ)], .dom [0, (9/13 : ℚ), (4/13 : ℚ)], .dom [0, (33/52 : ℚ), (19/52 : ℚ)], .kept 0, .kept 1, .dom [0, (51/52 : ℚ), (1/52 : ℚ)]], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 3, .kept 4, .kept 5, .kept 7, .kept 8, .kept 3, .kept 5, .kept 7, .kept 3, .kept 4, .kept 5, .kept 6, .kept 3, .kept 4, .kept 0, .kept 1, .kept 2], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 2, .kept 4, .kept 5, .kept 2, .kept 4, .kept 2, .kept 3, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 2, .kept 0, .kept 1], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]]]

/-- Branch candidate witnesses, in `candH` order. -/
def randic_sum_WHt : List (List Wit) := [
  [],
  [.kept 0],
  [.kept 0],
  [.kept 0, .dom [1]],
  [.kept 0, .dom [1], .dom [1]],
  [.kept 0, .dom [1, 0], .kept 1, .dom [1, 0], .dom [1, 0]],
  [.kept 0, .kept 0, .dom [1, 0], .kept 1, .dom [1, 0], .dom [1, 0], .dom [1, 0], .dom [1, 0]],
  [.kept 0, .kept 0, .dom [1, 0, 0], .dom [0, 1, 0], .kept 1, .dom [1, 0, 0], .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.kept 0, .kept 0, .kept 0, .dom [1, 0, 0], .dom [0, 1, 0], .dom [0, 1, 0], .kept 1, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [1, 0, 0], .kept 0, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 1, 0], .dom [0, 1, 0], .kept 1, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 1, 0], .dom [0, (9/14 : ℚ), (5/14 : ℚ)], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.kept 0, .kept 0, .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 1, 0], .kept 1, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 1, 0], .dom [0, 1, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 0, 1], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]],
  [.dom [1, 0, 0], .kept 0, .kept 0, .dom [1, 0, 0], .dom [0, 1, 0], .kept 1, .kept 1, .dom [1, 0, 0], .dom [1, 0, 0], .kept 2, .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 1, 0], .dom [0, 0, 1], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [0, 0, 1], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0], .dom [1, 0, 0]]]

/-- The certificate. -/
def randic_sum_C : Cert 3 where
  KB s c := (randic_sum_KBt.getD s []).getD c []
  KH m := randic_sum_KHt.getD m []
  WB s c := (randic_sum_WBt.getD s []).getD c []
  WH m := randic_sum_WHt.getD m []

/-- The sign conditions (positive multilinear recursion). -/
theorem randic_sum_signs : randic_sum_R.Signs 12 (0 : Fin 3) where
  e_nn := by decide +kernel
  e_pos := by decide +kernel
  T_nn := by decide +kernel
  T_pos := by decide +kernel
  T_left := by decide +kernel
  T_right := by decide +kernel
  P_nn := by decide +kernel
  P_pos := by decide +kernel
  P_col := by decide +kernel

/-- The dominance certificate: every candidate of every class has a checked
witness (exact rational arithmetic, evaluated by the kernel). -/
theorem randic_sum_valid : randic_sum_C.Valid randic_sum_R 12 (0 : Fin 3) := by decide +kernel

theorem randic_sum_F_nn : ∀ k, 1 ≤ k → k < 12 → ∀ i, 0 ≤ randic_sum_R.F k i := by
  decide +kernel

theorem randic_sum_F_pos : ∀ k, 1 ≤ k → k < 12 → ∀ i, 0 < randic_sum_R.F k i := by
  decide +kernel

/-- n = 2: every kept root bundle has value at most M_2 = 2. -/
theorem randic_sum_hV_2 : ∀ k, 1 ≤ k → k < 2 → ∀ p ∈ randic_sum_C.KB 1 k,
    randic_sum_R.root k p ≤ (2 : ℚ) := by
  decide +kernel

/-- n = 2: the listed maximizers (one rooting per isomorphism class)
attain 2. -/
theorem randic_sum_listed_2 : ∀ T ∈ ([RTree.node [RTree.node []]] : List RTree),
    T.size = 2 ∧ randic_sum_R.pi T = (2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 2 vertices. -/
theorem randic_sum_max_2 :
    IsGreatest {x | ∃ T : RTree, T.size = 2 ∧ randic_sum_R.pi T = x} (2 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 2) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_2 _
    (randic_sum_listed_2 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 2 vertices: a tree attaining 2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_2 : ∀ l : List RTree, (RTree.node l).size = 2 →
    randic_sum_R.pi (.node l) = (2 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 1 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_2

/-- n = 3: every kept root bundle has value at most M_3 = 2. -/
theorem randic_sum_hV_3 : ∀ k, 1 ≤ k → k < 3 → ∀ p ∈ randic_sum_C.KB 2 k,
    randic_sum_R.root k p ≤ (2 : ℚ) := by
  decide +kernel

/-- n = 3: the listed maximizers (one rooting per isomorphism class)
attain 2. -/
theorem randic_sum_listed_3 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node []]] : List RTree),
    T.size = 3 ∧ randic_sum_R.pi T = (2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 3 vertices. -/
theorem randic_sum_max_3 :
    IsGreatest {x | ∃ T : RTree, T.size = 3 ∧ randic_sum_R.pi T = x} (2 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 3) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_3 _
    (randic_sum_listed_3 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 3 vertices: a tree attaining 2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_3 : ∀ l : List RTree, (RTree.node l).size = 3 →
    randic_sum_R.pi (.node l) = (2 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 2 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_3

/-- n = 4: every kept root bundle has value at most M_4 = 9/4. -/
theorem randic_sum_hV_4 : ∀ k, 1 ≤ k → k < 4 → ∀ p ∈ randic_sum_C.KB 3 k,
    randic_sum_R.root k p ≤ (9 / 4 : ℚ) := by
  decide +kernel

/-- n = 4: the listed maximizers (one rooting per isomorphism class)
attain 9/4. -/
theorem randic_sum_listed_4 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node []]]] : List RTree),
    T.size = 4 ∧ randic_sum_R.pi T = (9 / 4 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 4 vertices. -/
theorem randic_sum_max_4 :
    IsGreatest {x | ∃ T : RTree, T.size = 4 ∧ randic_sum_R.pi T = x} (9 / 4 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 4) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_4 _
    (randic_sum_listed_4 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 4 vertices: a tree attaining 9/4 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_4 : ∀ l : List RTree, (RTree.node l).size = 4 →
    randic_sum_R.pi (.node l) = (9 / 4 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 3 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_4

/-- n = 5: every kept root bundle has value at most M_5 = 5/2. -/
theorem randic_sum_hV_5 : ∀ k, 1 ≤ k → k < 5 → ∀ p ∈ randic_sum_C.KB 4 k,
    randic_sum_R.root k p ≤ (5 / 2 : ℚ) := by
  decide +kernel

/-- n = 5: the listed maximizers (one rooting per isomorphism class)
attain 5/2. -/
theorem randic_sum_listed_5 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []]]]] : List RTree),
    T.size = 5 ∧ randic_sum_R.pi T = (5 / 2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 5 vertices. -/
theorem randic_sum_max_5 :
    IsGreatest {x | ∃ T : RTree, T.size = 5 ∧ randic_sum_R.pi T = x} (5 / 2 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 5) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_5 _
    (randic_sum_listed_5 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 5 vertices: a tree attaining 5/2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_5 : ∀ l : List RTree, (RTree.node l).size = 5 →
    randic_sum_R.pi (.node l) = (5 / 2 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 4 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_5

/-- n = 6: every kept root bundle has value at most M_6 = 11/4. -/
theorem randic_sum_hV_6 : ∀ k, 1 ≤ k → k < 6 → ∀ p ∈ randic_sum_C.KB 5 k,
    randic_sum_R.root k p ≤ (11 / 4 : ℚ) := by
  decide +kernel

/-- n = 6: the listed maximizers (one rooting per isomorphism class)
attain 11/4. -/
theorem randic_sum_listed_6 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 6 ∧ randic_sum_R.pi T = (11 / 4 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 6 vertices. -/
theorem randic_sum_max_6 :
    IsGreatest {x | ∃ T : RTree, T.size = 6 ∧ randic_sum_R.pi T = x} (11 / 4 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 6) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_6 _
    (randic_sum_listed_6 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 6 vertices: a tree attaining 11/4 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_6 : ∀ l : List RTree, (RTree.node l).size = 6 →
    randic_sum_R.pi (.node l) = (11 / 4 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 5 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_6

/-- n = 7: every kept root bundle has value at most M_7 = 3. -/
theorem randic_sum_hV_7 : ∀ k, 1 ≤ k → k < 7 → ∀ p ∈ randic_sum_C.KB 6 k,
    randic_sum_R.root k p ≤ (3 : ℚ) := by
  decide +kernel

/-- n = 7: the listed maximizers (one rooting per isomorphism class)
attain 3. -/
theorem randic_sum_listed_7 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]], RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []]]]] : List RTree),
    T.size = 7 ∧ randic_sum_R.pi T = (3 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 7 vertices. -/
theorem randic_sum_max_7 :
    IsGreatest {x | ∃ T : RTree, T.size = 7 ∧ randic_sum_R.pi T = x} (3 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 7) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_7 _
    (randic_sum_listed_7 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 7 vertices: a tree attaining 3 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_7 : ∀ l : List RTree, (RTree.node l).size = 7 →
    randic_sum_R.pi (.node l) = (3 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 6 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_7

/-- n = 8: every kept root bundle has value at most M_8 = 13/4. -/
theorem randic_sum_hV_8 : ∀ k, 1 ≤ k → k < 8 → ∀ p ∈ randic_sum_C.KB 7 k,
    randic_sum_R.root k p ≤ (13 / 4 : ℚ) := by
  decide +kernel

/-- n = 8: the listed maximizers (one rooting per isomorphism class)
attain 13/4. -/
theorem randic_sum_listed_8 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]], RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 8 ∧ randic_sum_R.pi T = (13 / 4 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 8 vertices. -/
theorem randic_sum_max_8 :
    IsGreatest {x | ∃ T : RTree, T.size = 8 ∧ randic_sum_R.pi T = x} (13 / 4 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 8) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_8 _
    (randic_sum_listed_8 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 8 vertices: a tree attaining 13/4 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_8 : ∀ l : List RTree, (RTree.node l).size = 8 →
    randic_sum_R.pi (.node l) = (13 / 4 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 7 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_8

/-- n = 9: every kept root bundle has value at most M_9 = 7/2. -/
theorem randic_sum_hV_9 : ∀ k, 1 ≤ k → k < 9 → ∀ p ∈ randic_sum_C.KB 8 k,
    randic_sum_R.root k p ≤ (7 / 2 : ℚ) := by
  decide +kernel

/-- n = 9: the listed maximizers (one rooting per isomorphism class)
attain 7/2. -/
theorem randic_sum_listed_9 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]]], RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node [RTree.node []]]]]], RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node [RTree.node []]], RTree.node [RTree.node [RTree.node []]]]], RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node []]]]] : List RTree),
    T.size = 9 ∧ randic_sum_R.pi T = (7 / 2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 9 vertices. -/
theorem randic_sum_max_9 :
    IsGreatest {x | ∃ T : RTree, T.size = 9 ∧ randic_sum_R.pi T = x} (7 / 2 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 9) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_9 _
    (randic_sum_listed_9 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 9 vertices: a tree attaining 7/2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_9 : ∀ l : List RTree, (RTree.node l).size = 9 →
    randic_sum_R.pi (.node l) = (7 / 2 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 8 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_9

/-- n = 10: every kept root bundle has value at most M_10 = 34/9. -/
theorem randic_sum_hV_10 : ∀ k, 1 ≤ k → k < 10 → ∀ p ∈ randic_sum_C.KB 9 k,
    randic_sum_R.root k p ≤ (34 / 9 : ℚ) := by
  decide +kernel

/-- n = 10: the listed maximizers (one rooting per isomorphism class)
attain 34/9. -/
theorem randic_sum_listed_10 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 10 ∧ randic_sum_R.pi T = (34 / 9 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 10 vertices. -/
theorem randic_sum_max_10 :
    IsGreatest {x | ∃ T : RTree, T.size = 10 ∧ randic_sum_R.pi T = x} (34 / 9 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 10) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_10 _
    (randic_sum_listed_10 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 10 vertices: a tree attaining 34/9 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_10 : ∀ l : List RTree, (RTree.node l).size = 10 →
    randic_sum_R.pi (.node l) = (34 / 9 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 9 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_10

/-- n = 11: every kept root bundle has value at most M_11 = 145/36. -/
theorem randic_sum_hV_11 : ∀ k, 1 ≤ k → k < 11 → ∀ p ∈ randic_sum_C.KB 10 k,
    randic_sum_R.root k p ≤ (145 / 36 : ℚ) := by
  decide +kernel

/-- n = 11: the listed maximizers (one rooting per isomorphism class)
attain 145/36. -/
theorem randic_sum_listed_11 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []]]]]]] : List RTree),
    T.size = 11 ∧ randic_sum_R.pi T = (145 / 36 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 11 vertices. -/
theorem randic_sum_max_11 :
    IsGreatest {x | ∃ T : RTree, T.size = 11 ∧ randic_sum_R.pi T = x} (145 / 36 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 11) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_11 _
    (randic_sum_listed_11 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 11 vertices: a tree attaining 145/36 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_11 : ∀ l : List RTree, (RTree.node l).size = 11 →
    randic_sum_R.pi (.node l) = (145 / 36 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 10 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_11

/-- n = 12: every kept root bundle has value at most M_12 = 103/24. -/
theorem randic_sum_hV_12 : ∀ k, 1 ≤ k → k < 12 → ∀ p ∈ randic_sum_C.KB 11 k,
    randic_sum_R.root k p ≤ (103 / 24 : ℚ) := by
  decide +kernel

/-- n = 12: the listed maximizers (one rooting per isomorphism class)
attain 103/24. -/
theorem randic_sum_listed_12 : ∀ T ∈ ([RTree.node [RTree.node [], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []], RTree.node [RTree.node [RTree.node []], RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 12 ∧ randic_sum_R.pi T = (103 / 24 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 12 vertices. -/
theorem randic_sum_max_12 :
    IsGreatest {x | ∃ T : RTree, T.size = 12 ∧ randic_sum_R.pi T = x} (103 / 24 : ℚ) :=
  isGreatest_pi randic_sum_signs randic_sum_valid (n := 12) (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_nn k h1 (by omega)) randic_sum_hV_12 _
    (randic_sum_listed_12 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 12 vertices: a tree attaining 103/24 has every
branch state and every partial bundle state on the kept hull points. -/
theorem randic_sum_kept_12 : ∀ l : List RTree, (RTree.node l).size = 12 →
    randic_sum_R.pi (.node l) = (103 / 24 : ℚ) →
      KeptL randic_sum_R randic_sum_C l ∧ randic_sum_R.bundle l ∈ randic_sum_C.KB 11 l.length :=
  kept_of_pi_eq randic_sum_signs randic_sum_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => randic_sum_F_pos k h1 (by omega)) randic_sum_hV_12

/-- MAIN.  The exact maximum for every n = 2..12. -/
theorem randic_sum :
    IsGreatest {x | ∃ T : RTree, T.size = 2 ∧ randic_sum_R.pi T = x} (2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 3 ∧ randic_sum_R.pi T = x} (2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 4 ∧ randic_sum_R.pi T = x} (9 / 4 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 5 ∧ randic_sum_R.pi T = x} (5 / 2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 6 ∧ randic_sum_R.pi T = x} (11 / 4 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 7 ∧ randic_sum_R.pi T = x} (3 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 8 ∧ randic_sum_R.pi T = x} (13 / 4 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 9 ∧ randic_sum_R.pi T = x} (7 / 2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 10 ∧ randic_sum_R.pi T = x} (34 / 9 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 11 ∧ randic_sum_R.pi T = x} (145 / 36 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 12 ∧ randic_sum_R.pi T = x} (103 / 24 : ℚ) :=
  ⟨randic_sum_max_2, randic_sum_max_3, randic_sum_max_4, randic_sum_max_5, randic_sum_max_6, randic_sum_max_7, randic_sum_max_8, randic_sum_max_9, randic_sum_max_10, randic_sum_max_11, randic_sum_max_12⟩

/-! ## Instance `synthetic`: a synthetic recursion

Dimension 2, trees on n = 2..12 vertices, 181 kept points, 536 candidate witnesses.
Certified values: M_2 = 2, M_3 = 23/12, M_4 = 9/4, M_5 = 185/72, M_6 = 53/18, M_7 = 1457/432, M_8 = 1669/432, M_9 = 11471/2592, M_10 = 365/72, M_11 = 90311/15552, M_12 = 103451/15552. -/

/-- The recursion. -/
def synthetic_R : Rec 2 where
  e := ![1, 0]
  T := fun i j l => (![![![1, 0], ![0, 0]], ![![0, 1], ![1, 0]]] : Fin 2 → Fin 2 → Fin 2 → ℚ) i j l
  P := fun c => ![![1, (2 * ((1 + ((c : ℚ) ^ 2) + (2 * (c : ℚ))))⁻¹)], ![((2 + (c : ℚ)))⁻¹, 0]]
  F := fun k => ![1, (2 * ((k : ℚ) ^ 2)⁻¹)]

/-- Kept bundle points, indexed [s][c]. -/
def synthetic_KBt : List (List (List (Vec 2))) := [
  [[![1, 0]]],
  [[], [![1, (1/2 : ℚ)]]],
  [[], [![(5/4 : ℚ), (1/3 : ℚ)]], [![1, 1]]],
  [[], [![(17/12 : ℚ), (5/12 : ℚ)]], [![(5/4 : ℚ), (23/24 : ℚ)]], [![1, (3/2 : ℚ)]]],
  [[], [![(13/8 : ℚ), (17/36 : ℚ)]], [![(17/12 : ℚ), (9/8 : ℚ)], ![(25/16 : ℚ), (5/6 : ℚ)]], [![(5/4 : ℚ), (19/12 : ℚ)]], [![1, 2]]],
  [[], [![(67/36 : ℚ), (13/24 : ℚ)]], [![(13/8 : ℚ), (185/144 : ℚ)], ![(85/48 : ℚ), (143/144 : ℚ)]], [![(17/12 : ℚ), (11/6 : ℚ)], ![(25/16 : ℚ), (155/96 : ℚ)]], [![(5/4 : ℚ), (53/24 : ℚ)]], [![1, (5/2 : ℚ)]]],
  [[], [![(307/144 : ℚ), (67/108 : ℚ)]], [![(67/36 : ℚ), (53/36 : ℚ)], ![(289/144 : ℚ), (85/72 : ℚ)], ![(65/32 : ℚ), (163/144 : ℚ)]], [![(13/8 : ℚ), (151/72 : ℚ)], ![(85/48 : ℚ), (541/288 : ℚ)], ![(125/64 : ℚ), (25/16 : ℚ)]], [![(17/12 : ℚ), (61/24 : ℚ)], ![(25/16 : ℚ), (115/48 : ℚ)]], [![(5/4 : ℚ), (17/6 : ℚ)]], [![1, 3]]],
  [[], [![(1055/432 : ℚ), (307/432 : ℚ)]], [![(307/144 : ℚ), (1457/864 : ℚ)], ![(221/96 : ℚ), (1163/864 : ℚ)], ![(335/144 : ℚ), (1121/864 : ℚ)]], [![(67/36 : ℚ), (173/72 : ℚ)], ![(289/144 : ℚ), (629/288 : ℚ)], ![(65/32 : ℚ), (1237/576 : ℚ)], ![(425/192 : ℚ), (1055/576 : ℚ)]], [![(13/8 : ℚ), (419/144 : ℚ)], ![(85/48 : ℚ), (199/72 : ℚ)], ![(125/64 : ℚ), (325/128 : ℚ)]], [![(17/12 : ℚ), (13/4 : ℚ)], ![(25/16 : ℚ), (305/96 : ℚ)]], [![(5/4 : ℚ), (83/24 : ℚ)]], [![1, (7/2 : ℚ)]]],
  [[], [![(2417/864 : ℚ), (1055/1296 : ℚ)]], [![(1055/432 : ℚ), (1669/864 : ℚ)], ![(1139/432 : ℚ), (1333/864 : ℚ)], ![(169/64 : ℚ), (221/144 : ℚ)], ![(1535/576 : ℚ), (107/72 : ℚ)]], [![(307/144 : ℚ), (1189/432 : ℚ)], ![(221/96 : ℚ), (4315/1728 : ℚ)], ![(335/144 : ℚ), (1063/432 : ℚ)], ![(1445/576 : ℚ), (1853/864 : ℚ)], ![(325/128 : ℚ), (1205/576 : ℚ)]], [![(67/36 : ℚ), (10/3 : ℚ)], ![(289/144 : ℚ), (51/16 : ℚ)], ![(65/32 : ℚ), (911/288 : ℚ)], ![(425/192 : ℚ), (3385/1152 : ℚ)], ![(625/256 : ℚ), (125/48 : ℚ)]], [![(13/8 : ℚ), (67/18 : ℚ)], ![(85/48 : ℚ), (1051/288 : ℚ)], ![(125/64 : ℚ), (225/64 : ℚ)]], [![(25/16 : ℚ), (95/24 : ℚ)]], [![(5/4 : ℚ), (49/12 : ℚ)]], [![1, 4]]],
  [[], [![(4153/1296 : ℚ), (2417/2592 : ℚ)]], [![(2417/864 : ℚ), (11471/5184 : ℚ)], ![(5219/1728 : ℚ), (9161/5184 : ℚ)], ![(871/288 : ℚ), (9119/5184 : ℚ)], ![(5275/1728 : ℚ), (8825/5184 : ℚ)]], [![(1055/432 : ℚ), (227/72 : ℚ)], ![(1139/432 : ℚ), (103/36 : ℚ)], ![(169/64 : ℚ), (3289/1152 : ℚ)], ![(1535/576 : ℚ), (3247/1152 : ℚ)], ![(1105/384 : ℚ), (8467/3456 : ℚ)], ![(1675/576 : ℚ), (8285/3456 : ℚ)]], [![(307/144 : ℚ), (3299/864 : ℚ)], ![(221/96 : ℚ), (197/54 : ℚ)], ![(335/144 : ℚ), (3131/864 : ℚ)], ![(1445/576 : ℚ), (11747/3456 : ℚ)], ![(325/128 : ℚ), (7745/2304 : ℚ)], ![(2125/768 : ℚ), (775/256 : ℚ)]], [![(67/36 : ℚ), (307/72 : ℚ)], ![(289/144 : ℚ), (1207/288 : ℚ)], ![(65/32 : ℚ), (2407/576 : ℚ)], ![(425/192 : ℚ), (1165/288 : ℚ)], ![(625/256 : ℚ), (5875/1536 : ℚ)]], [![(85/48 : ℚ), (653/144 : ℚ)], ![(125/64 : ℚ), (575/128 : ℚ)]], [![(25/16 : ℚ), (455/96 : ℚ)]], [![(5/4 : ℚ), (113/24 : ℚ)]], [![1, (9/2 : ℚ)]]],
  [[], [![(6343/1728 : ℚ), (4153/3888 : ℚ)]], [![(4153/1296 : ℚ), (365/144 : ℚ)], ![(17935/5184 : ℚ), (583/288 : ℚ)], ![(4489/1296 : ℚ), (871/432 : ℚ)], ![(3991/1152 : ℚ), (10445/5184 : ℚ)], ![(12085/3456 : ℚ), (10109/5184 : ℚ)]], [![(2417/864 : ℚ), (9361/2592 : ℚ)], ![(5219/1728 : ℚ), (33979/10368 : ℚ)], ![(871/288 : ℚ), (8479/2592 : ℚ)], ![(5275/1728 : ℚ), (33475/10368 : ℚ)], ![(5695/1728 : ℚ), (29107/10368 : ℚ)], ![(845/256 : ℚ), (403/144 : ℚ)], ![(7675/2304 : ℚ), (4745/1728 : ℚ)]], [![(1055/432 : ℚ), (3779/864 : ℚ)], ![(1139/432 : ℚ), (3611/864 : ℚ)], ![(169/64 : ℚ), (2405/576 : ℚ)], ![(1535/576 : ℚ), (797/192 : ℚ)], ![(1105/384 : ℚ), (26879/6912 : ℚ)], ![(1675/576 : ℚ), (6655/1728 : ℚ)], ![(7225/2304 : ℚ), (12155/3456 : ℚ)], ![(1625/512 : ℚ), (7975/2304 : ℚ)]], [![(307/144 : ℚ), (1055/216 : ℚ)], ![(221/96 : ℚ), (8293/1728 : ℚ)], ![(335/144 : ℚ), (517/108 : ℚ)], ![(1445/576 : ℚ), (8041/1728 : ℚ)], ![(325/128 : ℚ), (5335/1152 : ℚ)], ![(2125/768 : ℚ), (6775/1536 : ℚ)], ![(3125/1024 : ℚ), (3125/768 : ℚ)]], [![(65/32 : ℚ), (187/36 : ℚ)], ![(425/192 : ℚ), (5935/1152 : ℚ)], ![(625/256 : ℚ), (3875/768 : ℚ)]], [![(125/64 : ℚ), (175/32 : ℚ)]], [![(25/16 : ℚ), (265/48 : ℚ)]], [![(5/4 : ℚ), (16/3 : ℚ)]], [![1, 5]]],
  [[], [![(65393/15552 : ℚ), (6343/5184 : ℚ)]], [![(6343/1728 : ℚ), (90311/31104 : ℚ)], ![(41089/10368 : ℚ), (72125/31104 : ℚ)], ![(20569/5184 : ℚ), (71831/31104 : ℚ)], ![(13715/3456 : ℚ), (71789/31104 : ℚ)], ![(20765/5184 : ℚ), (69479/31104 : ℚ)]], [![(4153/1296 : ℚ), (10723/2592 : ℚ)], ![(17935/5184 : ℚ), (38923/10368 : ℚ)], ![(4489/1296 : ℚ), (9715/2592 : ℚ)], ![(3991/1152 : ℚ), (77699/20736 : ℚ)], ![(12085/3456 : ℚ), (76691/20736 : ℚ)], ![(26095/6912 : ℚ), (7409/2304 : ℚ)], ![(4355/1152 : ℚ), (66499/20736 : ℚ)], ![(26375/6912 : ℚ), (65225/20736 : ℚ)]], [![(2417/864 : ℚ), (25973/5184 : ℚ)], ![(5219/1728 : ℚ), (12409/2592 : ℚ)], ![(871/288 : ℚ), (24797/5184 : ℚ)], ![(5275/1728 : ℚ), (12325/2592 : ℚ)], ![(5695/1728 : ℚ), (2887/648 : ℚ)], ![(845/256 : ℚ), (20501/4608 : ℚ)], ![(7675/2304 : ℚ), (60985/13824 : ℚ)], ![(5525/1536 : ℚ), (55595/13824 : ℚ)], ![(8375/2304 : ℚ), (18275/4608 : ℚ)]], [![(1055/432 : ℚ), (2417/432 : ℚ)], ![(1139/432 : ℚ), (2375/432 : ℚ)], ![(169/64 : ℚ), (6331/1152 : ℚ)], ![(1535/576 : ℚ), (6317/1152 : ℚ)], ![(1105/384 : ℚ), (4603/864 : ℚ)], ![(1675/576 : ℚ), (18335/3456 : ℚ)], ![(7225/2304 : ℚ), (70295/13824 : ℚ)], ![(1625/512 : ℚ), (46525/9216 : ℚ)], ![(10625/3072 : ℚ), (43375/9216 : ℚ)]], [![(335/144 : ℚ), (5141/864 : ℚ)], ![(1445/576 : ℚ), (20417/3456 : ℚ)], ![(325/128 : ℚ), (13595/2304 : ℚ)], ![(2125/768 : ℚ), (2225/384 : ℚ)], ![(3125/1024 : ℚ), (34375/6144 : ℚ)]], [![(625/256 : ℚ), (9625/1536 : ℚ)]], [![(125/64 : ℚ), (825/128 : ℚ)]], [![(25/16 : ℚ), (605/96 : ℚ)]], [![(5/4 : ℚ), (143/24 : ℚ)]], [![1, (11/2 : ℚ)]]]]

/-- Kept branch points, indexed [m]. -/
def synthetic_KHt : List (List (Vec 2)) := [
  [],
  [![1, (1/2 : ℚ)]],
  [![(5/4 : ℚ), (1/3 : ℚ)]],
  [![(17/12 : ℚ), (5/12 : ℚ)]],
  [![(13/8 : ℚ), (17/36 : ℚ)]],
  [![(67/36 : ℚ), (13/24 : ℚ)]],
  [![(307/144 : ℚ), (67/108 : ℚ)]],
  [![(1055/432 : ℚ), (307/432 : ℚ)]],
  [![(2417/864 : ℚ), (1055/1296 : ℚ)]],
  [![(4153/1296 : ℚ), (2417/2592 : ℚ)]],
  [![(6343/1728 : ℚ), (4153/3888 : ℚ)]],
  [![(65393/15552 : ℚ), (6343/5184 : ℚ)]]]

/-- Bundle candidate witnesses, in `candB` order. -/
def synthetic_WBt : List (List (List Wit)) := [
  [[.kept 0]],
  [[], [.kept 0]],
  [[], [.kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 2, .kept 1, .kept 2, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 2, .kept 1, .kept 1, .kept 2, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 2, .kept 3, .kept 1, .kept 3, .kept 2, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 1, .kept 0], [.kept 0, .kept 1, .kept 1, .kept 0], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 3, .kept 1, .kept 2, .kept 1, .kept 3, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 2, .kept 3, .kept 4, .kept 1, .kept 3, .kept 1, .kept 4, .kept 2, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 2, .kept 3, .kept 4, .kept 1, .kept 3, .kept 2, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 1, .kept 2, .kept 1, .kept 0], [.dom [1], .kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 3, .kept 1, .kept 2, .kept 2, .kept 1, .kept 3, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 3, .kept 4, .kept 5, .kept 1, .dom [0, 0, 0, (17/105 : ℚ), (88/105 : ℚ), 0], .kept 4, .kept 2, .kept 4, .kept 1, .kept 5, .kept 3, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 4, .kept 5, .kept 1, .kept 3, .kept 5, .kept 1, .kept 4, .kept 2, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 2, .kept 3, .kept 4, .kept 1, .kept 3, .kept 2, .kept 0], [.dom [1, 0], .kept 0, .kept 1, .kept 0, .kept 1, .kept 0, .dom [1, 0]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 4, .kept 1, .kept 3, .kept 2, .kept 3, .kept 1, .kept 4, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 3, .kept 4, .kept 5, .kept 6, .kept 1, .dom [0, 0, 0, (17/120 : ℚ), (103/120 : ℚ), 0, 0], .kept 4, .kept 2, .dom [0, 0, 0, (17/120 : ℚ), (103/120 : ℚ), 0, 0], .kept 5, .kept 2, .kept 4, .kept 1, .kept 6, .kept 3, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 1, .dom [0, 0, 0, (17/105 : ℚ), (88/105 : ℚ), 0, 0, 0], .kept 4, .kept 6, .kept 2, .kept 4, .kept 7, .kept 1, .kept 5, .kept 3, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 1, .kept 3, .kept 5, .kept 1, .kept 4, .kept 2, .kept 0], [.dom [1, 0, 0], .dom [1, 0, 0], .kept 0, .kept 1, .kept 2, .kept 0, .kept 1, .kept 2, .dom [1, 0, 0], .kept 1, .kept 0, .dom [1, 0, 0]], [.dom [1], .kept 0, .kept 0, .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]],
  [[], [.kept 0], [.kept 0, .kept 4, .kept 1, .kept 3, .kept 2, .kept 2, .kept 3, .kept 1, .kept 4, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 4, .kept 5, .kept 6, .kept 7, .kept 1, .dom [0, 0, 0, 0, (119/825 : ℚ), (706/825 : ℚ), 0, 0], .dom [0, 0, 0, 0, (34/275 : ℚ), (241/275 : ℚ), 0, 0], .kept 5, .kept 3, .dom [0, 0, 0, 0, (34/275 : ℚ), (241/275 : ℚ), 0, 0], .kept 6, .kept 2, .dom [0, 0, 0, 0, (119/825 : ℚ), (706/825 : ℚ), 0, 0], .kept 6, .kept 3, .kept 5, .kept 1, .kept 7, .kept 4, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 1, .dom [0, 0, 0, (17/120 : ℚ), (103/120 : ℚ), 0, 0, 0, 0], .kept 4, .dom [0, 0, 0, 0, 0, 0, (17/105 : ℚ), (88/105 : ℚ), 0], .kept 7, .kept 2, .dom [0, 0, 0, (17/120 : ℚ), (103/120 : ℚ), 0, 0, 0, 0], .kept 5, .kept 7, .kept 2, .kept 4, .kept 8, .kept 1, .kept 6, .kept 3, .kept 0], [.kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 3, .kept 4, .kept 5, .kept 6, .kept 7, .kept 8, .kept 1, .dom [0, 0, 0, (17/105 : ℚ), (88/105 : ℚ), 0, 0, 0, 0], .kept 4, .kept 6, .kept 8, .kept 2, .kept 4, .kept 7, .kept 1, .kept 5, .kept 3, .kept 0], [.dom [1, 0, 0, 0, 0], .dom [1, 0, 0, 0, 0], .kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .kept 0, .kept 1, .kept 2, .kept 3, .kept 4, .dom [1, 0, 0, 0, 0], .kept 1, .kept 3, .dom [1, 0, 0, 0, 0], .kept 2, .kept 0, .dom [1, 0, 0, 0, 0]], [.dom [1], .dom [1], .kept 0, .dom [1], .kept 0, .dom [1], .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1], .dom [1]], [.kept 0, .kept 0, .dom [1]], [.kept 0, .kept 0], [.kept 0]]]

/-- Branch candidate witnesses, in `candH` order. -/
def synthetic_WHt : List (List Wit) := [
  [],
  [.kept 0],
  [.kept 0],
  [.kept 0, .dom [1]],
  [.kept 0, .dom [1], .dom [1]],
  [.kept 0, .dom [1], .dom [1], .dom [1], .dom [1]],
  [.kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]],
  [.kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]],
  [.kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]],
  [.kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]],
  [.kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]],
  [.kept 0, .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1], .dom [1]]]

/-- The certificate. -/
def synthetic_C : Cert 2 where
  KB s c := (synthetic_KBt.getD s []).getD c []
  KH m := synthetic_KHt.getD m []
  WB s c := (synthetic_WBt.getD s []).getD c []
  WH m := synthetic_WHt.getD m []

/-- The sign conditions (positive multilinear recursion). -/
theorem synthetic_signs : synthetic_R.Signs 12 (0 : Fin 2) where
  e_nn := by decide +kernel
  e_pos := by decide +kernel
  T_nn := by decide +kernel
  T_pos := by decide +kernel
  T_left := by decide +kernel
  T_right := by decide +kernel
  P_nn := by decide +kernel
  P_pos := by decide +kernel
  P_col := by decide +kernel

/-- The dominance certificate: every candidate of every class has a checked
witness (exact rational arithmetic, evaluated by the kernel). -/
theorem synthetic_valid : synthetic_C.Valid synthetic_R 12 (0 : Fin 2) := by decide +kernel

theorem synthetic_F_nn : ∀ k, 1 ≤ k → k < 12 → ∀ i, 0 ≤ synthetic_R.F k i := by
  decide +kernel

theorem synthetic_F_pos : ∀ k, 1 ≤ k → k < 12 → ∀ i, 0 < synthetic_R.F k i := by
  decide +kernel

/-- n = 2: every kept root bundle has value at most M_2 = 2. -/
theorem synthetic_hV_2 : ∀ k, 1 ≤ k → k < 2 → ∀ p ∈ synthetic_C.KB 1 k,
    synthetic_R.root k p ≤ (2 : ℚ) := by
  decide +kernel

/-- n = 2: the listed maximizers (one rooting per isomorphism class)
attain 2. -/
theorem synthetic_listed_2 : ∀ T ∈ ([RTree.node [RTree.node []]] : List RTree),
    T.size = 2 ∧ synthetic_R.pi T = (2 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 2 vertices. -/
theorem synthetic_max_2 :
    IsGreatest {x | ∃ T : RTree, T.size = 2 ∧ synthetic_R.pi T = x} (2 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 2) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_2 _
    (synthetic_listed_2 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 2 vertices: a tree attaining 2 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_2 : ∀ l : List RTree, (RTree.node l).size = 2 →
    synthetic_R.pi (.node l) = (2 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 1 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_2

/-- n = 3: every kept root bundle has value at most M_3 = 23/12. -/
theorem synthetic_hV_3 : ∀ k, 1 ≤ k → k < 3 → ∀ p ∈ synthetic_C.KB 2 k,
    synthetic_R.root k p ≤ (23 / 12 : ℚ) := by
  decide +kernel

/-- n = 3: the listed maximizers (one rooting per isomorphism class)
attain 23/12. -/
theorem synthetic_listed_3 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node []]]] : List RTree),
    T.size = 3 ∧ synthetic_R.pi T = (23 / 12 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 3 vertices. -/
theorem synthetic_max_3 :
    IsGreatest {x | ∃ T : RTree, T.size = 3 ∧ synthetic_R.pi T = x} (23 / 12 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 3) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_3 _
    (synthetic_listed_3 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 3 vertices: a tree attaining 23/12 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_3 : ∀ l : List RTree, (RTree.node l).size = 3 →
    synthetic_R.pi (.node l) = (23 / 12 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 2 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_3

/-- n = 4: every kept root bundle has value at most M_4 = 9/4. -/
theorem synthetic_hV_4 : ∀ k, 1 ≤ k → k < 4 → ∀ p ∈ synthetic_C.KB 3 k,
    synthetic_R.root k p ≤ (9 / 4 : ℚ) := by
  decide +kernel

/-- n = 4: the listed maximizers (one rooting per isomorphism class)
attain 9/4. -/
theorem synthetic_listed_4 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node []]]]] : List RTree),
    T.size = 4 ∧ synthetic_R.pi T = (9 / 4 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 4 vertices. -/
theorem synthetic_max_4 :
    IsGreatest {x | ∃ T : RTree, T.size = 4 ∧ synthetic_R.pi T = x} (9 / 4 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 4) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_4 _
    (synthetic_listed_4 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 4 vertices: a tree attaining 9/4 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_4 : ∀ l : List RTree, (RTree.node l).size = 4 →
    synthetic_R.pi (.node l) = (9 / 4 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 3 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_4

/-- n = 5: every kept root bundle has value at most M_5 = 185/72. -/
theorem synthetic_hV_5 : ∀ k, 1 ≤ k → k < 5 → ∀ p ∈ synthetic_C.KB 4 k,
    synthetic_R.root k p ≤ (185 / 72 : ℚ) := by
  decide +kernel

/-- n = 5: the listed maximizers (one rooting per isomorphism class)
attain 185/72. -/
theorem synthetic_listed_5 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]] : List RTree),
    T.size = 5 ∧ synthetic_R.pi T = (185 / 72 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 5 vertices. -/
theorem synthetic_max_5 :
    IsGreatest {x | ∃ T : RTree, T.size = 5 ∧ synthetic_R.pi T = x} (185 / 72 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 5) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_5 _
    (synthetic_listed_5 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 5 vertices: a tree attaining 185/72 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_5 : ∀ l : List RTree, (RTree.node l).size = 5 →
    synthetic_R.pi (.node l) = (185 / 72 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 4 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_5

/-- n = 6: every kept root bundle has value at most M_6 = 53/18. -/
theorem synthetic_hV_6 : ∀ k, 1 ≤ k → k < 6 → ∀ p ∈ synthetic_C.KB 5 k,
    synthetic_R.root k p ≤ (53 / 18 : ℚ) := by
  decide +kernel

/-- n = 6: the listed maximizers (one rooting per isomorphism class)
attain 53/18. -/
theorem synthetic_listed_6 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]] : List RTree),
    T.size = 6 ∧ synthetic_R.pi T = (53 / 18 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 6 vertices. -/
theorem synthetic_max_6 :
    IsGreatest {x | ∃ T : RTree, T.size = 6 ∧ synthetic_R.pi T = x} (53 / 18 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 6) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_6 _
    (synthetic_listed_6 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 6 vertices: a tree attaining 53/18 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_6 : ∀ l : List RTree, (RTree.node l).size = 6 →
    synthetic_R.pi (.node l) = (53 / 18 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 5 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_6

/-- n = 7: every kept root bundle has value at most M_7 = 1457/432. -/
theorem synthetic_hV_7 : ∀ k, 1 ≤ k → k < 7 → ∀ p ∈ synthetic_C.KB 6 k,
    synthetic_R.root k p ≤ (1457 / 432 : ℚ) := by
  decide +kernel

/-- n = 7: the listed maximizers (one rooting per isomorphism class)
attain 1457/432. -/
theorem synthetic_listed_7 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]]] : List RTree),
    T.size = 7 ∧ synthetic_R.pi T = (1457 / 432 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 7 vertices. -/
theorem synthetic_max_7 :
    IsGreatest {x | ∃ T : RTree, T.size = 7 ∧ synthetic_R.pi T = x} (1457 / 432 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 7) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_7 _
    (synthetic_listed_7 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 7 vertices: a tree attaining 1457/432 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_7 : ∀ l : List RTree, (RTree.node l).size = 7 →
    synthetic_R.pi (.node l) = (1457 / 432 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 6 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_7

/-- n = 8: every kept root bundle has value at most M_8 = 1669/432. -/
theorem synthetic_hV_8 : ∀ k, 1 ≤ k → k < 8 → ∀ p ∈ synthetic_C.KB 7 k,
    synthetic_R.root k p ≤ (1669 / 432 : ℚ) := by
  decide +kernel

/-- n = 8: the listed maximizers (one rooting per isomorphism class)
attain 1669/432. -/
theorem synthetic_listed_8 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]]]] : List RTree),
    T.size = 8 ∧ synthetic_R.pi T = (1669 / 432 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 8 vertices. -/
theorem synthetic_max_8 :
    IsGreatest {x | ∃ T : RTree, T.size = 8 ∧ synthetic_R.pi T = x} (1669 / 432 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 8) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_8 _
    (synthetic_listed_8 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 8 vertices: a tree attaining 1669/432 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_8 : ∀ l : List RTree, (RTree.node l).size = 8 →
    synthetic_R.pi (.node l) = (1669 / 432 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 7 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_8

/-- n = 9: every kept root bundle has value at most M_9 = 11471/2592. -/
theorem synthetic_hV_9 : ∀ k, 1 ≤ k → k < 9 → ∀ p ∈ synthetic_C.KB 8 k,
    synthetic_R.root k p ≤ (11471 / 2592 : ℚ) := by
  decide +kernel

/-- n = 9: the listed maximizers (one rooting per isomorphism class)
attain 11471/2592. -/
theorem synthetic_listed_9 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]]]]] : List RTree),
    T.size = 9 ∧ synthetic_R.pi T = (11471 / 2592 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 9 vertices. -/
theorem synthetic_max_9 :
    IsGreatest {x | ∃ T : RTree, T.size = 9 ∧ synthetic_R.pi T = x} (11471 / 2592 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 9) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_9 _
    (synthetic_listed_9 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 9 vertices: a tree attaining 11471/2592 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_9 : ∀ l : List RTree, (RTree.node l).size = 9 →
    synthetic_R.pi (.node l) = (11471 / 2592 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 8 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_9

/-- n = 10: every kept root bundle has value at most M_10 = 365/72. -/
theorem synthetic_hV_10 : ∀ k, 1 ≤ k → k < 10 → ∀ p ∈ synthetic_C.KB 9 k,
    synthetic_R.root k p ≤ (365 / 72 : ℚ) := by
  decide +kernel

/-- n = 10: the listed maximizers (one rooting per isomorphism class)
attain 365/72. -/
theorem synthetic_listed_10 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]]]]]] : List RTree),
    T.size = 10 ∧ synthetic_R.pi T = (365 / 72 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 10 vertices. -/
theorem synthetic_max_10 :
    IsGreatest {x | ∃ T : RTree, T.size = 10 ∧ synthetic_R.pi T = x} (365 / 72 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 10) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_10 _
    (synthetic_listed_10 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 10 vertices: a tree attaining 365/72 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_10 : ∀ l : List RTree, (RTree.node l).size = 10 →
    synthetic_R.pi (.node l) = (365 / 72 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 9 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_10

/-- n = 11: every kept root bundle has value at most M_11 = 90311/15552. -/
theorem synthetic_hV_11 : ∀ k, 1 ≤ k → k < 11 → ∀ p ∈ synthetic_C.KB 10 k,
    synthetic_R.root k p ≤ (90311 / 15552 : ℚ) := by
  decide +kernel

/-- n = 11: the listed maximizers (one rooting per isomorphism class)
attain 90311/15552. -/
theorem synthetic_listed_11 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]]]]]]] : List RTree),
    T.size = 11 ∧ synthetic_R.pi T = (90311 / 15552 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 11 vertices. -/
theorem synthetic_max_11 :
    IsGreatest {x | ∃ T : RTree, T.size = 11 ∧ synthetic_R.pi T = x} (90311 / 15552 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 11) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_11 _
    (synthetic_listed_11 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 11 vertices: a tree attaining 90311/15552 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_11 : ∀ l : List RTree, (RTree.node l).size = 11 →
    synthetic_R.pi (.node l) = (90311 / 15552 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 10 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_11

/-- n = 12: every kept root bundle has value at most M_12 = 103451/15552. -/
theorem synthetic_hV_12 : ∀ k, 1 ≤ k → k < 12 → ∀ p ∈ synthetic_C.KB 11 k,
    synthetic_R.root k p ≤ (103451 / 15552 : ℚ) := by
  decide +kernel

/-- n = 12: the listed maximizers (one rooting per isomorphism class)
attain 103451/15552. -/
theorem synthetic_listed_12 : ∀ T ∈ ([RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node [RTree.node []]]]]]]]]]]]] : List RTree),
    T.size = 12 ∧ synthetic_R.pi T = (103451 / 15552 : ℚ) := by
  decide +kernel

/-- EXACT MAXIMUM over all trees on 12 vertices. -/
theorem synthetic_max_12 :
    IsGreatest {x | ∃ T : RTree, T.size = 12 ∧ synthetic_R.pi T = x} (103451 / 15552 : ℚ) :=
  isGreatest_pi synthetic_signs synthetic_valid (n := 12) (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_nn k h1 (by omega)) synthetic_hV_12 _
    (synthetic_listed_12 _ List.mem_cons_self)

/-- MAXIMIZER STRUCTURE on 12 vertices: a tree attaining 103451/15552 has every
branch state and every partial bundle state on the kept hull points. -/
theorem synthetic_kept_12 : ∀ l : List RTree, (RTree.node l).size = 12 →
    synthetic_R.pi (.node l) = (103451 / 15552 : ℚ) →
      KeptL synthetic_R synthetic_C l ∧ synthetic_R.bundle l ∈ synthetic_C.KB 11 l.length :=
  kept_of_pi_eq synthetic_signs synthetic_valid (by norm_num) (by norm_num)
    (fun k h1 h2 => synthetic_F_pos k h1 (by omega)) synthetic_hV_12

/-- MAIN.  The exact maximum for every n = 2..12. -/
theorem synthetic :
    IsGreatest {x | ∃ T : RTree, T.size = 2 ∧ synthetic_R.pi T = x} (2 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 3 ∧ synthetic_R.pi T = x} (23 / 12 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 4 ∧ synthetic_R.pi T = x} (9 / 4 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 5 ∧ synthetic_R.pi T = x} (185 / 72 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 6 ∧ synthetic_R.pi T = x} (53 / 18 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 7 ∧ synthetic_R.pi T = x} (1457 / 432 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 8 ∧ synthetic_R.pi T = x} (1669 / 432 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 9 ∧ synthetic_R.pi T = x} (11471 / 2592 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 10 ∧ synthetic_R.pi T = x} (365 / 72 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 11 ∧ synthetic_R.pi T = x} (90311 / 15552 : ℚ) ∧
    IsGreatest {x | ∃ T : RTree, T.size = 12 ∧ synthetic_R.pi T = x} (103451 / 15552 : ℚ) :=
  ⟨synthetic_max_2, synthetic_max_3, synthetic_max_4, synthetic_max_5, synthetic_max_6, synthetic_max_7, synthetic_max_8, synthetic_max_9, synthetic_max_10, synthetic_max_11, synthetic_max_12⟩

end AffineHullDominance
