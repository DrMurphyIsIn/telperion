/- telperion 0.1.6 | family ConcavePooledInductionExt | input-hash 97c9813a8f757623
   198 theorems, 22 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace ConcavePooledInductionExt

/-! ## Generic concave pooled induction (emitted once per file)

Method: concave-witness induction,
from unpublished work communicated by Professor John L. Goldwasser.
conjecture1_proved = False. -/

namespace ConcavePooled

/-- Finite rooted trees; an internal node has `m + 1 ≥ 1` children. -/
inductive PTree : Type
  | leaf : PTree
  | node (m : ℕ) (cs : Fin (m + 1) → PTree) : PTree

namespace PTree

/-- Number of vertices. -/
def size : PTree → ℕ
  | leaf => 1
  | node _ cs => (∑ i, size (cs i)) + 1

/-- The message: `y_leaf` at a leaf, `h (#children) (sum of the children's messages)`. -/
def msg (h : ℕ → ℝ → ℝ) (y0 : ℝ) : PTree → ℝ
  | leaf => y0
  | node m cs => h (m + 1) (∑ i, msg h y0 (cs i))

/-- The profit: `l_leaf` at a leaf, the children's profits plus `g (#children) (sum)`. -/
def ell (g h : ℕ → ℝ → ℝ) (l0 y0 : ℝ) : PTree → ℝ
  | leaf => l0
  | node m cs => (∑ i, ell g h l0 y0 (cs i)) + g (m + 1) (∑ i, msg h y0 (cs i))

/-- Every internal node's child count satisfies `ok`. -/
def AllDeg (ok : ℕ → Prop) : PTree → Prop
  | leaf => True
  | node m cs => ok (m + 1) ∧ ∀ i, AllDeg ok (cs i)

theorem allDeg_true (b : PTree) : b.AllDeg (fun _ => True) := by
  induction b with
  | leaf => trivial
  | node m cs ih => exact ⟨trivial, ih⟩

end PTree

/-- THE INDUCTION.  A carried function `U` and a pooling function `V ≥ U` on `I = [lo, hi]`
with Jensen for `V`; if every admissible node satisfies the pooled-mean step and keeps the
message in `I`, then every tree satisfies `ell + α·size ≤ U (msg)`. -/
theorem pooled_induction_core (ok : ℕ → Prop) (h g : ℕ → ℝ → ℝ) (U V : ℝ → ℝ)
    (y0 l0 lo hi α : ℝ)
    (hJ : ∀ (n : ℕ) (y : Fin n → ℝ), 0 < n →
      ∑ i, V (y i) ≤ (n : ℝ) * V ((∑ i, y i) / n))
    (hUV : ∀ y, lo ≤ y → y ≤ hi → U y ≤ V y)
    (hy0 : lo ≤ y0 ∧ y0 ≤ hi)
    (hbase : l0 + α ≤ U y0)
    (hclos : ∀ m : ℕ, 1 ≤ m → ok m → ∀ yb, lo ≤ yb → yb ≤ hi →
      lo ≤ h m (m * yb) ∧ h m (m * yb) ≤ hi)
    (hstep : ∀ m : ℕ, 1 ≤ m → ok m → ∀ yb, lo ≤ yb → yb ≤ hi →
      (m : ℝ) * V yb + g m (m * yb) + α ≤ U (h m (m * yb))) :
    ∀ b : PTree, b.AllDeg ok →
      lo ≤ b.msg h y0 ∧ b.msg h y0 ≤ hi ∧
        b.ell g h l0 y0 + α * b.size ≤ U (b.msg h y0) := by
  intro b
  induction b with
  | leaf =>
    intro _
    simp only [PTree.msg, PTree.ell, PTree.size, Nat.cast_one, mul_one]
    exact ⟨hy0.1, hy0.2, hbase⟩
  | node m cs ih =>
    intro hdeg
    obtain ⟨hok, hcs⟩ := hdeg
    have hc : ∀ i, lo ≤ (cs i).msg h y0 ∧ (cs i).msg h y0 ≤ hi ∧
        (cs i).ell g h l0 y0 + α * (cs i).size ≤ U ((cs i).msg h y0) :=
      fun i => ih i (hcs i)
    set R := ∑ i, (cs i).msg h y0 with hR
    have hn : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hRlo : ((m + 1 : ℕ) : ℝ) * lo ≤ R := by
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
        (fun i _ => (hc i).1)
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    have hRhi : R ≤ ((m + 1 : ℕ) : ℝ) * hi := by
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
        (fun i _ => (hc i).2.1)
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    set yb := R / ((m + 1 : ℕ) : ℝ) with hyb
    have hmyb : ((m + 1 : ℕ) : ℝ) * yb = R := by
      rw [hyb]; field_simp
    have hyblo : lo ≤ yb := by
      rw [hyb, le_div_iff₀ hn]; linarith
    have hybhi : yb ≤ hi := by
      rw [hyb, div_le_iff₀ hn]; linarith
    have hm1 : 1 ≤ m + 1 := Nat.le_add_left 1 m
    have hcl := hclos (m + 1) hm1 hok yb hyblo hybhi
    have hst := hstep (m + 1) hm1 hok yb hyblo hybhi
    rw [hmyb] at hcl hst
    have hJ' := hJ (m + 1) (fun i => (cs i).msg h y0) (Nat.succ_pos m)
    have hsumU : ∑ i, ((cs i).ell g h l0 y0 + α * (cs i).size) ≤
        ∑ i, V ((cs i).msg h y0) :=
      Finset.sum_le_sum fun i _ =>
        le_trans (hc i).2.2 (hUV _ (hc i).1 (hc i).2.1)
    have hsize : (((PTree.node m cs).size : ℕ) : ℝ) = (∑ i, ((cs i).size : ℝ)) + 1 := by
      simp [PTree.size]
    refine ⟨hcl.1, hcl.2, ?_⟩
    simp only [PTree.msg, PTree.ell]
    rw [hsize, ← hR]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumU
    have : ∑ i, (cs i).ell g h l0 y0 + α * ∑ i, ((cs i).size : ℝ)
        ≤ ((m + 1 : ℕ) : ℝ) * V yb := le_trans hsumU hJ'
    linarith

/-- A concave piecewise-linear function as the MINIMUM of its `K + 1` affine pieces. -/
noncomputable def minPieces {K : ℕ} (a b : Fin (K + 1) → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k => a k * x + b k)

theorem minPieces_le {K : ℕ} (a b : Fin (K + 1) → ℝ) (x : ℝ) (k : Fin (K + 1)) :
    minPieces a b x ≤ a k * x + b k :=
  Finset.inf'_le _ (Finset.mem_univ k)

theorem le_minPieces {K : ℕ} (a b : Fin (K + 1) → ℝ) (x c : ℝ)
    (h : ∀ k, c ≤ a k * x + b k) : c ≤ minPieces a b x :=
  Finset.le_inf' _ _ (fun k _ => h k)

/-- Jensen for a minimum of affine pieces: the sum of minima is at most the minimum of the
sums, and each piece sums to `n` times its value at the mean. -/
theorem minPieces_jensen {K : ℕ} (a b : Fin (K + 1) → ℝ) (n : ℕ) (y : Fin n → ℝ)
    (hn : 0 < n) :
    ∑ i, minPieces a b (y i) ≤ (n : ℝ) * minPieces a b ((∑ i, y i) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_comm, ← div_le_iff₀ hn']
  apply le_minPieces
  intro k
  rw [div_le_iff₀ hn']
  calc ∑ i, minPieces a b (y i) ≤ ∑ i, (a k * y i + b k) :=
        Finset.sum_le_sum fun i _ => minPieces_le a b (y i) k
    _ = (a k * ((∑ i, y i) / n) + b k) * n := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp

end ConcavePooled

open ConcavePooled

/-! ## Log tangent bound (extension, 2026-10-01; emitted once per file when g has a log)

The tangent-line upper bound of the concave `log` (the mobius_tangent_cell lemma).
conjecture1_proved = False. -/

namespace ConcavePooled

/-- Concavity of `log` as a tangent bound at `u`, with `log u ≤ H`. -/
theorem log_tangent_le (u y H : ℝ) (hu : 0 < u) (hy : 0 < y) (hH : Real.log u ≤ H) :
    Real.log y ≤ H + (y - u) / u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hu)
  rw [Real.log_div hy.ne' hu.ne'] at h
  have e : (y - u) / u = y / u - 1 := by field_simp
  linarith

end ConcavePooled

/-! ## Leaf-exempt pooled induction (extension, 2026-10-01; emitted once per file when used)

Leaves are EXEMPT: a leaf child enters its parent's step with its exact pair `(y_leaf,
l_leaf)` and is excluded from the Jensen pooling, which runs over the non-leaf children only;
the claim is made for every NON-LEAF tree.  conjecture1_proved = False. -/

namespace ConcavePooled

/-- Is this tree an internal node (not a leaf)? -/
def PTree.isNode : PTree → Bool
  | PTree.leaf => false
  | PTree.node _ _ => true

theorem PTree.eq_leaf_of_not_isNode {b : PTree} (hb : ¬ b.isNode = true) : b = PTree.leaf := by
  cases b with
  | leaf => rfl
  | node m cs => exact absurd rfl hb

/-- Jensen for a minimum of affine pieces over a nonempty sub-family `s`. -/
theorem minPieces_jensen_on {K : ℕ} (a b : Fin (K + 1) → ℝ) {n : ℕ} (s : Finset (Fin n))
    (y : Fin n → ℝ) (hs : s.Nonempty) :
    ∑ i ∈ s, minPieces a b (y i) ≤ (s.card : ℝ) * minPieces a b ((∑ i ∈ s, y i) / s.card) := by
  have hn' : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [mul_comm, ← div_le_iff₀ hn']
  apply le_minPieces
  intro k
  rw [div_le_iff₀ hn']
  calc ∑ i ∈ s, minPieces a b (y i) ≤ ∑ i ∈ s, (a k * y i + b k) :=
        Finset.sum_le_sum fun i _ => minPieces_le a b (y i) k
    _ = (a k * ((∑ i ∈ s, y i) / s.card) + b k) * s.card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        field_simp

/-- THE LEAF-EXEMPT INDUCTION.  A node with `p` non-leaf children (pooled at their mean `yb`)
and `k` leaf children (exact) satisfies the step; then every non-leaf tree satisfies
`ell + α·size ≤ U (msg)` with `msg ∈ [lo, hi]`.  The leaf itself is not claimed. -/
theorem exempt_induction_core (ok : ℕ → Prop) (h g : ℕ → ℝ → ℝ) (U V : ℝ → ℝ)
    (y0 l0 lo hi α : ℝ)
    (hJ : ∀ (n : ℕ) (s : Finset (Fin n)) (y : Fin n → ℝ), s.Nonempty →
      ∑ i ∈ s, V (y i) ≤ (s.card : ℝ) * V ((∑ i ∈ s, y i) / s.card))
    (hUV : ∀ y, lo ≤ y → y ≤ hi → U y ≤ V y)
    (hlohi : lo ≤ hi)
    (hclos : ∀ p k : ℕ, 1 ≤ p + k → ok (p + k) → ∀ yb, lo ≤ yb → yb ≤ hi →
      lo ≤ h (p + k) (p * yb + k * y0) ∧ h (p + k) (p * yb + k * y0) ≤ hi)
    (hstep : ∀ p k : ℕ, 1 ≤ p + k → ok (p + k) → ∀ yb, lo ≤ yb → yb ≤ hi →
      (p : ℝ) * V yb + k * (l0 + α) + g (p + k) (p * yb + k * y0) + α ≤
        U (h (p + k) (p * yb + k * y0))) :
    ∀ b : PTree, b.isNode = true → b.AllDeg ok →
      lo ≤ b.msg h y0 ∧ b.msg h y0 ≤ hi ∧
        b.ell g h l0 y0 + α * b.size ≤ U (b.msg h y0) := by
  intro b
  induction b with
  | leaf => intro hb; exact absurd hb (by simp [PTree.isNode])
  | node m cs ih =>
    intro _ hdeg
    obtain ⟨hok, hcs⟩ := hdeg
    classical
    set S := Finset.univ.filter (fun i => (cs i).isNode = true) with hS
    set T := Finset.univ.filter (fun i => ¬ (cs i).isNode = true) with hT
    have hcard : S.card + T.card = m + 1 := by
      rw [hS, hT, Finset.card_filter_add_card_filter_not, Finset.card_univ,
        Fintype.card_fin]
    have hleaf : ∀ i ∈ T, cs i = PTree.leaf := fun i hi =>
      PTree.eq_leaf_of_not_isNode (Finset.mem_filter.mp hi).2
    have hc : ∀ i ∈ S, lo ≤ (cs i).msg h y0 ∧ (cs i).msg h y0 ≤ hi ∧
        (cs i).ell g h l0 y0 + α * (cs i).size ≤ U ((cs i).msg h y0) :=
      fun i hi => ih i (Finset.mem_filter.mp hi).2 (hcs i)
    -- split every child sum into the non-leaf part (over S) and the leaf part (over T)
    have split : ∀ f : PTree → ℝ, ∑ i, f (cs i) = ∑ i ∈ S, f (cs i) + T.card * f PTree.leaf := by
      intro f
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => (cs i).isNode = true)]
      congr 1
      rw [Finset.sum_congr rfl (fun i hi => by rw [hleaf i hi]), Finset.sum_const,
        nsmul_eq_mul]
    set p := S.card with hp
    set k := T.card with hk
    set RS := ∑ i ∈ S, (cs i).msg h y0 with hRS
    have hRlo : (p : ℝ) * lo ≤ RS := by
      have := Finset.sum_le_sum (fun i hi => (hc i hi).1)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have hRhi : RS ≤ (p : ℝ) * hi := by
      have := Finset.sum_le_sum (fun i hi => (hc i hi).2.1)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    -- the pooled mean (any point of I when there is no non-leaf child)
    set yb : ℝ := if p = 0 then lo else RS / p with hyb
    have hpyb : (p : ℝ) * yb = RS := by
      by_cases h0 : p = 0
      · have hSe : S = ∅ := Finset.card_eq_zero.mp h0
        simp [hyb, h0, hRS, hSe]
      · have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero h0
        rw [hyb, if_neg h0]; field_simp
    have hyblo : lo ≤ yb := by
      by_cases h0 : p = 0
      · rw [hyb, if_pos h0]
      · have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero h0
        rw [hyb, if_neg h0, le_div_iff₀ hp']; linarith
    have hybhi : yb ≤ hi := by
      by_cases h0 : p = 0
      · rw [hyb, if_pos h0]; exact hlohi
      · have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero h0
        rw [hyb, if_neg h0, div_le_iff₀ hp']; linarith
    have hn : 1 ≤ p + k := by omega
    have hok' : ok (p + k) := by rw [hcard]; exact hok
    have hcl := hclos p k hn hok' yb hyblo hybhi
    have hst := hstep p k hn hok' yb hyblo hybhi
    have hR : ∑ i, (cs i).msg h y0 = (p : ℝ) * yb + k * y0 := by
      have e := split (fun c => c.msg h y0)
      simp only [PTree.msg] at e
      rw [e, hpyb, hRS]
    rw [hcard] at hcl hst
    -- Jensen over the non-leaf children
    have hjen : ∑ i ∈ S, ((cs i).ell g h l0 y0 + α * (cs i).size) ≤ (p : ℝ) * V yb := by
      have h1 : ∑ i ∈ S, ((cs i).ell g h l0 y0 + α * (cs i).size) ≤
          ∑ i ∈ S, V ((cs i).msg h y0) :=
        Finset.sum_le_sum fun i hi => le_trans (hc i hi).2.2 (hUV _ (hc i hi).1 (hc i hi).2.1)
      by_cases h0 : p = 0
      · have hSe : S = ∅ := Finset.card_eq_zero.mp h0
        simp [hSe, h0]
      · have hne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        have := hJ (m + 1) S (fun i => (cs i).msg h y0) hne
        have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero h0
        have hyb' : yb = RS / p := by rw [hyb, if_neg h0]
        rw [hyb']
        exact le_trans h1 this
    have hsz : (((PTree.node m cs).size : ℕ) : ℝ) =
        (∑ i ∈ S, ((cs i).size : ℝ)) + k * 1 + 1 := by
      have := split (fun c => (c.size : ℝ))
      simp only [PTree.size, Nat.cast_add, Nat.cast_sum, Nat.cast_one] at this ⊢
      rw [this]
    have hell : (PTree.node m cs).ell g h l0 y0 =
        ∑ i ∈ S, (cs i).ell g h l0 y0 + k * l0 + g (m + 1) ((p : ℝ) * yb + k * y0) := by
      have e := split (fun c => c.ell g h l0 y0)
      simp only [PTree.ell] at e ⊢
      rw [e, hR]
    have hmsg : (PTree.node m cs).msg h y0 = h (m + 1) ((p : ℝ) * yb + k * y0) := by
      simp only [PTree.msg]; rw [hR]
    rw [hmsg]
    refine ⟨hcl.1, hcl.2, ?_⟩
    rw [hell, hsz]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hjen
    nlinarith [hjen, hst]

end ConcavePooled

/-! ## Instance `leaf_exempt_matched` (LEAF-EXEMPT, extension 2026-10-01)

Claim: `ell + (27/100) * size ≤ U (msg)` on every NON-LEAF finite rooted tree of child count at most 2, for
  h(m, R) = 1/(R + 1),  g(m, R) = -R/(R + 1),
  leaf (y, l) = (1, 0) entering EXACTLY (never pooled), U the concave interpolant of
  (1/3, 29/200), (3/5, 4/25), (3/4, 83/500).
Certificate: 6 cells over the child mixes (p pooled, k leaves), p + k ≤ 2, plus 2 all-leaves cases. -/

noncomputable def leaf_exempt_matched_A : Fin 2 → ℝ := ![(9 / 160 : ℝ), (1 / 25 : ℝ)]
noncomputable def leaf_exempt_matched_B : Fin 2 → ℝ := ![(101 / 800 : ℝ), (17 / 125 : ℝ)]
/-- The witness: the minimum of its 2 affine pieces. -/
noncomputable def leaf_exempt_matched_U : ℝ → ℝ := minPieces leaf_exempt_matched_A leaf_exempt_matched_B
noncomputable def leaf_exempt_matched_h : ℕ → ℝ → ℝ := fun _ R => ((1 : ℝ)) / ((1 : ℝ) + R)
noncomputable def leaf_exempt_matched_g : ℕ → ℝ → ℝ := fun _ R => ((-1 : ℝ) * R) / ((1 : ℝ) + R)

theorem leaf_exempt_matched_piece0 (x : ℝ) : leaf_exempt_matched_U x ≤ (9 / 160 : ℝ) * x + (101 / 800 : ℝ) := by
  have := minPieces_le leaf_exempt_matched_A leaf_exempt_matched_B x 0
  simpa [leaf_exempt_matched_U, leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_piece1 (x : ℝ) : leaf_exempt_matched_U x ≤ (1 / 25 : ℝ) * x + (17 / 125 : ℝ) := by
  have := minPieces_le leaf_exempt_matched_A leaf_exempt_matched_B x 1
  simpa [leaf_exempt_matched_U, leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_node0 : leaf_exempt_matched_U (1 / 3 : ℝ) = (29 / 200 : ℝ) := by
  apply le_antisymm
  · linarith [leaf_exempt_matched_piece0 (1 / 3 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [leaf_exempt_matched_A, leaf_exempt_matched_B]

theorem leaf_exempt_matched_node1 : leaf_exempt_matched_U (3 / 5 : ℝ) = (4 / 25 : ℝ) := by
  apply le_antisymm
  · linarith [leaf_exempt_matched_piece0 (3 / 5 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [leaf_exempt_matched_A, leaf_exempt_matched_B]

theorem leaf_exempt_matched_node2 : leaf_exempt_matched_U (3 / 4 : ℝ) = (83 / 500 : ℝ) := by
  apply le_antisymm
  · linarith [leaf_exempt_matched_piece1 (3 / 4 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [leaf_exempt_matched_A, leaf_exempt_matched_B]

theorem leaf_exempt_matched_c0_k0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + leaf_exempt_matched_g 1 R + (27 / 100 : ℝ) ≤ (9 / 160 : ℝ) * leaf_exempt_matched_h 1 R + (101 / 800 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 1 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-171 / 800 : ℝ) + (539 / 800 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((9 / 160 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (101 / 800 : ℝ)) - ((9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-171 / 800 : ℝ) + (539 / 800 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c0_k1 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + leaf_exempt_matched_g 1 R + (27 / 100 : ℝ) ≤ (1 / 25 : ℝ) * leaf_exempt_matched_h 1 R + (17 / 125 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 1 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-881 / 4000 : ℝ) + (1367 / 2000 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 / 25 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (17 / 125 : ℝ)) - ((9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-881 / 4000 : ℝ) + (1367 / 2000 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c0_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 1 R := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c0_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    leaf_exempt_matched_h 1 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + leaf_exempt_matched_g 1 R + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_matched_c0_k0 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this
  · have := leaf_exempt_matched_c0_k1 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_c0_cl (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 1 R ∧ leaf_exempt_matched_h 1 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_matched_c0_lo R h1 h2, leaf_exempt_matched_c0_hi R h1 h2⟩

theorem leaf_exempt_matched_c1_k0 (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + leaf_exempt_matched_g 1 R + (27 / 100 : ℝ) ≤ (9 / 160 : ℝ) * leaf_exempt_matched_h 1 R + (101 / 800 : ℝ) := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 1 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-447 / 2000 : ℝ) + (2721 / 4000 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((9 / 160 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (101 / 800 : ℝ)) - ((1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-447 / 2000 : ℝ) + (2721 / 4000 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c1_k1 (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + leaf_exempt_matched_g 1 R + (27 / 100 : ℝ) ≤ (1 / 25 : ℝ) * leaf_exempt_matched_h 1 R + (17 / 125 : ℝ) := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 1 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-23 / 100 : ℝ) + (69 / 100 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 / 25 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (17 / 125 : ℝ)) - ((1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-23 / 100 : ℝ) + (69 / 100 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c1_lo (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 1 R := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c1_hi (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    leaf_exempt_matched_h 1 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c1 (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + leaf_exempt_matched_g 1 R + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_matched_c1_k0 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this
  · have := leaf_exempt_matched_c1_k1 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_c1_cl (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 1 R ∧ leaf_exempt_matched_h 1 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_matched_c1_lo R h1 h2, leaf_exempt_matched_c1_hi R h1 h2⟩

theorem leaf_exempt_matched_c2_k0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g 2 (R + (1 : ℝ)) + (27 / 100 : ℝ) ≤ (9 / 160 : ℝ) * leaf_exempt_matched_h 2 (R + (1 : ℝ)) + (101 / 800 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have eg : leaf_exempt_matched_g 2 (R + (1 : ℝ)) = (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]; ring
  have key : 0 ≤ ((-19 / 800 : ℝ) + (139 / 400 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((9 / 160 : ℝ) * (((1 : ℝ)) / ((2 : ℝ) + R)) + (101 / 800 : ℝ)) - ((9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-19 / 800 : ℝ) + (139 / 400 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c2_k1 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g 2 (R + (1 : ℝ)) + (27 / 100 : ℝ) ≤ (1 / 25 : ℝ) * leaf_exempt_matched_h 2 (R + (1 : ℝ)) + (17 / 125 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have eg : leaf_exempt_matched_g 2 (R + (1 : ℝ)) = (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]; ring
  have key : 0 ≤ ((-41 / 2000 : ℝ) + (1429 / 4000 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 / 25 : ℝ) * (((1 : ℝ)) / ((2 : ℝ) + R)) + (17 / 125 : ℝ)) - ((9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-41 / 2000 : ℝ) + (1429 / 4000 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c2_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 (R + (1 : ℝ)) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have key : 0 ≤ ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((2 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c2_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    leaf_exempt_matched_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have key : 0 ≤ ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((2 : ℝ) + R))) = ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c2 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (1 : ℝ) * (101 / 800 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g 2 (R + (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h 2 (R + (1 : ℝ))) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_matched_c2_k0 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this
  · have := leaf_exempt_matched_c2_k1 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_c2_cl (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 5 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 (R + (1 : ℝ)) ∧ leaf_exempt_matched_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_matched_c2_lo R h1 h2, leaf_exempt_matched_c2_hi R h1 h2⟩

theorem leaf_exempt_matched_c3_k0 (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g 2 (R + (1 : ℝ)) + (27 / 100 : ℝ) ≤ (9 / 160 : ℝ) * leaf_exempt_matched_h 2 (R + (1 : ℝ)) + (101 / 800 : ℝ) := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have eg : leaf_exempt_matched_g 2 (R + (1 : ℝ)) = (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]; ring
  have key : 0 ≤ ((-173 / 4000 : ℝ) + (1481 / 4000 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((9 / 160 : ℝ) * (((1 : ℝ)) / ((2 : ℝ) + R)) + (101 / 800 : ℝ)) - ((1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-173 / 4000 : ℝ) + (1481 / 4000 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c3_k1 (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g 2 (R + (1 : ℝ)) + (27 / 100 : ℝ) ≤ (1 / 25 : ℝ) * leaf_exempt_matched_h 2 (R + (1 : ℝ)) + (17 / 125 : ℝ) := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have eg : leaf_exempt_matched_g 2 (R + (1 : ℝ)) = (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]; ring
  have key : 0 ≤ ((-1 / 25 : ℝ) + (19 / 50 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 / 25 : ℝ) * (((1 : ℝ)) / ((2 : ℝ) + R)) + (17 / 125 : ℝ)) - ((1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-1 / 25 : ℝ) + (19 / 50 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c3_lo (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 (R + (1 : ℝ)) := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have key : 0 ≤ ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((2 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c3_hi (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    leaf_exempt_matched_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (3 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]; ring
  have key : 0 ≤ ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((2 : ℝ) + R))) = ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c3 (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 25 : ℝ) * R + (1 : ℝ) * (17 / 125 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g 2 (R + (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h 2 (R + (1 : ℝ))) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_matched_c3_k0 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this
  · have := leaf_exempt_matched_c3_k1 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_c3_cl (R : ℝ) (h1 : (3 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 (R + (1 : ℝ)) ∧ leaf_exempt_matched_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_matched_c3_lo R h1 h2, leaf_exempt_matched_c3_hi R h1 h2⟩

theorem leaf_exempt_matched_c4_k0 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (6 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (2 : ℝ) * (101 / 800 : ℝ) + leaf_exempt_matched_g 2 R + (27 / 100 : ℝ) ≤ (9 / 160 : ℝ) * leaf_exempt_matched_h 2 R + (101 / 800 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (6 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 2 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-17 / 50 : ℝ) + (219 / 400 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((9 / 160 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (101 / 800 : ℝ)) - ((9 / 160 : ℝ) * R + (2 : ℝ) * (101 / 800 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-17 / 50 : ℝ) + (219 / 400 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c4_k1 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (6 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (2 : ℝ) * (101 / 800 : ℝ) + leaf_exempt_matched_g 2 R + (27 / 100 : ℝ) ≤ (1 / 25 : ℝ) * leaf_exempt_matched_h 2 R + (17 / 125 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (6 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 2 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-693 / 2000 : ℝ) + (2229 / 4000 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 / 25 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (17 / 125 : ℝ)) - ((9 / 160 : ℝ) * R + (2 : ℝ) * (101 / 800 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-693 / 2000 : ℝ) + (2229 / 4000 : ℝ) * R + (-9 / 160 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c4_lo (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (6 / 5 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 R := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (6 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c4_hi (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (6 / 5 : ℝ)) :
    leaf_exempt_matched_h 2 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (6 / 5 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c4 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (6 / 5 : ℝ)) :
    (9 / 160 : ℝ) * R + (2 : ℝ) * (101 / 800 : ℝ) + leaf_exempt_matched_g 2 R + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_matched_c4_k0 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this
  · have := leaf_exempt_matched_c4_k1 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_c4_cl (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (6 / 5 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 R ∧ leaf_exempt_matched_h 2 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_matched_c4_lo R h1 h2, leaf_exempt_matched_c4_hi R h1 h2⟩

theorem leaf_exempt_matched_c5_k0 (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 25 : ℝ) * R + (2 : ℝ) * (17 / 125 : ℝ) + leaf_exempt_matched_g 2 R + (27 / 100 : ℝ) ≤ (9 / 160 : ℝ) * leaf_exempt_matched_h 2 R + (101 / 800 : ℝ) := by
  have hs : 0 ≤ R - (6 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 2 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-719 / 2000 : ℝ) + (2177 / 4000 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((9 / 160 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (101 / 800 : ℝ)) - ((1 / 25 : ℝ) * R + (2 : ℝ) * (17 / 125 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-719 / 2000 : ℝ) + (2177 / 4000 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c5_k1 (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 25 : ℝ) * R + (2 : ℝ) * (17 / 125 : ℝ) + leaf_exempt_matched_g 2 R + (27 / 100 : ℝ) ≤ (1 / 25 : ℝ) * leaf_exempt_matched_h 2 R + (17 / 125 : ℝ) := by
  have hs : 0 ≤ R - (6 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 2 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_g]
  have key : 0 ≤ ((-183 / 500 : ℝ) + (277 / 500 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 / 25 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (17 / 125 : ℝ)) - ((1 / 25 : ℝ) * R + (2 : ℝ) * (17 / 125 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (27 / 100 : ℝ)) = ((-183 / 500 : ℝ) + (277 / 500 : ℝ) * R + (-1 / 25 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_matched_c5_lo (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 R := by
  have hs : 0 ≤ R - (6 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c5_hi (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    leaf_exempt_matched_h 2 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (6 / 5 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_matched_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_matched_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_matched_c5 (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 25 : ℝ) * R + (2 : ℝ) * (17 / 125 : ℝ) + leaf_exempt_matched_g 2 R + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_matched_c5_k0 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this
  · have := leaf_exempt_matched_c5_k1 R h1 h2
    simpa [leaf_exempt_matched_A, leaf_exempt_matched_B] using this

theorem leaf_exempt_matched_c5_cl (R : ℝ) (h1 : (6 / 5 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h 2 R ∧ leaf_exempt_matched_h 2 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_matched_c5_lo R h1 h2, leaf_exempt_matched_c5_hi R h1 h2⟩

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_xs_0_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((0 : ℕ) : ℝ) * leaf_exempt_matched_U yb + ((1 : ℕ) : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) := by push_cast; ring
  rw [show (0 + 1 : ℕ) = 1 from rfl, e1]
  have eh : leaf_exempt_matched_h 1 (1 : ℝ) = (1 / 2 : ℝ) := by norm_num [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 1 (1 : ℝ) = (-1 / 2 : ℝ) := by norm_num [leaf_exempt_matched_g]
  rw [eh, eg]
  have hU : (1 / 25 : ℝ) ≤ leaf_exempt_matched_U (1 / 2 : ℝ) := by
    apply le_minPieces; intro K; fin_cases K <;> norm_num [leaf_exempt_matched_A, leaf_exempt_matched_B]
  push_cast
  linarith [hU]

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_xc_0_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_matched_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) := by push_cast; ring
  rw [show (0 + 1 : ℕ) = 1 from rfl, e1]
  norm_num [leaf_exempt_matched_h]

theorem leaf_exempt_matched_xs_1_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((1 : ℕ) : ℝ) * leaf_exempt_matched_U yb + ((0 : ℕ) : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb := by push_cast; ring
  rw [show (1 + 0 : ℕ) = 1 from rfl, e1]
  push_cast
  rcases le_or_gt ((1 : ℝ) * yb) (3 / 5 : ℝ) with h_0 | h_0
  · linarith [leaf_exempt_matched_c0 ((1 : ℝ) * yb) (by linarith) h_0, leaf_exempt_matched_piece0 yb]
  · linarith [leaf_exempt_matched_c1 ((1 : ℝ) * yb) h_0.le (by linarith), leaf_exempt_matched_piece1 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_xc_1_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_matched_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb := by push_cast; ring
  rw [show (1 + 0 : ℕ) = 1 from rfl, e1]
  rcases le_or_gt ((1 : ℝ) * yb) (3 / 5 : ℝ) with h_0 | h_0
  · exact leaf_exempt_matched_c0_cl ((1 : ℝ) * yb) (by linarith) h_0
  · exact leaf_exempt_matched_c1_cl ((1 : ℝ) * yb) h_0.le (by linarith)

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_xs_0_2 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((0 : ℕ) : ℝ) * leaf_exempt_matched_U yb + ((2 : ℕ) : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) := by push_cast; ring
  rw [show (0 + 2 : ℕ) = 2 from rfl, e1]
  have eh : leaf_exempt_matched_h 2 (2 : ℝ) = (1 / 3 : ℝ) := by norm_num [leaf_exempt_matched_h]
  have eg : leaf_exempt_matched_g 2 (2 : ℝ) = (-2 / 3 : ℝ) := by norm_num [leaf_exempt_matched_g]
  rw [eh, eg]
  have hU : (43 / 300 : ℝ) ≤ leaf_exempt_matched_U (1 / 3 : ℝ) := by
    apply le_minPieces; intro K; fin_cases K <;> norm_num [leaf_exempt_matched_A, leaf_exempt_matched_B]
  push_cast
  linarith [hU]

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_xc_0_2 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_matched_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) := by push_cast; ring
  rw [show (0 + 2 : ℕ) = 2 from rfl, e1]
  norm_num [leaf_exempt_matched_h]

theorem leaf_exempt_matched_xs_1_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((1 : ℕ) : ℝ) * leaf_exempt_matched_U yb + ((1 : ℕ) : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb + (1 : ℝ) := by push_cast; ring
  rw [show (1 + 1 : ℕ) = 2 from rfl, e1]
  push_cast
  rcases le_or_gt ((1 : ℝ) * yb) (3 / 5 : ℝ) with h_0 | h_0
  · linarith [leaf_exempt_matched_c2 ((1 : ℝ) * yb) (by linarith) h_0, leaf_exempt_matched_piece0 yb]
  · linarith [leaf_exempt_matched_c3 ((1 : ℝ) * yb) h_0.le (by linarith), leaf_exempt_matched_piece1 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_xc_1_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_matched_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb + (1 : ℝ) := by push_cast; ring
  rw [show (1 + 1 : ℕ) = 2 from rfl, e1]
  rcases le_or_gt ((1 : ℝ) * yb) (3 / 5 : ℝ) with h_0 | h_0
  · exact leaf_exempt_matched_c2_cl ((1 : ℝ) * yb) (by linarith) h_0
  · exact leaf_exempt_matched_c3_cl ((1 : ℝ) * yb) h_0.le (by linarith)

theorem leaf_exempt_matched_xs_2_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((2 : ℕ) : ℝ) * leaf_exempt_matched_U yb + ((0 : ℕ) : ℝ) * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) * yb := by push_cast; ring
  rw [show (2 + 0 : ℕ) = 2 from rfl, e1]
  push_cast
  rcases le_or_gt ((2 : ℝ) * yb) (6 / 5 : ℝ) with h_0 | h_0
  · linarith [leaf_exempt_matched_c4 ((2 : ℝ) * yb) (by linarith) h_0, leaf_exempt_matched_piece0 yb]
  · linarith [leaf_exempt_matched_c5 ((2 : ℝ) * yb) h_0.le (by linarith), leaf_exempt_matched_piece1 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_xc_2_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_matched_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) * yb := by push_cast; ring
  rw [show (2 + 0 : ℕ) = 2 from rfl, e1]
  rcases le_or_gt ((2 : ℝ) * yb) (6 / 5 : ℝ) with h_0 | h_0
  · exact leaf_exempt_matched_c4_cl ((2 : ℝ) * yb) (by linarith) h_0
  · exact leaf_exempt_matched_c5_cl ((2 : ℝ) * yb) h_0.le (by linarith)

theorem leaf_exempt_matched_xhstep : ∀ p k : ℕ, 1 ≤ p + k → p + k ≤ 2 → ∀ yb : ℝ, (1 / 3 : ℝ) ≤ yb → yb ≤ (3 / 4 : ℝ) →
    (p : ℝ) * leaf_exempt_matched_U yb + k * ((0 : ℝ) + (27 / 100 : ℝ)) + leaf_exempt_matched_g (p + k) (p * yb + k * (1 : ℝ)) + (27 / 100 : ℝ) ≤ leaf_exempt_matched_U (leaf_exempt_matched_h (p + k) (p * yb + k * (1 : ℝ))) := by
  intro p k h1 h2 yb hl hu
  have hp : p ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p <;> interval_cases k <;> first | (exfalso; omega) | exact leaf_exempt_matched_xs_0_1 yb hl hu | exact leaf_exempt_matched_xs_1_0 yb hl hu | exact leaf_exempt_matched_xs_0_2 yb hl hu | exact leaf_exempt_matched_xs_1_1 yb hl hu | exact leaf_exempt_matched_xs_2_0 yb hl hu

theorem leaf_exempt_matched_xhclos : ∀ p k : ℕ, 1 ≤ p + k → p + k ≤ 2 → ∀ yb : ℝ, (1 / 3 : ℝ) ≤ yb → yb ≤ (3 / 4 : ℝ) →
    (1 / 3 : ℝ) ≤ leaf_exempt_matched_h (p + k) (p * yb + k * (1 : ℝ)) ∧ leaf_exempt_matched_h (p + k) (p * yb + k * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  intro p k h1 h2 yb hl hu
  have hp : p ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p <;> interval_cases k <;> first | (exfalso; omega) | exact leaf_exempt_matched_xc_0_1 yb hl hu | exact leaf_exempt_matched_xc_1_0 yb hl hu | exact leaf_exempt_matched_xc_0_2 yb hl hu | exact leaf_exempt_matched_xc_1_1 yb hl hu | exact leaf_exempt_matched_xc_2_0 yb hl hu

set_option linter.unusedVariables false in
theorem leaf_exempt_matched_U_le_max (x : ℝ) (hl : (1 / 3 : ℝ) ≤ x) (hu : x ≤ (3 / 4 : ℝ)) : leaf_exempt_matched_U x ≤ (83 / 500 : ℝ) := by
  rcases le_or_gt x (3 / 5 : ℝ) with h_0 | h_0
  · linarith [leaf_exempt_matched_piece0 x]
  · linarith [leaf_exempt_matched_piece1 x]

/-- MAIN.  The certified bound on every NON-LEAF tree of child count at most 2 (leaves exempt). -/
theorem leaf_exempt_matched (b : PTree) (hn : b.isNode = true) (hb : b.AllDeg (fun m => m ≤ 2)) :
    (1 / 3 : ℝ) ≤ b.msg leaf_exempt_matched_h (1 : ℝ) ∧ b.msg leaf_exempt_matched_h (1 : ℝ) ≤ (3 / 4 : ℝ) ∧
      b.ell leaf_exempt_matched_g leaf_exempt_matched_h (0 : ℝ) (1 : ℝ) + (27 / 100 : ℝ) * b.size ≤ leaf_exempt_matched_U (b.msg leaf_exempt_matched_h (1 : ℝ)) :=
  exempt_induction_core (fun m => m ≤ 2) leaf_exempt_matched_h leaf_exempt_matched_g leaf_exempt_matched_U leaf_exempt_matched_U (1 : ℝ) (0 : ℝ) (1 / 3 : ℝ) (3 / 4 : ℝ) (27 / 100 : ℝ)
    (fun _ s y hs => minPieces_jensen_on leaf_exempt_matched_A leaf_exempt_matched_B s y hs) (fun _ _ _ => le_rfl) (by norm_num) leaf_exempt_matched_xhclos leaf_exempt_matched_xhstep b hn hb

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 83/500` on every non-leaf tree. -/
theorem leaf_exempt_matched_uniform (b : PTree) (hn : b.isNode = true) (hb : b.AllDeg (fun m => m ≤ 2)) :
    b.ell leaf_exempt_matched_g leaf_exempt_matched_h (0 : ℝ) (1 : ℝ) + (27 / 100 : ℝ) * b.size ≤ (83 / 500 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := leaf_exempt_matched b hn hb
  linarith [leaf_exempt_matched_U_le_max _ h1 h2]

/-- The single leaf VIOLATES the uniform bound (`l_leaf + α = 27/100 > 83/500`): no certificate that pools the leaves (and so covers the leaf tree) can prove it; exempting them can. -/
theorem leaf_exempt_matched_leaf_breaks : (83 / 500 : ℝ) < (0 : ℝ) + (27 / 100 : ℝ) := by norm_num

/-! ## Instance `leaf_exempt_flat` (LEAF-EXEMPT, extension 2026-10-01)

Claim: `ell + (1/4) * size ≤ U (msg)` on every NON-LEAF finite rooted tree of child count at most 2, for
  h(m, R) = 1/(R + 1),  g(m, R) = -R/(R + 1),
  leaf (y, l) = (1, 0) entering EXACTLY (never pooled), U the concave interpolant of
  (1/3, 1/12), (3/4, 1/12).
Certificate: 3 cells over the child mixes (p pooled, k leaves), p + k ≤ 2, plus 2 all-leaves cases. -/

noncomputable def leaf_exempt_flat_A : Fin 1 → ℝ := ![(0 : ℝ)]
noncomputable def leaf_exempt_flat_B : Fin 1 → ℝ := ![(1 / 12 : ℝ)]
/-- The witness: the minimum of its 1 affine pieces. -/
noncomputable def leaf_exempt_flat_U : ℝ → ℝ := minPieces leaf_exempt_flat_A leaf_exempt_flat_B
noncomputable def leaf_exempt_flat_h : ℕ → ℝ → ℝ := fun _ R => ((1 : ℝ)) / ((1 : ℝ) + R)
noncomputable def leaf_exempt_flat_g : ℕ → ℝ → ℝ := fun _ R => ((-1 : ℝ) * R) / ((1 : ℝ) + R)

theorem leaf_exempt_flat_piece0 (x : ℝ) : leaf_exempt_flat_U x ≤ (0 : ℝ) * x + (1 / 12 : ℝ) := by
  have := minPieces_le leaf_exempt_flat_A leaf_exempt_flat_B x 0
  simpa [leaf_exempt_flat_U, leaf_exempt_flat_A, leaf_exempt_flat_B] using this

theorem leaf_exempt_flat_node0 : leaf_exempt_flat_U (1 / 3 : ℝ) = (1 / 12 : ℝ) := by
  apply le_antisymm
  · linarith [leaf_exempt_flat_piece0 (1 / 3 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k ; norm_num [leaf_exempt_flat_A, leaf_exempt_flat_B]

theorem leaf_exempt_flat_node1 : leaf_exempt_flat_U (3 / 4 : ℝ) = (1 / 12 : ℝ) := by
  apply le_antisymm
  · linarith [leaf_exempt_flat_piece0 (3 / 4 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k ; norm_num [leaf_exempt_flat_A, leaf_exempt_flat_B]

theorem leaf_exempt_flat_c0_k0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 12 : ℝ) + leaf_exempt_flat_g 1 R + (1 / 4 : ℝ) ≤ (0 : ℝ) * leaf_exempt_flat_h 1 R + (1 / 12 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]
  have eg : leaf_exempt_flat_g 1 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_g]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 12 : ℝ)) - ((0 : ℝ) * R + (1 : ℝ) * (1 / 12 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (1 / 4 : ℝ)) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_flat_c0_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h 1 R := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_flat_c0_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    leaf_exempt_flat_h 1 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_flat_c0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 12 : ℝ) + leaf_exempt_flat_g 1 R + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_flat_c0_k0 R h1 h2
    simpa [leaf_exempt_flat_A, leaf_exempt_flat_B] using this

theorem leaf_exempt_flat_c0_cl (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h 1 R ∧ leaf_exempt_flat_h 1 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_flat_c0_lo R h1 h2, leaf_exempt_flat_c0_hi R h1 h2⟩

theorem leaf_exempt_flat_c1_k0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 12 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g 2 (R + (1 : ℝ)) + (1 / 4 : ℝ) ≤ (0 : ℝ) * leaf_exempt_flat_h 2 (R + (1 : ℝ)) + (1 / 12 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]; ring
  have eg : leaf_exempt_flat_g 2 (R + (1 : ℝ)) = (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_flat_g]; ring
  have key : 0 ≤ ((1 / 2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 : ℝ)) / ((2 : ℝ) + R)) + (1 / 12 : ℝ)) - ((0 : ℝ) * R + (1 : ℝ) * (1 / 12 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) + (1 / 4 : ℝ)) = ((1 / 2 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_flat_c1_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h 2 (R + (1 : ℝ)) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]; ring
  have key : 0 ≤ ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((2 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_flat_c1_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    leaf_exempt_flat_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]; ring
  have key : 0 ≤ ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((2 : ℝ) + R))) = ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_flat_c1 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 12 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g 2 (R + (1 : ℝ)) + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h 2 (R + (1 : ℝ))) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_flat_c1_k0 R h1 h2
    simpa [leaf_exempt_flat_A, leaf_exempt_flat_B] using this

theorem leaf_exempt_flat_c1_cl (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h 2 (R + (1 : ℝ)) ∧ leaf_exempt_flat_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_flat_c1_lo R h1 h2, leaf_exempt_flat_c1_hi R h1 h2⟩

theorem leaf_exempt_flat_c2_k0 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (0 : ℝ) * R + (2 : ℝ) * (1 / 12 : ℝ) + leaf_exempt_flat_g 2 R + (1 / 4 : ℝ) ≤ (0 : ℝ) * leaf_exempt_flat_h 2 R + (1 / 12 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]
  have eg : leaf_exempt_flat_g 2 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_g]
  have key : 0 ≤ ((-1 / 3 : ℝ) + (2 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 12 : ℝ)) - ((0 : ℝ) * R + (2 : ℝ) * (1 / 12 : ℝ) + (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (1 / 4 : ℝ)) = ((-1 / 3 : ℝ) + (2 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_flat_c2_lo (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h 2 R := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_flat_c2_hi (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    leaf_exempt_flat_h 2 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_flat_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_flat_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_flat_c2 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (0 : ℝ) * R + (2 : ℝ) * (1 / 12 : ℝ) + leaf_exempt_flat_g 2 R + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_flat_c2_k0 R h1 h2
    simpa [leaf_exempt_flat_A, leaf_exempt_flat_B] using this

theorem leaf_exempt_flat_c2_cl (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h 2 R ∧ leaf_exempt_flat_h 2 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_flat_c2_lo R h1 h2, leaf_exempt_flat_c2_hi R h1 h2⟩

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_xs_0_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((0 : ℕ) : ℝ) * leaf_exempt_flat_U yb + ((1 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) := by push_cast; ring
  rw [show (0 + 1 : ℕ) = 1 from rfl, e1]
  have eh : leaf_exempt_flat_h 1 (1 : ℝ) = (1 / 2 : ℝ) := by norm_num [leaf_exempt_flat_h]
  have eg : leaf_exempt_flat_g 1 (1 : ℝ) = (-1 / 2 : ℝ) := by norm_num [leaf_exempt_flat_g]
  rw [eh, eg]
  have hU : (0 : ℝ) ≤ leaf_exempt_flat_U (1 / 2 : ℝ) := by
    apply le_minPieces; intro K; fin_cases K; norm_num [leaf_exempt_flat_A, leaf_exempt_flat_B]
  push_cast
  linarith [hU]

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_xc_0_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_flat_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) := by push_cast; ring
  rw [show (0 + 1 : ℕ) = 1 from rfl, e1]
  norm_num [leaf_exempt_flat_h]

theorem leaf_exempt_flat_xs_1_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((1 : ℕ) : ℝ) * leaf_exempt_flat_U yb + ((0 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb := by push_cast; ring
  rw [show (1 + 0 : ℕ) = 1 from rfl, e1]
  push_cast
  · linarith [leaf_exempt_flat_c0 ((1 : ℝ) * yb) (by linarith) (by linarith), leaf_exempt_flat_piece0 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_xc_1_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_flat_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb := by push_cast; ring
  rw [show (1 + 0 : ℕ) = 1 from rfl, e1]
  · exact leaf_exempt_flat_c0_cl ((1 : ℝ) * yb) (by linarith) (by linarith)

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_xs_0_2 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((0 : ℕ) : ℝ) * leaf_exempt_flat_U yb + ((2 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) := by push_cast; ring
  rw [show (0 + 2 : ℕ) = 2 from rfl, e1]
  have eh : leaf_exempt_flat_h 2 (2 : ℝ) = (1 / 3 : ℝ) := by norm_num [leaf_exempt_flat_h]
  have eg : leaf_exempt_flat_g 2 (2 : ℝ) = (-2 / 3 : ℝ) := by norm_num [leaf_exempt_flat_g]
  rw [eh, eg]
  have hU : (1 / 12 : ℝ) ≤ leaf_exempt_flat_U (1 / 3 : ℝ) := by
    apply le_minPieces; intro K; fin_cases K; norm_num [leaf_exempt_flat_A, leaf_exempt_flat_B]
  push_cast
  linarith [hU]

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_xc_0_2 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_flat_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) := by push_cast; ring
  rw [show (0 + 2 : ℕ) = 2 from rfl, e1]
  norm_num [leaf_exempt_flat_h]

theorem leaf_exempt_flat_xs_1_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((1 : ℕ) : ℝ) * leaf_exempt_flat_U yb + ((1 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb + (1 : ℝ) := by push_cast; ring
  rw [show (1 + 1 : ℕ) = 2 from rfl, e1]
  push_cast
  · linarith [leaf_exempt_flat_c1 ((1 : ℝ) * yb) (by linarith) (by linarith), leaf_exempt_flat_piece0 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_xc_1_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_flat_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb + (1 : ℝ) := by push_cast; ring
  rw [show (1 + 1 : ℕ) = 2 from rfl, e1]
  · exact leaf_exempt_flat_c1_cl ((1 : ℝ) * yb) (by linarith) (by linarith)

theorem leaf_exempt_flat_xs_2_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((2 : ℕ) : ℝ) * leaf_exempt_flat_U yb + ((0 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) * yb := by push_cast; ring
  rw [show (2 + 0 : ℕ) = 2 from rfl, e1]
  push_cast
  · linarith [leaf_exempt_flat_c2 ((2 : ℝ) * yb) (by linarith) (by linarith), leaf_exempt_flat_piece0 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_xc_2_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_flat_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) * yb := by push_cast; ring
  rw [show (2 + 0 : ℕ) = 2 from rfl, e1]
  · exact leaf_exempt_flat_c2_cl ((2 : ℝ) * yb) (by linarith) (by linarith)

theorem leaf_exempt_flat_xhstep : ∀ p k : ℕ, 1 ≤ p + k → p + k ≤ 2 → ∀ yb : ℝ, (1 / 3 : ℝ) ≤ yb → yb ≤ (3 / 4 : ℝ) →
    (p : ℝ) * leaf_exempt_flat_U yb + k * ((0 : ℝ) + (1 / 4 : ℝ)) + leaf_exempt_flat_g (p + k) (p * yb + k * (1 : ℝ)) + (1 / 4 : ℝ) ≤ leaf_exempt_flat_U (leaf_exempt_flat_h (p + k) (p * yb + k * (1 : ℝ))) := by
  intro p k h1 h2 yb hl hu
  have hp : p ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p <;> interval_cases k <;> first | (exfalso; omega) | exact leaf_exempt_flat_xs_0_1 yb hl hu | exact leaf_exempt_flat_xs_1_0 yb hl hu | exact leaf_exempt_flat_xs_0_2 yb hl hu | exact leaf_exempt_flat_xs_1_1 yb hl hu | exact leaf_exempt_flat_xs_2_0 yb hl hu

theorem leaf_exempt_flat_xhclos : ∀ p k : ℕ, 1 ≤ p + k → p + k ≤ 2 → ∀ yb : ℝ, (1 / 3 : ℝ) ≤ yb → yb ≤ (3 / 4 : ℝ) →
    (1 / 3 : ℝ) ≤ leaf_exempt_flat_h (p + k) (p * yb + k * (1 : ℝ)) ∧ leaf_exempt_flat_h (p + k) (p * yb + k * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  intro p k h1 h2 yb hl hu
  have hp : p ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p <;> interval_cases k <;> first | (exfalso; omega) | exact leaf_exempt_flat_xc_0_1 yb hl hu | exact leaf_exempt_flat_xc_1_0 yb hl hu | exact leaf_exempt_flat_xc_0_2 yb hl hu | exact leaf_exempt_flat_xc_1_1 yb hl hu | exact leaf_exempt_flat_xc_2_0 yb hl hu

set_option linter.unusedVariables false in
theorem leaf_exempt_flat_U_le_max (x : ℝ) (hl : (1 / 3 : ℝ) ≤ x) (hu : x ≤ (3 / 4 : ℝ)) : leaf_exempt_flat_U x ≤ (1 / 12 : ℝ) := by
  · linarith [leaf_exempt_flat_piece0 x]

/-- MAIN.  The certified bound on every NON-LEAF tree of child count at most 2 (leaves exempt). -/
theorem leaf_exempt_flat (b : PTree) (hn : b.isNode = true) (hb : b.AllDeg (fun m => m ≤ 2)) :
    (1 / 3 : ℝ) ≤ b.msg leaf_exempt_flat_h (1 : ℝ) ∧ b.msg leaf_exempt_flat_h (1 : ℝ) ≤ (3 / 4 : ℝ) ∧
      b.ell leaf_exempt_flat_g leaf_exempt_flat_h (0 : ℝ) (1 : ℝ) + (1 / 4 : ℝ) * b.size ≤ leaf_exempt_flat_U (b.msg leaf_exempt_flat_h (1 : ℝ)) :=
  exempt_induction_core (fun m => m ≤ 2) leaf_exempt_flat_h leaf_exempt_flat_g leaf_exempt_flat_U leaf_exempt_flat_U (1 : ℝ) (0 : ℝ) (1 / 3 : ℝ) (3 / 4 : ℝ) (1 / 4 : ℝ)
    (fun _ s y hs => minPieces_jensen_on leaf_exempt_flat_A leaf_exempt_flat_B s y hs) (fun _ _ _ => le_rfl) (by norm_num) leaf_exempt_flat_xhclos leaf_exempt_flat_xhstep b hn hb

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 1/12` on every non-leaf tree. -/
theorem leaf_exempt_flat_uniform (b : PTree) (hn : b.isNode = true) (hb : b.AllDeg (fun m => m ≤ 2)) :
    b.ell leaf_exempt_flat_g leaf_exempt_flat_h (0 : ℝ) (1 : ℝ) + (1 / 4 : ℝ) * b.size ≤ (1 / 12 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := leaf_exempt_flat b hn hb
  linarith [leaf_exempt_flat_U_le_max _ h1 h2]

/-- The single leaf VIOLATES the uniform bound (`l_leaf + α = 1/4 > 1/12`): no certificate that pools the leaves (and so covers the leaf tree) can prove it; exempting them can. -/
theorem leaf_exempt_flat_leaf_breaks : (1 / 12 : ℝ) < (0 : ℝ) + (1 / 4 : ℝ) := by norm_num

/-! ## Instance `log_profit_density`

Claim: `ell + (1/2) * size ≤ U (msg)` on every finite rooted tree, for
  h(m, R) = 1/(R + 1),  g(m, R) = -1/(R + 1),
  leaf (y, l) = (1, -1), U the concave interpolant of
  (0, 0), (1/2, -1/8), (1, -3/10).
Certificate: 6 cells (explicit m = 1..2, plus the m-free tail m ≥ 3). -/

noncomputable def log_profit_density_A : Fin 2 → ℝ := ![(-1 / 4 : ℝ), (-7 / 20 : ℝ)]
noncomputable def log_profit_density_B : Fin 2 → ℝ := ![(0 : ℝ), (1 / 20 : ℝ)]
/-- The witness: the minimum of its 2 affine pieces. -/
noncomputable def log_profit_density_U : ℝ → ℝ := minPieces log_profit_density_A log_profit_density_B
noncomputable def log_profit_density_h : ℕ → ℝ → ℝ := fun _ R => ((1 : ℝ)) / ((1 : ℝ) + R)
noncomputable def log_profit_density_g : ℕ → ℝ → ℝ := fun _ R => ((-1 : ℝ)) / ((1 : ℝ) + R) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R)

/-- `log 9/8 <= H` (u = 2^0 * 9/8, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem log_profit_density_logH0 : Real.log (9 / 8) ≤ (117783035658337 / 1000000000000000) := by
  have hx : |((-1 / 8) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [show (1 : ℝ) - (-1 / 8) = (9 / 8) by norm_num] at h
  generalize Real.log (9 / 8) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 11/8 <= H` (u = 2^1 * 11/16, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem log_profit_density_logH1 : Real.log (11 / 8) ≤ (318454155011679 / 1000000000000000) := by
  have hx : |((5 / 16) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
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

/-- `log 5/4 <= H` (u = 2^0 * 5/4, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem log_profit_density_logH2 : Real.log (5 / 4) ≤ (3486618285187 / 15625000000000) := by
  have hx : |((-1 / 4) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [show (1 : ℝ) - (-1 / 4) = (5 / 4) by norm_num] at h
  generalize Real.log (5 / 4) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 7/4 <= H` (u = 2^1 * 7/8, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem log_profit_density_logH3 : Real.log (7 / 4) ≤ (111923157635543 / 200000000000000) := by
  have hx : |((1 / 8) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [show (1 : ℝ) - (1 / 8) = (7 / 8) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (7 / 8) = Real.log (7 / 4) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (7 / 8) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 2 <= H` (u = 2^1 * 1, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem log_profit_density_logH4 : Real.log (2) ≤ (108304247 / 156250000) := by
  have hx : |((0) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
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

theorem log_profit_density_piece0 (x : ℝ) : log_profit_density_U x ≤ (-1 / 4 : ℝ) * x + (0 : ℝ) := by
  have := minPieces_le log_profit_density_A log_profit_density_B x 0
  simpa [log_profit_density_U, log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_piece1 (x : ℝ) : log_profit_density_U x ≤ (-7 / 20 : ℝ) * x + (1 / 20 : ℝ) := by
  have := minPieces_le log_profit_density_A log_profit_density_B x 1
  simpa [log_profit_density_U, log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_node0 : log_profit_density_U (0 : ℝ) = (0 : ℝ) := by
  apply le_antisymm
  · linarith [log_profit_density_piece0 (0 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [log_profit_density_A, log_profit_density_B]

theorem log_profit_density_node1 : log_profit_density_U (1 / 2 : ℝ) = (-1 / 8 : ℝ) := by
  apply le_antisymm
  · linarith [log_profit_density_piece0 (1 / 2 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [log_profit_density_A, log_profit_density_B]

theorem log_profit_density_node2 : log_profit_density_U (1 : ℝ) = (-3 / 10 : ℝ) := by
  apply le_antisymm
  · linarith [log_profit_density_piece1 (1 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [log_profit_density_A, log_profit_density_B]

theorem log_profit_density_base : (-1 : ℝ) + (1 / 2 : ℝ) ≤ log_profit_density_U (1 : ℝ) := by
  apply le_minPieces; intro k; fin_cases k <;> norm_num [log_profit_density_A, log_profit_density_B]

theorem log_profit_density_c0_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + log_profit_density_g 1 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * log_profit_density_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (9 / 8 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (117783035658337 / 1000000000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((11189952679074967 / 45000000000000000 : ℝ) + (-5103349106975011 / 15000000000000000 : ℝ) * R + (29 / 180 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((117783035658337 / 1000000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (9 / 8 : ℝ)) / (9 / 8 : ℝ))) + (1 / 2 : ℝ)) = ((11189952679074967 / 45000000000000000 : ℝ) + (-5103349106975011 / 15000000000000000 : ℝ) * R + (29 / 180 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c0_k1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + log_profit_density_g 1 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * log_profit_density_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (9 / 8 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (117783035658337 / 1000000000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((8939952679074967 / 45000000000000000 : ℝ) + (-4353349106975011 / 15000000000000000 : ℝ) * R + (29 / 180 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((117783035658337 / 1000000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (9 / 8 : ℝ)) / (9 / 8 : ℝ))) + (1 / 2 : ℝ)) = ((8939952679074967 / 45000000000000000 : ℝ) + (-4353349106975011 / 15000000000000000 : ℝ) * R + (29 / 180 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 1 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    log_profit_density_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + log_profit_density_g 1 R + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := log_profit_density_c0_k0 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this
  · have := log_profit_density_c0_k1 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_c0_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 1 R ∧ log_profit_density_h 1 R ≤ (1 : ℝ) :=
  ⟨log_profit_density_c0_lo R h1 h2, log_profit_density_c0_hi R h1 h2⟩

theorem log_profit_density_c1_k0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + log_profit_density_g 1 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * log_profit_density_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (11 / 8 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (318454155011679 / 1000000000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH1
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((10497004294871531 / 55000000000000000 : ℝ) + (-15502995705128469 / 55000000000000000 : ℝ) * R + (61 / 220 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((318454155011679 / 1000000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (11 / 8 : ℝ)) / (11 / 8 : ℝ))) + (1 / 2 : ℝ)) = ((10497004294871531 / 55000000000000000 : ℝ) + (-15502995705128469 / 55000000000000000 : ℝ) * R + (61 / 220 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c1_k1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + log_profit_density_g 1 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * log_profit_density_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (11 / 8 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (318454155011679 / 1000000000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH1
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((7747004294871531 / 55000000000000000 : ℝ) + (-12752995705128469 / 55000000000000000 : ℝ) * R + (61 / 220 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((318454155011679 / 1000000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (11 / 8 : ℝ)) / (11 / 8 : ℝ))) + (1 / 2 : ℝ)) = ((7747004294871531 / 55000000000000000 : ℝ) + (-12752995705128469 / 55000000000000000 : ℝ) * R + (61 / 220 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c1_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 1 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c1_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    log_profit_density_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + log_profit_density_g 1 R + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := log_profit_density_c1_k0 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this
  · have := log_profit_density_c1_k1 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_c1_cl (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 1 R ∧ log_profit_density_h 1 R ≤ (1 : ℝ) :=
  ⟨log_profit_density_c1_lo R h1 h2, log_profit_density_c1_hi R h1 h2⟩

theorem log_profit_density_c2_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + log_profit_density_g 2 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * log_profit_density_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (5 / 4 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (3486618285187 / 15625000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH2
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((19169631714813 / 78125000000000 : ℝ) + (-26142868285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((3486618285187 / 15625000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (5 / 4 : ℝ)) / (5 / 4 : ℝ))) + (1 / 2 : ℝ)) = ((19169631714813 / 78125000000000 : ℝ) + (-26142868285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c2_k1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + log_profit_density_g 2 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * log_profit_density_h 2 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (5 / 4 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (3486618285187 / 15625000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH2
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((15263381714813 / 78125000000000 : ℝ) + (-22236618285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((3486618285187 / 15625000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (5 / 4 : ℝ)) / (5 / 4 : ℝ))) + (1 / 2 : ℝ)) = ((15263381714813 / 78125000000000 : ℝ) + (-22236618285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c2_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 2 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c2_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    log_profit_density_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c2 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + log_profit_density_g 2 R + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := log_profit_density_c2_k0 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this
  · have := log_profit_density_c2_k1 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_c2_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 2 R ∧ log_profit_density_h 2 R ≤ (1 : ℝ) :=
  ⟨log_profit_density_c2_lo R h1 h2, log_profit_density_c2_hi R h1 h2⟩

theorem log_profit_density_c3_k0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + log_profit_density_g 2 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * log_profit_density_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (7 / 4 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (111923157635543 / 200000000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH3
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((866537896551199 / 7000000000000000 : ℝ) + (-2333462103448801 / 7000000000000000 : ℝ) * R + (41 / 140 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((111923157635543 / 200000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (7 / 4 : ℝ)) / (7 / 4 : ℝ))) + (1 / 2 : ℝ)) = ((866537896551199 / 7000000000000000 : ℝ) + (-2333462103448801 / 7000000000000000 : ℝ) * R + (41 / 140 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c3_k1 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + log_profit_density_g 2 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * log_profit_density_h 2 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (7 / 4 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (111923157635543 / 200000000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH3
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((516537896551199 / 7000000000000000 : ℝ) + (-1983462103448801 / 7000000000000000 : ℝ) * R + (41 / 140 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((111923157635543 / 200000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (7 / 4 : ℝ)) / (7 / 4 : ℝ))) + (1 / 2 : ℝ)) = ((516537896551199 / 7000000000000000 : ℝ) + (-1983462103448801 / 7000000000000000 : ℝ) * R + (41 / 140 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c3_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c3_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    log_profit_density_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c3 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + log_profit_density_g 2 R + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := log_profit_density_c3_k0 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this
  · have := log_profit_density_c3_k1 R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_c3_cl (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 2 R ∧ log_profit_density_h 2 R ≤ (1 : ℝ) :=
  ⟨log_profit_density_c3_lo R h1 h2, log_profit_density_c3_hi R h1 h2⟩

theorem log_profit_density_c4_k0 (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + log_profit_density_g m R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * log_profit_density_h m R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (5 / 4 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (3486618285187 / 15625000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH2
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((19169631714813 / 78125000000000 : ℝ) + (-26142868285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((3486618285187 / 15625000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (5 / 4 : ℝ)) / (5 / 4 : ℝ))) + (1 / 2 : ℝ)) = ((19169631714813 / 78125000000000 : ℝ) + (-26142868285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c4_k1 (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + log_profit_density_g m R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * log_profit_density_h m R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (5 / 4 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (3486618285187 / 15625000000000 : ℝ) (by norm_num) hy0 log_profit_density_logH2
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((15263381714813 / 78125000000000 : ℝ) + (-22236618285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((3486618285187 / 15625000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (5 / 4 : ℝ)) / (5 / 4 : ℝ))) + (1 / 2 : ℝ)) = ((15263381714813 / 78125000000000 : ℝ) + (-22236618285187 / 78125000000000 : ℝ) * R + (17 / 100 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c4_lo (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h m R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c4_hi (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    log_profit_density_h m R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c4 (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + log_profit_density_g m R + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h m R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := log_profit_density_c4_k0 m R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this
  · have := log_profit_density_c4_k1 m R h1 h2
    simpa [log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_c4_cl (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h m R ∧ log_profit_density_h m R ≤ (1 : ℝ) :=
  ⟨log_profit_density_c4_lo m R h1 h2, log_profit_density_c4_hi m R h1 h2⟩

theorem log_profit_density_c5_k0 (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (-1 / 4 : ℝ) * R + log_profit_density_g m R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * log_profit_density_h m R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (2 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (108304247 / 156250000 : ℝ) (by norm_num) hy0 log_profit_density_logH4
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((165133253 / 781250000 : ℝ) + (-264554247 / 781250000 : ℝ) * R + (1 / 5 : ℝ) * R ^ 2) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((108304247 / 156250000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (2 : ℝ)) / (2 : ℝ))) + (1 / 2 : ℝ)) = ((165133253 / 781250000 : ℝ) + (-264554247 / 781250000 : ℝ) * R + (1 / 5 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c5_k1 (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (-1 / 4 : ℝ) * R + log_profit_density_g m R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * log_profit_density_h m R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have eg : log_profit_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [log_profit_density_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (2 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (108304247 / 156250000 : ℝ) (by norm_num) hy0 log_profit_density_logH4
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
  have key : 0 ≤ ((126070753 / 781250000 : ℝ) + (-225491747 / 781250000 : ℝ) * R + (1 / 5 : ℝ) * R ^ 2) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + ((((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 5 : ℝ) * ((108304247 / 156250000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (2 : ℝ)) / (2 : ℝ))) + (1 / 2 : ℝ)) = ((126070753 / 781250000 : ℝ) + (-225491747 / 781250000 : ℝ) * R + (1 / 5 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem log_profit_density_c5_lo (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (0 : ℝ) ≤ log_profit_density_h m R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [pow_nonneg hs 0]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c5_hi (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    log_profit_density_h m R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : log_profit_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [log_profit_density_h]
  have key : 0 ≤ (R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem log_profit_density_c5 (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (-1 / 4 : ℝ) * R + log_profit_density_g m R + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h m R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := log_profit_density_c5_k0 m R h1
    simpa [log_profit_density_A, log_profit_density_B] using this
  · have := log_profit_density_c5_k1 m R h1
    simpa [log_profit_density_A, log_profit_density_B] using this

theorem log_profit_density_c5_cl (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (0 : ℝ) ≤ log_profit_density_h m R ∧ log_profit_density_h m R ≤ (1 : ℝ) :=
  ⟨log_profit_density_c5_lo m R h1, log_profit_density_c5_hi m R h1⟩

theorem log_profit_density_step1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((1 : ℕ) : ℝ) * log_profit_density_U yb + log_profit_density_g 1 (((1 : ℕ) : ℝ) * yb) + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h 1 (((1 : ℕ) : ℝ) * yb)) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · linarith [log_profit_density_c0 (1 * yb) (by linarith) h_0, log_profit_density_piece0 yb]
  · linarith [log_profit_density_c1 (1 * yb) h_0.le (by linarith), log_profit_density_piece1 yb]

theorem log_profit_density_clos1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 1 (((1 : ℕ) : ℝ) * yb) ∧ log_profit_density_h 1 (((1 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · exact log_profit_density_c0_cl (1 * yb) (by linarith) h_0
  · exact log_profit_density_c1_cl (1 * yb) h_0.le (by linarith)

theorem log_profit_density_step2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((2 : ℕ) : ℝ) * log_profit_density_U yb + log_profit_density_g 2 (((2 : ℕ) : ℝ) * yb) + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h 2 (((2 : ℕ) : ℝ) * yb)) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  rcases le_or_gt (2 * yb) (1 : ℝ) with h_0 | h_0
  · linarith [log_profit_density_c2 (2 * yb) (by linarith) h_0, log_profit_density_piece0 yb]
  · linarith [log_profit_density_c3 (2 * yb) h_0.le (by linarith), log_profit_density_piece1 yb]

theorem log_profit_density_clos2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h 2 (((2 : ℕ) : ℝ) * yb) ∧ log_profit_density_h 2 (((2 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  rcases le_or_gt (2 * yb) (1 : ℝ) with h_0 | h_0
  · exact log_profit_density_c2_cl (2 * yb) (by linarith) h_0
  · exact log_profit_density_c3_cl (2 * yb) h_0.le (by linarith)

theorem log_profit_density_tail (m : ℕ) (hm : 2 < m) (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (m : ℝ) * log_profit_density_U yb + log_profit_density_g m ((m : ℝ) * yb) + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h m ((m : ℝ) * yb)) := by
  have hm4 : 3 ≤ m := hm
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hR0 : (3 : ℝ) * (0 : ℝ) ≤ (m : ℝ) * yb :=
    mul_le_mul hmr hl (by norm_num) hm0
  have hP0 : (m : ℝ) * log_profit_density_U yb ≤ (m : ℝ) * ((-1 / 4 : ℝ) * yb + (0 : ℝ)) :=
    mul_le_mul_of_nonneg_left (log_profit_density_piece0 yb) hm0
  have hM0 : (m : ℝ) * (0 : ℝ) ≤ (3 : ℝ) * (0 : ℝ) :=
    mul_le_mul_of_nonpos_right hmr (by norm_num)
  have hH0 : 0 ≤ (m : ℝ) * (-(0 : ℝ)) * ((1 : ℝ) - yb) :=
    mul_nonneg (mul_nonneg hm0 (by norm_num)) (by linarith)
  rcases le_or_gt ((m : ℝ) * yb) (1 : ℝ) with h_0 | h_0
  · linarith [log_profit_density_c4 m ((m : ℝ) * yb) (by linarith) h_0, hP0, hM0, hH0]
  · linarith [log_profit_density_c5 m ((m : ℝ) * yb) h_0.le, hP0, hM0, hH0]

set_option linter.unusedVariables false in
theorem log_profit_density_tail_clos (m : ℕ) (hm : 2 < m) (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ log_profit_density_h m ((m : ℝ) * yb) ∧ log_profit_density_h m ((m : ℝ) * yb) ≤ (1 : ℝ) := by
  have hm4 : 3 ≤ m := hm
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hR0 : (3 : ℝ) * (0 : ℝ) ≤ (m : ℝ) * yb :=
    mul_le_mul hmr hl (by norm_num) hm0
  rcases le_or_gt ((m : ℝ) * yb) (1 : ℝ) with h_0 | h_0
  · exact log_profit_density_c4_cl m ((m : ℝ) * yb) (by linarith) h_0
  · exact log_profit_density_c5_cl m ((m : ℝ) * yb) h_0.le

theorem log_profit_density_hstep : ∀ m : ℕ, 1 ≤ m → True → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (m : ℝ) * log_profit_density_U yb + log_profit_density_g m (m * yb) + (1 / 2 : ℝ) ≤ log_profit_density_U (log_profit_density_h m (m * yb)) := by
  intro m hm hok yb hl hu
  rcases Nat.lt_or_ge 2 m with hM | hM
  · exact log_profit_density_tail m hM yb hl hu
  · interval_cases m
    · exact log_profit_density_step1 yb hl hu
    · exact log_profit_density_step2 yb hl hu

theorem log_profit_density_hclos : ∀ m : ℕ, 1 ≤ m → True → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (0 : ℝ) ≤ log_profit_density_h m (m * yb) ∧ log_profit_density_h m (m * yb) ≤ (1 : ℝ) := by
  intro m hm hok yb hl hu
  rcases Nat.lt_or_ge 2 m with hM | hM
  · exact log_profit_density_tail_clos m hM yb hl hu
  · interval_cases m
    · exact log_profit_density_clos1 yb hl hu
    · exact log_profit_density_clos2 yb hl hu

set_option linter.unusedVariables false in
theorem log_profit_density_U_le_max (x : ℝ) (hl : (0 : ℝ) ≤ x) (hu : x ≤ (1 : ℝ)) : log_profit_density_U x ≤ (0 : ℝ) := by
  rcases le_or_gt x (1 / 2 : ℝ) with h_0 | h_0
  · linarith [log_profit_density_piece0 x]
  · linarith [log_profit_density_piece1 x]

/-- MAIN.  The certified bound on every finite rooted tree. -/
theorem log_profit_density (b : PTree) :
    (0 : ℝ) ≤ b.msg log_profit_density_h (1 : ℝ) ∧ b.msg log_profit_density_h (1 : ℝ) ≤ (1 : ℝ) ∧
      b.ell log_profit_density_g log_profit_density_h (-1 : ℝ) (1 : ℝ) + (1 / 2 : ℝ) * b.size ≤ log_profit_density_U (b.msg log_profit_density_h (1 : ℝ)) :=
  pooled_induction_core (fun _ => True) log_profit_density_h log_profit_density_g log_profit_density_U log_profit_density_U (1 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1 / 2 : ℝ)
    (minPieces_jensen log_profit_density_A log_profit_density_B) (fun _ _ _ => le_rfl) ⟨by norm_num, by norm_num⟩ log_profit_density_base log_profit_density_hclos log_profit_density_hstep b (PTree.allDeg_true b)

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 0`. -/
theorem log_profit_density_uniform (b : PTree) :
    b.ell log_profit_density_g log_profit_density_h (-1 : ℝ) (1 : ℝ) + (1 / 2 : ℝ) * b.size ≤ (0 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := log_profit_density b
  linarith [log_profit_density_U_le_max _ h1 h2]

/-! ## Instance `leaf_exempt_log` (LEAF-EXEMPT, extension 2026-10-01)

Claim: `ell + (1/5) * size ≤ U (msg)` on every NON-LEAF finite rooted tree of child count at most 2, for
  h(m, R) = 1/(R + 1),  g(m, R) = -R/(R + 1) + 1/10 log(1 + 1/2 R),
  leaf (y, l) = (1, 0) entering EXACTLY (never pooled), U the concave interpolant of
  (1/3, 1/10), (3/4, 1/10).
Certificate: 3 cells over the child mixes (p pooled, k leaves), p + k ≤ 2, plus 2 all-leaves cases. -/

noncomputable def leaf_exempt_log_A : Fin 1 → ℝ := ![(0 : ℝ)]
noncomputable def leaf_exempt_log_B : Fin 1 → ℝ := ![(1 / 10 : ℝ)]
/-- The witness: the minimum of its 1 affine pieces. -/
noncomputable def leaf_exempt_log_U : ℝ → ℝ := minPieces leaf_exempt_log_A leaf_exempt_log_B
noncomputable def leaf_exempt_log_h : ℕ → ℝ → ℝ := fun _ R => ((1 : ℝ)) / ((1 : ℝ) + R)
noncomputable def leaf_exempt_log_g : ℕ → ℝ → ℝ := fun _ R => ((-1 : ℝ) * R) / ((1 : ℝ) + R) + (1 / 10 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R)

/-- `log 61/48 <= H` (u = 2^0 * 61/48, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem leaf_exempt_log_logH0 : Real.log (61 / 48) ≤ (239672908521783 / 1000000000000000) := by
  have hx : |((-13 / 48) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [show (1 : ℝ) - (-13 / 48) = (61 / 48) by norm_num] at h
  generalize Real.log (61 / 48) = L at h ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 85/48 <= H` (u = 2^1 * 85/96, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem leaf_exempt_log_logH1 : Real.log (85 / 48) ≤ (285725122911597 / 500000000000000) := by
  have hx : |((11 / 96) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [show (1 : ℝ) - (11 / 96) = (85 / 96) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (85 / 96) = Real.log (85 / 48) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (85 / 96) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 37/24 <= H` (u = 2^1 * 37/48, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem leaf_exempt_log_logH2 : Real.log (37 / 24) ≤ (432864089243801 / 1000000000000000) := by
  have hx : |((11 / 48) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [show (1 : ℝ) - (11 / 48) = (37 / 48) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (37 / 48) = Real.log (37 / 24) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (37 / 48) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 3/2 <= H` (u = 2^1 * 3/4, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem leaf_exempt_log_logH3 : Real.log (3 / 2) ≤ (202732564854947 / 500000000000000) := by
  have hx : |((1 / 4) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [show (1 : ℝ) - (1 / 4) = (3 / 4) by norm_num] at h
  have hs : ((1 : ℕ) : ℝ) * Real.log 2 + Real.log (3 / 4) = Real.log (3 / 2) := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [← hs]
  generalize Real.log (3 / 4) = L at h ⊢
  generalize Real.log 2 = T at h2 ⊢
  norm_num at h2 ⊢
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log 2 <= H` (u = 2^1 * 1, order-12 Taylor box of Real.abs_log_sub_add_sum_range_le + Real.log_two_lt_d9).
    conjecture1_proved = False. -/
theorem leaf_exempt_log_logH4 : Real.log (2) ≤ (108304247 / 156250000) := by
  have hx : |((0) : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
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

theorem leaf_exempt_log_piece0 (x : ℝ) : leaf_exempt_log_U x ≤ (0 : ℝ) * x + (1 / 10 : ℝ) := by
  have := minPieces_le leaf_exempt_log_A leaf_exempt_log_B x 0
  simpa [leaf_exempt_log_U, leaf_exempt_log_A, leaf_exempt_log_B] using this

theorem leaf_exempt_log_node0 : leaf_exempt_log_U (1 / 3 : ℝ) = (1 / 10 : ℝ) := by
  apply le_antisymm
  · linarith [leaf_exempt_log_piece0 (1 / 3 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k ; norm_num [leaf_exempt_log_A, leaf_exempt_log_B]

theorem leaf_exempt_log_node1 : leaf_exempt_log_U (3 / 4 : ℝ) = (1 / 10 : ℝ) := by
  apply le_antisymm
  · linarith [leaf_exempt_log_piece0 (3 / 4 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k ; norm_num [leaf_exempt_log_A, leaf_exempt_log_B]

theorem leaf_exempt_log_c0_k0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 10 : ℝ) + leaf_exempt_log_g 1 R + (1 / 5 : ℝ) ≤ (0 : ℝ) * leaf_exempt_log_h 1 R + (1 / 10 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_log_h]
  have eg : leaf_exempt_log_g 1 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (1 / 10 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [leaf_exempt_log_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (61 / 48 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (239672908521783 / 1000000000000000 : ℝ) (by norm_num) hy0 leaf_exempt_log_logH0
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 10 : ℝ))
  have key : 0 ≤ ((-123620047419828763 / 610000000000000000 : ℝ) + (462379952580171237 / 610000000000000000 : ℝ) * R + (-12 / 305 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 10 : ℝ)) - ((0 : ℝ) * R + (1 : ℝ) * (1 / 10 : ℝ) + ((((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (1 / 10 : ℝ) * ((239672908521783 / 1000000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (61 / 48 : ℝ)) / (61 / 48 : ℝ))) + (1 / 5 : ℝ)) = ((-123620047419828763 / 610000000000000000 : ℝ) + (462379952580171237 / 610000000000000000 : ℝ) * R + (-12 / 305 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_log_c0_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h 1 R := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_log_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_log_c0_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    leaf_exempt_log_h 1 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_log_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_log_c0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 10 : ℝ) + leaf_exempt_log_g 1 R + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_log_c0_k0 R h1 h2
    simpa [leaf_exempt_log_A, leaf_exempt_log_B] using this

theorem leaf_exempt_log_c0_cl (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h 1 R ∧ leaf_exempt_log_h 1 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_log_c0_lo R h1 h2, leaf_exempt_log_c0_hi R h1 h2⟩

theorem leaf_exempt_log_c1_k0 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 10 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g 2 (R + (1 : ℝ)) + (1 / 5 : ℝ) ≤ (0 : ℝ) * leaf_exempt_log_h 2 (R + (1 : ℝ)) + (1 / 10 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_log_h]; ring
  have eg : leaf_exempt_log_g 2 (R + (1 : ℝ)) = (((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) + (1 / 10 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * (R + (1 : ℝ))) := by simp only [leaf_exempt_log_g]; ring
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * (R + (1 : ℝ)) := by linarith
  have hl0 := log_tangent_le (85 / 48 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * (R + (1 : ℝ))) (285725122911597 / 500000000000000 : ℝ) (by norm_num) hy0 leaf_exempt_log_logH1
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 10 : ℝ))
  have key : 0 ≤ ((4942672910502851 / 42500000000000000 : ℝ) + (42642672910502851 / 85000000000000000 : ℝ) * R + (-12 / 425 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 : ℝ)) / ((2 : ℝ) + R)) + (1 / 10 : ℝ)) - ((0 : ℝ) * R + (1 : ℝ) * (1 / 10 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + ((((-1 : ℝ) + (-1 : ℝ) * R) / ((2 : ℝ) + R)) + (1 / 10 : ℝ) * ((285725122911597 / 500000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * (R + (1 : ℝ)) - (85 / 48 : ℝ)) / (85 / 48 : ℝ))) + (1 / 5 : ℝ)) = ((4942672910502851 / 42500000000000000 : ℝ) + (42642672910502851 / 85000000000000000 : ℝ) * R + (-12 / 425 : ℝ) * R ^ 2) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_log_c1_lo (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h 2 (R + (1 : ℝ)) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_log_h]; ring
  have key : 0 ≤ ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((2 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((1 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_log_c1_hi (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    leaf_exempt_log_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (1 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 4 : ℝ) - R := by linarith
  have hDt : 0 < ((2 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 2 (R + (1 : ℝ)) = (((1 : ℝ)) / ((2 : ℝ) + R)) := by simp only [leaf_exempt_log_h]; ring
  have key : 0 ≤ ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((2 : ℝ) + R))) = ((1 / 2 : ℝ) + (3 / 4 : ℝ) * R) / ((2 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_log_c1 (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (1 / 10 : ℝ) + (1 : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g 2 (R + (1 : ℝ)) + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h 2 (R + (1 : ℝ))) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_log_c1_k0 R h1 h2
    simpa [leaf_exempt_log_A, leaf_exempt_log_B] using this

theorem leaf_exempt_log_c1_cl (R : ℝ) (h1 : (1 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h 2 (R + (1 : ℝ)) ∧ leaf_exempt_log_h 2 (R + (1 : ℝ)) ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_log_c1_lo R h1 h2, leaf_exempt_log_c1_hi R h1 h2⟩

theorem leaf_exempt_log_c2_k0 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (0 : ℝ) * R + (2 : ℝ) * (1 / 10 : ℝ) + leaf_exempt_log_g 2 R + (1 / 5 : ℝ) ≤ (0 : ℝ) * leaf_exempt_log_h 2 R + (1 / 10 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_log_h]
  have eg : leaf_exempt_log_g 2 R = (((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (1 / 10 : ℝ) * Real.log ((1 : ℝ) + (1 / 2 : ℝ) * R) := by simp only [leaf_exempt_log_g]
  have hy0 : 0 < (1 : ℝ) + (1 / 2 : ℝ) * R := by linarith
  have hl0 := log_tangent_le (37 / 24 : ℝ) ((1 : ℝ) + (1 / 2 : ℝ) * R) (432864089243801 / 1000000000000000 : ℝ) (by norm_num) hy0 leaf_exempt_log_logH2
  have hk0 := mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ (1 / 10 : ℝ))
  have key : 0 ≤ ((-114015971302020637 / 370000000000000000 : ℝ) + (243984028697979363 / 370000000000000000 : ℝ) * R + (-6 / 185 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 10 : ℝ)) - ((0 : ℝ) * R + (2 : ℝ) * (1 / 10 : ℝ) + ((((-1 : ℝ) * R) / ((1 : ℝ) + R)) + (1 / 10 : ℝ) * ((432864089243801 / 1000000000000000 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ) * R - (37 / 24 : ℝ)) / (37 / 24 : ℝ))) + (1 / 5 : ℝ)) = ((-114015971302020637 / 370000000000000000 : ℝ) + (243984028697979363 / 370000000000000000 : ℝ) * R + (-6 / 185 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem leaf_exempt_log_c2_lo (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h 2 R := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_log_h]
  have key : 0 ≤ ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((1 / 3 : ℝ)) = ((2 / 3 : ℝ) + (-1 / 3 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_log_c2_hi (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    leaf_exempt_log_h 2 R ≤ (3 / 4 : ℝ) := by
  have hs : 0 ≤ R - (2 / 3 : ℝ) := by linarith
  have ht : 0 ≤ (3 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : leaf_exempt_log_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [leaf_exempt_log_h]
  have key : 0 ≤ ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((3 / 4 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = ((-1 / 4 : ℝ) + (3 / 4 : ℝ) * R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem leaf_exempt_log_c2 (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (0 : ℝ) * R + (2 : ℝ) * (1 / 10 : ℝ) + leaf_exempt_log_g 2 R + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := leaf_exempt_log_c2_k0 R h1 h2
    simpa [leaf_exempt_log_A, leaf_exempt_log_B] using this

theorem leaf_exempt_log_c2_cl (R : ℝ) (h1 : (2 / 3 : ℝ) ≤ R) (h2 : R ≤ (3 / 2 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h 2 R ∧ leaf_exempt_log_h 2 R ≤ (3 / 4 : ℝ) :=
  ⟨leaf_exempt_log_c2_lo R h1 h2, leaf_exempt_log_c2_hi R h1 h2⟩

set_option linter.unusedVariables false in
theorem leaf_exempt_log_xs_0_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((0 : ℕ) : ℝ) * leaf_exempt_log_U yb + ((1 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) := by push_cast; ring
  rw [show (0 + 1 : ℕ) = 1 from rfl, e1]
  have eh : leaf_exempt_log_h 1 (1 : ℝ) = (1 / 2 : ℝ) := by norm_num [leaf_exempt_log_h]
  have eg : leaf_exempt_log_g 1 (1 : ℝ) = (-1 / 2 : ℝ) + (1 / 10 : ℝ) * Real.log (3 / 2 : ℝ) := by norm_num [leaf_exempt_log_g]
  rw [eh, eg]
  have hU : (-297267435145053 / 5000000000000000 : ℝ) ≤ leaf_exempt_log_U (1 / 2 : ℝ) := by
    apply le_minPieces; intro K; fin_cases K; norm_num [leaf_exempt_log_A, leaf_exempt_log_B]
  have hk0 := mul_le_mul_of_nonneg_left leaf_exempt_log_logH3 (by norm_num : (0 : ℝ) ≤ (1 / 10 : ℝ))
  push_cast
  linarith [hU, hk0]

set_option linter.unusedVariables false in
theorem leaf_exempt_log_xc_0_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_log_h (0 + 1) (((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) := by push_cast; ring
  rw [show (0 + 1 : ℕ) = 1 from rfl, e1]
  norm_num [leaf_exempt_log_h]

theorem leaf_exempt_log_xs_1_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((1 : ℕ) : ℝ) * leaf_exempt_log_U yb + ((0 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb := by push_cast; ring
  rw [show (1 + 0 : ℕ) = 1 from rfl, e1]
  push_cast
  · linarith [leaf_exempt_log_c0 ((1 : ℝ) * yb) (by linarith) (by linarith), leaf_exempt_log_piece0 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_log_xc_1_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_log_h (1 + 0) (((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb := by push_cast; ring
  rw [show (1 + 0 : ℕ) = 1 from rfl, e1]
  · exact leaf_exempt_log_c0_cl ((1 : ℝ) * yb) (by linarith) (by linarith)

set_option linter.unusedVariables false in
theorem leaf_exempt_log_xs_0_2 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((0 : ℕ) : ℝ) * leaf_exempt_log_U yb + ((2 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) := by push_cast; ring
  rw [show (0 + 2 : ℕ) = 2 from rfl, e1]
  have eh : leaf_exempt_log_h 2 (2 : ℝ) = (1 / 3 : ℝ) := by norm_num [leaf_exempt_log_h]
  have eg : leaf_exempt_log_g 2 (2 : ℝ) = (-2 / 3 : ℝ) + (1 / 10 : ℝ) * Real.log (2 : ℝ) := by norm_num [leaf_exempt_log_g]
  rw [eh, eg]
  have hU : (12412741 / 4687500000 : ℝ) ≤ leaf_exempt_log_U (1 / 3 : ℝ) := by
    apply le_minPieces; intro K; fin_cases K; norm_num [leaf_exempt_log_A, leaf_exempt_log_B]
  have hk0 := mul_le_mul_of_nonneg_left leaf_exempt_log_logH4 (by norm_num : (0 : ℝ) ≤ (1 / 10 : ℝ))
  push_cast
  linarith [hU, hk0]

set_option linter.unusedVariables false in
theorem leaf_exempt_log_xc_0_2 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_log_h (0 + 2) (((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((0 : ℕ) : ℝ) * yb + ((2 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) := by push_cast; ring
  rw [show (0 + 2 : ℕ) = 2 from rfl, e1]
  norm_num [leaf_exempt_log_h]

theorem leaf_exempt_log_xs_1_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((1 : ℕ) : ℝ) * leaf_exempt_log_U yb + ((1 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb + (1 : ℝ) := by push_cast; ring
  rw [show (1 + 1 : ℕ) = 2 from rfl, e1]
  push_cast
  · linarith [leaf_exempt_log_c1 ((1 : ℝ) * yb) (by linarith) (by linarith), leaf_exempt_log_piece0 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_log_xc_1_1 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_log_h (1 + 1) (((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((1 : ℕ) : ℝ) * yb + ((1 : ℕ) : ℝ) * (1 : ℝ) = (1 : ℝ) * yb + (1 : ℝ) := by push_cast; ring
  rw [show (1 + 1 : ℕ) = 2 from rfl, e1]
  · exact leaf_exempt_log_c1_cl ((1 : ℝ) * yb) (by linarith) (by linarith)

theorem leaf_exempt_log_xs_2_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    ((2 : ℕ) : ℝ) * leaf_exempt_log_U yb + ((0 : ℕ) : ℝ) * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ))) := by
  have e1 : ((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) * yb := by push_cast; ring
  rw [show (2 + 0 : ℕ) = 2 from rfl, e1]
  push_cast
  · linarith [leaf_exempt_log_c2 ((2 : ℝ) * yb) (by linarith) (by linarith), leaf_exempt_log_piece0 yb]

set_option linter.unusedVariables false in
theorem leaf_exempt_log_xc_2_0 (yb : ℝ) (hl : (1 / 3 : ℝ) ≤ yb) (hu : yb ≤ (3 / 4 : ℝ)) :
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ∧ leaf_exempt_log_h (2 + 0) (((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  have e1 : ((2 : ℕ) : ℝ) * yb + ((0 : ℕ) : ℝ) * (1 : ℝ) = (2 : ℝ) * yb := by push_cast; ring
  rw [show (2 + 0 : ℕ) = 2 from rfl, e1]
  · exact leaf_exempt_log_c2_cl ((2 : ℝ) * yb) (by linarith) (by linarith)

theorem leaf_exempt_log_xhstep : ∀ p k : ℕ, 1 ≤ p + k → p + k ≤ 2 → ∀ yb : ℝ, (1 / 3 : ℝ) ≤ yb → yb ≤ (3 / 4 : ℝ) →
    (p : ℝ) * leaf_exempt_log_U yb + k * ((0 : ℝ) + (1 / 5 : ℝ)) + leaf_exempt_log_g (p + k) (p * yb + k * (1 : ℝ)) + (1 / 5 : ℝ) ≤ leaf_exempt_log_U (leaf_exempt_log_h (p + k) (p * yb + k * (1 : ℝ))) := by
  intro p k h1 h2 yb hl hu
  have hp : p ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p <;> interval_cases k <;> first | (exfalso; omega) | exact leaf_exempt_log_xs_0_1 yb hl hu | exact leaf_exempt_log_xs_1_0 yb hl hu | exact leaf_exempt_log_xs_0_2 yb hl hu | exact leaf_exempt_log_xs_1_1 yb hl hu | exact leaf_exempt_log_xs_2_0 yb hl hu

theorem leaf_exempt_log_xhclos : ∀ p k : ℕ, 1 ≤ p + k → p + k ≤ 2 → ∀ yb : ℝ, (1 / 3 : ℝ) ≤ yb → yb ≤ (3 / 4 : ℝ) →
    (1 / 3 : ℝ) ≤ leaf_exempt_log_h (p + k) (p * yb + k * (1 : ℝ)) ∧ leaf_exempt_log_h (p + k) (p * yb + k * (1 : ℝ)) ≤ (3 / 4 : ℝ) := by
  intro p k h1 h2 yb hl hu
  have hp : p ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p <;> interval_cases k <;> first | (exfalso; omega) | exact leaf_exempt_log_xc_0_1 yb hl hu | exact leaf_exempt_log_xc_1_0 yb hl hu | exact leaf_exempt_log_xc_0_2 yb hl hu | exact leaf_exempt_log_xc_1_1 yb hl hu | exact leaf_exempt_log_xc_2_0 yb hl hu

set_option linter.unusedVariables false in
theorem leaf_exempt_log_U_le_max (x : ℝ) (hl : (1 / 3 : ℝ) ≤ x) (hu : x ≤ (3 / 4 : ℝ)) : leaf_exempt_log_U x ≤ (1 / 10 : ℝ) := by
  · linarith [leaf_exempt_log_piece0 x]

/-- MAIN.  The certified bound on every NON-LEAF tree of child count at most 2 (leaves exempt). -/
theorem leaf_exempt_log (b : PTree) (hn : b.isNode = true) (hb : b.AllDeg (fun m => m ≤ 2)) :
    (1 / 3 : ℝ) ≤ b.msg leaf_exempt_log_h (1 : ℝ) ∧ b.msg leaf_exempt_log_h (1 : ℝ) ≤ (3 / 4 : ℝ) ∧
      b.ell leaf_exempt_log_g leaf_exempt_log_h (0 : ℝ) (1 : ℝ) + (1 / 5 : ℝ) * b.size ≤ leaf_exempt_log_U (b.msg leaf_exempt_log_h (1 : ℝ)) :=
  exempt_induction_core (fun m => m ≤ 2) leaf_exempt_log_h leaf_exempt_log_g leaf_exempt_log_U leaf_exempt_log_U (1 : ℝ) (0 : ℝ) (1 / 3 : ℝ) (3 / 4 : ℝ) (1 / 5 : ℝ)
    (fun _ s y hs => minPieces_jensen_on leaf_exempt_log_A leaf_exempt_log_B s y hs) (fun _ _ _ => le_rfl) (by norm_num) leaf_exempt_log_xhclos leaf_exempt_log_xhstep b hn hb

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 1/10` on every non-leaf tree. -/
theorem leaf_exempt_log_uniform (b : PTree) (hn : b.isNode = true) (hb : b.AllDeg (fun m => m ≤ 2)) :
    b.ell leaf_exempt_log_g leaf_exempt_log_h (0 : ℝ) (1 : ℝ) + (1 / 5 : ℝ) * b.size ≤ (1 / 10 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := leaf_exempt_log b hn hb
  linarith [leaf_exempt_log_U_le_max _ h1 h2]

/-- The single leaf VIOLATES the uniform bound (`l_leaf + α = 1/5 > 1/10`): no certificate that pools the leaves (and so covers the leaf tree) can prove it; exempting them can. -/
theorem leaf_exempt_log_leaf_breaks : (1 / 10 : ℝ) < (0 : ℝ) + (1 / 5 : ℝ) := by norm_num

end ConcavePooledInductionExt
