/- telperion 0.1.6 | family ConcavePooledInduction | input-hash f93eb2c8c3c4c6e1
   165 theorems, 21 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace ConcavePooledInduction

/-! ## Generic concave pooled induction (emitted once per file)

Method: concave-witness induction, from the draft "The maximum Laplacian ratio of a tree for
all n >= 303: concave witnesses and one-variable certificates" (28 September 2026),
communicated by Professor John L. Goldwasser (author: his London colleague; name to be added).
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

/-! ## Instance `matching_density`

Claim: `ell + (3/5) * size ≤ U (msg)` on every finite rooted tree, for
  h(m, R) = 1/(R + 1),  g(m, R) = -1/(R + 1),
  leaf (y, l) = (1, -1), U the concave interpolant of
  (0, 0), (1/2, -1/8), (1, -3/10).
Certificate: 8 cells (explicit m = 1..2, plus the m-free tail m ≥ 3). -/

noncomputable def matching_density_A : Fin 2 → ℝ := ![(-1 / 4 : ℝ), (-7 / 20 : ℝ)]
noncomputable def matching_density_B : Fin 2 → ℝ := ![(0 : ℝ), (1 / 20 : ℝ)]
/-- The witness: the minimum of its 2 affine pieces. -/
noncomputable def matching_density_U : ℝ → ℝ := minPieces matching_density_A matching_density_B
noncomputable def matching_density_h : ℕ → ℝ → ℝ := fun _ R => ((1 : ℝ)) / ((1 : ℝ) + R)
noncomputable def matching_density_g : ℕ → ℝ → ℝ := fun _ R => ((-1 : ℝ)) / ((1 : ℝ) + R)

theorem matching_density_piece0 (x : ℝ) : matching_density_U x ≤ (-1 / 4 : ℝ) * x + (0 : ℝ) := by
  have := minPieces_le matching_density_A matching_density_B x 0
  simpa [matching_density_U, matching_density_A, matching_density_B] using this

theorem matching_density_piece1 (x : ℝ) : matching_density_U x ≤ (-7 / 20 : ℝ) * x + (1 / 20 : ℝ) := by
  have := minPieces_le matching_density_A matching_density_B x 1
  simpa [matching_density_U, matching_density_A, matching_density_B] using this

theorem matching_density_node0 : matching_density_U (0 : ℝ) = (0 : ℝ) := by
  apply le_antisymm
  · linarith [matching_density_piece0 (0 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [matching_density_A, matching_density_B]

theorem matching_density_node1 : matching_density_U (1 / 2 : ℝ) = (-1 / 8 : ℝ) := by
  apply le_antisymm
  · linarith [matching_density_piece0 (1 / 2 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [matching_density_A, matching_density_B]

theorem matching_density_node2 : matching_density_U (1 : ℝ) = (-3 / 10 : ℝ) := by
  apply le_antisymm
  · linarith [matching_density_piece1 (1 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [matching_density_A, matching_density_B]

theorem matching_density_base : (-1 : ℝ) + (3 / 5 : ℝ) ≤ matching_density_U (1 : ℝ) := by
  apply le_minPieces; intro k; fin_cases k <;> norm_num [matching_density_A, matching_density_B]

theorem matching_density_c0_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + matching_density_g 1 R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c0_k1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + matching_density_g 1 R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 1 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    matching_density_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + matching_density_g 1 R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c0_k0 R h1 h2
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c0_k1 R h1 h2
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c0_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 1 R ∧ matching_density_h 1 R ≤ (1 : ℝ) :=
  ⟨matching_density_c0_lo R h1 h2, matching_density_c0_hi R h1 h2⟩

theorem matching_density_c1_k0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + matching_density_g 1 R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c1_k1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + matching_density_g 1 R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 20 : ℝ) + (-1 / 4 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 20 : ℝ) + (-1 / 4 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c1_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 1 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c1_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    matching_density_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + matching_density_g 1 R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c1_k0 R h1 h2
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c1_k1 R h1 h2
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c1_cl (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 1 R ∧ matching_density_h 1 R ≤ (1 : ℝ) :=
  ⟨matching_density_c1_lo R h1 h2, matching_density_c1_hi R h1 h2⟩

theorem matching_density_c2_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c2_k1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h 2 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c2_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 2 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c2_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    matching_density_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c2 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c2_k0 R h1 h2
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c2_k1 R h1 h2
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c2_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 2 R ∧ matching_density_h 2 R ≤ (1 : ℝ) :=
  ⟨matching_density_c2_lo R h1 h2, matching_density_c2_hi R h1 h2⟩

theorem matching_density_c3_k0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c3_k1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h 2 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c3_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 2 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c3_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    matching_density_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c3 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c3_k0 R h1 h2
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c3_k1 R h1 h2
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c3_cl (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 2 R ∧ matching_density_h 2 R ≤ (1 : ℝ) :=
  ⟨matching_density_c3_lo R h1 h2, matching_density_c3_hi R h1 h2⟩

theorem matching_density_c4_k0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c4_k1 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h 2 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((-3 / 10 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((-3 / 10 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c4_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c4_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    matching_density_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h 2 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c4 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + matching_density_g 2 R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c4_k0 R h1 h2
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c4_k1 R h1 h2
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c4_cl (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 2 R ∧ matching_density_h 2 R ≤ (1 : ℝ) :=
  ⟨matching_density_c4_lo R h1 h2, matching_density_c4_hi R h1 h2⟩

theorem matching_density_c5_k0 (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h m R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c5_k1 (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h m R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c5_lo (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h m R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c5_hi (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    matching_density_h m R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c5 (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h m R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c5_k0 m R h1 h2
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c5_k1 m R h1 h2
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c5_cl (m : ℕ) (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h m R ∧ matching_density_h m R ≤ (1 : ℝ) :=
  ⟨matching_density_c5_lo m R h1 h2, matching_density_c5_hi m R h1 h2⟩

theorem matching_density_c6_k0 (m : ℕ) (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h m R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c6_k1 (m : ℕ) (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h m R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c6_lo (m : ℕ) (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h m R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c6_hi (m : ℕ) (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    matching_density_h m R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c6 (m : ℕ) (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h m R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c6_k0 m R h1 h2
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c6_k1 m R h1 h2
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c6_cl (m : ℕ) (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h m R ∧ matching_density_h m R ≤ (1 : ℝ) :=
  ⟨matching_density_c6_lo m R h1 h2, matching_density_c6_hi m R h1 h2⟩

theorem matching_density_c7_k0 (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * matching_density_h m R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c7_k1 (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * matching_density_h m R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have eg : matching_density_g m R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1, pow_nonneg hs 2]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem matching_density_c7_lo (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (0 : ℝ) ≤ matching_density_h m R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [pow_nonneg hs 0]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c7_hi (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    matching_density_h m R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have hDt' := hDt.ne'
  have eh : matching_density_h m R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [matching_density_h]
  have key : 0 ≤ (R) := by linarith [pow_nonneg hs 0, pow_nonneg hs 1]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem matching_density_c7 (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (-1 / 4 : ℝ) * R + matching_density_g m R + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h m R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := matching_density_c7_k0 m R h1
    simpa [matching_density_A, matching_density_B] using this
  · have := matching_density_c7_k1 m R h1
    simpa [matching_density_A, matching_density_B] using this

theorem matching_density_c7_cl (m : ℕ) (R : ℝ) (h1 : (1 : ℝ) ≤ R) :
    (0 : ℝ) ≤ matching_density_h m R ∧ matching_density_h m R ≤ (1 : ℝ) :=
  ⟨matching_density_c7_lo m R h1, matching_density_c7_hi m R h1⟩

theorem matching_density_step1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((1 : ℕ) : ℝ) * matching_density_U yb + matching_density_g 1 (((1 : ℕ) : ℝ) * yb) + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h 1 (((1 : ℕ) : ℝ) * yb)) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · linarith [matching_density_c0 (1 * yb) (by linarith) h_0, matching_density_piece0 yb]
  · linarith [matching_density_c1 (1 * yb) h_0.le (by linarith), matching_density_piece1 yb]

theorem matching_density_clos1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 1 (((1 : ℕ) : ℝ) * yb) ∧ matching_density_h 1 (((1 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · exact matching_density_c0_cl (1 * yb) (by linarith) h_0
  · exact matching_density_c1_cl (1 * yb) h_0.le (by linarith)

theorem matching_density_step2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((2 : ℕ) : ℝ) * matching_density_U yb + matching_density_g 2 (((2 : ℕ) : ℝ) * yb) + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h 2 (((2 : ℕ) : ℝ) * yb)) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  rcases le_or_gt (2 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · linarith [matching_density_c2 (2 * yb) (by linarith) h_0, matching_density_piece0 yb]
  rcases le_or_gt (2 * yb) (1 : ℝ) with h_1 | h_1
  · linarith [matching_density_c3 (2 * yb) h_0.le h_1, matching_density_piece0 yb]
  · linarith [matching_density_c4 (2 * yb) h_1.le (by linarith), matching_density_piece1 yb]

theorem matching_density_clos2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h 2 (((2 : ℕ) : ℝ) * yb) ∧ matching_density_h 2 (((2 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  rcases le_or_gt (2 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · exact matching_density_c2_cl (2 * yb) (by linarith) h_0
  rcases le_or_gt (2 * yb) (1 : ℝ) with h_1 | h_1
  · exact matching_density_c3_cl (2 * yb) h_0.le h_1
  · exact matching_density_c4_cl (2 * yb) h_1.le (by linarith)

theorem matching_density_tail (m : ℕ) (hm : 2 < m) (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (m : ℝ) * matching_density_U yb + matching_density_g m ((m : ℝ) * yb) + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h m ((m : ℝ) * yb)) := by
  have hm4 : 3 ≤ m := hm
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hR0 : (3 : ℝ) * (0 : ℝ) ≤ (m : ℝ) * yb :=
    mul_le_mul hmr hl (by norm_num) hm0
  have hP0 : (m : ℝ) * matching_density_U yb ≤ (m : ℝ) * ((-1 / 4 : ℝ) * yb + (0 : ℝ)) :=
    mul_le_mul_of_nonneg_left (matching_density_piece0 yb) hm0
  have hM0 : (m : ℝ) * (0 : ℝ) ≤ (3 : ℝ) * (0 : ℝ) :=
    mul_le_mul_of_nonpos_right hmr (by norm_num)
  have hH0 : 0 ≤ (m : ℝ) * (-(0 : ℝ)) * ((1 : ℝ) - yb) :=
    mul_nonneg (mul_nonneg hm0 (by norm_num)) (by linarith)
  rcases le_or_gt ((m : ℝ) * yb) (1 / 2 : ℝ) with h_0 | h_0
  · linarith [matching_density_c5 m ((m : ℝ) * yb) (by linarith) h_0, hP0, hM0, hH0]
  rcases le_or_gt ((m : ℝ) * yb) (1 : ℝ) with h_1 | h_1
  · linarith [matching_density_c6 m ((m : ℝ) * yb) h_0.le h_1, hP0, hM0, hH0]
  · linarith [matching_density_c7 m ((m : ℝ) * yb) h_1.le, hP0, hM0, hH0]

set_option linter.unusedVariables false in
theorem matching_density_tail_clos (m : ℕ) (hm : 2 < m) (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ matching_density_h m ((m : ℝ) * yb) ∧ matching_density_h m ((m : ℝ) * yb) ≤ (1 : ℝ) := by
  have hm4 : 3 ≤ m := hm
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hR0 : (3 : ℝ) * (0 : ℝ) ≤ (m : ℝ) * yb :=
    mul_le_mul hmr hl (by norm_num) hm0
  rcases le_or_gt ((m : ℝ) * yb) (1 / 2 : ℝ) with h_0 | h_0
  · exact matching_density_c5_cl m ((m : ℝ) * yb) (by linarith) h_0
  rcases le_or_gt ((m : ℝ) * yb) (1 : ℝ) with h_1 | h_1
  · exact matching_density_c6_cl m ((m : ℝ) * yb) h_0.le h_1
  · exact matching_density_c7_cl m ((m : ℝ) * yb) h_1.le

theorem matching_density_hstep : ∀ m : ℕ, 1 ≤ m → True → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (m : ℝ) * matching_density_U yb + matching_density_g m (m * yb) + (3 / 5 : ℝ) ≤ matching_density_U (matching_density_h m (m * yb)) := by
  intro m hm hok yb hl hu
  rcases Nat.lt_or_ge 2 m with hM | hM
  · exact matching_density_tail m hM yb hl hu
  · interval_cases m
    · exact matching_density_step1 yb hl hu
    · exact matching_density_step2 yb hl hu

theorem matching_density_hclos : ∀ m : ℕ, 1 ≤ m → True → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (0 : ℝ) ≤ matching_density_h m (m * yb) ∧ matching_density_h m (m * yb) ≤ (1 : ℝ) := by
  intro m hm hok yb hl hu
  rcases Nat.lt_or_ge 2 m with hM | hM
  · exact matching_density_tail_clos m hM yb hl hu
  · interval_cases m
    · exact matching_density_clos1 yb hl hu
    · exact matching_density_clos2 yb hl hu

set_option linter.unusedVariables false in
theorem matching_density_U_le_max (x : ℝ) (hl : (0 : ℝ) ≤ x) (hu : x ≤ (1 : ℝ)) : matching_density_U x ≤ (0 : ℝ) := by
  rcases le_or_gt x (1 / 2 : ℝ) with h_0 | h_0
  · linarith [matching_density_piece0 x]
  · linarith [matching_density_piece1 x]

/-- MAIN.  The certified bound on every finite rooted tree. -/
theorem matching_density (b : PTree) :
    (0 : ℝ) ≤ b.msg matching_density_h (1 : ℝ) ∧ b.msg matching_density_h (1 : ℝ) ≤ (1 : ℝ) ∧
      b.ell matching_density_g matching_density_h (-1 : ℝ) (1 : ℝ) + (3 / 5 : ℝ) * b.size ≤ matching_density_U (b.msg matching_density_h (1 : ℝ)) :=
  pooled_induction_core (fun _ => True) matching_density_h matching_density_g matching_density_U matching_density_U (1 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (3 / 5 : ℝ)
    (minPieces_jensen matching_density_A matching_density_B) (fun _ _ _ => le_rfl) ⟨by norm_num, by norm_num⟩ matching_density_base matching_density_hclos matching_density_hstep b (PTree.allDeg_true b)

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 0`. -/
theorem matching_density_uniform (b : PTree) :
    b.ell matching_density_g matching_density_h (-1 : ℝ) (1 : ℝ) + (3 / 5 : ℝ) * b.size ≤ (0 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := matching_density b
  linarith [matching_density_U_le_max _ h1 h2]

/-! ## Instance `path_density`

Claim: `ell + (3/5) * size ≤ U (msg)` on every finite rooted tree of child count at most 1, for
  h(m, R) = 1/(R + 1),  g(m, R) = -1/(R + 1),
  leaf (y, l) = (1, -1), U the concave interpolant of
  (0, 0), (1/2, -1/8), (1, -3/10).
Certificate: 2 cells (explicit m = 1..1). -/

noncomputable def path_density_A : Fin 2 → ℝ := ![(-1 / 4 : ℝ), (-7 / 20 : ℝ)]
noncomputable def path_density_B : Fin 2 → ℝ := ![(0 : ℝ), (1 / 20 : ℝ)]
/-- The witness: the minimum of its 2 affine pieces. -/
noncomputable def path_density_U : ℝ → ℝ := minPieces path_density_A path_density_B
noncomputable def path_density_h : ℕ → ℝ → ℝ := fun _ R => ((1 : ℝ)) / ((1 : ℝ) + R)
noncomputable def path_density_g : ℕ → ℝ → ℝ := fun _ R => ((-1 : ℝ)) / ((1 : ℝ) + R)

theorem path_density_piece0 (x : ℝ) : path_density_U x ≤ (-1 / 4 : ℝ) * x + (0 : ℝ) := by
  have := minPieces_le path_density_A path_density_B x 0
  simpa [path_density_U, path_density_A, path_density_B] using this

theorem path_density_piece1 (x : ℝ) : path_density_U x ≤ (-7 / 20 : ℝ) * x + (1 / 20 : ℝ) := by
  have := minPieces_le path_density_A path_density_B x 1
  simpa [path_density_U, path_density_A, path_density_B] using this

theorem path_density_node0 : path_density_U (0 : ℝ) = (0 : ℝ) := by
  apply le_antisymm
  · linarith [path_density_piece0 (0 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [path_density_A, path_density_B]

theorem path_density_node1 : path_density_U (1 / 2 : ℝ) = (-1 / 8 : ℝ) := by
  apply le_antisymm
  · linarith [path_density_piece0 (1 / 2 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [path_density_A, path_density_B]

theorem path_density_node2 : path_density_U (1 : ℝ) = (-3 / 10 : ℝ) := by
  apply le_antisymm
  · linarith [path_density_piece1 (1 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [path_density_A, path_density_B]

theorem path_density_base : (-1 : ℝ) + (3 / 5 : ℝ) ≤ path_density_U (1 : ℝ) := by
  apply le_minPieces; intro k; fin_cases k <;> norm_num [path_density_A, path_density_B]

theorem path_density_c0_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + path_density_g 1 R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * path_density_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have eg : path_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((3 / 20 : ℝ) + (-7 / 20 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem path_density_c0_k1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + path_density_g 1 R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * path_density_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have eg : path_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (1 / 4 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem path_density_c0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ path_density_h 1 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem path_density_c0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    path_density_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem path_density_c0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + path_density_g 1 R + (3 / 5 : ℝ) ≤ path_density_U (path_density_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := path_density_c0_k0 R h1 h2
    simpa [path_density_A, path_density_B] using this
  · have := path_density_c0_k1 R h1 h2
    simpa [path_density_A, path_density_B] using this

theorem path_density_c0_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ path_density_h 1 R ∧ path_density_h 1 R ≤ (1 : ℝ) :=
  ⟨path_density_c0_lo R h1 h2, path_density_c0_hi R h1 h2⟩

theorem path_density_c1_k0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + path_density_g 1 R + (3 / 5 : ℝ) ≤ (-1 / 4 : ℝ) * path_density_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have eg : path_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_g]
  have key : 0 ≤ ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (0 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 10 : ℝ) + (-3 / 10 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem path_density_c1_k1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + path_density_g 1 R + (3 / 5 : ℝ) ≤ (-7 / 20 : ℝ) * path_density_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have eg : path_density_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_g]
  have key : 0 ≤ ((1 / 20 : ℝ) + (-1 / 4 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 20 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (3 / 5 : ℝ)) = ((1 / 20 : ℝ) + (-1 / 4 : ℝ) * R + (7 / 20 : ℝ) * R ^ 2) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem path_density_c1_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ path_density_h 1 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have key : 0 ≤ ((1 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + R))) - ((0 : ℝ)) = ((1 : ℝ)) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem path_density_c1_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    path_density_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hDt : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : path_density_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [path_density_h]
  have key : 0 ≤ (R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + R))) = (R) / ((1 : ℝ) + R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem path_density_c1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + path_density_g 1 R + (3 / 5 : ℝ) ≤ path_density_U (path_density_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := path_density_c1_k0 R h1 h2
    simpa [path_density_A, path_density_B] using this
  · have := path_density_c1_k1 R h1 h2
    simpa [path_density_A, path_density_B] using this

theorem path_density_c1_cl (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ path_density_h 1 R ∧ path_density_h 1 R ≤ (1 : ℝ) :=
  ⟨path_density_c1_lo R h1 h2, path_density_c1_hi R h1 h2⟩

theorem path_density_step1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((1 : ℕ) : ℝ) * path_density_U yb + path_density_g 1 (((1 : ℕ) : ℝ) * yb) + (3 / 5 : ℝ) ≤ path_density_U (path_density_h 1 (((1 : ℕ) : ℝ) * yb)) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · linarith [path_density_c0 (1 * yb) (by linarith) h_0, path_density_piece0 yb]
  · linarith [path_density_c1 (1 * yb) h_0.le (by linarith), path_density_piece1 yb]

theorem path_density_clos1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ path_density_h 1 (((1 : ℕ) : ℝ) * yb) ∧ path_density_h 1 (((1 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · exact path_density_c0_cl (1 * yb) (by linarith) h_0
  · exact path_density_c1_cl (1 * yb) h_0.le (by linarith)

theorem path_density_hstep : ∀ m : ℕ, 1 ≤ m → m ≤ 1 → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (m : ℝ) * path_density_U yb + path_density_g m (m * yb) + (3 / 5 : ℝ) ≤ path_density_U (path_density_h m (m * yb)) := by
  intro m hm hok yb hl hu
  interval_cases m
  · exact path_density_step1 yb hl hu

theorem path_density_hclos : ∀ m : ℕ, 1 ≤ m → m ≤ 1 → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (0 : ℝ) ≤ path_density_h m (m * yb) ∧ path_density_h m (m * yb) ≤ (1 : ℝ) := by
  intro m hm hok yb hl hu
  interval_cases m
  · exact path_density_clos1 yb hl hu

set_option linter.unusedVariables false in
theorem path_density_U_le_max (x : ℝ) (hl : (0 : ℝ) ≤ x) (hu : x ≤ (1 : ℝ)) : path_density_U x ≤ (0 : ℝ) := by
  rcases le_or_gt x (1 / 2 : ℝ) with h_0 | h_0
  · linarith [path_density_piece0 x]
  · linarith [path_density_piece1 x]

/-- MAIN.  The certified bound on every tree of child count at most 1. -/
theorem path_density (b : PTree) (hb : b.AllDeg (fun m => m ≤ 1)) :
    (0 : ℝ) ≤ b.msg path_density_h (1 : ℝ) ∧ b.msg path_density_h (1 : ℝ) ≤ (1 : ℝ) ∧
      b.ell path_density_g path_density_h (-1 : ℝ) (1 : ℝ) + (3 / 5 : ℝ) * b.size ≤ path_density_U (b.msg path_density_h (1 : ℝ)) :=
  pooled_induction_core (fun m => m ≤ 1) path_density_h path_density_g path_density_U path_density_U (1 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (3 / 5 : ℝ)
    (minPieces_jensen path_density_A path_density_B) (fun _ _ _ => le_rfl) ⟨by norm_num, by norm_num⟩ path_density_base path_density_hclos path_density_hstep b hb

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 0`. -/
theorem path_density_uniform (b : PTree) (hb : b.AllDeg (fun m => m ≤ 1)) :
    b.ell path_density_g path_density_h (-1 : ℝ) (1 : ℝ) + (3 / 5 : ℝ) * b.size ≤ (0 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := path_density b hb
  linarith [path_density_U_le_max _ h1 h2]

/-! ## Instance `synthetic_mdep`

Claim: `ell + (1/2) * size ≤ U (msg)` on every finite rooted tree of child count at most 2, for
  h(m, R) = m/(2*R + m),  g(m, R) = -1/(R + 1),
  leaf (y, l) = (1, -1), U the concave interpolant of
  (0, 0), (1/2, -1/8), (1, -3/10).
Certificate: 4 cells (explicit m = 1..2). -/

noncomputable def synthetic_mdep_A : Fin 2 → ℝ := ![(-1 / 4 : ℝ), (-7 / 20 : ℝ)]
noncomputable def synthetic_mdep_B : Fin 2 → ℝ := ![(0 : ℝ), (1 / 20 : ℝ)]
/-- The witness: the minimum of its 2 affine pieces. -/
noncomputable def synthetic_mdep_U : ℝ → ℝ := minPieces synthetic_mdep_A synthetic_mdep_B
noncomputable def synthetic_mdep_h : ℕ → ℝ → ℝ := fun m R => ((m : ℝ)) / ((2 : ℝ) * R + (m : ℝ))
noncomputable def synthetic_mdep_g : ℕ → ℝ → ℝ := fun _ R => ((-1 : ℝ)) / ((1 : ℝ) + R)

theorem synthetic_mdep_piece0 (x : ℝ) : synthetic_mdep_U x ≤ (-1 / 4 : ℝ) * x + (0 : ℝ) := by
  have := minPieces_le synthetic_mdep_A synthetic_mdep_B x 0
  simpa [synthetic_mdep_U, synthetic_mdep_A, synthetic_mdep_B] using this

theorem synthetic_mdep_piece1 (x : ℝ) : synthetic_mdep_U x ≤ (-7 / 20 : ℝ) * x + (1 / 20 : ℝ) := by
  have := minPieces_le synthetic_mdep_A synthetic_mdep_B x 1
  simpa [synthetic_mdep_U, synthetic_mdep_A, synthetic_mdep_B] using this

theorem synthetic_mdep_node0 : synthetic_mdep_U (0 : ℝ) = (0 : ℝ) := by
  apply le_antisymm
  · linarith [synthetic_mdep_piece0 (0 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [synthetic_mdep_A, synthetic_mdep_B]

theorem synthetic_mdep_node1 : synthetic_mdep_U (1 / 2 : ℝ) = (-1 / 8 : ℝ) := by
  apply le_antisymm
  · linarith [synthetic_mdep_piece0 (1 / 2 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [synthetic_mdep_A, synthetic_mdep_B]

theorem synthetic_mdep_node2 : synthetic_mdep_U (1 : ℝ) = (-3 / 10 : ℝ) := by
  apply le_antisymm
  · linarith [synthetic_mdep_piece1 (1 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k <;> norm_num [synthetic_mdep_A, synthetic_mdep_B]

theorem synthetic_mdep_base : (-1 : ℝ) + (1 / 2 : ℝ) ≤ synthetic_mdep_U (1 : ℝ) := by
  apply le_minPieces; intro k; fin_cases k <;> norm_num [synthetic_mdep_A, synthetic_mdep_B]

theorem synthetic_mdep_c0_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + synthetic_mdep_g 1 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * synthetic_mdep_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((1 / 4 : ℝ) + (1 / 2 : ℝ) * R + (-1 / 4 : ℝ) * R ^ 2 + (1 / 2 : ℝ) * R ^ 3) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 3), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 3) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((1 / 4 : ℝ) + (1 / 2 : ℝ) * R + (-1 / 4 : ℝ) * R ^ 2 + (1 / 2 : ℝ) * R ^ 3) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c0_k1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + synthetic_mdep_g 1 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * synthetic_mdep_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((1 / 5 : ℝ) + (11 / 20 : ℝ) * R + (-3 / 20 : ℝ) * R ^ 2 + (1 / 2 : ℝ) * R ^ 3) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 3), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 3) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((1 / 5 : ℝ) + (11 / 20 : ℝ) * R + (-3 / 20 : ℝ) * R ^ 2 + (1 / 2 : ℝ) * R ^ 3) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 1 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R))) - ((0 : ℝ)) = ((1 : ℝ) + R) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    synthetic_mdep_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 / 2 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((2 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R))) = ((2 : ℝ) * R + (2 : ℝ) * R ^ 2) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (-1 / 4 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + synthetic_mdep_g 1 R + (1 / 2 : ℝ) ≤ synthetic_mdep_U (synthetic_mdep_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := synthetic_mdep_c0_k0 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this
  · have := synthetic_mdep_c0_k1 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this

theorem synthetic_mdep_c0_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 1 R ∧ synthetic_mdep_h 1 R ≤ (1 : ℝ) :=
  ⟨synthetic_mdep_c0_lo R h1 h2, synthetic_mdep_c0_hi R h1 h2⟩

theorem synthetic_mdep_c1_k0 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + synthetic_mdep_g 1 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * synthetic_mdep_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((1 / 5 : ℝ) + (9 / 20 : ℝ) * R + (-1 / 20 : ℝ) * R ^ 2 + (7 / 10 : ℝ) * R ^ 3) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 3), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 3) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) + (0 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((1 / 5 : ℝ) + (9 / 20 : ℝ) * R + (-1 / 20 : ℝ) * R ^ 2 + (7 / 10 : ℝ) * R ^ 3) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c1_k1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + synthetic_mdep_g 1 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * synthetic_mdep_h 1 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 1 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((3 / 20 : ℝ) + (1 / 2 : ℝ) * R + (1 / 20 : ℝ) * R ^ 2 + (7 / 10 : ℝ) * R ^ 3) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 3), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 3) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) + (1 / 20 : ℝ)) - ((-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((3 / 20 : ℝ) + (1 / 2 : ℝ) * R + (1 / 20 : ℝ) * R ^ 2 + (7 / 10 : ℝ) * R ^ 3) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c1_lo (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 1 R := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R))) - ((0 : ℝ)) = ((1 : ℝ) + R) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c1_hi (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synthetic_mdep_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 / 2 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD0 : 0 < ((1 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 1 R = (((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((2 : ℝ) * R + (2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 : ℝ)) / ((1 : ℝ) + (2 : ℝ) * R))) = ((2 : ℝ) * R + (2 : ℝ) * R ^ 2) / ((1 : ℝ) + (3 : ℝ) * R + (2 : ℝ) * R ^ 2) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c1 (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-7 / 20 : ℝ) * R + (1 : ℝ) * (1 / 20 : ℝ) + synthetic_mdep_g 1 R + (1 / 2 : ℝ) ≤ synthetic_mdep_U (synthetic_mdep_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := synthetic_mdep_c1_k0 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this
  · have := synthetic_mdep_c1_k1 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this

theorem synthetic_mdep_c1_cl (R : ℝ) (h1 : (1 / 2 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 1 R ∧ synthetic_mdep_h 1 R ≤ (1 : ℝ) :=
  ⟨synthetic_mdep_c1_lo R h1 h2, synthetic_mdep_c1_hi R h1 h2⟩

theorem synthetic_mdep_c2_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + synthetic_mdep_g 2 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * synthetic_mdep_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R + (1 / 2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) + (0 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((1 / 2 : ℝ) + (-1 / 2 : ℝ) * R + (1 / 2 : ℝ) * R ^ 2) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c2_k1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + synthetic_mdep_g 2 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * synthetic_mdep_h 2 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((2 / 5 : ℝ) + (-2 / 5 : ℝ) * R + (1 / 2 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) + (1 / 20 : ℝ)) - ((-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((2 / 5 : ℝ) + (-2 / 5 : ℝ) * R + (1 / 2 : ℝ) * R ^ 2) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c2_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 2 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((2 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R))) - ((0 : ℝ)) = ((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c2_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synthetic_mdep_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R))) = ((2 : ℝ) * R) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c2 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (-1 / 4 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + synthetic_mdep_g 2 R + (1 / 2 : ℝ) ≤ synthetic_mdep_U (synthetic_mdep_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := synthetic_mdep_c2_k0 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this
  · have := synthetic_mdep_c2_k1 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this

theorem synthetic_mdep_c2_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 2 R ∧ synthetic_mdep_h 2 R ≤ (1 : ℝ) :=
  ⟨synthetic_mdep_c2_lo R h1 h2, synthetic_mdep_c2_hi R h1 h2⟩

theorem synthetic_mdep_c3_k0 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + synthetic_mdep_g 2 R + (1 / 2 : ℝ) ≤ (-1 / 4 : ℝ) * synthetic_mdep_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((3 / 10 : ℝ) + (-1 / 2 : ℝ) * R + (7 / 10 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-1 / 4 : ℝ) * (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) + (0 : ℝ)) - ((-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((3 / 10 : ℝ) + (-1 / 2 : ℝ) * R + (7 / 10 : ℝ) * R ^ 2) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c3_k1 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + synthetic_mdep_g 2 R + (1 / 2 : ℝ) ≤ (-7 / 20 : ℝ) * synthetic_mdep_h 2 R + (1 / 20 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have eg : synthetic_mdep_g 2 R = (((-1 : ℝ)) / ((1 : ℝ) + R)) := by simp only [synthetic_mdep_g]
  have key : 0 ≤ ((1 / 5 : ℝ) + (-2 / 5 : ℝ) * R + (7 / 10 : ℝ) * R ^ 2) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]
  have e : ((-7 / 20 : ℝ) * (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) + (1 / 20 : ℝ)) - ((-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + (((-1 : ℝ)) / ((1 : ℝ) + R)) + (1 / 2 : ℝ)) = ((1 / 5 : ℝ) + (-2 / 5 : ℝ) * R + (7 / 10 : ℝ) * R ^ 2) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh, eg]
  linarith

theorem synthetic_mdep_c3_lo (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 2 R := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((2 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R))) - ((0 : ℝ)) = ((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c3_hi (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synthetic_mdep_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (1 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have hD1 : 0 < ((1 : ℝ) + R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt : 0 < ((2 : ℝ) + (2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have hDt' := hDt.ne'
  have eh : synthetic_mdep_h 2 R = (((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R)) := by simp only [synthetic_mdep_h]; ring
  have key : 0 ≤ ((2 : ℝ) * R) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((2 : ℝ)) / ((2 : ℝ) + (2 : ℝ) * R))) = ((2 : ℝ) * R) / ((2 : ℝ) + (2 : ℝ) * R) := by
    field_simp
    ring
  have hq := div_nonneg key hDt.le
  rw [eh]
  linarith

theorem synthetic_mdep_c3 (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (-7 / 20 : ℝ) * R + (2 : ℝ) * (1 / 20 : ℝ) + synthetic_mdep_g 2 R + (1 / 2 : ℝ) ≤ synthetic_mdep_U (synthetic_mdep_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := synthetic_mdep_c3_k0 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this
  · have := synthetic_mdep_c3_k1 R h1 h2
    simpa [synthetic_mdep_A, synthetic_mdep_B] using this

theorem synthetic_mdep_c3_cl (R : ℝ) (h1 : (1 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 2 R ∧ synthetic_mdep_h 2 R ≤ (1 : ℝ) :=
  ⟨synthetic_mdep_c3_lo R h1 h2, synthetic_mdep_c3_hi R h1 h2⟩

theorem synthetic_mdep_step1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((1 : ℕ) : ℝ) * synthetic_mdep_U yb + synthetic_mdep_g 1 (((1 : ℕ) : ℝ) * yb) + (1 / 2 : ℝ) ≤ synthetic_mdep_U (synthetic_mdep_h 1 (((1 : ℕ) : ℝ) * yb)) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · linarith [synthetic_mdep_c0 (1 * yb) (by linarith) h_0, synthetic_mdep_piece0 yb]
  · linarith [synthetic_mdep_c1 (1 * yb) h_0.le (by linarith), synthetic_mdep_piece1 yb]

theorem synthetic_mdep_clos1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 1 (((1 : ℕ) : ℝ) * yb) ∧ synthetic_mdep_h 1 (((1 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  rcases le_or_gt (1 * yb) (1 / 2 : ℝ) with h_0 | h_0
  · exact synthetic_mdep_c0_cl (1 * yb) (by linarith) h_0
  · exact synthetic_mdep_c1_cl (1 * yb) h_0.le (by linarith)

theorem synthetic_mdep_step2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((2 : ℕ) : ℝ) * synthetic_mdep_U yb + synthetic_mdep_g 2 (((2 : ℕ) : ℝ) * yb) + (1 / 2 : ℝ) ≤ synthetic_mdep_U (synthetic_mdep_h 2 (((2 : ℕ) : ℝ) * yb)) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  rcases le_or_gt (2 * yb) (1 : ℝ) with h_0 | h_0
  · linarith [synthetic_mdep_c2 (2 * yb) (by linarith) h_0, synthetic_mdep_piece0 yb]
  · linarith [synthetic_mdep_c3 (2 * yb) h_0.le (by linarith), synthetic_mdep_piece1 yb]

theorem synthetic_mdep_clos2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_mdep_h 2 (((2 : ℕ) : ℝ) * yb) ∧ synthetic_mdep_h 2 (((2 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  rcases le_or_gt (2 * yb) (1 : ℝ) with h_0 | h_0
  · exact synthetic_mdep_c2_cl (2 * yb) (by linarith) h_0
  · exact synthetic_mdep_c3_cl (2 * yb) h_0.le (by linarith)

theorem synthetic_mdep_hstep : ∀ m : ℕ, 1 ≤ m → m ≤ 2 → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (m : ℝ) * synthetic_mdep_U yb + synthetic_mdep_g m (m * yb) + (1 / 2 : ℝ) ≤ synthetic_mdep_U (synthetic_mdep_h m (m * yb)) := by
  intro m hm hok yb hl hu
  interval_cases m
  · exact synthetic_mdep_step1 yb hl hu
  · exact synthetic_mdep_step2 yb hl hu

theorem synthetic_mdep_hclos : ∀ m : ℕ, 1 ≤ m → m ≤ 2 → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (0 : ℝ) ≤ synthetic_mdep_h m (m * yb) ∧ synthetic_mdep_h m (m * yb) ≤ (1 : ℝ) := by
  intro m hm hok yb hl hu
  interval_cases m
  · exact synthetic_mdep_clos1 yb hl hu
  · exact synthetic_mdep_clos2 yb hl hu

set_option linter.unusedVariables false in
theorem synthetic_mdep_U_le_max (x : ℝ) (hl : (0 : ℝ) ≤ x) (hu : x ≤ (1 : ℝ)) : synthetic_mdep_U x ≤ (0 : ℝ) := by
  rcases le_or_gt x (1 / 2 : ℝ) with h_0 | h_0
  · linarith [synthetic_mdep_piece0 x]
  · linarith [synthetic_mdep_piece1 x]

/-- MAIN.  The certified bound on every tree of child count at most 2. -/
theorem synthetic_mdep (b : PTree) (hb : b.AllDeg (fun m => m ≤ 2)) :
    (0 : ℝ) ≤ b.msg synthetic_mdep_h (1 : ℝ) ∧ b.msg synthetic_mdep_h (1 : ℝ) ≤ (1 : ℝ) ∧
      b.ell synthetic_mdep_g synthetic_mdep_h (-1 : ℝ) (1 : ℝ) + (1 / 2 : ℝ) * b.size ≤ synthetic_mdep_U (b.msg synthetic_mdep_h (1 : ℝ)) :=
  pooled_induction_core (fun m => m ≤ 2) synthetic_mdep_h synthetic_mdep_g synthetic_mdep_U synthetic_mdep_U (1 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1 / 2 : ℝ)
    (minPieces_jensen synthetic_mdep_A synthetic_mdep_B) (fun _ _ _ => le_rfl) ⟨by norm_num, by norm_num⟩ synthetic_mdep_base synthetic_mdep_hclos synthetic_mdep_hstep b hb

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 0`. -/
theorem synthetic_mdep_uniform (b : PTree) (hb : b.AllDeg (fun m => m ≤ 2)) :
    b.ell synthetic_mdep_g synthetic_mdep_h (-1 : ℝ) (1 : ℝ) + (1 / 2 : ℝ) * b.size ≤ (0 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := synthetic_mdep b hb
  linarith [synthetic_mdep_U_le_max _ h1 h2]

/-! ## Instance `synthetic_edge`

Claim: `ell + (1) * size ≤ U (msg)` on every finite rooted tree of child count at most 3, for
  h(m, R) = 1/(m + 1),  g(m, R) = -1,
  leaf (y, l) = (1, -1), U the concave interpolant of
  (0, 0), (1, 0).
Certificate: 3 cells (explicit m = 1..3). -/

noncomputable def synthetic_edge_A : Fin 1 → ℝ := ![(0 : ℝ)]
noncomputable def synthetic_edge_B : Fin 1 → ℝ := ![(0 : ℝ)]
/-- The witness: the minimum of its 1 affine pieces. -/
noncomputable def synthetic_edge_U : ℝ → ℝ := minPieces synthetic_edge_A synthetic_edge_B
noncomputable def synthetic_edge_h : ℕ → ℝ → ℝ := fun m _ => ((1 : ℝ)) / ((1 : ℝ) + (m : ℝ))
noncomputable def synthetic_edge_g : ℕ → ℝ → ℝ := fun _ _ => ((-1 : ℝ))

theorem synthetic_edge_piece0 (x : ℝ) : synthetic_edge_U x ≤ (0 : ℝ) * x + (0 : ℝ) := by
  have := minPieces_le synthetic_edge_A synthetic_edge_B x 0
  simpa [synthetic_edge_U, synthetic_edge_A, synthetic_edge_B] using this

theorem synthetic_edge_node0 : synthetic_edge_U (0 : ℝ) = (0 : ℝ) := by
  apply le_antisymm
  · linarith [synthetic_edge_piece0 (0 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k ; norm_num [synthetic_edge_A, synthetic_edge_B]

theorem synthetic_edge_node1 : synthetic_edge_U (1 : ℝ) = (0 : ℝ) := by
  apply le_antisymm
  · linarith [synthetic_edge_piece0 (1 : ℝ)]
  · apply le_minPieces; intro k; fin_cases k ; norm_num [synthetic_edge_A, synthetic_edge_B]

theorem synthetic_edge_base : (-1 : ℝ) + (1 : ℝ) ≤ synthetic_edge_U (1 : ℝ) := by
  apply le_minPieces; intro k; fin_cases k ; norm_num [synthetic_edge_A, synthetic_edge_B]

theorem synthetic_edge_c0_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + synthetic_edge_g 1 R + (1 : ℝ) ≤ (0 : ℝ) * synthetic_edge_h 1 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 1 R = (((1 / 2 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have eg : synthetic_edge_g 1 R = (((-1 : ℝ))) := by simp only [synthetic_edge_g]
  have key : 0 ≤ ((0 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 / 2 : ℝ))) + (0 : ℝ)) - ((0 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + (((-1 : ℝ))) + (1 : ℝ)) = ((0 : ℝ)) := by ring
  rw [eh, eg] <;> linarith

theorem synthetic_edge_c0_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 1 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 1 R = (((1 / 2 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have key : 0 ≤ ((1 / 2 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 / 2 : ℝ)))) - ((0 : ℝ)) = ((1 / 2 : ℝ)) := by ring
  rw [eh]
  linarith

theorem synthetic_edge_c0_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    synthetic_edge_h 1 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (1 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 1 R = (((1 / 2 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have key : 0 ≤ ((1 / 2 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 / 2 : ℝ)))) = ((1 / 2 : ℝ)) := by ring
  rw [eh]
  linarith

theorem synthetic_edge_c0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) * R + (1 : ℝ) * (0 : ℝ) + synthetic_edge_g 1 R + (1 : ℝ) ≤ synthetic_edge_U (synthetic_edge_h 1 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := synthetic_edge_c0_k0 R h1 h2
    simpa [synthetic_edge_A, synthetic_edge_B] using this

theorem synthetic_edge_c0_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 1 R ∧ synthetic_edge_h 1 R ≤ (1 : ℝ) :=
  ⟨synthetic_edge_c0_lo R h1 h2, synthetic_edge_c0_hi R h1 h2⟩

theorem synthetic_edge_c1_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + synthetic_edge_g 2 R + (1 : ℝ) ≤ (0 : ℝ) * synthetic_edge_h 2 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 2 R = (((1 / 3 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have eg : synthetic_edge_g 2 R = (((-1 : ℝ))) := by simp only [synthetic_edge_g]
  have key : 0 ≤ ((0 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 / 3 : ℝ))) + (0 : ℝ)) - ((0 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + (((-1 : ℝ))) + (1 : ℝ)) = ((0 : ℝ)) := by ring
  rw [eh, eg] <;> linarith

theorem synthetic_edge_c1_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 2 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 2 R = (((1 / 3 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have key : 0 ≤ ((1 / 3 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 / 3 : ℝ)))) - ((0 : ℝ)) = ((1 / 3 : ℝ)) := by ring
  rw [eh]
  linarith

theorem synthetic_edge_c1_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    synthetic_edge_h 2 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (2 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 2 R = (((1 / 3 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have key : 0 ≤ ((2 / 3 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 / 3 : ℝ)))) = ((2 / 3 : ℝ)) := by ring
  rw [eh]
  linarith

theorem synthetic_edge_c1 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) * R + (2 : ℝ) * (0 : ℝ) + synthetic_edge_g 2 R + (1 : ℝ) ≤ synthetic_edge_U (synthetic_edge_h 2 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := synthetic_edge_c1_k0 R h1 h2
    simpa [synthetic_edge_A, synthetic_edge_B] using this

theorem synthetic_edge_c1_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (2 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 2 R ∧ synthetic_edge_h 2 R ≤ (1 : ℝ) :=
  ⟨synthetic_edge_c1_lo R h1 h2, synthetic_edge_c1_hi R h1 h2⟩

theorem synthetic_edge_c2_k0 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (0 : ℝ) * R + (3 : ℝ) * (0 : ℝ) + synthetic_edge_g 3 R + (1 : ℝ) ≤ (0 : ℝ) * synthetic_edge_h 3 R + (0 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (3 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 3 R = (((1 / 4 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have eg : synthetic_edge_g 3 R = (((-1 : ℝ))) := by simp only [synthetic_edge_g]
  have key : 0 ≤ ((0 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((0 : ℝ) * (((1 / 4 : ℝ))) + (0 : ℝ)) - ((0 : ℝ) * R + (3 : ℝ) * (0 : ℝ) + (((-1 : ℝ))) + (1 : ℝ)) = ((0 : ℝ)) := by ring
  rw [eh, eg] <;> linarith

theorem synthetic_edge_c2_lo (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 3 R := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (3 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 3 R = (((1 / 4 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have key : 0 ≤ ((1 / 4 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((((1 / 4 : ℝ)))) - ((0 : ℝ)) = ((1 / 4 : ℝ)) := by ring
  rw [eh]
  linarith

theorem synthetic_edge_c2_hi (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    synthetic_edge_h 3 R ≤ (1 : ℝ) := by
  have hs : 0 ≤ R - (0 : ℝ) := by linarith
  have ht : 0 ≤ (3 : ℝ) - R := by linarith
  have eh : synthetic_edge_h 3 R = (((1 / 4 : ℝ))) := by simp only [synthetic_edge_h]; ring
  have key : 0 ≤ ((3 / 4 : ℝ)) := by linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]
  have e : ((1 : ℝ)) - ((((1 / 4 : ℝ)))) = ((3 / 4 : ℝ)) := by ring
  rw [eh]
  linarith

theorem synthetic_edge_c2 (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (0 : ℝ) * R + (3 : ℝ) * (0 : ℝ) + synthetic_edge_g 3 R + (1 : ℝ) ≤ synthetic_edge_U (synthetic_edge_h 3 R) := by
  apply le_minPieces; intro k; fin_cases k
  · have := synthetic_edge_c2_k0 R h1 h2
    simpa [synthetic_edge_A, synthetic_edge_B] using this

theorem synthetic_edge_c2_cl (R : ℝ) (h1 : (0 : ℝ) ≤ R) (h2 : R ≤ (3 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 3 R ∧ synthetic_edge_h 3 R ≤ (1 : ℝ) :=
  ⟨synthetic_edge_c2_lo R h1 h2, synthetic_edge_c2_hi R h1 h2⟩

theorem synthetic_edge_step1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((1 : ℕ) : ℝ) * synthetic_edge_U yb + synthetic_edge_g 1 (((1 : ℕ) : ℝ) * yb) + (1 : ℝ) ≤ synthetic_edge_U (synthetic_edge_h 1 (((1 : ℕ) : ℝ) * yb)) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  · linarith [synthetic_edge_c0 (1 * yb) (by linarith) (by linarith), synthetic_edge_piece0 yb]

theorem synthetic_edge_clos1 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 1 (((1 : ℕ) : ℝ) * yb) ∧ synthetic_edge_h 1 (((1 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
  · exact synthetic_edge_c0_cl (1 * yb) (by linarith) (by linarith)

theorem synthetic_edge_step2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((2 : ℕ) : ℝ) * synthetic_edge_U yb + synthetic_edge_g 2 (((2 : ℕ) : ℝ) * yb) + (1 : ℝ) ≤ synthetic_edge_U (synthetic_edge_h 2 (((2 : ℕ) : ℝ) * yb)) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  · linarith [synthetic_edge_c1 (2 * yb) (by linarith) (by linarith), synthetic_edge_piece0 yb]

theorem synthetic_edge_clos2 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 2 (((2 : ℕ) : ℝ) * yb) ∧ synthetic_edge_h 2 (((2 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
  · exact synthetic_edge_c1_cl (2 * yb) (by linarith) (by linarith)

theorem synthetic_edge_step3 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    ((3 : ℕ) : ℝ) * synthetic_edge_U yb + synthetic_edge_g 3 (((3 : ℕ) : ℝ) * yb) + (1 : ℝ) ≤ synthetic_edge_U (synthetic_edge_h 3 (((3 : ℕ) : ℝ) * yb)) := by
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
  · linarith [synthetic_edge_c2 (3 * yb) (by linarith) (by linarith), synthetic_edge_piece0 yb]

theorem synthetic_edge_clos3 (yb : ℝ) (hl : (0 : ℝ) ≤ yb) (hu : yb ≤ (1 : ℝ)) :
    (0 : ℝ) ≤ synthetic_edge_h 3 (((3 : ℕ) : ℝ) * yb) ∧ synthetic_edge_h 3 (((3 : ℕ) : ℝ) * yb) ≤ (1 : ℝ) := by
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
  · exact synthetic_edge_c2_cl (3 * yb) (by linarith) (by linarith)

theorem synthetic_edge_hstep : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (m : ℝ) * synthetic_edge_U yb + synthetic_edge_g m (m * yb) + (1 : ℝ) ≤ synthetic_edge_U (synthetic_edge_h m (m * yb)) := by
  intro m hm hok yb hl hu
  interval_cases m
  · exact synthetic_edge_step1 yb hl hu
  · exact synthetic_edge_step2 yb hl hu
  · exact synthetic_edge_step3 yb hl hu

theorem synthetic_edge_hclos : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ∀ yb : ℝ, (0 : ℝ) ≤ yb → yb ≤ (1 : ℝ) →
    (0 : ℝ) ≤ synthetic_edge_h m (m * yb) ∧ synthetic_edge_h m (m * yb) ≤ (1 : ℝ) := by
  intro m hm hok yb hl hu
  interval_cases m
  · exact synthetic_edge_clos1 yb hl hu
  · exact synthetic_edge_clos2 yb hl hu
  · exact synthetic_edge_clos3 yb hl hu

set_option linter.unusedVariables false in
theorem synthetic_edge_U_le_max (x : ℝ) (hl : (0 : ℝ) ≤ x) (hu : x ≤ (1 : ℝ)) : synthetic_edge_U x ≤ (0 : ℝ) := by
  · linarith [synthetic_edge_piece0 x]

/-- MAIN.  The certified bound on every tree of child count at most 3. -/
theorem synthetic_edge (b : PTree) (hb : b.AllDeg (fun m => m ≤ 3)) :
    (0 : ℝ) ≤ b.msg synthetic_edge_h (1 : ℝ) ∧ b.msg synthetic_edge_h (1 : ℝ) ≤ (1 : ℝ) ∧
      b.ell synthetic_edge_g synthetic_edge_h (-1 : ℝ) (1 : ℝ) + (1 : ℝ) * b.size ≤ synthetic_edge_U (b.msg synthetic_edge_h (1 : ℝ)) :=
  pooled_induction_core (fun m => m ≤ 3) synthetic_edge_h synthetic_edge_g synthetic_edge_U synthetic_edge_U (1 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1 : ℝ)
    (minPieces_jensen synthetic_edge_A synthetic_edge_B) (fun _ _ _ => le_rfl) ⟨by norm_num, by norm_num⟩ synthetic_edge_base synthetic_edge_hclos synthetic_edge_hstep b hb

/-- Uniform corollary: `ell + α·size ≤ max_j v_j = 0`. -/
theorem synthetic_edge_uniform (b : PTree) (hb : b.AllDeg (fun m => m ≤ 3)) :
    b.ell synthetic_edge_g synthetic_edge_h (-1 : ℝ) (1 : ℝ) + (1 : ℝ) * b.size ≤ (0 : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := synthetic_edge b hb
  linarith [synthetic_edge_U_le_max _ h1 h2]

end ConcavePooledInduction
