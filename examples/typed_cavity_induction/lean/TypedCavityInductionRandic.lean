/-
Hand-written companion of the generated `TypedCavityInduction.lean` (this file is NOT
generated; `generate.py --check` covers the other one).

It restates the two Balister-Bollobás-Gerke instances `bbg3` and `bbg4` in terms of the
generalized Randić index `R_{-1}` itself:

  P. Balister, B. Bollobás, S. Gerke, "The generalized Randić index of trees",
  J. Graph Theory 56 (2007) 270-286: half-trees, recursion (2), the constants (4)-(5),
  Lemma 4 and Theorem 6, at α = γ = 1 with the published β₃ = 7/27 and β₄ = 139/528.

A half-tree is a rooted tree with one dangling edge at its root (a planted rooted tree); the
dangling edge counts in the root degree but contributes no term.  `R_{-1}` of a half-tree sums
`1 / (d(u) d(v))` over its non-dangling edges.  A tree whose maximum degree is `Δ`, rooted at a
vertex of degree `Δ`, is that root joined to `Δ` half-trees; every tree of maximum degree `Δ`
has such a presentation (root it at a vertex of maximum degree), which is the form the
Theorem 6 statements below take.  (Rooting an unrooted tree is not formalized here.)

conjecture1_proved = False.
-/
import TypedCavityInduction

namespace TypedCavityInduction.Randic

open TypedCavityInduction TypedCavity

/-- The degree of the root of a half-tree: its children plus the dangling edge. -/
def deg : PTree → ℕ
  | .leaf => 1
  | .node m _ => m + 2

/-- `R_{-1}` of a half-tree: the edges from the root to its children, `1 / (d(root) d(child))`,
plus the children's own `R_{-1}`. -/
noncomputable def randic : PTree → ℝ
  | .leaf => 0
  | .node m cs => ∑ i, (randic (cs i) + 1 / (((m + 2 : ℕ) : ℝ) * (deg (cs i) : ℝ)))

/-- `R_{-1}` of the tree made of a root joined to the half-trees `b 0, ..., b (K-1)` (the
root has degree `K`; the half-trees' dangling edges become the root's edges). -/
noncomputable def treeRandic {K : ℕ} (b : Fin K → PTree) : ℝ :=
  ∑ i, (randic (b i) + 1 / ((K : ℝ) * (deg (b i) : ℝ)))

/-- The number of vertices of that tree. -/
def treeSize {K : ℕ} (b : Fin K → PTree) : ℕ := (∑ i, (b i).size) + 1

/-- With `h(m, R) = 1/(m+1)` the message of a half-tree is `1 / deg`. -/
theorem msg_eq (h : ℕ → ℝ → ℝ) (hh : ∀ k R, h k R = 1 / (1 + (k : ℝ))) (b : PTree) :
    b.msg h 1 = 1 / (deg b : ℝ) := by
  cases b with
  | leaf => simp [PTree.msg, deg]
  | node m cs =>
    rw [PTree.msg, hh]
    simp only [deg]
    push_cast
    ring

/-- With `g(m, R) = R/(m+1) - β` and the leaf `(1, -β)`, the value of a half-tree is
BBG's `c_T = R_{-1}(T) - β n(T)` (their recursion (2)). -/
theorem ell_eq (β : ℝ) (g h : ℕ → ℝ → ℝ) (hh : ∀ k R, h k R = 1 / (1 + (k : ℝ)))
    (hg : ∀ k R, g k R = R / (1 + (k : ℝ)) - β) (b : PTree) :
    b.ell g h (-β) 1 = randic b - β * b.size := by
  induction b with
  | leaf => simp [PTree.ell, randic, PTree.size]
  | node m cs ih =>
    rw [PTree.ell, hg, Finset.sum_congr rfl (fun i _ => ih i),
      Finset.sum_congr rfl (fun i _ => msg_eq h hh (cs i))]
    simp only [randic, PTree.size]
    have e1 : (∑ i, 1 / (deg (cs i) : ℝ)) / (1 + ((m + 1 : ℕ) : ℝ)) =
        ∑ i, 1 / (((m + 2 : ℕ) : ℝ) * (deg (cs i) : ℝ)) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rw [div_div]
      ring_nf
    rw [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    push_cast
    ring

/-- Joining: the tree's `R_{-1} - β n` is the join value of its half-trees. -/
theorem join_eq (β : ℝ) (K : ℕ) (hK : 0 < K) (g h : ℕ → ℝ → ℝ)
    (hh : ∀ k R, h k R = 1 / (1 + (k : ℝ))) (hg : ∀ k R, g k R = R / (1 + (k : ℝ)) - β)
    (b : Fin K → PTree) :
    (∑ i, (b i).ell g h (-β) 1) + (-β + (1 / (K : ℝ)) * ∑ i, (b i).msg h 1) =
      treeRandic b - β * (treeSize b : ℝ) := by
  have hK' : (K : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_congr rfl (fun i _ => ell_eq β g h hh hg (b i)),
    Finset.sum_congr rfl (fun i _ => msg_eq h hh (b i))]
  simp only [treeRandic, treeSize]
  have e1 : ∀ i, 1 / (K : ℝ) * (1 / (deg (b i) : ℝ)) = 1 / ((K : ℝ) * (deg (b i) : ℝ)) := by
    intro i; rw [div_mul_div_comm, one_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_congr rfl (fun i _ => e1 i)]
  push_cast
  rw [mul_add, Finset.mul_sum]
  ring

/-! ### Maximum degree 3, `β₃ = 7/27` -/

theorem bbg3_hh : ∀ k R, bbg3_h k R = 1 / (1 + (k : ℝ)) := fun k R => by simp [bbg3_h]

theorem bbg3_hg : ∀ k R, bbg3_g k R = R / (1 + (k : ℝ)) - 7 / 27 := fun k R => by
  have : (27 : ℝ) + 27 * (k : ℝ) ≠ 0 := by positivity
  have : (1 : ℝ) + (k : ℝ) ≠ 0 := by positivity
  simp only [bbg3_g]
  field_simp
  ring

/-- BBG Lemma 4 at `Δ = 3`: every half-tree of maximum degree at most 3 has
`R_{-1} ≤ (7/27) n + c_{d}` for its root degree `d`; uniformly, `R_{-1} ≤ (7/27) n + 1/27`. -/
theorem halftree_delta3 (b : PTree) (hb : b.AllDeg (fun k => k ≤ 2)) :
    randic b ≤ 7 / 27 * (b.size : ℝ) + 1 / 27 := by
  have := bbg3_uniform b hb
  rw [show (-7 / 27 : ℝ) = -(7 / 27) by norm_num, ell_eq (7 / 27) bbg3_g bbg3_h bbg3_hh bbg3_hg b]
    at this
  linarith

/-- BBG Theorem 6 at `Δ = 3`, `α = γ = 1`: a tree of maximum degree 3 (rooted at a vertex of
degree 3, its three branches half-trees of maximum degree at most 3) has
`R_{-1}(T) ≤ (7/27) n + 5/27`.  (`5/27 = 10/54`; the paper prints `11/54`, which this implies.) -/
theorem bbg_theorem6_delta3 (b : Fin 3 → PTree) (hb : ∀ i, (b i).AllDeg (fun k => k ≤ 2)) :
    treeRandic b ≤ 7 / 27 * (treeSize b : ℝ) + 5 / 27 := by
  have hj := bbg3_join b hb
  have e := join_eq (7 / 27) 3 (by norm_num) bbg3_g bbg3_h bbg3_hh bbg3_hg b
  rw [show (-7 / 27 : ℝ) = -(7 / 27) by norm_num] at hj
  simp only [bbg3_gJ] at hj
  push_cast at e
  linarith

/-! ### Maximum degree 4, `β₄ = 139/528` -/

theorem bbg4_hh : ∀ k R, bbg4_h k R = 1 / (1 + (k : ℝ)) := fun k R => by simp [bbg4_h]

theorem bbg4_hg : ∀ k R, bbg4_g k R = R / (1 + (k : ℝ)) - 139 / 528 := fun k R => by
  have : (528 : ℝ) + 528 * (k : ℝ) ≠ 0 := by positivity
  have : (1 : ℝ) + (k : ℝ) ≠ 0 := by positivity
  simp only [bbg4_g]
  field_simp
  ring

/-- BBG Lemma 4 at `Δ = 4`: every half-tree of maximum degree at most 4 has
`R_{-1} ≤ (139/528) n + 5/132`. -/
theorem halftree_delta4 (b : PTree) (hb : b.AllDeg (fun k => k ≤ 3)) :
    randic b ≤ 139 / 528 * (b.size : ℝ) + 5 / 132 := by
  have := bbg4_uniform b hb
  rw [show (-139 / 528 : ℝ) = -(139 / 528) by norm_num,
    ell_eq (139 / 528) bbg4_g bbg4_h bbg4_hh bbg4_hg b] at this
  linarith

/-- BBG Theorem 6 at `Δ = 4` (chemical trees), `α = γ = 1`: a tree of maximum degree 4 (rooted
at a vertex of degree 4) has `R_{-1}(T) ≤ (139/528) n + 73/528`, the published bound. -/
theorem bbg_theorem6_delta4 (b : Fin 4 → PTree) (hb : ∀ i, (b i).AllDeg (fun k => k ≤ 3)) :
    treeRandic b ≤ 139 / 528 * (treeSize b : ℝ) + 73 / 528 := by
  have hj := bbg4_join b hb
  have e := join_eq (139 / 528) 4 (by norm_num) bbg4_g bbg4_h bbg4_hh bbg4_hg b
  rw [show (-139 / 528 : ℝ) = -(139 / 528) by norm_num] at hj
  simp only [bbg4_gJ] at hj
  push_cast at e
  linarith

end TypedCavityInduction.Randic
