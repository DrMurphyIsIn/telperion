/-
RHInertia -- the interval-to-inertia bridge for Telperion's `interval_gram_inertia` emitter.

Built on the ported RHLinalg block (Apache-2.0, anthropics zeta-23-lean, Lean v4.32.0): `posIndex`,
`hermForm`, `PosDefOn`, `finrank_le_posIndex_of_posDefOn`, `posIndex_eq_max_finrank_posDefOn`.
Every lemma here is general (no instance data) and proof-complete: no placeholder
tactic appears anywhere in this file.

`defect hA := posIndex hA.neg` is definitionally the `DefectDictionary.defect` of the
zeta_zero_localization island, so certificates emitted against this prelude are consumable there.

conjecture1_proved = False -- a finite linear-algebra instrument, not a step toward RH.
-/
import RHLinalg

noncomputable section
open Matrix Finset Submodule
namespace RHInertia
open RHLinalg

/-! ### Entry-reduction tactics

A bare `simp` reduces `!![...] i j` and `![...] i` at numeral indices, but its full simp set blows
the `isDefEq` heartbeat budget on 4x4 literals.  These macros wrap the minimal `simp only` set that
does the same job in seconds; every emitted instance uses them, so the emitted Lean stays short and
the set is maintained in ONE place. -/

/-- Reduce matrix/vector literal applications at numeral indices. -/
macro "inertia_entries" : tactic =>
  `(tactic| simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply])

/-- `inertia_entries`, also expanding `Finset.univ` sums over `Fin`. -/
macro "inertia_entries_sum" : tactic =>
  `(tactic| simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply])

/-- `inertia_entries_sum`, also unfolding matrix products and transposes. -/
macro "inertia_entries_mul" : tactic =>
  `(tactic| simp only [Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply])

/-- `simpa only` with the entry-reduction set. -/
macro "inertia_entries_using " t:term : tactic =>
  `(tactic| simpa only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.neg_apply] using $t)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `hermForm (-A) x = - hermForm A x`. -/
lemma hermForm_neg (A : Matrix n n 𝕜) (x : n → 𝕜) : hermForm (-A) x = - hermForm A x := by
  unfold hermForm; simp [neg_mulVec, dotProduct_neg]

/-- The **defect** (negative index) `n₋(A) = n₊(−A)`.  Definitionally identical to
`DefectDictionary.defect`. -/
def defect {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ := posIndex hA.neg

/-- **Upper half of Sylvester's law**: a Hermitian form and its negative cannot both be positive
definite on subspaces that meet nontrivially, so `n₊(A) + n₊(−A) ≤ n`. -/
theorem posIndex_add_posIndex_neg_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    posIndex hA + posIndex hA.neg ≤ Fintype.card n := by
  obtain ⟨W, hW, hWdim⟩ := posIndex_eq_max_finrank_posDefOn hA
  obtain ⟨V, hV, hVdim⟩ := posIndex_eq_max_finrank_posDefOn hA.neg
  have hinf : W ⊓ V = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxW, hxV⟩ := hx
    simp only [Submodule.mem_bot]
    by_contra hne
    have h1 := hW x hxW hne
    have h2 := hV x hxV hne
    rw [hermForm_neg] at h2
    linarith
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq W V
  rw [hinf] at hsup
  simp only [finrank_bot, add_zero] at hsup
  have hle : Module.finrank 𝕜 (W ⊔ V : Submodule 𝕜 (n → 𝕜)) ≤ Module.finrank 𝕜 (n → 𝕜) :=
    Submodule.finrank_le _
  rw [Module.finrank_fintype_fun_eq_card] at hle
  omega

/-- **Lower half of Sylvester's law, in witness form**: if the compressed form `Xᴴ A X` is positive
definite then `X` is injective and `range X` is a `card p`-dimensional `PosDefOn` subspace, so
`card p ≤ posIndex hA`.  (The mechanism behind `offline_pairs_le_defect`, generic in `X`.) -/
theorem card_le_posIndex_of_compress_posDef {p : Type*} [Fintype p] [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (X : Matrix n p 𝕜)
    (hpos : ∀ v : p → 𝕜, v ≠ 0 → 0 < hermForm (Xᴴ * A * X) v) :
    Fintype.card p ≤ posIndex hA := by
  set L : (p → 𝕜) →ₗ[𝕜] (n → 𝕜) := X.mulVecLin with hL
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    simp only [LinearMap.mem_ker] at hv
    simp only [Submodule.mem_bot]
    by_contra hne
    have hp := hpos v hne
    rw [hermForm_conj] at hp
    have hXv : X *ᵥ v = 0 := hv
    rw [hXv] at hp
    simp [hermForm] at hp
  have hW : PosDefOn A (LinearMap.range L) := by
    rintro _ ⟨v, rfl⟩ hne
    have hv : v ≠ 0 := by rintro rfl; exact hne (by simp [hL])
    have hp := hpos v hv
    rw [hermForm_conj] at hp
    exact hp
  have hfin := finrank_le_posIndex_of_posDefOn hA hW
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at hfin

/-- The real Hermitian form, entrywise. -/
lemma hermForm_real {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    hermForm A x = ∑ i, ∑ j, x i * A i j * x j := by
  simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Column absolute-sums control the absolute-sum of `X *ᵥ v`. -/
lemma sum_abs_mulVec_le {N P : ℕ} (X : Matrix (Fin N) (Fin P) ℝ) (s : Fin P → ℝ)
    (hs : ∀ k, ∑ i, |X i k| ≤ s k) (v : Fin P → ℝ) :
    ∑ i, |(X *ᵥ v) i| ≤ ∑ k, s k * |v k| := by
  have step1 : ∀ i, |(X *ᵥ v) i| ≤ ∑ k, |X i k| * |v k| := by
    intro i
    have h : (X *ᵥ v) i = ∑ k, X i k * v k := rfl
    rw [h]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    simp [abs_mul]
  calc ∑ i, |(X *ᵥ v) i| ≤ ∑ i, ∑ k, |X i k| * |v k| := Finset.sum_le_sum (fun i _ => step1 i)
    _ = ∑ k, (∑ i, |X i k|) * |v k| := by rw [Finset.sum_comm]; simp [Finset.sum_mul]
    _ ≤ ∑ k, s k * |v k| :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hs k) (abs_nonneg _))

/-- An entrywise `w`-perturbation moves the real Hermitian form by at most `w * (∑ |u i|)²`. -/
lemma abs_hermForm_diff_le {N : ℕ} (G M : Matrix (Fin N) (Fin N) ℝ) (w : ℝ)
    (hw : ∀ i j, |G i j - M i j| ≤ w) (u : Fin N → ℝ) :
    |∑ i, ∑ j, u i * (G i j - M i j) * u j| ≤ w * (∑ i, |u i|) ^ 2 := by
  calc |∑ i, ∑ j, u i * (G i j - M i j) * u j|
      ≤ ∑ i, |∑ j, u i * (G i j - M i j) * u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |u i| * w * |u j| := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hw i j) (abs_nonneg _)) (abs_nonneg _)
    _ = w * (∑ i, |u i|) ^ 2 := by
        have h1 : ∀ i : Fin N, ∑ j, |u i| * w * |u j| = (|u i| * w) * ∑ j, |u j| := by
          intro i; rw [Finset.mul_sum]
        simp_rw [h1]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-- **The interval step.**  If `G` lies entrywise within `w` of `M`, the compressed midpoint form
`C = Xᵀ M X` dominates `δ • I`, the columns of `X` have absolute-sums bounded by `s` with
`S = ∑ s k ^ 2`, and `w * S < δ`, then the compressed form of `G` is positive definite. -/
theorem compress_posDef_of_interval {N P : ℕ}
    (G M : Matrix (Fin N) (Fin N) ℝ) (X : Matrix (Fin N) (Fin P) ℝ)
    (C : Matrix (Fin P) (Fin P) ℝ) (s : Fin P → ℝ) (w δ S : ℝ)
    (hw : ∀ i j, |G i j - M i j| ≤ w) (hw0 : 0 ≤ w)
    (hs : ∀ k, ∑ i, |X i k| ≤ s k)
    (hS : S = ∑ k, (s k) ^ 2)
    (hC : C = Xᵀ * M * X)
    (hd : ∀ v : Fin P → ℝ, δ * (∑ k, (v k) ^ 2) ≤ ∑ k, ∑ l, v k * C k l * v l)
    (hslack : w * S < δ) :
    ∀ v : Fin P → ℝ, v ≠ 0 → 0 < hermForm (Xᴴ * G * X) v := by
  intro v hv
  have hXH : (Xᴴ : Matrix (Fin P) (Fin N) ℝ) = Xᵀ := Matrix.conjTranspose_eq_transpose_of_trivial X
  have key : hermForm (Xᴴ * G * X) v = hermForm G (X *ᵥ v) := hermForm_conj G X v
  have hMcomp : hermForm M (X *ᵥ v) = ∑ k, ∑ l, v k * C k l * v l := by
    rw [← hermForm_conj M X v, hC, ← hXH, hermForm_real]
  have hsplit : hermForm G (X *ᵥ v)
      = hermForm M (X *ᵥ v) + ∑ i, ∑ j, (X *ᵥ v) i * (G i j - M i j) * (X *ᵥ v) j := by
    rw [hermForm_real, hermForm_real, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hpert := abs_hermForm_diff_le G M w hw (X *ᵥ v)
  have habs : -(w * (∑ i, |(X *ᵥ v) i|) ^ 2)
      ≤ ∑ i, ∑ j, (X *ᵥ v) i * (G i j - M i j) * (X *ᵥ v) j := (abs_le.mp hpert).1
  have hsum : (∑ i, |(X *ᵥ v) i|) ≤ ∑ k, s k * |v k| := sum_abs_mulVec_le X s hs v
  have hsum0 : 0 ≤ ∑ i, |(X *ᵥ v) i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hcs : (∑ k, s k * |v k|) ^ 2 ≤ S * ∑ k, (v k) ^ 2 := by
    rw [hS]
    simpa [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s (fun k => |v k|)
  have hsq : (∑ i, |(X *ᵥ v) i|) ^ 2 ≤ S * ∑ k, (v k) ^ 2 :=
    le_trans (pow_le_pow_left₀ hsum0 hsum 2) hcs
  have hvpos : 0 < ∑ k, (v k) ^ 2 := by
    rcases Function.ne_iff.mp hv with ⟨k, hk⟩
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨k, Finset.mem_univ k, ?_⟩
    have hk' : v k ≠ 0 := hk
    positivity
  have hdelta := hd v
  rw [key, hsplit, hMcomp]
  nlinarith [mul_le_mul_of_nonneg_left hsq hw0, mul_pos (sub_pos.mpr hslack) hvpos]

/-- **The assembly.**  Witness bases of sizes `P` and `Q` with `P + Q = N` pin the signature of `G`
exactly: `posIndex hG = P` and `defect hG = Q`. -/
theorem inertia_eq_of_witnesses {N P Q : ℕ}
    {G : Matrix (Fin N) (Fin N) ℝ} (hG : G.IsHermitian)
    (X : Matrix (Fin N) (Fin P) ℝ) (Y : Matrix (Fin N) (Fin Q) ℝ)
    (hpq : P + Q = N)
    (hX : ∀ v : Fin P → ℝ, v ≠ 0 → 0 < hermForm (Xᴴ * G * X) v)
    (hY : ∀ v : Fin Q → ℝ, v ≠ 0 → 0 < hermForm (Yᴴ * (-G) * Y) v) :
    posIndex hG = P ∧ defect hG = Q := by
  have h1 := card_le_posIndex_of_compress_posDef hG X hX
  have h2 := card_le_posIndex_of_compress_posDef hG.neg Y hY
  have h3 := posIndex_add_posIndex_neg_le hG
  simp only [Fintype.card_fin] at h1 h2 h3
  constructor
  · omega
  · show posIndex hG.neg = Q
    omega

end RHInertia
