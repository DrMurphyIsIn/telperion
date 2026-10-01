/- telperion 0.1.6 | family CurvatureBoundary | input-hash 0fb87326a5d0e9e0
   53 theorems, 16 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace CurvatureBoundary

-- Provenance: ports a proof idea (not code) from AxiomMath/ZetaZeros
-- (arXiv:2609.02882; Montgomery-Taylor kernel, `extremalG_const`),
-- generalized here to the curvature-sign setting. Independently
-- re-implemented; see NOTICE.md for full attribution.

-- (1) ABSTRACT CONCAVE→ENDPOINTS.  A function concave on `[a,b]` dominates the
-- MIN of its two endpoint values everywhere on `[a,b]`: the extremum (here the
-- minimum) of a sign-definite-curvature function sits at a boundary point.
-- Proof: `x ∈ [a,b]` is a convex combination `x = t·a + (1-t)·b`; concavity gives
-- `f x ≥ t·f a + (1-t)·f b ≥ min (f a) (f b)`.
theorem concave_ge_min_endpoints {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hcave : ConcaveOn ℝ (Set.Icc a b) f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    min (f a) (f b) ≤ f x := by
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  rcases eq_or_lt_of_le hab with he | hlt
  · -- degenerate a = b: x is forced to a, and min (f a) (f b) = f a = f x.
    subst he
    have hxa : x = a := le_antisymm hx.2 hx.1
    simp [hxa]
  · -- a < b: write x = t·a + (1-t)·b with t = (b-x)/(b-a) ∈ [0,1].
    set t : ℝ := (b - x) / (b - a) with ht
    have hba : 0 < b - a := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg (sub_nonneg.mpr hx.2) (le_of_lt hba)
    have ht1 : 0 ≤ 1 - t := by
      rw [ht]
      have : (b - x) / (b - a) ≤ 1 :=
        (div_le_one hba).mpr (by linarith [hx.1])
      linarith
    have hsum : t + (1 - t) = 1 := by ring
    have hne : b - a ≠ 0 := ne_of_gt hba
    have hxconv : t • a + (1 - t) • b = x := by
      simp only [ht, smul_eq_mul]
      field_simp
      ring
    have hkey := hcave.2 ha hb ht0 ht1 hsum
    rw [hxconv] at hkey
    -- hkey : t • f a + (1 - t) • f b ≤ f x  (concavity: value ≥ chord)
    simp only [smul_eq_mul] at hkey
    have hmina : min (f a) (f b) ≤ f a := min_le_left _ _
    have hminb : min (f a) (f b) ≤ f b := min_le_right _ _
    have hchord : min (f a) (f b) ≤ t * f a + (1 - t) * f b := by
      nlinarith [mul_le_mul_of_nonneg_left hmina ht0,
                 mul_le_mul_of_nonneg_left hminb ht1]
    linarith

-- (3) AFFINE FACE (f'' = 0).  The `affine_param_endpoint` core restated in the
-- curvature framing: an affine `A + x·B` that is `≥ m` at both endpoints of
-- `[a,b]` is `≥ m` throughout — the extremum of a ZERO-curvature function sits at
-- a boundary point.
theorem affine_boundary {a b m x : ℝ} (hab : a < b) (A B : ℝ)
    (hL : m ≤ A + a * B) (hH : m ≤ A + b * B) (hx : x ∈ Set.Icc a b) :
    m ≤ A + x * B := by
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hba : 0 < b - a := sub_pos.mpr hab
  -- (b−x)(A+aB) + (x−a)(A+bB) = (b−a)(A+xB); both summands ≥ (·)·m, sum ≥ (b−a)m.
  have hprodL : 0 ≤ (b - x) * (A + a * B - m) :=
    mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hL)
  have hprodH : 0 ≤ (x - a) * (A + b * B - m) :=
    mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hH)
  nlinarith [hprodL, hprodH, hba]

-- (4) CONVEX→ENDPOINTS (f'' ≥ 0).  Dual of (1): a function convex on `[a,b]` is
-- dominated by the MAX of its two endpoint values — the (maximum) extremum of a
-- convex function sits at a boundary point.
theorem convex_le_max_endpoints {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hcvx : ConvexOn ℝ (Set.Icc a b) f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f x ≤ max (f a) (f b) := by
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  rcases eq_or_lt_of_le hab with he | hlt
  · subst he
    have hxa : x = a := le_antisymm hx.2 hx.1
    simp [hxa]
  · set t : ℝ := (b - x) / (b - a) with ht
    have hba : 0 < b - a := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg (sub_nonneg.mpr hx.2) (le_of_lt hba)
    have ht1 : 0 ≤ 1 - t := by
      rw [ht]
      have : (b - x) / (b - a) ≤ 1 :=
        (div_le_one hba).mpr (by linarith [hx.1])
      linarith
    have hsum : t + (1 - t) = 1 := by ring
    have hne : b - a ≠ 0 := ne_of_gt hba
    have hxconv : t • a + (1 - t) • b = x := by
      simp only [ht, smul_eq_mul]
      field_simp
      ring
    have hkey := hcvx.2 ha hb ht0 ht1 hsum
    rw [hxconv] at hkey
    simp only [smul_eq_mul] at hkey
    have hmaxa : f a ≤ max (f a) (f b) := le_max_left _ _
    have hmaxb : f b ≤ max (f a) (f b) := le_max_right _ _
    have hchord : t * f a + (1 - t) * f b ≤ max (f a) (f b) := by
      nlinarith [mul_le_mul_of_nonneg_left hmaxa ht0,
                 mul_le_mul_of_nonneg_left hmaxb ht1]
    linarith

-- CONCRETE CONCAVE INSTANCE `concave_quad_min_endpoints` (ports AxiomMath extremalG_const
-- move to the concave quadratic f x = -x^2 + x, f'' = -2 ≤ 0
-- on [0,1]): the minimum sits at a boundary, so
-- `min (f 0) (f 1) ≤ f x` for all x∈[0,1], by the (x−0)(1−x) ≥ 0 witness.
theorem concave_quad_min_endpoints : ∀ x ∈ Set.Icc (0 : ℝ) (1),
    min ((0 : ℝ)) (0) ≤ (fun x : ℝ => -x^2 + x) x := by
  intro x hx
  have hxa : (0 : ℝ) ≤ x := hx.1
  have hxb : x ≤ (1 : ℝ) := hx.2
  simp only
  have hmin : min ((0 : ℝ)) (0) ≤ 0 := min_le_left _ _
  have hmin2 : min ((0 : ℝ)) (0) ≤ 0 := min_le_right _ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hxb),
             hmin, hmin2]

-- CONCRETE CONCAVE INSTANCE `concave_quad2_min_endpoints` (ports AxiomMath extremalG_const
-- move to the concave quadratic f x = -2*x^2 + x + 1, f'' = -4 ≤ 0
-- on [0,1]): the minimum sits at a boundary, so
-- `min (f 0) (f 1) ≤ f x` for all x∈[0,1], by the (x−0)(1−x) ≥ 0 witness.
theorem concave_quad2_min_endpoints : ∀ x ∈ Set.Icc (0 : ℝ) (1),
    min ((1 : ℝ)) (0) ≤ (fun x : ℝ => -2*x^2 + x + 1) x := by
  intro x hx
  have hxa : (0 : ℝ) ≤ x := hx.1
  have hxb : x ≤ (1 : ℝ) := hx.2
  simp only
  have hmin : min ((1 : ℝ)) (0) ≤ 1 := min_le_left _ _
  have hmin2 : min ((1 : ℝ)) (0) ≤ 0 := min_le_right _ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hxb),
             hmin, hmin2]

-- CONCRETE CONVEX INSTANCE `convex_quad_max_endpoints` (dual of the extremalG_const move:
-- f x = x^2, f'' = 2 ≥ 0 on [0,1]): the maximum sits
-- at a boundary, so `f x ≤ max (f 0) (f 1)` for all x∈[0,1].
theorem convex_quad_max_endpoints : ∀ x ∈ Set.Icc (0 : ℝ) (1),
    (fun x : ℝ => x^2) x ≤ max ((0 : ℝ)) (1) := by
  intro x hx
  have hxa : (0 : ℝ) ≤ x := hx.1
  have hxb : x ≤ (1 : ℝ) := hx.2
  simp only
  have hmax : (0 : ℝ) ≤ max ((0 : ℝ)) (1) := le_max_left _ _
  have hmax2 : (1 : ℝ) ≤ max ((0 : ℝ)) (1) := le_max_right _ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hxb),
             hmax, hmax2]

-- CONCRETE AFFINE INSTANCE `affine_line_boundary` (f'' = 0 face — the `affine_param_endpoint`
-- core in curvature framing): f x = 2*x + 1 = 1 + x·(2); with the endpoint
-- floor m = 1 met at both a=0, b=1, `m ≤ 1 + x·(2)` throughout.
theorem affine_line_boundary : ∀ x ∈ Set.Icc (0 : ℝ) (1),
    (1 : ℝ) ≤ (1) + x * (2) := by
  intro x hx
  exact affine_boundary (by norm_num) (1) (2)
    (by norm_num) (by norm_num) hx

-- (5) KINK MINIMUM (extension, 2026-10-01).  A function antitone on `[a,k]` and monotone
-- on `[k,b]` attains its minimum over `[a,b]` at the kink `k`.
theorem kink_min_of_anti_mono {a k b : ℝ} (f : ℝ → ℝ)
    (hL : AntitoneOn f (Set.Icc a k)) (hR : MonotoneOn f (Set.Icc k b))
    (hak : a ≤ k) (hkb : k ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) : f k ≤ f x := by
  rcases le_total x k with h | h
  · exact hL ⟨hx.1, h⟩ ⟨hak, le_rfl⟩ h
  · exact hR ⟨le_rfl, hkb⟩ ⟨h, hx.2⟩ h

-- KINK-MINIMUM INSTANCE `kink_abs_quad_min` (extension, 2026-10-01): f = L on [0, 1/3], f = R on (1/3, 1],
-- L' ≤ 0 and R' ≥ 0 certified by Bernstein cells (1 + 1), so min f = f(1/3) = 1/9.
noncomputable def kink_abs_quad_min_L : Polynomial ℝ := Polynomial.C (1 / 3 : ℝ) * Polynomial.X ^ 0 + Polynomial.C (-1 : ℝ) * Polynomial.X ^ 1 + Polynomial.C (1 : ℝ) * Polynomial.X ^ 2
noncomputable def kink_abs_quad_min_R : Polynomial ℝ := Polynomial.C (-1 / 3 : ℝ) * Polynomial.X ^ 0 + Polynomial.C (1 : ℝ) * Polynomial.X ^ 1 + Polynomial.C (1 : ℝ) * Polynomial.X ^ 2
/-- The piecewise function: `L` up to the kink, `R` after it. -/
noncomputable def kink_abs_quad_min_f (x : ℝ) : ℝ := if x ≤ (1 / 3 : ℝ) then kink_abs_quad_min_L.eval x else kink_abs_quad_min_R.eval x

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem kink_abs_quad_min_dL (x : ℝ) :
    (Polynomial.derivative kink_abs_quad_min_L).eval x = ((-1 : ℝ) + (2 : ℝ) * x) := by
  simp only [kink_abs_quad_min_L, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] <;> norm_num <;> ring_nf

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem kink_abs_quad_min_dR (x : ℝ) :
    (Polynomial.derivative kink_abs_quad_min_R).eval x = ((1 : ℝ) + (2 : ℝ) * x) := by
  simp only [kink_abs_quad_min_R, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] <;> norm_num <;> ring_nf

theorem kink_abs_quad_min_dL_nonpos (x : ℝ) (h1 : (0 : ℝ) ≤ x) (h2 : x ≤ (1 / 3 : ℝ)) :
    ((-1 : ℝ) + (2 : ℝ) * x) ≤ 0 := by
  suffices H : 0 ≤ ((1 : ℝ) + (-2 : ℝ) * x) by linarith
  have hs : 0 ≤ x - (0 : ℝ) := by linarith [h1]
  have ht : 0 ≤ (1 / 3 : ℝ) - x := by linarith [h2]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem kink_abs_quad_min_dR_nonneg (x : ℝ) (h1 : (1 / 3 : ℝ) ≤ x) (h2 : x ≤ (1 : ℝ)) :
    0 ≤ ((1 : ℝ) + (2 : ℝ) * x) := by
  have hs : 0 ≤ x - (1 / 3 : ℝ) := by linarith [h1]
  have ht : 0 ≤ (1 : ℝ) - x := by linarith [h2]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem kink_abs_quad_min_L_anti : AntitoneOn (fun x => kink_abs_quad_min_L.eval x) (Set.Icc (0 : ℝ) (1 / 3 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) kink_abs_quad_min_L.continuous.continuousOn
    kink_abs_quad_min_L.differentiable.differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv, kink_abs_quad_min_dL]
  exact kink_abs_quad_min_dL_nonpos x hx.1.le hx.2.le

theorem kink_abs_quad_min_R_mono : MonotoneOn (fun x => kink_abs_quad_min_R.eval x) (Set.Icc (1 / 3 : ℝ) (1 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) kink_abs_quad_min_R.continuous.continuousOn
    kink_abs_quad_min_R.differentiable.differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv, kink_abs_quad_min_dR]
  exact kink_abs_quad_min_dR_nonneg x hx.1.le hx.2.le

theorem kink_abs_quad_min_cont : kink_abs_quad_min_L.eval (1 / 3 : ℝ) = kink_abs_quad_min_R.eval (1 / 3 : ℝ) := by
  simp only [kink_abs_quad_min_L, kink_abs_quad_min_R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

theorem kink_abs_quad_min_f_anti : AntitoneOn kink_abs_quad_min_f (Set.Icc (0 : ℝ) (1 / 3 : ℝ)) := by
  refine kink_abs_quad_min_L_anti.congr ?_
  intro x hx
  simp only [kink_abs_quad_min_f]
  rw [if_pos hx.2]

theorem kink_abs_quad_min_f_mono : MonotoneOn kink_abs_quad_min_f (Set.Icc (1 / 3 : ℝ) (1 : ℝ)) := by
  refine kink_abs_quad_min_R_mono.congr ?_
  intro x hx
  simp only [kink_abs_quad_min_f]
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h, if_pos le_rfl]; exact kink_abs_quad_min_cont.symm
  · rw [if_neg (not_le.mpr h)]

/-- The value at the kink. -/
theorem kink_abs_quad_min_value : kink_abs_quad_min_f (1 / 3 : ℝ) = (1 / 9 : ℝ) := by
  simp only [kink_abs_quad_min_f, if_pos (le_refl (1 / 3 : ℝ)), kink_abs_quad_min_L, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

/-- The minimum over `[0, 1]` is attained at the kink: `1/9 ≤ f x`. -/
theorem kink_abs_quad_min : ∀ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), (1 / 9 : ℝ) ≤ kink_abs_quad_min_f x := by
  intro x hx
  rw [← kink_abs_quad_min_value]
  exact kink_min_of_anti_mono kink_abs_quad_min_f kink_abs_quad_min_f_anti kink_abs_quad_min_f_mono (by norm_num) (by norm_num) hx

/-- `min_{[a,b]} f = f(kappa) = 1/9` as an `IsLeast` statement. -/
theorem kink_abs_quad_min_isLeast : IsLeast (kink_abs_quad_min_f '' Set.Icc (0 : ℝ) (1 : ℝ)) (1 / 9 : ℝ) :=
  ⟨⟨(1 / 3 : ℝ), ⟨by norm_num, by norm_num⟩, kink_abs_quad_min_value⟩, by
    rintro _ ⟨x, hx, rfl⟩; exact kink_abs_quad_min x hx⟩

/-- Nonnegativity on `[0, 1]` (the kink value is `≥ 0`). -/
theorem kink_abs_quad_min_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), 0 ≤ kink_abs_quad_min_f x := fun x hx =>
  le_trans (by norm_num) (kink_abs_quad_min x hx)

/-- The closed form agrees with the piecewise `f` on `[0, 1]`. -/
theorem kink_abs_quad_min_expr_eq : ∀ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), (x ^ 2 + |((-1 / 3 : ℝ) + x)|) = kink_abs_quad_min_f x := by
  intro x hx
  simp only [kink_abs_quad_min_f]
  rcases le_or_gt x (1 / 3 : ℝ) with h | h
  · rw [if_pos h, abs_of_nonpos (show ((-1 / 3 : ℝ) + x) ≤ 0 by linarith [hx.1, hx.2])]
    simp only [kink_abs_quad_min_L, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  · rw [if_neg (not_le.mpr h), abs_of_nonneg (show 0 ≤ ((-1 / 3 : ℝ) + x) by linarith [hx.1, hx.2])]
    simp only [kink_abs_quad_min_R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

theorem kink_abs_quad_min_expr_min : ∀ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), (1 / 9 : ℝ) ≤ (x ^ 2 + |((-1 / 3 : ℝ) + x)|) := by
  intro x hx
  rw [kink_abs_quad_min_expr_eq x hx]
  exact kink_abs_quad_min x hx

theorem kink_abs_quad_min_expr_isLeast :
    IsLeast ((fun x : ℝ => (x ^ 2 + |((-1 / 3 : ℝ) + x)|)) '' Set.Icc (0 : ℝ) (1 : ℝ)) (1 / 9 : ℝ) := by
  refine ⟨⟨(1 / 3 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
  · simp only
    rw [kink_abs_quad_min_expr_eq (1 / 3 : ℝ) ⟨by norm_num, by norm_num⟩, kink_abs_quad_min_value]
  · rintro _ ⟨x, hx, rfl⟩
    exact kink_abs_quad_min_expr_min x hx

-- KINK-MINIMUM INSTANCE `kink_cubic_pieces_min` (extension, 2026-10-01): f = L on [-1, 1], f = R on (1, 2],
-- L' ≤ 0 and R' ≥ 0 certified by Bernstein cells (1 + 1), so min f = f(1) = 0.
noncomputable def kink_cubic_pieces_min_L : Polynomial ℝ := Polynomial.C (2 : ℝ) * Polynomial.X ^ 0 + Polynomial.C (-3 : ℝ) * Polynomial.X ^ 1 + Polynomial.C (1 : ℝ) * Polynomial.X ^ 3
noncomputable def kink_cubic_pieces_min_R : Polynomial ℝ := Polynomial.C (-1 : ℝ) * Polynomial.X ^ 1 + Polynomial.C (1 : ℝ) * Polynomial.X ^ 3
/-- The piecewise function: `L` up to the kink, `R` after it. -/
noncomputable def kink_cubic_pieces_min_f (x : ℝ) : ℝ := if x ≤ (1 : ℝ) then kink_cubic_pieces_min_L.eval x else kink_cubic_pieces_min_R.eval x

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem kink_cubic_pieces_min_dL (x : ℝ) :
    (Polynomial.derivative kink_cubic_pieces_min_L).eval x = ((-3 : ℝ) + (3 : ℝ) * x ^ 2) := by
  simp only [kink_cubic_pieces_min_L, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] <;> norm_num <;> ring_nf

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem kink_cubic_pieces_min_dR (x : ℝ) :
    (Polynomial.derivative kink_cubic_pieces_min_R).eval x = ((-1 : ℝ) + (3 : ℝ) * x ^ 2) := by
  simp only [kink_cubic_pieces_min_R, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] <;> norm_num <;> ring_nf

theorem kink_cubic_pieces_min_dL_nonpos (x : ℝ) (h1 : (-1 : ℝ) ≤ x) (h2 : x ≤ (1 : ℝ)) :
    ((-3 : ℝ) + (3 : ℝ) * x ^ 2) ≤ 0 := by
  suffices H : 0 ≤ ((3 : ℝ) + (-3 : ℝ) * x ^ 2) by linarith
  have hs : 0 ≤ x - (-1 : ℝ) := by linarith [h1]
  have ht : 0 ≤ (1 : ℝ) - x := by linarith [h2]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem kink_cubic_pieces_min_dR_nonneg (x : ℝ) (h1 : (1 : ℝ) ≤ x) (h2 : x ≤ (2 : ℝ)) :
    0 ≤ ((-1 : ℝ) + (3 : ℝ) * x ^ 2) := by
  have hs : 0 ≤ x - (1 : ℝ) := by linarith [h1]
  have ht : 0 ≤ (2 : ℝ) - x := by linarith [h2]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 2), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 2) (pow_nonneg ht 0)]

theorem kink_cubic_pieces_min_L_anti : AntitoneOn (fun x => kink_cubic_pieces_min_L.eval x) (Set.Icc (-1 : ℝ) (1 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) kink_cubic_pieces_min_L.continuous.continuousOn
    kink_cubic_pieces_min_L.differentiable.differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv, kink_cubic_pieces_min_dL]
  exact kink_cubic_pieces_min_dL_nonpos x hx.1.le hx.2.le

theorem kink_cubic_pieces_min_R_mono : MonotoneOn (fun x => kink_cubic_pieces_min_R.eval x) (Set.Icc (1 : ℝ) (2 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) kink_cubic_pieces_min_R.continuous.continuousOn
    kink_cubic_pieces_min_R.differentiable.differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv, kink_cubic_pieces_min_dR]
  exact kink_cubic_pieces_min_dR_nonneg x hx.1.le hx.2.le

theorem kink_cubic_pieces_min_cont : kink_cubic_pieces_min_L.eval (1 : ℝ) = kink_cubic_pieces_min_R.eval (1 : ℝ) := by
  simp only [kink_cubic_pieces_min_L, kink_cubic_pieces_min_R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

theorem kink_cubic_pieces_min_f_anti : AntitoneOn kink_cubic_pieces_min_f (Set.Icc (-1 : ℝ) (1 : ℝ)) := by
  refine kink_cubic_pieces_min_L_anti.congr ?_
  intro x hx
  simp only [kink_cubic_pieces_min_f]
  rw [if_pos hx.2]

theorem kink_cubic_pieces_min_f_mono : MonotoneOn kink_cubic_pieces_min_f (Set.Icc (1 : ℝ) (2 : ℝ)) := by
  refine kink_cubic_pieces_min_R_mono.congr ?_
  intro x hx
  simp only [kink_cubic_pieces_min_f]
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h, if_pos le_rfl]; exact kink_cubic_pieces_min_cont.symm
  · rw [if_neg (not_le.mpr h)]

/-- The value at the kink. -/
theorem kink_cubic_pieces_min_value : kink_cubic_pieces_min_f (1 : ℝ) = (0 : ℝ) := by
  simp only [kink_cubic_pieces_min_f, if_pos (le_refl (1 : ℝ)), kink_cubic_pieces_min_L, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

/-- The minimum over `[-1, 2]` is attained at the kink: `0 ≤ f x`. -/
theorem kink_cubic_pieces_min : ∀ x ∈ Set.Icc (-1 : ℝ) (2 : ℝ), (0 : ℝ) ≤ kink_cubic_pieces_min_f x := by
  intro x hx
  rw [← kink_cubic_pieces_min_value]
  exact kink_min_of_anti_mono kink_cubic_pieces_min_f kink_cubic_pieces_min_f_anti kink_cubic_pieces_min_f_mono (by norm_num) (by norm_num) hx

/-- `min_{[a,b]} f = f(kappa) = 0` as an `IsLeast` statement. -/
theorem kink_cubic_pieces_min_isLeast : IsLeast (kink_cubic_pieces_min_f '' Set.Icc (-1 : ℝ) (2 : ℝ)) (0 : ℝ) :=
  ⟨⟨(1 : ℝ), ⟨by norm_num, by norm_num⟩, kink_cubic_pieces_min_value⟩, by
    rintro _ ⟨x, hx, rfl⟩; exact kink_cubic_pieces_min x hx⟩

/-- Nonnegativity on `[-1, 2]` (the kink value is `≥ 0`). -/
theorem kink_cubic_pieces_min_nonneg : ∀ x ∈ Set.Icc (-1 : ℝ) (2 : ℝ), 0 ≤ kink_cubic_pieces_min_f x := fun x hx =>
  le_trans (by norm_num) (kink_cubic_pieces_min x hx)

-- KINK-MINIMUM INSTANCE `kink_signed_abs_min` (extension, 2026-10-01): f = L on [-1, 0], f = R on (0, 1],
-- L' ≤ 0 and R' ≥ 0 certified by Bernstein cells (1 + 1), so min f = f(0) = 0.
noncomputable def kink_signed_abs_min_L : Polynomial ℝ := Polynomial.C (-1 / 2 : ℝ) * Polynomial.X ^ 1
noncomputable def kink_signed_abs_min_R : Polynomial ℝ := Polynomial.C (1 / 2 : ℝ) * Polynomial.X ^ 1 + Polynomial.C (1 : ℝ) * Polynomial.X ^ 2
/-- The piecewise function: `L` up to the kink, `R` after it. -/
noncomputable def kink_signed_abs_min_f (x : ℝ) : ℝ := if x ≤ (0 : ℝ) then kink_signed_abs_min_L.eval x else kink_signed_abs_min_R.eval x

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem kink_signed_abs_min_dL (x : ℝ) :
    (Polynomial.derivative kink_signed_abs_min_L).eval x = ((-1 / 2 : ℝ)) := by
  simp only [kink_signed_abs_min_L, Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] <;> norm_num <;> ring_nf

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem kink_signed_abs_min_dR (x : ℝ) :
    (Polynomial.derivative kink_signed_abs_min_R).eval x = ((1 / 2 : ℝ) + (2 : ℝ) * x) := by
  simp only [kink_signed_abs_min_R, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] <;> norm_num <;> ring_nf

theorem kink_signed_abs_min_dL_nonpos (x : ℝ) (h1 : (-1 : ℝ) ≤ x) (h2 : x ≤ (0 : ℝ)) :
    ((-1 / 2 : ℝ)) ≤ 0 := by
  suffices H : 0 ≤ ((1 / 2 : ℝ)) by linarith
  have hs : 0 ≤ x - (-1 : ℝ) := by linarith [h1]
  have ht : 0 ≤ (0 : ℝ) - x := by linarith [h2]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 0)]

theorem kink_signed_abs_min_dR_nonneg (x : ℝ) (h1 : (0 : ℝ) ≤ x) (h2 : x ≤ (1 : ℝ)) :
    0 ≤ ((1 / 2 : ℝ) + (2 : ℝ) * x) := by
  have hs : 0 ≤ x - (0 : ℝ) := by linarith [h1]
  have ht : 0 ≤ (1 : ℝ) - x := by linarith [h2]
  linarith [mul_nonneg (pow_nonneg hs 0) (pow_nonneg ht 1), mul_nonneg (pow_nonneg hs 1) (pow_nonneg ht 0)]

theorem kink_signed_abs_min_L_anti : AntitoneOn (fun x => kink_signed_abs_min_L.eval x) (Set.Icc (-1 : ℝ) (0 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) kink_signed_abs_min_L.continuous.continuousOn
    kink_signed_abs_min_L.differentiable.differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv, kink_signed_abs_min_dL]
  exact kink_signed_abs_min_dL_nonpos x hx.1.le hx.2.le

theorem kink_signed_abs_min_R_mono : MonotoneOn (fun x => kink_signed_abs_min_R.eval x) (Set.Icc (0 : ℝ) (1 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) kink_signed_abs_min_R.continuous.continuousOn
    kink_signed_abs_min_R.differentiable.differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv, kink_signed_abs_min_dR]
  exact kink_signed_abs_min_dR_nonneg x hx.1.le hx.2.le

theorem kink_signed_abs_min_cont : kink_signed_abs_min_L.eval (0 : ℝ) = kink_signed_abs_min_R.eval (0 : ℝ) := by
  simp only [kink_signed_abs_min_L, kink_signed_abs_min_R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

theorem kink_signed_abs_min_f_anti : AntitoneOn kink_signed_abs_min_f (Set.Icc (-1 : ℝ) (0 : ℝ)) := by
  refine kink_signed_abs_min_L_anti.congr ?_
  intro x hx
  simp only [kink_signed_abs_min_f]
  rw [if_pos hx.2]

theorem kink_signed_abs_min_f_mono : MonotoneOn kink_signed_abs_min_f (Set.Icc (0 : ℝ) (1 : ℝ)) := by
  refine kink_signed_abs_min_R_mono.congr ?_
  intro x hx
  simp only [kink_signed_abs_min_f]
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h, if_pos le_rfl]; exact kink_signed_abs_min_cont.symm
  · rw [if_neg (not_le.mpr h)]

/-- The value at the kink. -/
theorem kink_signed_abs_min_value : kink_signed_abs_min_f (0 : ℝ) = (0 : ℝ) := by
  simp only [kink_signed_abs_min_f, if_pos (le_refl (0 : ℝ)), kink_signed_abs_min_L, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

/-- The minimum over `[-1, 1]` is attained at the kink: `0 ≤ f x`. -/
theorem kink_signed_abs_min : ∀ x ∈ Set.Icc (-1 : ℝ) (1 : ℝ), (0 : ℝ) ≤ kink_signed_abs_min_f x := by
  intro x hx
  rw [← kink_signed_abs_min_value]
  exact kink_min_of_anti_mono kink_signed_abs_min_f kink_signed_abs_min_f_anti kink_signed_abs_min_f_mono (by norm_num) (by norm_num) hx

/-- `min_{[a,b]} f = f(kappa) = 0` as an `IsLeast` statement. -/
theorem kink_signed_abs_min_isLeast : IsLeast (kink_signed_abs_min_f '' Set.Icc (-1 : ℝ) (1 : ℝ)) (0 : ℝ) :=
  ⟨⟨(0 : ℝ), ⟨by norm_num, by norm_num⟩, kink_signed_abs_min_value⟩, by
    rintro _ ⟨x, hx, rfl⟩; exact kink_signed_abs_min x hx⟩

/-- Nonnegativity on `[-1, 1]` (the kink value is `≥ 0`). -/
theorem kink_signed_abs_min_nonneg : ∀ x ∈ Set.Icc (-1 : ℝ) (1 : ℝ), 0 ≤ kink_signed_abs_min_f x := fun x hx =>
  le_trans (by norm_num) (kink_signed_abs_min x hx)

/-- The closed form agrees with the piecewise `f` on `[-1, 1]`. -/
theorem kink_signed_abs_min_expr_eq : ∀ x ∈ Set.Icc (-1 : ℝ) (1 : ℝ), (((1 / 2 : ℝ) * x ^ 2) + ((1 / 2 : ℝ) * |x|) + ((1 / 2 : ℝ) * x * |x|)) = kink_signed_abs_min_f x := by
  intro x hx
  simp only [kink_signed_abs_min_f]
  rcases le_or_gt x (0 : ℝ) with h | h
  · rw [if_pos h, abs_of_nonpos (show x ≤ 0 by linarith [hx.1, hx.2])]
    simp only [kink_signed_abs_min_L, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  · rw [if_neg (not_le.mpr h), abs_of_nonneg (show 0 ≤ x by linarith [hx.1, hx.2])]
    simp only [kink_signed_abs_min_R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

theorem kink_signed_abs_min_expr_min : ∀ x ∈ Set.Icc (-1 : ℝ) (1 : ℝ), (0 : ℝ) ≤ (((1 / 2 : ℝ) * x ^ 2) + ((1 / 2 : ℝ) * |x|) + ((1 / 2 : ℝ) * x * |x|)) := by
  intro x hx
  rw [kink_signed_abs_min_expr_eq x hx]
  exact kink_signed_abs_min x hx

theorem kink_signed_abs_min_expr_isLeast :
    IsLeast ((fun x : ℝ => (((1 / 2 : ℝ) * x ^ 2) + ((1 / 2 : ℝ) * |x|) + ((1 / 2 : ℝ) * x * |x|))) '' Set.Icc (-1 : ℝ) (1 : ℝ)) (0 : ℝ) := by
  refine ⟨⟨(0 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
  · simp only
    rw [kink_signed_abs_min_expr_eq (0 : ℝ) ⟨by norm_num, by norm_num⟩, kink_signed_abs_min_value]
  · rintro _ ⟨x, hx, rfl⟩
    exact kink_signed_abs_min_expr_min x hx

end CurvatureBoundary
