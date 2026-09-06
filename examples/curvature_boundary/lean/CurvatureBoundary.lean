/- telperion 0.1.6 | family CurvatureBoundary | input-hash c14f3a61a290c1b7
   7 theorems, 4 generation-time self-checks passed.
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

end CurvatureBoundary
