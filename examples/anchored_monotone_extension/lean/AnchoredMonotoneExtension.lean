/- telperion 0.1.6 | family AnchoredMonotoneExtension | input-hash a6c4c1cb03900c59
   136 theorems, 49 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace AnchoredMonotoneExtension

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Generic anchored monotone extension (emitted once per file)

A parametric recursion on finite rooted trees, its log-derivative recursion (the derivative
prelude), a two-row inductive invariant whose per-node content is finitely many polynomial
checks, the antitone normalized ratio, and the anchored extension.  Everything here is
re-derived from Mathlib; per instance only the polynomial checks remain.
conjecture1_proved = False. -/

namespace AnchoredMonotone

set_option linter.unusedVariables false

/-- Finite rooted trees: a node with `k ≥ 0` children (`k = 0` is a leaf). -/
inductive RTree : Type
  | node (k : ℕ) (cs : Fin k → RTree) : RTree

namespace RTree

/-- Number of vertices. -/
def size : RTree → ℕ
  | node _ cs => 1 + ∑ i, size (cs i)

end RTree

/-! ### Two-variable polynomials as coefficient lists `[(i, j, c), ...] ↦ Σ c x^i a^j`. -/

noncomputable def p2 : List (ℕ × ℕ × ℝ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | t :: L, x, a => t.2.2 * x ^ t.1 * a ^ t.2.1 + p2 L x a

/-- The `x`-partial derivative's coefficient list. -/
def p2dx : List (ℕ × ℕ × ℝ) → List (ℕ × ℕ × ℝ)
  | [] => []
  | t :: L => (t.1 - 1, t.2.1, t.2.2 * t.1) :: p2dx L

/-- The `a`-partial derivative's coefficient list. -/
def p2da : List (ℕ × ℕ × ℝ) → List (ℕ × ℕ × ℝ)
  | [] => []
  | t :: L => (t.1, t.2.1 - 1, t.2.2 * t.2.1) :: p2da L

/-- Chain rule for a two-variable polynomial along `t ↦ (t, U t)`. -/
theorem hasDerivAt_p2 (L : List (ℕ × ℕ × ℝ)) {U : ℝ → ℝ} {u' x : ℝ}
    (hU : HasDerivAt U u' x) :
    HasDerivAt (fun t => p2 L t (U t)) (p2 (p2dx L) x (U x) + p2 (p2da L) x (U x) * u') x := by
  induction L with
  | nil => simpa [p2, p2dx, p2da] using hasDerivAt_const x (0 : ℝ)
  | cons t L ih =>
    obtain ⟨i, j, c⟩ := t
    have h1 := ((hasDerivAt_pow i x).const_mul c).mul (hU.fun_pow j)
    have h2 : HasDerivAt (fun t => c * t ^ i * U t ^ j + p2 L t (U t)) _ x := h1.add ih
    refine h2.congr_deriv ?_
    simp only [p2, p2dx, p2da]
    ring

/-- The quotient `N / D` of two coefficient lists and its two partial derivatives. -/
noncomputable def rq (N D : List (ℕ × ℕ × ℝ)) (x a : ℝ) : ℝ := p2 N x a / p2 D x a

noncomputable def rqx (N D : List (ℕ × ℕ × ℝ)) (x a : ℝ) : ℝ :=
  (p2 (p2dx N) x a * p2 D x a - p2 N x a * p2 (p2dx D) x a) / p2 D x a ^ 2

noncomputable def rqa (N D : List (ℕ × ℕ × ℝ)) (x a : ℝ) : ℝ :=
  (p2 (p2da N) x a * p2 D x a - p2 N x a * p2 (p2da D) x a) / p2 D x a ^ 2

theorem hasDerivAt_rq (N D : List (ℕ × ℕ × ℝ)) {U : ℝ → ℝ} {u' x : ℝ}
    (hU : HasDerivAt U u' x) (hD : p2 D x (U x) ≠ 0) :
    HasDerivAt (fun t => rq N D t (U t)) (rqx N D x (U x) + rqa N D x (U x) * u') x := by
  have h := (hasDerivAt_p2 N hU).fun_div (hasDerivAt_p2 D hU) hD
  refine h.congr_deriv ?_
  simp only [rqx, rqa]
  field_simp
  ring

/-- A product of positive functions, from the log-derivatives of the factors. -/
theorem hasDerivAt_prod_log {k : ℕ} (F : Fin k → ℝ → ℝ) (e : Fin k → ℝ) {x : ℝ}
    (hF : ∀ i, HasDerivAt (F i) (F i x * e i) x) :
    HasDerivAt (fun t => ∏ i, F i t) ((∏ i, F i x) * ∑ i, e i) x := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hF i)
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [smul_eq_mul, ← Finset.prod_erase_mul _ _ hi]
  ring

/-! ### The parametric tree recursion and its log-derivative recursion -/

/-- A parametric recursion on rooted trees.  At a node with children `c`, the aggregate
`A = ∏ y_c` (`prod = true`) or `A = Σ y_c` (`prod = false`); the node value is
`T = (∏ T_c) · g(x, A)` and the message is `y = h(x, A)`, with `g = gN / gD`, `h = hN / hD`. -/
structure Rec where
  prod : Bool
  gN : List (ℕ × ℕ × ℝ)
  gD : List (ℕ × ℕ × ℝ)
  hN : List (ℕ × ℕ × ℝ)
  hD : List (ℕ × ℕ × ℝ)

namespace Rec

noncomputable def agg (R : Rec) {k : ℕ} (f : Fin k → ℝ) : ℝ :=
  if R.prod then ∏ i, f i else ∑ i, f i

/-- The derivative of the aggregate, from the children's values `f` and log-derivatives `e`. -/
noncomputable def aggD (R : Rec) {k : ℕ} (f e : Fin k → ℝ) : ℝ :=
  if R.prod then (∏ i, f i) * ∑ i, e i else ∑ i, f i * e i

/-- The aggregate's range: `0 ≤ a ≤ 1` for a product of messages in the unit interval, `0 ≤ a`
for a sum. -/
def inA (R : Rec) (a : ℝ) : Prop := 0 ≤ a ∧ (R.prod = true → a ≤ 1)

/-- The message. -/
noncomputable def y (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x => rq R.hN R.hD x (R.agg fun i => y R (cs i) x)

/-- The tree value. -/
noncomputable def T (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x => (∏ i, T R (cs i) x) * rq R.gN R.gD x (R.agg fun i => y R (cs i) x)

/-- The log-derivative of the message, by recursion. -/
noncomputable def E (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x =>
      (rqx R.hN R.hD x (R.agg fun i => y R (cs i) x) +
        rqa R.hN R.hD x (R.agg fun i => y R (cs i) x) *
          R.aggD (fun i => y R (cs i) x) (fun i => E R (cs i) x)) /
      rq R.hN R.hD x (R.agg fun i => y R (cs i) x)

/-- The log-derivative of the tree value, by recursion. -/
noncomputable def D (R : Rec) : RTree → ℝ → ℝ
  | .node _ cs, x =>
      (∑ i, D R (cs i) x) +
      (rqx R.gN R.gD x (R.agg fun i => y R (cs i) x) +
        rqa R.gN R.gD x (R.agg fun i => y R (cs i) x) *
          R.aggD (fun i => y R (cs i) x) (fun i => E R (cs i) x)) /
      rq R.gN R.gD x (R.agg fun i => y R (cs i) x)

/-- Pointwise well-posedness at `x`: the four node polynomials are positive on the aggregate
range, and in product mode the message stays `≤ 1`. -/
def Good (R : Rec) (x : ℝ) : Prop :=
  ∀ a, R.inA a → 0 < p2 R.gN x a ∧ 0 < p2 R.gD x a ∧ 0 < p2 R.hN x a ∧ 0 < p2 R.hD x a ∧
    (R.prod = true → p2 R.hN x a ≤ p2 R.hD x a)

theorem agg_inA (R : Rec) {k : ℕ} (f : Fin k → ℝ) (hpos : ∀ i, 0 < f i)
    (hle : R.prod = true → ∀ i, f i ≤ 1) : R.inA (R.agg f) := by
  unfold agg inA
  cases hp : R.prod
  · simp only [Bool.false_eq_true, if_false, false_implies, and_true]
    exact Finset.sum_nonneg (fun i _ => (hpos i).le)
  · simp only [if_true, forall_const]
    exact ⟨Finset.prod_nonneg (fun i _ => (hpos i).le),
      Finset.prod_le_one (fun i _ => (hpos i).le) (fun i _ => hle hp i)⟩

theorem hasDerivAt_agg (R : Rec) {k : ℕ} (F : Fin k → ℝ → ℝ) (e : Fin k → ℝ) {x : ℝ}
    (hF : ∀ i, HasDerivAt (F i) (F i x * e i) x) :
    HasDerivAt (fun t => R.agg fun i => F i t) (R.aggD (fun i => F i x) e) x := by
  unfold agg aggD
  cases R.prod
  · simp only [Bool.false_eq_true, if_false]
    exact HasDerivAt.fun_sum (fun i _ => hF i)
  · simp only [if_true]
    exact hasDerivAt_prod_log F e hF

/-- THE DERIVATIVE PRELUDE: under pointwise well-posedness, every message is positive (and
`≤ 1` in product mode), every tree value is positive, and the recursively
defined `E`, `D` are the log-derivatives of the message and of the tree value. -/
theorem hasDeriv_rec (R : Rec) {x : ℝ} (hG : R.Good x) :
    ∀ b : RTree, 0 < R.y b x ∧ (R.prod = true → R.y b x ≤ 1) ∧ 0 < R.T b x ∧
      HasDerivAt (R.y b) (R.y b x * R.E b x) x ∧ HasDerivAt (R.T b) (R.T b x * R.D b x) x := by
  intro b
  induction b with
  | node k cs ih =>
    set A := R.agg fun i => R.y (cs i) x with hA
    have hAin : R.inA A := R.agg_inA _ (fun i => (ih i).1) (fun hp i => (ih i).2.1 hp)
    obtain ⟨hgN, hgD, hhN, hhD, hle⟩ := hG A hAin
    have hAd := R.hasDerivAt_agg (fun i => R.y (cs i)) (fun i => R.E (cs i) x)
      (fun i => (ih i).2.2.2.1)
    have hyv : R.y (.node k cs) x = rq R.hN R.hD x A := by simp only [y, hA]
    have hTv : R.T (.node k cs) x = (∏ i, R.T (cs i) x) * rq R.gN R.gD x A := by
      simp only [T, hA]
    have hq : 0 < rq R.hN R.hD x A := div_pos hhN hhD
    have hg : 0 < rq R.gN R.gD x A := div_pos hgN hgD
    have hP : 0 < ∏ i, R.T (cs i) x := Finset.prod_pos (fun i _ => (ih i).2.2.1)
    refine ⟨hyv ▸ hq, fun hp => ?_, hTv ▸ mul_pos hP hg, ?_, ?_⟩
    · rw [hyv, rq, div_le_one hhD]; exact hle hp
    · have h := hasDerivAt_rq R.hN R.hD hAd hhD.ne'
      have hfun : R.y (.node k cs) = fun t => rq R.hN R.hD t (R.agg fun i => R.y (cs i) t) := by
        funext t; simp only [y]
      rw [hfun]
      refine h.congr_deriv ?_
      simp only [E, ← hA]
      field_simp
    · have h1 := hasDerivAt_prod_log (fun i => R.T (cs i)) (fun i => R.D (cs i) x)
        (fun i => (ih i).2.2.2.2)
      have h2 := hasDerivAt_rq R.gN R.gD hAd hgD.ne'
      have h := h1.mul h2
      have hfun : R.T (.node k cs) =
          fun t => (∏ i, R.T (cs i) t) * rq R.gN R.gD t (R.agg fun i => R.y (cs i) t) := by
        funext t; simp only [T]
      rw [hfun]
      refine h.congr_deriv ?_
      simp only [D, ← hA]
      field_simp

/-- `D` is the derivative of `log T`. -/
theorem hasDerivAt_log_T (R : Rec) {x : ℝ} (hG : R.Good x) (b : RTree) :
    HasDerivAt (fun t => Real.log (R.T b t)) (R.D b x) x := by
  obtain ⟨-, -, hT, -, hd⟩ := R.hasDeriv_rec hG b
  have := hd.log hT.ne'
  refine this.congr_deriv ?_
  field_simp

end Rec

/-! ### The normalizer, the auxiliary invariant row and the cleared node checks -/

/-- The normalizer `N(x, n) = ψ(x) ^ (ρ n)` with `ψ = pN / pD` (lists in `x` alone). -/
structure Norm where
  pN : List (ℕ × ℕ × ℝ)
  pD : List (ℕ × ℕ × ℝ)
  rho : ℝ

/-- The auxiliary invariant row `x D + μ (x E) ≤ n C + κ`, `μ = mN / mD`, `κ = kN / kD`. -/
structure Aux where
  mN : List (ℕ × ℕ × ℝ)
  mD : List (ℕ × ℕ × ℝ)
  kN : List (ℕ × ℕ × ℝ)
  kD : List (ℕ × ℕ × ℝ)

noncomputable def Norm.psi (N : Norm) (x : ℝ) : ℝ := p2 N.pN x 0 / p2 N.pD x 0
/-- `ψ'(x) pN pD / ψ = pN' pD - pN pD'`. -/
noncomputable def Norm.Px (N : Norm) (x : ℝ) : ℝ :=
  p2 (p2dx N.pN) x 0 * p2 N.pD x 0 - p2 N.pN x 0 * p2 (p2dx N.pD) x 0
/-- The per-vertex budget `C(x) = ρ x ψ'(x) / ψ(x)`, so that `x ∂ₓ log N(x, n) = n C(x)`. -/
noncomputable def Norm.C (N : Norm) (x : ℝ) : ℝ :=
  N.rho * x * N.Px x / (p2 N.pN x 0 * p2 N.pD x 0)
noncomputable def Aux.mu (I : Aux) (x : ℝ) : ℝ := p2 I.mN x 0 / p2 I.mD x 0
noncomputable def Aux.kap (I : Aux) (x : ℝ) : ℝ := p2 I.kN x 0 / p2 I.kD x 0

namespace Rec

/-- Cleared partials: `x gₓ/g = x Gx / Dg`, `g_a/g = Gq / Dg`, same for `h`. -/
noncomputable def Gx (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2dx R.gN) x a * p2 R.gD x a - p2 R.gN x a * p2 (p2dx R.gD) x a
noncomputable def Gq (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2da R.gN) x a * p2 R.gD x a - p2 R.gN x a * p2 (p2da R.gD) x a
noncomputable def Dg (R : Rec) (x a : ℝ) : ℝ := p2 R.gN x a * p2 R.gD x a
noncomputable def Hx (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2dx R.hN) x a * p2 R.hD x a - p2 R.hN x a * p2 (p2dx R.hD) x a
noncomputable def Hq (R : Rec) (x a : ℝ) : ℝ :=
  p2 (p2da R.hN) x a * p2 R.hD x a - p2 R.hN x a * p2 (p2da R.hD) x a
noncomputable def Dh (R : Rec) (x a : ℝ) : ℝ := p2 R.hN x a * p2 R.hD x a

/-- `K_ι · Dg · Dh · mD`, where `K_ι = g_a/g + ι μ h_a/h` is the coefficient of a child's
`x E` in row `ι` (row 0: `x D ≤ n C`; row 1: the auxiliary row). -/
noncomputable def KN (R : Rec) (I : Aux) (ι x a : ℝ) : ℝ :=
  p2 I.mD x 0 * R.Dh x a * R.Gq x a + ι * p2 I.mN x 0 * R.Dg x a * R.Hq x a

/-- The children's weight total: `k·A` (product mode) or `A` (sum mode). -/
noncomputable def wt (R : Rec) (k : ℕ) (a : ℝ) : ℝ := if R.prod then (k : ℝ) * a else a

/-- The cleared residual of row `ι` (must be `≥ 0`):
`(C + ικ − α − ιμγ − (κ/μ) K_ι W) · Dg Dh mD mN kD pN pD`. -/
noncomputable def Q (R : Rec) (N : Norm) (I : Aux) (ι x a w : ℝ) : ℝ :=
  N.rho * x * N.Px x * R.Dg x a * R.Dh x a * p2 I.mD x 0 * p2 I.mN x 0 * p2 I.kD x 0
  + ι * p2 I.kN x 0 * R.Dg x a * R.Dh x a * p2 I.mD x 0 * p2 I.mN x 0 * p2 N.pN x 0 * p2 N.pD x 0
  - x * R.Gx x a * R.Dh x a * p2 I.mD x 0 * p2 I.mN x 0 * p2 I.kD x 0 * p2 N.pN x 0 * p2 N.pD x 0
  - ι * p2 I.mN x 0 ^ 2 * x * R.Hx x a * R.Dg x a * p2 I.kD x 0 * p2 N.pN x 0 * p2 N.pD x 0
  - p2 I.kN x 0 * p2 I.mD x 0 * R.KN I ι x a * w * p2 N.pN x 0 * p2 N.pD x 0

end Rec

/-- The cleared residual, generically: one `field_simp` for every instance. -/
theorem resid_of_Q (ρ x Gx Gq Dg Hx Hq Dh mN mD kN kD pN pD Px ι W : ℝ)
    (hDg : 0 < Dg) (hDh : 0 < Dh) (hmN : 0 < mN) (hmD : 0 < mD) (hkD : 0 < kD)
    (hpN : 0 < pN) (hpD : 0 < pD)
    (hQ : 0 ≤ ρ * x * Px * Dg * Dh * mD * mN * kD
      + ι * kN * Dg * Dh * mD * mN * pN * pD
      - x * Gx * Dh * mD * mN * kD * pN * pD
      - ι * mN ^ 2 * x * Hx * Dg * kD * pN * pD
      - kN * mD * (mD * Dh * Gq + ι * mN * Dg * Hq) * W * pN * pD) :
    x * Gx / Dg + ι * (mN / mD) * (x * Hx / Dh)
      + (kN / kD) / (mN / mD) * ((Gq / Dg + ι * (mN / mD) * (Hq / Dh)) * W)
      ≤ ρ * x * Px / (pN * pD) + ι * (kN / kD) := by
  rw [← sub_nonneg]
  have hM : 0 < Dg * Dh * mD * mN * kD * pN * pD := by positivity
  have key : ρ * x * Px / (pN * pD) + ι * (kN / kD) - (x * Gx / Dg + ι * (mN / mD) * (x * Hx / Dh)
      + (kN / kD) / (mN / mD) * ((Gq / Dg + ι * (mN / mD) * (Hq / Dh)) * W)) =
      (ρ * x * Px * Dg * Dh * mD * mN * kD
      + ι * kN * Dg * Dh * mD * mN * pN * pD
      - x * Gx * Dh * mD * mN * kD * pN * pD
      - ι * mN ^ 2 * x * Hx * Dg * kD * pN * pD
      - kN * mD * (mD * Dh * Gq + ι * mN * Dg * Hq) * W * pN * pD) /
        (Dg * Dh * mD * mN * kD * pN * pD) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg hQ hM.le

/-- `K_ι = KN_ι / (Dg Dh mD)` in semantic form. -/
theorem K_eq (Gq Dg Hq Dh mN mD ι : ℝ) (hDg : 0 < Dg) (hDh : 0 < Dh) (hmD : 0 < mD) :
    Gq / Dg + ι * (mN / mD) * (Hq / Dh) = (mD * Dh * Gq + ι * mN * Dg * Hq) / (Dg * Dh * mD) := by
  field_simp

namespace Rec

/-- The per-instance obligations: finitely many polynomial inequalities in `(x, a[, k])`. -/
structure Checks (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) : Prop where
  x0_nonneg : 0 ≤ x0
  good : ∀ x, x0 ≤ x → R.Good x
  pos1 : ∀ x, x0 ≤ x → 0 < p2 N.pN x 0 ∧ 0 < p2 N.pD x 0 ∧ 0 < p2 I.mN x 0 ∧
    0 < p2 I.mD x 0 ∧ 0 < p2 I.kD x 0
  K0 : ∀ x a, x0 ≤ x → R.inA a → 0 ≤ R.KN I 0 x a
  K0le : ∀ x a, x0 ≤ x → R.inA a → a * R.KN I 0 x a ≤ p2 I.mN x 0 * R.Dg x a * R.Dh x a
  K1 : ∀ x a, x0 ≤ x → R.inA a → 0 ≤ R.KN I 1 x a
  K1le : ∀ x a, x0 ≤ x → R.inA a → a * R.KN I 1 x a ≤ p2 I.mN x 0 * R.Dg x a * R.Dh x a
  res0 : ∀ x a (k : ℕ), x0 ≤ x → R.inA a → 0 ≤ R.Q N I 0 x a (R.wt k a)
  res1 : ∀ x a (k : ℕ), x0 ≤ x → R.inA a → 0 ≤ R.Q N I 1 x a (R.wt k a)

/-- One child's contribution: from the two rows at the child and a weight `m ∈ [0, μ]`. -/
theorem child_step (d σ nC μ κ m : ℝ) (hμ : 0 < μ) (hm0 : 0 ≤ m) (hm1 : m ≤ μ)
    (r0 : d ≤ nC) (r1 : d + μ * σ ≤ nC + κ) : d + m * σ ≤ nC + m / μ * κ := by
  set θ := m / μ with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hm0 hμ.le
  have hθ1 : θ ≤ 1 := (div_le_one hμ).2 hm1
  have hm : m = θ * μ := by rw [hθ]; field_simp
  have e1 := mul_le_mul_of_nonneg_left r0 (sub_nonneg.2 hθ1)
  have e2 := mul_le_mul_of_nonneg_left r1 hθ0
  rw [hm]
  nlinarith [e1, e2]

/-- THE INDUCTIVE INVARIANT: for `x ≥ x0`, every tree satisfies the target row
`x D_b ≤ n_b C(x)` and the auxiliary row `x D_b + μ (x E_b) ≤ n_b C(x) + κ`. -/
theorem invariant (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0) :
    ∀ b : RTree, ∀ x, x0 ≤ x → x * R.D b x ≤ b.size * N.C x ∧
      x * R.D b x + I.mu x * (x * R.E b x) ≤ b.size * N.C x + I.kap x := by
  intro b
  induction b with
  | node k cs ih =>
    intro x hx
    have hG := hc.good x hx
    obtain ⟨hpN, hpD, hmN, hmD, hkD⟩ := hc.pos1 x hx
    have hch := fun i => R.hasDeriv_rec hG (cs i)
    set A := R.agg fun i => R.y (cs i) x with hA
    set Ad := R.aggD (fun i => R.y (cs i) x) (fun i => R.E (cs i) x) with hAd
    have hAin : R.inA A := R.agg_inA _ (fun i => (hch i).1) (fun hp i => (hch i).2.1 hp)
    obtain ⟨hgN, hgD, hhN, hhD, -⟩ := hG A hAin
    have hDg : 0 < R.Dg x A := mul_pos hgN hgD
    have hDh : 0 < R.Dh x A := mul_pos hhN hhD
    have hμ : 0 < I.mu x := div_pos hmN hmD
    -- the weights `w i` and the aggregate derivative
    let w : Fin k → ℝ := fun i => if R.prod then A else R.y (cs i) x
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i; simp only [w]; split_ifs
      · exact hAin.1
      · exact (hch i).1.le
    have hwA : ∀ i, w i ≤ A := by
      intro i; simp only [w]; split_ifs with hp
      · exact le_rfl
      · simp only [hA, agg, hp, Bool.false_eq_true, if_false]
        exact Finset.single_le_sum (f := fun j => R.y (cs j) x)
          (fun j _ => (hch j).1.le) (Finset.mem_univ i)
    have hwsum : ∑ i, w i = R.wt k A := by
      simp only [w, wt]; split_ifs
      · simp
      · simp only [hA, agg]; split_ifs; rfl
    have hxAd : x * Ad = ∑ i, w i * (x * R.E (cs i) x) := by
      simp only [hAd, aggD, w, hA, agg]
      split_ifs
      · simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
    have k1 : x * R.D (.node k cs) x = (∑ i, x * R.D (cs i) x) + x * R.Gx x A / R.Dg x A
        + R.Gq x A / R.Dg x A * (x * Ad) := by
      simp only [D, ← hA, ← hAd]
      rw [← Finset.mul_sum]
      simp only [rqx, rqa, rq, Gx, Gq, Dg]
      field_simp
      ring
    have k2 : x * R.E (.node k cs) x = x * R.Hx x A / R.Dh x A
        + R.Hq x A / R.Dh x A * (x * Ad) := by
      simp only [E, ← hA, ← hAd]
      simp only [rqx, rqa, rq, Hx, Hq, Dh]
      field_simp
    have hsize : ((RTree.node k cs).size : ℝ) = 1 + ∑ i, ((cs i).size : ℝ) := by
      simp [RTree.size]
    -- one row, uniformly in `ι ∈ {0, 1}`
    have row : ∀ ι : ℝ, (ι = 0 ∨ ι = 1) → 0 ≤ R.KN I ι x A →
        A * R.KN I ι x A ≤ p2 I.mN x 0 * R.Dg x A * R.Dh x A →
        0 ≤ R.Q N I ι x A (R.wt k A) →
        x * R.D (.node k cs) x + ι * I.mu x * (x * R.E (.node k cs) x) ≤
          (RTree.node k cs).size * N.C x + ι * I.kap x := by
      intro ι hι hK hKA hQ
      set K := R.Gq x A / R.Dg x A + ι * I.mu x * (R.Hq x A / R.Dh x A) with hK'
      have hKeq : K = R.KN I ι x A / (R.Dg x A * R.Dh x A * p2 I.mD x 0) := by
        rw [hK', Aux.mu, KN]; field_simp
      have hK0 : 0 ≤ K := by rw [hKeq]; positivity
      have hKA' : A * K ≤ I.mu x := by
        rw [hKeq, Aux.mu, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hmD]
        nlinarith [hKA, mul_pos (mul_pos hDg hDh) hmD]
      have hchild : ∀ i, x * R.D (cs i) x + K * w i * (x * R.E (cs i) x) ≤
          ((cs i).size : ℝ) * N.C x + K * w i / I.mu x * I.kap x := by
        intro i
        obtain ⟨r0, r1⟩ := ih i x hx
        exact child_step _ _ _ _ _ _ hμ (mul_nonneg hK0 (hw0 i))
          (le_trans (mul_le_mul_of_nonneg_left (hwA i) hK0) (by linarith [hKA'])) r0 r1
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hchild i)
      have hL : ∑ i, (x * R.D (cs i) x + K * w i * (x * R.E (cs i) x)) =
          (∑ i, x * R.D (cs i) x) + K * (x * Ad) := by
        rw [Finset.sum_add_distrib, hxAd, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      have hR : ∑ i, (((cs i).size : ℝ) * N.C x + K * w i / I.mu x * I.kap x) =
          (∑ i, ((cs i).size : ℝ)) * N.C x + I.kap x / I.mu x * (K * R.wt k A) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, ← hwsum, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      rw [hL, hR] at hsum
      have hres := resid_of_Q N.rho x (R.Gx x A) (R.Gq x A) (R.Dg x A) (R.Hx x A) (R.Hq x A)
        (R.Dh x A) (p2 I.mN x 0) (p2 I.mD x 0) (p2 I.kN x 0) (p2 I.kD x 0)
        (p2 N.pN x 0) (p2 N.pD x 0) (N.Px x) ι (R.wt k A) hDg hDh hmN hmD hkD hpN hpD
        (by simpa only [Q, KN] using hQ)
      have hC : N.C x = N.rho * x * N.Px x / (p2 N.pN x 0 * p2 N.pD x 0) := rfl
      rw [← hC] at hres
      simp only [Aux.mu, Aux.kap] at hres hsum ⊢
      rw [k1, k2, hsize]
      simp only [hK', Aux.mu] at hsum
      nlinarith [hres, hsum]
    refine ⟨?_, ?_⟩
    · have := row 0 (Or.inl rfl) (hc.K0 x A hx hAin) (hc.K0le x A hx hAin) (hc.res0 x A k hx hAin)
      simpa using this
    · have := row 1 (Or.inr rfl) (hc.K1 x A hx hAin) (hc.K1le x A hx hAin) (hc.res1 x A k hx hAin)
      simpa using this

end Rec

namespace Rec

theorem hasDerivAt_log_psi (N : Norm) {x : ℝ} (hpN : 0 < p2 N.pN x 0) (hpD : 0 < p2 N.pD x 0) :
    HasDerivAt (fun t => Real.log (N.psi t)) (N.Px x / (p2 N.pN x 0 * p2 N.pD x 0)) x := by
  have hU : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
  have h := (hasDerivAt_rq N.pN N.pD hU hpD.ne').log (div_pos hpN hpD).ne'
  refine (show HasDerivAt (fun t => Real.log (N.psi t)) _ x from h).congr_deriv ?_
  simp only [rqx, rqa, rq, Norm.Px]
  field_simp
  ring

/-- THE MONOTONICITY STEP: `log T_b − ρ n_b log ψ` is antitone on `Set.Ici x0`. -/
theorem logratio_antitone (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0)
    (b : RTree) :
    AntitoneOn (fun t => Real.log (R.T b t) - N.rho * b.size * Real.log (N.psi t)) (Set.Ici x0) := by
  have hd : ∀ x ∈ Set.Ici x0, HasDerivAt
      (fun t => Real.log (R.T b t) - N.rho * b.size * Real.log (N.psi t))
      (R.D b x - N.rho * b.size * (N.Px x / (p2 N.pN x 0 * p2 N.pD x 0))) x := by
    intro x hx
    obtain ⟨hpN, hpD, -⟩ := hc.pos1 x hx
    exact (R.hasDerivAt_log_T (hc.good x hx) b).sub
      ((hasDerivAt_log_psi N hpN hpD).const_mul (N.rho * b.size))
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici x0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => ?_)
  rw [interior_Ici] at hx
  have hxpos : 0 < x := lt_of_le_of_lt hc.x0_nonneg hx
  have hinv := (R.invariant N I x0 hc b x (le_of_lt hx)).1
  simp only [Norm.C] at hinv
  by_contra hneg
  rw [not_le] at hneg
  have := mul_pos hxpos hneg
  have key : x * (R.D b x - N.rho * b.size * (N.Px x / (p2 N.pN x 0 * p2 N.pD x 0))) =
      x * R.D b x - b.size * (N.rho * x * N.Px x / (p2 N.pN x 0 * p2 N.pD x 0)) := by ring
  linarith

theorem ratio_eq_exp (R : Rec) (N : Norm) {x r : ℝ} (b : RTree) (hT : 0 < R.T b x)
    (hψ : 0 < N.psi x) :
    R.T b x / N.psi x ^ r = Real.exp (Real.log (R.T b x) - r * Real.log (N.psi x)) := by
  rw [Real.exp_sub, Real.exp_log hT, Real.rpow_def_of_pos hψ, mul_comm r]

/-- `T_b / N(·, n_b)` is antitone on `Set.Ici x0` (`N = ψ ^ (ρ n)`, a real power). -/
theorem ratio_antitone (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0)
    (b : RTree) :
    AntitoneOn (fun t => R.T b t / N.psi t ^ (N.rho * b.size)) (Set.Ici x0) := by
  have hpos : ∀ x ∈ Set.Ici x0, 0 < R.T b x ∧ 0 < N.psi x := by
    intro x hx
    obtain ⟨hpN, hpD, -⟩ := hc.pos1 x hx
    exact ⟨(R.hasDeriv_rec (hc.good x hx) b).2.2.1, div_pos hpN hpD⟩
  intro u hu v hv huv
  have hΦ := R.logratio_antitone N I x0 hc b hu hv huv
  simp only at hΦ ⊢
  rw [ratio_eq_exp R N b (hpos u hu).1 (hpos u hu).2,
    ratio_eq_exp R N b (hpos v hv).1 (hpos v hv).2]
  exact Real.exp_le_exp.2 (by linarith)

/-- THE ANCHORED EXTENSION: an anchor at `xa ≥ x0` extends to every `x ≥ xa`. -/
theorem anchored_extension (R : Rec) (N : Norm) (I : Aux) (x0 : ℝ) (hc : R.Checks N I x0)
    (xa : ℝ) (hxa : x0 ≤ xa) (hanchor : ∀ b : RTree, R.T b xa ≤ N.psi xa ^ (N.rho * b.size)) :
    ∀ b : RTree, ∀ x, xa ≤ x → R.T b x ≤ N.psi x ^ (N.rho * b.size) := by
  intro b x hx
  have hψ : ∀ t, x0 ≤ t → 0 < N.psi t ^ (N.rho * b.size) := by
    intro t ht
    obtain ⟨hpN, hpD, -⟩ := hc.pos1 t ht
    exact Real.rpow_pos_of_pos (div_pos hpN hpD) _
  have hmono := R.ratio_antitone N I x0 hc b (show xa ∈ Set.Ici x0 from hxa)
    (show x ∈ Set.Ici x0 from le_trans hxa hx) hx
  simp only at hmono
  have h1 : R.T b xa / N.psi xa ^ (N.rho * b.size) ≤ 1 :=
    (div_le_one (hψ xa hxa)).2 (hanchor b)
  exact (div_le_one (hψ x (le_trans hxa hx))).1 (le_trans hmono h1)

/-- THE ANCHOR FROM A NODE CHECK at `x0` (`ρ = p / q`): `g(x0, a)^q ≤ ψ(x0)^p` on the aggregate
range gives `T_b(x0) ≤ ψ(x0)^(ρ n_b)` for every tree. -/
theorem anchor_of_node (R : Rec) (N : Norm) (x0 : ℝ) (hG : R.Good x0)
    (hpN : 0 < p2 N.pN x0 0) (hpD : 0 < p2 N.pD x0 0) (p q : ℕ) (hq : 0 < q)
    (hρ : N.rho = p / q)
    (hnode : ∀ a, R.inA a → p2 R.gN x0 a ^ q * p2 N.pD x0 0 ^ p ≤
      p2 N.pN x0 0 ^ p * p2 R.gD x0 a ^ q) :
    ∀ b : RTree, R.T b x0 ≤ N.psi x0 ^ (N.rho * b.size) := by
  have hψ : 0 < N.psi x0 := div_pos hpN hpD
  have hlog : ∀ b : RTree, Real.log (R.T b x0) ≤ N.rho * b.size * Real.log (N.psi x0) := by
    intro b
    induction b with
    | node k cs ih =>
      have hch := fun i => R.hasDeriv_rec hG (cs i)
      set A := R.agg fun i => R.y (cs i) x0 with hA
      have hAin : R.inA A := R.agg_inA _ (fun i => (hch i).1) (fun hp i => (hch i).2.1 hp)
      obtain ⟨hgN, hgD, -⟩ := hG A hAin
      have hg : 0 < rq R.gN R.gD x0 A := div_pos hgN hgD
      have hTv : R.T (.node k cs) x0 = (∏ i, R.T (cs i) x0) * rq R.gN R.gD x0 A := by
        simp only [T, hA]
      have hgq : rq R.gN R.gD x0 A ^ q ≤ N.psi x0 ^ p := by
        simp only [rq, Norm.psi, div_pow]
        rw [div_le_div_iff₀ (pow_pos hgD q) (pow_pos hpD p)]
        linarith [hnode A hAin]
      have hlg : Real.log (rq R.gN R.gD x0 A) ≤ N.rho * Real.log (N.psi x0) := by
        have h1 := Real.log_le_log (pow_pos hg q) hgq
        rw [Real.log_pow, Real.log_pow] at h1
        rw [hρ, div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hq)]
        linarith
      rw [hTv, Real.log_mul (Finset.prod_pos (fun i _ => (hch i).2.2.1)).ne' hg.ne',
        Real.log_prod (fun i _ => (hch i).2.2.1.ne')]
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ih i)
      have hsize : ((RTree.node k cs).size : ℝ) = 1 + ∑ i, ((cs i).size : ℝ) := by
        simp [RTree.size]
      rw [hsize]
      have : ∑ i, N.rho * ((cs i).size : ℝ) * Real.log (N.psi x0) =
          N.rho * (∑ i, ((cs i).size : ℝ)) * Real.log (N.psi x0) := by
        rw [Finset.mul_sum, Finset.sum_mul]
      linarith
  intro b
  have hT := (R.hasDeriv_rec hG b).2.2.1
  rw [Real.rpow_def_of_pos hψ, ← Real.exp_log hT]
  exact Real.exp_le_exp.2 (by linarith [hlog b])

end Rec

end AnchoredMonotone

open AnchoredMonotone

/-! ## Instance `hardcore`

In Lean `x` is the parameter `λ` and `a` the aggregate `A`.
Recursion (prod mode): `T_b = (∏ T_c) · g(x, a)`, `y_b = h(x, a)`, `g = a*x + 1`, `h = 1/(a*x + 1)`.
Normalizer `ψ(x)^(ρ n)`, `ψ = x + 1`, `ρ = 1`; threshold `λ0 = 0`; auxiliary row `μ = 1`, `κ = -x/(x + 1)`; anchor: node check at lam0.
conjecture1_proved = False. -/

noncomputable def hardcore_R : Rec :=
  { prod := true,
    gN := [(0, 0, (1 : ℝ)), (1, 1, (1 : ℝ))],
    gD := [(0, 0, (1 : ℝ))],
    hN := [(0, 0, (1 : ℝ))],
    hD := [(0, 0, (1 : ℝ)), (1, 1, (1 : ℝ))] }

noncomputable def hardcore_N : Norm :=
  { pN := [(0, 0, (1 : ℝ)), (1, 0, (1 : ℝ))],
    pD := [(0, 0, (1 : ℝ))],
    rho := (1 : ℝ) }

noncomputable def hardcore_I : Aux :=
  { mN := [(0, 0, (1 : ℝ))],
    mD := [(0, 0, (1 : ℝ))],
    kN := [(1, 0, (-1 : ℝ))],
    kD := [(0, 0, (1 : ℝ)), (1, 0, (1 : ℝ))] }

theorem hardcore_prod : hardcore_R.prod = true := rfl

theorem hardcore_rho : hardcore_N.rho = (1 : ℝ) := rfl

theorem hardcore_e_gN (x a : ℝ) : p2 hardcore_R.gN x a = ((1 : ℝ) + x * a) := by
  simp only [hardcore_R, p2]
  push_cast
  ring

theorem hardcore_e_gN_dx (x a : ℝ) : p2 (p2dx hardcore_R.gN) x a = (a) := by
  simp only [hardcore_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_e_gN_da (x a : ℝ) : p2 (p2da hardcore_R.gN) x a = (x) := by
  simp only [hardcore_R, p2, p2da]
  push_cast
  ring

theorem hardcore_e_gD (x a : ℝ) : p2 hardcore_R.gD x a = ((1 : ℝ)) := by
  simp only [hardcore_R, p2]
  push_cast
  ring

theorem hardcore_e_gD_dx (x a : ℝ) : p2 (p2dx hardcore_R.gD) x a = ((0 : ℝ)) := by
  simp only [hardcore_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_e_gD_da (x a : ℝ) : p2 (p2da hardcore_R.gD) x a = ((0 : ℝ)) := by
  simp only [hardcore_R, p2, p2da]
  push_cast
  ring

theorem hardcore_e_hN (x a : ℝ) : p2 hardcore_R.hN x a = ((1 : ℝ)) := by
  simp only [hardcore_R, p2]
  push_cast
  ring

theorem hardcore_e_hN_dx (x a : ℝ) : p2 (p2dx hardcore_R.hN) x a = ((0 : ℝ)) := by
  simp only [hardcore_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_e_hN_da (x a : ℝ) : p2 (p2da hardcore_R.hN) x a = ((0 : ℝ)) := by
  simp only [hardcore_R, p2, p2da]
  push_cast
  ring

theorem hardcore_e_hD (x a : ℝ) : p2 hardcore_R.hD x a = ((1 : ℝ) + x * a) := by
  simp only [hardcore_R, p2]
  push_cast
  ring

theorem hardcore_e_hD_dx (x a : ℝ) : p2 (p2dx hardcore_R.hD) x a = (a) := by
  simp only [hardcore_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_e_hD_da (x a : ℝ) : p2 (p2da hardcore_R.hD) x a = (x) := by
  simp only [hardcore_R, p2, p2da]
  push_cast
  ring

theorem hardcore_e_pN (x : ℝ) : p2 hardcore_N.pN x 0 = ((1 : ℝ) + x) := by
  simp only [hardcore_N, p2]
  push_cast
  ring

theorem hardcore_e_pN_dx (x : ℝ) : p2 (p2dx hardcore_N.pN) x 0 = ((1 : ℝ)) := by
  simp only [hardcore_N, p2, p2dx]
  push_cast
  ring

theorem hardcore_e_pD (x : ℝ) : p2 hardcore_N.pD x 0 = ((1 : ℝ)) := by
  simp only [hardcore_N, p2]
  push_cast
  ring

theorem hardcore_e_pD_dx (x : ℝ) : p2 (p2dx hardcore_N.pD) x 0 = ((0 : ℝ)) := by
  simp only [hardcore_N, p2, p2dx]
  push_cast
  ring

theorem hardcore_e_mN (x : ℝ) : p2 hardcore_I.mN x 0 = ((1 : ℝ)) := by
  simp only [hardcore_I, p2]
  push_cast
  ring

theorem hardcore_e_mD (x : ℝ) : p2 hardcore_I.mD x 0 = ((1 : ℝ)) := by
  simp only [hardcore_I, p2]
  push_cast
  ring

theorem hardcore_e_kN (x : ℝ) : p2 hardcore_I.kN x 0 = ((-1 : ℝ) * x) := by
  simp only [hardcore_I, p2]
  push_cast
  ring

theorem hardcore_e_kD (x : ℝ) : p2 hardcore_I.kD x 0 = ((1 : ℝ) + x) := by
  simp only [hardcore_I, p2]
  push_cast
  ring

/-- Well-posedness on `λ ≥ λ0`: the node polynomials are positive on the aggregate range and the message stays `≤ 1`. -/
theorem hardcore_good : ∀ x, (0 : ℝ) ≤ x → hardcore_R.Good x := by
  intro x hx a ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hardcore_e_gN]
    have hgNxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hgNas : 0 ≤ a - (0 : ℝ) := by linarith
    have hgNat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hgNxs 0) (mul_nonneg (pow_nonneg hgNas 0) (pow_nonneg hgNat 1)), mul_nonneg (pow_nonneg hgNxs 0) (mul_nonneg (pow_nonneg hgNas 1) (pow_nonneg hgNat 0)), mul_nonneg (pow_nonneg hgNxs 1) (mul_nonneg (pow_nonneg hgNas 1) (pow_nonneg hgNat 0))]
  · rw [hardcore_e_gD]
    have hgDxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hgDas : 0 ≤ a - (0 : ℝ) := by linarith
    have hgDat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hgDxs 0) (mul_nonneg (pow_nonneg hgDas 0) (pow_nonneg hgDat 0))]
  · rw [hardcore_e_hN]
    have hhNxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hhNas : 0 ≤ a - (0 : ℝ) := by linarith
    have hhNat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hhNxs 0) (mul_nonneg (pow_nonneg hhNas 0) (pow_nonneg hhNat 0))]
  · rw [hardcore_e_hD]
    have hhDxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hhDas : 0 ≤ a - (0 : ℝ) := by linarith
    have hhDat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hhDxs 0) (mul_nonneg (pow_nonneg hhDas 0) (pow_nonneg hhDat 1)), mul_nonneg (pow_nonneg hhDxs 0) (mul_nonneg (pow_nonneg hhDas 1) (pow_nonneg hhDat 0)), mul_nonneg (pow_nonneg hhDxs 1) (mul_nonneg (pow_nonneg hhDas 1) (pow_nonneg hhDat 0))]
  · intro _
    rw [hardcore_e_hN, hardcore_e_hD]
    have hhlexs : 0 ≤ x - (0 : ℝ) := by linarith
    have hhleas : 0 ≤ a - (0 : ℝ) := by linarith
    have hhleat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hhlexs 1) (mul_nonneg (pow_nonneg hhleas 1) (pow_nonneg hhleat 0))]

theorem hardcore_pos1 : ∀ x, (0 : ℝ) ≤ x → 0 < p2 hardcore_N.pN x 0 ∧ 0 < p2 hardcore_N.pD x 0 ∧
    0 < p2 hardcore_I.mN x 0 ∧ 0 < p2 hardcore_I.mD x 0 ∧ 0 < p2 hardcore_I.kD x 0 := by
  intro x hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hardcore_e_pN]
    have hpNxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hpNxs 0, pow_nonneg hpNxs 1]
  · rw [hardcore_e_pD]
    have hpDxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hpDxs 0]
  · rw [hardcore_e_mN]
    have hmNxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hmNxs 0]
  · rw [hardcore_e_mD]
    have hmDxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hmDxs 0]
  · rw [hardcore_e_kD]
    have hkDxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hkDxs 0, pow_nonneg hkDxs 1]

/-- Row 0: the child weight is `≥ 0` (`K0 ≥ 0`). -/
theorem hardcore_K0 : ∀ x a, (0 : ℝ) ≤ x → hardcore_R.inA a → 0 ≤ hardcore_R.KN hardcore_I 0 x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_rho, hardcore_e_gN, hardcore_e_gN_dx, hardcore_e_gN_da, hardcore_e_gD, hardcore_e_gD_dx, hardcore_e_gD_da, hardcore_e_hN, hardcore_e_hN_dx, hardcore_e_hN_da, hardcore_e_hD, hardcore_e_hD_dx, hardcore_e_hD_da, hardcore_e_pN, hardcore_e_pN_dx, hardcore_e_pD, hardcore_e_pD_dx, hardcore_e_mN, hardcore_e_mD, hardcore_e_kN, hardcore_e_kD]
  have hK0xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK0as : 0 ≤ a - (0 : ℝ) := by linarith
  have hK0at : 0 ≤ (1 : ℝ) - a := by linarith
  linarith [mul_nonneg (pow_nonneg hK0xs 1) (mul_nonneg (pow_nonneg hK0as 0) (pow_nonneg hK0at 1)), mul_nonneg (pow_nonneg hK0xs 1) (mul_nonneg (pow_nonneg hK0as 1) (pow_nonneg hK0at 0)), mul_nonneg (pow_nonneg hK0xs 2) (mul_nonneg (pow_nonneg hK0as 1) (pow_nonneg hK0at 0))]

/-- Row 0: the child weight is `≤ μ` (`A K0 ≤ μ`). -/
theorem hardcore_K0le : ∀ x a, (0 : ℝ) ≤ x → hardcore_R.inA a →
    a * hardcore_R.KN hardcore_I 0 x a ≤ p2 hardcore_I.mN x 0 * hardcore_R.Dg x a * hardcore_R.Dh x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_rho, hardcore_e_gN, hardcore_e_gN_dx, hardcore_e_gN_da, hardcore_e_gD, hardcore_e_gD_dx, hardcore_e_gD_da, hardcore_e_hN, hardcore_e_hN_dx, hardcore_e_hN_da, hardcore_e_hD, hardcore_e_hD_dx, hardcore_e_hD_da, hardcore_e_pN, hardcore_e_pN_dx, hardcore_e_pD, hardcore_e_pD_dx, hardcore_e_mN, hardcore_e_mD, hardcore_e_kN, hardcore_e_kD]
  have hK0lexs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK0leas : 0 ≤ a - (0 : ℝ) := by linarith
  have hK0leat : 0 ≤ (1 : ℝ) - a := by linarith
  linarith [mul_nonneg (pow_nonneg hK0lexs 0) (mul_nonneg (pow_nonneg hK0leas 0) (pow_nonneg hK0leat 1)), mul_nonneg (pow_nonneg hK0lexs 0) (mul_nonneg (pow_nonneg hK0leas 1) (pow_nonneg hK0leat 0)), mul_nonneg (pow_nonneg hK0lexs 1) (mul_nonneg (pow_nonneg hK0leas 1) (pow_nonneg hK0leat 0))]

/-- Row 0: the cleared residual of the inductive step is `≥ 0`. -/
theorem hardcore_res0 : ∀ x a (k : ℕ), (0 : ℝ) ≤ x → hardcore_R.inA a →
    0 ≤ hardcore_R.Q hardcore_N hardcore_I 0 x a (hardcore_R.wt k a) := by
  intro x a k hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [Rec.Q, Rec.wt, hardcore_prod, if_true, Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_rho, hardcore_e_gN, hardcore_e_gN_dx, hardcore_e_gN_da, hardcore_e_gD, hardcore_e_gD_dx, hardcore_e_gD_da, hardcore_e_hN, hardcore_e_hN_dx, hardcore_e_hN_da, hardcore_e_hD, hardcore_e_hD_dx, hardcore_e_hD_da, hardcore_e_pN, hardcore_e_pN_dx, hardcore_e_pD, hardcore_e_pD_dx, hardcore_e_mN, hardcore_e_mD, hardcore_e_kN, hardcore_e_kD]
  have hres0xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hres0as : 0 ≤ a - (0 : ℝ) := by linarith
  have hres0at : 0 ≤ (1 : ℝ) - a := by linarith
  have hres0ks : 0 ≤ (k : ℝ) - (0 : ℝ) := by linarith
  linarith [mul_nonneg (mul_nonneg (pow_nonneg hres0xs 1) (mul_nonneg (pow_nonneg hres0as 0) (pow_nonneg hres0at 2))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 1) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 0) (pow_nonneg hres0at 2))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 3) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 3) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 3) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 4) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1)]

/-- Row 1: the child weight is `≥ 0` (`K1 ≥ 0`). -/
theorem hardcore_K1 : ∀ x a, (0 : ℝ) ≤ x → hardcore_R.inA a → 0 ≤ hardcore_R.KN hardcore_I 1 x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_rho, hardcore_e_gN, hardcore_e_gN_dx, hardcore_e_gN_da, hardcore_e_gD, hardcore_e_gD_dx, hardcore_e_gD_da, hardcore_e_hN, hardcore_e_hN_dx, hardcore_e_hN_da, hardcore_e_hD, hardcore_e_hD_dx, hardcore_e_hD_da, hardcore_e_pN, hardcore_e_pN_dx, hardcore_e_pD, hardcore_e_pD_dx, hardcore_e_mN, hardcore_e_mD, hardcore_e_kN, hardcore_e_kD]
  have hK1xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK1as : 0 ≤ a - (0 : ℝ) := by linarith
  have hK1at : 0 ≤ (1 : ℝ) - a := by linarith
  linarith

/-- Row 1: the child weight is `≤ μ` (`A K1 ≤ μ`). -/
theorem hardcore_K1le : ∀ x a, (0 : ℝ) ≤ x → hardcore_R.inA a →
    a * hardcore_R.KN hardcore_I 1 x a ≤ p2 hardcore_I.mN x 0 * hardcore_R.Dg x a * hardcore_R.Dh x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_rho, hardcore_e_gN, hardcore_e_gN_dx, hardcore_e_gN_da, hardcore_e_gD, hardcore_e_gD_dx, hardcore_e_gD_da, hardcore_e_hN, hardcore_e_hN_dx, hardcore_e_hN_da, hardcore_e_hD, hardcore_e_hD_dx, hardcore_e_hD_da, hardcore_e_pN, hardcore_e_pN_dx, hardcore_e_pD, hardcore_e_pD_dx, hardcore_e_mN, hardcore_e_mD, hardcore_e_kN, hardcore_e_kD]
  have hK1lexs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK1leas : 0 ≤ a - (0 : ℝ) := by linarith
  have hK1leat : 0 ≤ (1 : ℝ) - a := by linarith
  linarith [mul_nonneg (pow_nonneg hK1lexs 0) (mul_nonneg (pow_nonneg hK1leas 0) (pow_nonneg hK1leat 2)), mul_nonneg (pow_nonneg hK1lexs 0) (mul_nonneg (pow_nonneg hK1leas 1) (pow_nonneg hK1leat 1)), mul_nonneg (pow_nonneg hK1lexs 0) (mul_nonneg (pow_nonneg hK1leas 2) (pow_nonneg hK1leat 0)), mul_nonneg (pow_nonneg hK1lexs 1) (mul_nonneg (pow_nonneg hK1leas 1) (pow_nonneg hK1leat 1)), mul_nonneg (pow_nonneg hK1lexs 1) (mul_nonneg (pow_nonneg hK1leas 2) (pow_nonneg hK1leat 0)), mul_nonneg (pow_nonneg hK1lexs 2) (mul_nonneg (pow_nonneg hK1leas 2) (pow_nonneg hK1leat 0))]

/-- Row 1: the cleared residual of the inductive step is `≥ 0`. -/
theorem hardcore_res1 : ∀ x a (k : ℕ), (0 : ℝ) ≤ x → hardcore_R.inA a →
    0 ≤ hardcore_R.Q hardcore_N hardcore_I 1 x a (hardcore_R.wt k a) := by
  intro x a k hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [Rec.Q, Rec.wt, hardcore_prod, if_true, Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_rho, hardcore_e_gN, hardcore_e_gN_dx, hardcore_e_gN_da, hardcore_e_gD, hardcore_e_gD_dx, hardcore_e_gD_da, hardcore_e_hN, hardcore_e_hN_dx, hardcore_e_hN_da, hardcore_e_hD, hardcore_e_hD_dx, hardcore_e_hD_da, hardcore_e_pN, hardcore_e_pN_dx, hardcore_e_pD, hardcore_e_pD_dx, hardcore_e_mN, hardcore_e_mD, hardcore_e_kN, hardcore_e_kD]
  have hres1xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hres1as : 0 ≤ a - (0 : ℝ) := by linarith
  have hres1at : 0 ≤ (1 : ℝ) - a := by linarith
  have hres1ks : 0 ≤ (k : ℝ) - (0 : ℝ) := by linarith
  linarith

/-- The per-instance obligations, assembled. -/
theorem hardcore_checks : hardcore_R.Checks hardcore_N hardcore_I (0 : ℝ) where
  x0_nonneg := by norm_num
  good := hardcore_good
  pos1 := hardcore_pos1
  K0 := hardcore_K0
  K0le := hardcore_K0le
  K1 := hardcore_K1
  K1le := hardcore_K1le
  res0 := hardcore_res0
  res1 := hardcore_res1

/-- (1) The derivative prelude: `D` is the log-derivative of `T` on `λ ≥ λ0`. -/
theorem hardcore_logderiv : ∀ b : RTree, ∀ x, (0 : ℝ) ≤ x →
    HasDerivAt (fun t => Real.log (hardcore_R.T b t)) (hardcore_R.D b x) x :=
  fun b x hx => hardcore_R.hasDerivAt_log_T (hardcore_good x hx) b

/-- (2) The derivative bound `λ D_b ≤ n_b c(λ)` on `λ ≥ λ0`. -/
theorem hardcore_deriv_bound : ∀ b : RTree, ∀ x, (0 : ℝ) ≤ x →
    x * hardcore_R.D b x ≤ b.size * hardcore_N.C x :=
  fun b x hx => (Rec.invariant _ _ _ _ hardcore_checks b x hx).1

/-- (2) `T_b / ψ^(ρ n_b)` is antitone on `λ ≥ λ0`. -/
theorem hardcore_antitone : ∀ b : RTree,
    AntitoneOn (fun t => hardcore_R.T b t / hardcore_N.psi t ^ (hardcore_N.rho * b.size)) (Set.Ici (0 : ℝ)) :=
  Rec.ratio_antitone _ _ _ _ hardcore_checks

/-- The anchor node check at `λ0`: `g(λ0, A)^1 ≤ ψ(λ0)^1`. -/
theorem hardcore_node : ∀ a, hardcore_R.inA a → p2 hardcore_R.gN (0 : ℝ) a ^ 1 * p2 hardcore_N.pD (0 : ℝ) 0 ^ 1 ≤
    p2 hardcore_N.pN (0 : ℝ) 0 ^ 1 * p2 hardcore_R.gD (0 : ℝ) a ^ 1 := by
  intro a ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_prod
  simp only [hardcore_e_gN, hardcore_e_gN_dx, hardcore_e_gN_da, hardcore_e_gD, hardcore_e_gD_dx, hardcore_e_gD_da, hardcore_e_hN, hardcore_e_hN_dx, hardcore_e_hN_da, hardcore_e_hD, hardcore_e_hD_dx, hardcore_e_hD_da, hardcore_e_pN, hardcore_e_pN_dx, hardcore_e_pD, hardcore_e_pD_dx, hardcore_e_mN, hardcore_e_mD, hardcore_e_kN, hardcore_e_kD]
  have hanchoras : 0 ≤ a - (0 : ℝ) := by linarith
  have hanchorat : 0 ≤ (1 : ℝ) - a := by linarith
  linarith

/-- (3) The anchor: `T_b(λ0) ≤ ψ(λ0)^(ρ n_b)` for every tree. -/
theorem hardcore_anchor : ∀ b : RTree, hardcore_R.T b (0 : ℝ) ≤ hardcore_N.psi (0 : ℝ) ^ (hardcore_N.rho * b.size) := by
  obtain ⟨hpN, hpD, -⟩ := hardcore_pos1 (0 : ℝ) le_rfl
  exact Rec.anchor_of_node _ _ _ (hardcore_good _ le_rfl) hpN hpD 1 1 (by norm_num) (by rw [hardcore_rho]; norm_num) hardcore_node

/-- (3) THE ANCHORED EXTENSION: `T_b(λ) ≤ ψ(λ)^(ρ n_b)` for every tree and every `λ ≥ λ0`. -/
theorem hardcore : ∀ b : RTree, ∀ x, (0 : ℝ) ≤ x →
    hardcore_R.T b x ≤ hardcore_N.psi x ^ (hardcore_N.rho * b.size) :=
  Rec.anchored_extension _ _ _ _ hardcore_checks (0 : ℝ) le_rfl hardcore_anchor

theorem hardcore_psi (x : ℝ) : hardcore_N.psi x = ((1 : ℝ) + x) := by
  simp only [Norm.psi, hardcore_e_pN, hardcore_e_pD]
  ring

/-- The extension with a natural-number power: `T_b(λ) ≤ ((1 : ℝ) + x) ^ n_b`. -/
theorem hardcore_pow :
    ∀ b : RTree, ∀ x, (0 : ℝ) ≤ x → hardcore_R.T b x ≤ ((1 : ℝ) + x) ^ b.size := by
  intro b x hx
  have h := hardcore b x hx
  rwa [hardcore_psi, hardcore_rho, one_mul, Real.rpow_natCast] at h

/-- The antitone ratio with a natural-number power: `T_b / ((1 : ℝ) + x) ^ n_b`. -/
theorem hardcore_antitone_pow : ∀ b : RTree,
    AntitoneOn (fun t => hardcore_R.T b t / ((1 : ℝ) + t) ^ b.size) (Set.Ici (0 : ℝ)) := by
  intro b u hu v hv huv
  have h := hardcore_antitone b hu hv huv
  simp only [hardcore_psi, hardcore_rho, one_mul, Real.rpow_natCast] at h
  exact h

/-- Sanity: the recursion on `RTree.node 0 Fin.elim0`. -/
theorem hardcore_sanity0 (x : ℝ) (_hx : 0 ≤ x) : hardcore_R.T (RTree.node 0 Fin.elim0) x = 1 + x := by
  simp [Rec.T, Rec.y, Rec.agg, rq, p2, hardcore_R]
  all_goals (try field_simp)
  all_goals ring

/-- Sanity: the recursion on `RTree.node 1 (fun _ => RTree.node 0 Fin.elim0)`. -/
theorem hardcore_sanity1 (x : ℝ) (_hx : 0 ≤ x) : hardcore_R.T (RTree.node 1 (fun _ => RTree.node 0 Fin.elim0)) x = 1 + 2 * x := by
  simp [Rec.T, Rec.y, Rec.agg, rq, p2, hardcore_R]
  all_goals (try field_simp)
  all_goals ring

/-! ## Instance `matching_sum`

In Lean `x` is the parameter `λ` and `a` the aggregate `A`.
Recursion (sum mode): `T_b = (∏ T_c) · g(x, a)`, `y_b = h(x, a)`, `g = a*x + 1`, `h = 1/(a*x + 1)`.
Normalizer `ψ(x)^(ρ n)`, `ψ = x + 1`, `ρ = 1`; threshold `λ0 = 1`; auxiliary row `μ = 1`, `κ = -x/(x + 1)`; anchor: hypothesis at lam = 1.
conjecture1_proved = False. -/

noncomputable def matching_sum_R : Rec :=
  { prod := false,
    gN := [(0, 0, (1 : ℝ)), (1, 1, (1 : ℝ))],
    gD := [(0, 0, (1 : ℝ))],
    hN := [(0, 0, (1 : ℝ))],
    hD := [(0, 0, (1 : ℝ)), (1, 1, (1 : ℝ))] }

noncomputable def matching_sum_N : Norm :=
  { pN := [(0, 0, (1 : ℝ)), (1, 0, (1 : ℝ))],
    pD := [(0, 0, (1 : ℝ))],
    rho := (1 : ℝ) }

noncomputable def matching_sum_I : Aux :=
  { mN := [(0, 0, (1 : ℝ))],
    mD := [(0, 0, (1 : ℝ))],
    kN := [(1, 0, (-1 : ℝ))],
    kD := [(0, 0, (1 : ℝ)), (1, 0, (1 : ℝ))] }

theorem matching_sum_prod : matching_sum_R.prod = false := rfl

theorem matching_sum_rho : matching_sum_N.rho = (1 : ℝ) := rfl

theorem matching_sum_e_gN (x a : ℝ) : p2 matching_sum_R.gN x a = ((1 : ℝ) + x * a) := by
  simp only [matching_sum_R, p2]
  push_cast
  ring

theorem matching_sum_e_gN_dx (x a : ℝ) : p2 (p2dx matching_sum_R.gN) x a = (a) := by
  simp only [matching_sum_R, p2, p2dx]
  push_cast
  ring

theorem matching_sum_e_gN_da (x a : ℝ) : p2 (p2da matching_sum_R.gN) x a = (x) := by
  simp only [matching_sum_R, p2, p2da]
  push_cast
  ring

theorem matching_sum_e_gD (x a : ℝ) : p2 matching_sum_R.gD x a = ((1 : ℝ)) := by
  simp only [matching_sum_R, p2]
  push_cast
  ring

theorem matching_sum_e_gD_dx (x a : ℝ) : p2 (p2dx matching_sum_R.gD) x a = ((0 : ℝ)) := by
  simp only [matching_sum_R, p2, p2dx]
  push_cast
  ring

theorem matching_sum_e_gD_da (x a : ℝ) : p2 (p2da matching_sum_R.gD) x a = ((0 : ℝ)) := by
  simp only [matching_sum_R, p2, p2da]
  push_cast
  ring

theorem matching_sum_e_hN (x a : ℝ) : p2 matching_sum_R.hN x a = ((1 : ℝ)) := by
  simp only [matching_sum_R, p2]
  push_cast
  ring

theorem matching_sum_e_hN_dx (x a : ℝ) : p2 (p2dx matching_sum_R.hN) x a = ((0 : ℝ)) := by
  simp only [matching_sum_R, p2, p2dx]
  push_cast
  ring

theorem matching_sum_e_hN_da (x a : ℝ) : p2 (p2da matching_sum_R.hN) x a = ((0 : ℝ)) := by
  simp only [matching_sum_R, p2, p2da]
  push_cast
  ring

theorem matching_sum_e_hD (x a : ℝ) : p2 matching_sum_R.hD x a = ((1 : ℝ) + x * a) := by
  simp only [matching_sum_R, p2]
  push_cast
  ring

theorem matching_sum_e_hD_dx (x a : ℝ) : p2 (p2dx matching_sum_R.hD) x a = (a) := by
  simp only [matching_sum_R, p2, p2dx]
  push_cast
  ring

theorem matching_sum_e_hD_da (x a : ℝ) : p2 (p2da matching_sum_R.hD) x a = (x) := by
  simp only [matching_sum_R, p2, p2da]
  push_cast
  ring

theorem matching_sum_e_pN (x : ℝ) : p2 matching_sum_N.pN x 0 = ((1 : ℝ) + x) := by
  simp only [matching_sum_N, p2]
  push_cast
  ring

theorem matching_sum_e_pN_dx (x : ℝ) : p2 (p2dx matching_sum_N.pN) x 0 = ((1 : ℝ)) := by
  simp only [matching_sum_N, p2, p2dx]
  push_cast
  ring

theorem matching_sum_e_pD (x : ℝ) : p2 matching_sum_N.pD x 0 = ((1 : ℝ)) := by
  simp only [matching_sum_N, p2]
  push_cast
  ring

theorem matching_sum_e_pD_dx (x : ℝ) : p2 (p2dx matching_sum_N.pD) x 0 = ((0 : ℝ)) := by
  simp only [matching_sum_N, p2, p2dx]
  push_cast
  ring

theorem matching_sum_e_mN (x : ℝ) : p2 matching_sum_I.mN x 0 = ((1 : ℝ)) := by
  simp only [matching_sum_I, p2]
  push_cast
  ring

theorem matching_sum_e_mD (x : ℝ) : p2 matching_sum_I.mD x 0 = ((1 : ℝ)) := by
  simp only [matching_sum_I, p2]
  push_cast
  ring

theorem matching_sum_e_kN (x : ℝ) : p2 matching_sum_I.kN x 0 = ((-1 : ℝ) * x) := by
  simp only [matching_sum_I, p2]
  push_cast
  ring

theorem matching_sum_e_kD (x : ℝ) : p2 matching_sum_I.kD x 0 = ((1 : ℝ) + x) := by
  simp only [matching_sum_I, p2]
  push_cast
  ring

/-- Well-posedness on `λ ≥ λ0`: the node polynomials are positive on the aggregate range. -/
theorem matching_sum_good : ∀ x, (1 : ℝ) ≤ x → matching_sum_R.Good x := by
  intro x hx a ha
  obtain ⟨ha0, ha1⟩ := ha
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [matching_sum_e_gN]
    have hgNxs : 0 ≤ x - (1 : ℝ) := by linarith
    have hgNas : 0 ≤ a - (0 : ℝ) := by linarith
    linarith [mul_nonneg (pow_nonneg hgNxs 0) (pow_nonneg hgNas 0), mul_nonneg (pow_nonneg hgNxs 0) (pow_nonneg hgNas 1), mul_nonneg (pow_nonneg hgNxs 1) (pow_nonneg hgNas 1)]
  · rw [matching_sum_e_gD]
    have hgDxs : 0 ≤ x - (1 : ℝ) := by linarith
    have hgDas : 0 ≤ a - (0 : ℝ) := by linarith
    linarith [mul_nonneg (pow_nonneg hgDxs 0) (pow_nonneg hgDas 0)]
  · rw [matching_sum_e_hN]
    have hhNxs : 0 ≤ x - (1 : ℝ) := by linarith
    have hhNas : 0 ≤ a - (0 : ℝ) := by linarith
    linarith [mul_nonneg (pow_nonneg hhNxs 0) (pow_nonneg hhNas 0)]
  · rw [matching_sum_e_hD]
    have hhDxs : 0 ≤ x - (1 : ℝ) := by linarith
    have hhDas : 0 ≤ a - (0 : ℝ) := by linarith
    linarith [mul_nonneg (pow_nonneg hhDxs 0) (pow_nonneg hhDas 0), mul_nonneg (pow_nonneg hhDxs 0) (pow_nonneg hhDas 1), mul_nonneg (pow_nonneg hhDxs 1) (pow_nonneg hhDas 1)]
  · intro h
    exact absurd h (by simp [matching_sum_R])

theorem matching_sum_pos1 : ∀ x, (1 : ℝ) ≤ x → 0 < p2 matching_sum_N.pN x 0 ∧ 0 < p2 matching_sum_N.pD x 0 ∧
    0 < p2 matching_sum_I.mN x 0 ∧ 0 < p2 matching_sum_I.mD x 0 ∧ 0 < p2 matching_sum_I.kD x 0 := by
  intro x hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [matching_sum_e_pN]
    have hpNxs : 0 ≤ x - (1 : ℝ) := by linarith
    linarith [pow_nonneg hpNxs 0, pow_nonneg hpNxs 1]
  · rw [matching_sum_e_pD]
    have hpDxs : 0 ≤ x - (1 : ℝ) := by linarith
    linarith [pow_nonneg hpDxs 0]
  · rw [matching_sum_e_mN]
    have hmNxs : 0 ≤ x - (1 : ℝ) := by linarith
    linarith [pow_nonneg hmNxs 0]
  · rw [matching_sum_e_mD]
    have hmDxs : 0 ≤ x - (1 : ℝ) := by linarith
    linarith [pow_nonneg hmDxs 0]
  · rw [matching_sum_e_kD]
    have hkDxs : 0 ≤ x - (1 : ℝ) := by linarith
    linarith [pow_nonneg hkDxs 0, pow_nonneg hkDxs 1]

/-- Row 0: the child weight is `≥ 0` (`K0 ≥ 0`). -/
theorem matching_sum_K0 : ∀ x a, (1 : ℝ) ≤ x → matching_sum_R.inA a → 0 ≤ matching_sum_R.KN matching_sum_I 0 x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, matching_sum_rho, matching_sum_e_gN, matching_sum_e_gN_dx, matching_sum_e_gN_da, matching_sum_e_gD, matching_sum_e_gD_dx, matching_sum_e_gD_da, matching_sum_e_hN, matching_sum_e_hN_dx, matching_sum_e_hN_da, matching_sum_e_hD, matching_sum_e_hD_dx, matching_sum_e_hD_da, matching_sum_e_pN, matching_sum_e_pN_dx, matching_sum_e_pD, matching_sum_e_pD_dx, matching_sum_e_mN, matching_sum_e_mD, matching_sum_e_kN, matching_sum_e_kD]
  have hK0xs : 0 ≤ x - (1 : ℝ) := by linarith
  have hK0as : 0 ≤ a - (0 : ℝ) := by linarith
  linarith [mul_nonneg (pow_nonneg hK0xs 0) (pow_nonneg hK0as 0), mul_nonneg (pow_nonneg hK0xs 0) (pow_nonneg hK0as 1), mul_nonneg (pow_nonneg hK0xs 1) (pow_nonneg hK0as 0), mul_nonneg (pow_nonneg hK0xs 1) (pow_nonneg hK0as 1), mul_nonneg (pow_nonneg hK0xs 2) (pow_nonneg hK0as 1)]

/-- Row 0: the child weight is `≤ μ` (`A K0 ≤ μ`). -/
theorem matching_sum_K0le : ∀ x a, (1 : ℝ) ≤ x → matching_sum_R.inA a →
    a * matching_sum_R.KN matching_sum_I 0 x a ≤ p2 matching_sum_I.mN x 0 * matching_sum_R.Dg x a * matching_sum_R.Dh x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, matching_sum_rho, matching_sum_e_gN, matching_sum_e_gN_dx, matching_sum_e_gN_da, matching_sum_e_gD, matching_sum_e_gD_dx, matching_sum_e_gD_da, matching_sum_e_hN, matching_sum_e_hN_dx, matching_sum_e_hN_da, matching_sum_e_hD, matching_sum_e_hD_dx, matching_sum_e_hD_da, matching_sum_e_pN, matching_sum_e_pN_dx, matching_sum_e_pD, matching_sum_e_pD_dx, matching_sum_e_mN, matching_sum_e_mD, matching_sum_e_kN, matching_sum_e_kD]
  have hK0lexs : 0 ≤ x - (1 : ℝ) := by linarith
  have hK0leas : 0 ≤ a - (0 : ℝ) := by linarith
  linarith [mul_nonneg (pow_nonneg hK0lexs 0) (pow_nonneg hK0leas 0), mul_nonneg (pow_nonneg hK0lexs 0) (pow_nonneg hK0leas 1), mul_nonneg (pow_nonneg hK0lexs 1) (pow_nonneg hK0leas 1)]

/-- Row 0: the cleared residual of the inductive step is `≥ 0`. -/
theorem matching_sum_res0 : ∀ x a (k : ℕ), (1 : ℝ) ≤ x → matching_sum_R.inA a →
    0 ≤ matching_sum_R.Q matching_sum_N matching_sum_I 0 x a (matching_sum_R.wt k a) := by
  intro x a k hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [Rec.Q, Rec.wt, matching_sum_prod, Bool.false_eq_true, if_false, Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, matching_sum_rho, matching_sum_e_gN, matching_sum_e_gN_dx, matching_sum_e_gN_da, matching_sum_e_gD, matching_sum_e_gD_dx, matching_sum_e_gD_da, matching_sum_e_hN, matching_sum_e_hN_dx, matching_sum_e_hN_da, matching_sum_e_hD, matching_sum_e_hD_dx, matching_sum_e_hD_da, matching_sum_e_pN, matching_sum_e_pN_dx, matching_sum_e_pD, matching_sum_e_pD_dx, matching_sum_e_mN, matching_sum_e_mD, matching_sum_e_kN, matching_sum_e_kD]
  have hres0xs : 0 ≤ x - (1 : ℝ) := by linarith
  have hres0as : 0 ≤ a - (0 : ℝ) := by linarith
  linarith [mul_nonneg (pow_nonneg hres0xs 0) (pow_nonneg hres0as 0), mul_nonneg (pow_nonneg hres0xs 0) (pow_nonneg hres0as 1), mul_nonneg (pow_nonneg hres0xs 1) (pow_nonneg hres0as 0), mul_nonneg (pow_nonneg hres0xs 1) (pow_nonneg hres0as 1), mul_nonneg (pow_nonneg hres0xs 1) (pow_nonneg hres0as 2), mul_nonneg (pow_nonneg hres0xs 2) (pow_nonneg hres0as 0), mul_nonneg (pow_nonneg hres0xs 2) (pow_nonneg hres0as 1), mul_nonneg (pow_nonneg hres0xs 2) (pow_nonneg hres0as 2), mul_nonneg (pow_nonneg hres0xs 3) (pow_nonneg hres0as 1), mul_nonneg (pow_nonneg hres0xs 3) (pow_nonneg hres0as 2), mul_nonneg (pow_nonneg hres0xs 4) (pow_nonneg hres0as 2)]

/-- Row 1: the child weight is `≥ 0` (`K1 ≥ 0`). -/
theorem matching_sum_K1 : ∀ x a, (1 : ℝ) ≤ x → matching_sum_R.inA a → 0 ≤ matching_sum_R.KN matching_sum_I 1 x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, matching_sum_rho, matching_sum_e_gN, matching_sum_e_gN_dx, matching_sum_e_gN_da, matching_sum_e_gD, matching_sum_e_gD_dx, matching_sum_e_gD_da, matching_sum_e_hN, matching_sum_e_hN_dx, matching_sum_e_hN_da, matching_sum_e_hD, matching_sum_e_hD_dx, matching_sum_e_hD_da, matching_sum_e_pN, matching_sum_e_pN_dx, matching_sum_e_pD, matching_sum_e_pD_dx, matching_sum_e_mN, matching_sum_e_mD, matching_sum_e_kN, matching_sum_e_kD]
  have hK1xs : 0 ≤ x - (1 : ℝ) := by linarith
  have hK1as : 0 ≤ a - (0 : ℝ) := by linarith
  linarith

/-- Row 1: the child weight is `≤ μ` (`A K1 ≤ μ`). -/
theorem matching_sum_K1le : ∀ x a, (1 : ℝ) ≤ x → matching_sum_R.inA a →
    a * matching_sum_R.KN matching_sum_I 1 x a ≤ p2 matching_sum_I.mN x 0 * matching_sum_R.Dg x a * matching_sum_R.Dh x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, matching_sum_rho, matching_sum_e_gN, matching_sum_e_gN_dx, matching_sum_e_gN_da, matching_sum_e_gD, matching_sum_e_gD_dx, matching_sum_e_gD_da, matching_sum_e_hN, matching_sum_e_hN_dx, matching_sum_e_hN_da, matching_sum_e_hD, matching_sum_e_hD_dx, matching_sum_e_hD_da, matching_sum_e_pN, matching_sum_e_pN_dx, matching_sum_e_pD, matching_sum_e_pD_dx, matching_sum_e_mN, matching_sum_e_mD, matching_sum_e_kN, matching_sum_e_kD]
  have hK1lexs : 0 ≤ x - (1 : ℝ) := by linarith
  have hK1leas : 0 ≤ a - (0 : ℝ) := by linarith
  linarith [mul_nonneg (pow_nonneg hK1lexs 0) (pow_nonneg hK1leas 0), mul_nonneg (pow_nonneg hK1lexs 0) (pow_nonneg hK1leas 1), mul_nonneg (pow_nonneg hK1lexs 0) (pow_nonneg hK1leas 2), mul_nonneg (pow_nonneg hK1lexs 1) (pow_nonneg hK1leas 1), mul_nonneg (pow_nonneg hK1lexs 1) (pow_nonneg hK1leas 2), mul_nonneg (pow_nonneg hK1lexs 2) (pow_nonneg hK1leas 2)]

/-- Row 1: the cleared residual of the inductive step is `≥ 0`. -/
theorem matching_sum_res1 : ∀ x a (k : ℕ), (1 : ℝ) ≤ x → matching_sum_R.inA a →
    0 ≤ matching_sum_R.Q matching_sum_N matching_sum_I 1 x a (matching_sum_R.wt k a) := by
  intro x a k hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [Rec.Q, Rec.wt, matching_sum_prod, Bool.false_eq_true, if_false, Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, matching_sum_rho, matching_sum_e_gN, matching_sum_e_gN_dx, matching_sum_e_gN_da, matching_sum_e_gD, matching_sum_e_gD_dx, matching_sum_e_gD_da, matching_sum_e_hN, matching_sum_e_hN_dx, matching_sum_e_hN_da, matching_sum_e_hD, matching_sum_e_hD_dx, matching_sum_e_hD_da, matching_sum_e_pN, matching_sum_e_pN_dx, matching_sum_e_pD, matching_sum_e_pD_dx, matching_sum_e_mN, matching_sum_e_mD, matching_sum_e_kN, matching_sum_e_kD]
  have hres1xs : 0 ≤ x - (1 : ℝ) := by linarith
  have hres1as : 0 ≤ a - (0 : ℝ) := by linarith
  linarith

/-- The per-instance obligations, assembled. -/
theorem matching_sum_checks : matching_sum_R.Checks matching_sum_N matching_sum_I (1 : ℝ) where
  x0_nonneg := by norm_num
  good := matching_sum_good
  pos1 := matching_sum_pos1
  K0 := matching_sum_K0
  K0le := matching_sum_K0le
  K1 := matching_sum_K1
  K1le := matching_sum_K1le
  res0 := matching_sum_res0
  res1 := matching_sum_res1

/-- (1) The derivative prelude: `D` is the log-derivative of `T` on `λ ≥ λ0`. -/
theorem matching_sum_logderiv : ∀ b : RTree, ∀ x, (1 : ℝ) ≤ x →
    HasDerivAt (fun t => Real.log (matching_sum_R.T b t)) (matching_sum_R.D b x) x :=
  fun b x hx => matching_sum_R.hasDerivAt_log_T (matching_sum_good x hx) b

/-- (2) The derivative bound `λ D_b ≤ n_b c(λ)` on `λ ≥ λ0`. -/
theorem matching_sum_deriv_bound : ∀ b : RTree, ∀ x, (1 : ℝ) ≤ x →
    x * matching_sum_R.D b x ≤ b.size * matching_sum_N.C x :=
  fun b x hx => (Rec.invariant _ _ _ _ matching_sum_checks b x hx).1

/-- (2) `T_b / ψ^(ρ n_b)` is antitone on `λ ≥ λ0`. -/
theorem matching_sum_antitone : ∀ b : RTree,
    AntitoneOn (fun t => matching_sum_R.T b t / matching_sum_N.psi t ^ (matching_sum_N.rho * b.size)) (Set.Ici (1 : ℝ)) :=
  Rec.ratio_antitone _ _ _ _ matching_sum_checks

/-- (3) THE ANCHORED EXTENSION from an anchor at `λ = 1` (a hypothesis, certified elsewhere): `T_b(λ) ≤ ψ(λ)^(ρ n_b)` for every tree and every `λ ≥ 1`. -/
theorem matching_sum (hanchor : ∀ b : RTree, matching_sum_R.T b (1 : ℝ) ≤ matching_sum_N.psi (1 : ℝ) ^ (matching_sum_N.rho * b.size)) :
    ∀ b : RTree, ∀ x, (1 : ℝ) ≤ x → matching_sum_R.T b x ≤ matching_sum_N.psi x ^ (matching_sum_N.rho * b.size) :=
  Rec.anchored_extension _ _ _ _ matching_sum_checks (1 : ℝ) (by norm_num) hanchor

theorem matching_sum_psi (x : ℝ) : matching_sum_N.psi x = ((1 : ℝ) + x) := by
  simp only [Norm.psi, matching_sum_e_pN, matching_sum_e_pD]
  ring

/-- The extension with a natural-number power: `T_b(λ) ≤ ((1 : ℝ) + x) ^ n_b`. -/
theorem matching_sum_pow (hanchor : ∀ b : RTree, matching_sum_R.T b (1 : ℝ) ≤ (2 : ℝ) ^ b.size) :
    ∀ b : RTree, ∀ x, (1 : ℝ) ≤ x → matching_sum_R.T b x ≤ ((1 : ℝ) + x) ^ b.size := by
  intro b x hx
  have h := matching_sum (fun b => by
    rw [matching_sum_psi, matching_sum_rho, one_mul, Real.rpow_natCast]
    convert hanchor b using 2 <;> norm_num) b x hx
  rwa [matching_sum_psi, matching_sum_rho, one_mul, Real.rpow_natCast] at h

/-- The antitone ratio with a natural-number power: `T_b / ((1 : ℝ) + x) ^ n_b`. -/
theorem matching_sum_antitone_pow : ∀ b : RTree,
    AntitoneOn (fun t => matching_sum_R.T b t / ((1 : ℝ) + t) ^ b.size) (Set.Ici (1 : ℝ)) := by
  intro b u hu v hv huv
  have h := matching_sum_antitone b hu hv huv
  simp only [matching_sum_psi, matching_sum_rho, one_mul, Real.rpow_natCast] at h
  exact h

/-- Sanity: the recursion on `RTree.node 0 Fin.elim0`. -/
theorem matching_sum_sanity0 (x : ℝ) (_hx : 0 ≤ x) : matching_sum_R.T (RTree.node 0 Fin.elim0) x = 1 := by
  simp [Rec.T, Rec.y, Rec.agg, rq, p2, matching_sum_R]
  all_goals (try field_simp)
  all_goals ring

/-- Sanity: the recursion on `RTree.node 1 (fun _ => RTree.node 0 Fin.elim0)`. -/
theorem matching_sum_sanity1 (x : ℝ) (_hx : 0 ≤ x) : matching_sum_R.T (RTree.node 1 (fun _ => RTree.node 0 Fin.elim0)) x = 1 + x := by
  simp [Rec.T, Rec.y, Rec.agg, rq, p2, matching_sum_R]
  all_goals (try field_simp)
  all_goals ring

/-! ## Instance `hardcore_cube_root`

In Lean `x` is the parameter `λ` and `a` the aggregate `A`.
Recursion (prod mode): `T_b = (∏ T_c) · g(x, a)`, `y_b = h(x, a)`, `g = a*x + 1`, `h = 1/(a*x + 1)`.
Normalizer `ψ(x)^(ρ n)`, `ψ = (x + 1)**3`, `ρ = 1/3`; threshold `λ0 = 0`; auxiliary row `μ = 1`, `κ = -x/(x + 1)`; anchor: node check at lam0.
conjecture1_proved = False. -/

noncomputable def hardcore_cube_root_R : Rec :=
  { prod := true,
    gN := [(0, 0, (1 : ℝ)), (1, 1, (1 : ℝ))],
    gD := [(0, 0, (1 : ℝ))],
    hN := [(0, 0, (1 : ℝ))],
    hD := [(0, 0, (1 : ℝ)), (1, 1, (1 : ℝ))] }

noncomputable def hardcore_cube_root_N : Norm :=
  { pN := [(0, 0, (1 : ℝ)), (1, 0, (3 : ℝ)), (2, 0, (3 : ℝ)), (3, 0, (1 : ℝ))],
    pD := [(0, 0, (1 : ℝ))],
    rho := (1 / 3 : ℝ) }

noncomputable def hardcore_cube_root_I : Aux :=
  { mN := [(0, 0, (1 : ℝ))],
    mD := [(0, 0, (1 : ℝ))],
    kN := [(1, 0, (-1 : ℝ))],
    kD := [(0, 0, (1 : ℝ)), (1, 0, (1 : ℝ))] }

theorem hardcore_cube_root_prod : hardcore_cube_root_R.prod = true := rfl

theorem hardcore_cube_root_rho : hardcore_cube_root_N.rho = (1 / 3 : ℝ) := rfl

theorem hardcore_cube_root_e_gN (x a : ℝ) : p2 hardcore_cube_root_R.gN x a = ((1 : ℝ) + x * a) := by
  simp only [hardcore_cube_root_R, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_gN_dx (x a : ℝ) : p2 (p2dx hardcore_cube_root_R.gN) x a = (a) := by
  simp only [hardcore_cube_root_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_cube_root_e_gN_da (x a : ℝ) : p2 (p2da hardcore_cube_root_R.gN) x a = (x) := by
  simp only [hardcore_cube_root_R, p2, p2da]
  push_cast
  ring

theorem hardcore_cube_root_e_gD (x a : ℝ) : p2 hardcore_cube_root_R.gD x a = ((1 : ℝ)) := by
  simp only [hardcore_cube_root_R, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_gD_dx (x a : ℝ) : p2 (p2dx hardcore_cube_root_R.gD) x a = ((0 : ℝ)) := by
  simp only [hardcore_cube_root_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_cube_root_e_gD_da (x a : ℝ) : p2 (p2da hardcore_cube_root_R.gD) x a = ((0 : ℝ)) := by
  simp only [hardcore_cube_root_R, p2, p2da]
  push_cast
  ring

theorem hardcore_cube_root_e_hN (x a : ℝ) : p2 hardcore_cube_root_R.hN x a = ((1 : ℝ)) := by
  simp only [hardcore_cube_root_R, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_hN_dx (x a : ℝ) : p2 (p2dx hardcore_cube_root_R.hN) x a = ((0 : ℝ)) := by
  simp only [hardcore_cube_root_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_cube_root_e_hN_da (x a : ℝ) : p2 (p2da hardcore_cube_root_R.hN) x a = ((0 : ℝ)) := by
  simp only [hardcore_cube_root_R, p2, p2da]
  push_cast
  ring

theorem hardcore_cube_root_e_hD (x a : ℝ) : p2 hardcore_cube_root_R.hD x a = ((1 : ℝ) + x * a) := by
  simp only [hardcore_cube_root_R, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_hD_dx (x a : ℝ) : p2 (p2dx hardcore_cube_root_R.hD) x a = (a) := by
  simp only [hardcore_cube_root_R, p2, p2dx]
  push_cast
  ring

theorem hardcore_cube_root_e_hD_da (x a : ℝ) : p2 (p2da hardcore_cube_root_R.hD) x a = (x) := by
  simp only [hardcore_cube_root_R, p2, p2da]
  push_cast
  ring

theorem hardcore_cube_root_e_pN (x : ℝ) : p2 hardcore_cube_root_N.pN x 0 = ((1 : ℝ) + (3 : ℝ) * x + (3 : ℝ) * x ^ 2 + x ^ 3) := by
  simp only [hardcore_cube_root_N, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_pN_dx (x : ℝ) : p2 (p2dx hardcore_cube_root_N.pN) x 0 = ((3 : ℝ) + (6 : ℝ) * x + (3 : ℝ) * x ^ 2) := by
  simp only [hardcore_cube_root_N, p2, p2dx]
  push_cast
  ring

theorem hardcore_cube_root_e_pD (x : ℝ) : p2 hardcore_cube_root_N.pD x 0 = ((1 : ℝ)) := by
  simp only [hardcore_cube_root_N, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_pD_dx (x : ℝ) : p2 (p2dx hardcore_cube_root_N.pD) x 0 = ((0 : ℝ)) := by
  simp only [hardcore_cube_root_N, p2, p2dx]
  push_cast
  ring

theorem hardcore_cube_root_e_mN (x : ℝ) : p2 hardcore_cube_root_I.mN x 0 = ((1 : ℝ)) := by
  simp only [hardcore_cube_root_I, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_mD (x : ℝ) : p2 hardcore_cube_root_I.mD x 0 = ((1 : ℝ)) := by
  simp only [hardcore_cube_root_I, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_kN (x : ℝ) : p2 hardcore_cube_root_I.kN x 0 = ((-1 : ℝ) * x) := by
  simp only [hardcore_cube_root_I, p2]
  push_cast
  ring

theorem hardcore_cube_root_e_kD (x : ℝ) : p2 hardcore_cube_root_I.kD x 0 = ((1 : ℝ) + x) := by
  simp only [hardcore_cube_root_I, p2]
  push_cast
  ring

/-- Well-posedness on `λ ≥ λ0`: the node polynomials are positive on the aggregate range and the message stays `≤ 1`. -/
theorem hardcore_cube_root_good : ∀ x, (0 : ℝ) ≤ x → hardcore_cube_root_R.Good x := by
  intro x hx a ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hardcore_cube_root_e_gN]
    have hgNxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hgNas : 0 ≤ a - (0 : ℝ) := by linarith
    have hgNat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hgNxs 0) (mul_nonneg (pow_nonneg hgNas 0) (pow_nonneg hgNat 1)), mul_nonneg (pow_nonneg hgNxs 0) (mul_nonneg (pow_nonneg hgNas 1) (pow_nonneg hgNat 0)), mul_nonneg (pow_nonneg hgNxs 1) (mul_nonneg (pow_nonneg hgNas 1) (pow_nonneg hgNat 0))]
  · rw [hardcore_cube_root_e_gD]
    have hgDxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hgDas : 0 ≤ a - (0 : ℝ) := by linarith
    have hgDat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hgDxs 0) (mul_nonneg (pow_nonneg hgDas 0) (pow_nonneg hgDat 0))]
  · rw [hardcore_cube_root_e_hN]
    have hhNxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hhNas : 0 ≤ a - (0 : ℝ) := by linarith
    have hhNat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hhNxs 0) (mul_nonneg (pow_nonneg hhNas 0) (pow_nonneg hhNat 0))]
  · rw [hardcore_cube_root_e_hD]
    have hhDxs : 0 ≤ x - (0 : ℝ) := by linarith
    have hhDas : 0 ≤ a - (0 : ℝ) := by linarith
    have hhDat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hhDxs 0) (mul_nonneg (pow_nonneg hhDas 0) (pow_nonneg hhDat 1)), mul_nonneg (pow_nonneg hhDxs 0) (mul_nonneg (pow_nonneg hhDas 1) (pow_nonneg hhDat 0)), mul_nonneg (pow_nonneg hhDxs 1) (mul_nonneg (pow_nonneg hhDas 1) (pow_nonneg hhDat 0))]
  · intro _
    rw [hardcore_cube_root_e_hN, hardcore_cube_root_e_hD]
    have hhlexs : 0 ≤ x - (0 : ℝ) := by linarith
    have hhleas : 0 ≤ a - (0 : ℝ) := by linarith
    have hhleat : 0 ≤ (1 : ℝ) - a := by linarith
    linarith [mul_nonneg (pow_nonneg hhlexs 1) (mul_nonneg (pow_nonneg hhleas 1) (pow_nonneg hhleat 0))]

theorem hardcore_cube_root_pos1 : ∀ x, (0 : ℝ) ≤ x → 0 < p2 hardcore_cube_root_N.pN x 0 ∧ 0 < p2 hardcore_cube_root_N.pD x 0 ∧
    0 < p2 hardcore_cube_root_I.mN x 0 ∧ 0 < p2 hardcore_cube_root_I.mD x 0 ∧ 0 < p2 hardcore_cube_root_I.kD x 0 := by
  intro x hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hardcore_cube_root_e_pN]
    have hpNxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hpNxs 0, pow_nonneg hpNxs 1, pow_nonneg hpNxs 2, pow_nonneg hpNxs 3]
  · rw [hardcore_cube_root_e_pD]
    have hpDxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hpDxs 0]
  · rw [hardcore_cube_root_e_mN]
    have hmNxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hmNxs 0]
  · rw [hardcore_cube_root_e_mD]
    have hmDxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hmDxs 0]
  · rw [hardcore_cube_root_e_kD]
    have hkDxs : 0 ≤ x - (0 : ℝ) := by linarith
    linarith [pow_nonneg hkDxs 0, pow_nonneg hkDxs 1]

/-- Row 0: the child weight is `≥ 0` (`K0 ≥ 0`). -/
theorem hardcore_cube_root_K0 : ∀ x a, (0 : ℝ) ≤ x → hardcore_cube_root_R.inA a → 0 ≤ hardcore_cube_root_R.KN hardcore_cube_root_I 0 x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_cube_root_rho, hardcore_cube_root_e_gN, hardcore_cube_root_e_gN_dx, hardcore_cube_root_e_gN_da, hardcore_cube_root_e_gD, hardcore_cube_root_e_gD_dx, hardcore_cube_root_e_gD_da, hardcore_cube_root_e_hN, hardcore_cube_root_e_hN_dx, hardcore_cube_root_e_hN_da, hardcore_cube_root_e_hD, hardcore_cube_root_e_hD_dx, hardcore_cube_root_e_hD_da, hardcore_cube_root_e_pN, hardcore_cube_root_e_pN_dx, hardcore_cube_root_e_pD, hardcore_cube_root_e_pD_dx, hardcore_cube_root_e_mN, hardcore_cube_root_e_mD, hardcore_cube_root_e_kN, hardcore_cube_root_e_kD]
  have hK0xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK0as : 0 ≤ a - (0 : ℝ) := by linarith
  have hK0at : 0 ≤ (1 : ℝ) - a := by linarith
  linarith [mul_nonneg (pow_nonneg hK0xs 1) (mul_nonneg (pow_nonneg hK0as 0) (pow_nonneg hK0at 1)), mul_nonneg (pow_nonneg hK0xs 1) (mul_nonneg (pow_nonneg hK0as 1) (pow_nonneg hK0at 0)), mul_nonneg (pow_nonneg hK0xs 2) (mul_nonneg (pow_nonneg hK0as 1) (pow_nonneg hK0at 0))]

/-- Row 0: the child weight is `≤ μ` (`A K0 ≤ μ`). -/
theorem hardcore_cube_root_K0le : ∀ x a, (0 : ℝ) ≤ x → hardcore_cube_root_R.inA a →
    a * hardcore_cube_root_R.KN hardcore_cube_root_I 0 x a ≤ p2 hardcore_cube_root_I.mN x 0 * hardcore_cube_root_R.Dg x a * hardcore_cube_root_R.Dh x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_cube_root_rho, hardcore_cube_root_e_gN, hardcore_cube_root_e_gN_dx, hardcore_cube_root_e_gN_da, hardcore_cube_root_e_gD, hardcore_cube_root_e_gD_dx, hardcore_cube_root_e_gD_da, hardcore_cube_root_e_hN, hardcore_cube_root_e_hN_dx, hardcore_cube_root_e_hN_da, hardcore_cube_root_e_hD, hardcore_cube_root_e_hD_dx, hardcore_cube_root_e_hD_da, hardcore_cube_root_e_pN, hardcore_cube_root_e_pN_dx, hardcore_cube_root_e_pD, hardcore_cube_root_e_pD_dx, hardcore_cube_root_e_mN, hardcore_cube_root_e_mD, hardcore_cube_root_e_kN, hardcore_cube_root_e_kD]
  have hK0lexs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK0leas : 0 ≤ a - (0 : ℝ) := by linarith
  have hK0leat : 0 ≤ (1 : ℝ) - a := by linarith
  linarith [mul_nonneg (pow_nonneg hK0lexs 0) (mul_nonneg (pow_nonneg hK0leas 0) (pow_nonneg hK0leat 1)), mul_nonneg (pow_nonneg hK0lexs 0) (mul_nonneg (pow_nonneg hK0leas 1) (pow_nonneg hK0leat 0)), mul_nonneg (pow_nonneg hK0lexs 1) (mul_nonneg (pow_nonneg hK0leas 1) (pow_nonneg hK0leat 0))]

/-- Row 0: the cleared residual of the inductive step is `≥ 0`. -/
theorem hardcore_cube_root_res0 : ∀ x a (k : ℕ), (0 : ℝ) ≤ x → hardcore_cube_root_R.inA a →
    0 ≤ hardcore_cube_root_R.Q hardcore_cube_root_N hardcore_cube_root_I 0 x a (hardcore_cube_root_R.wt k a) := by
  intro x a k hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [Rec.Q, Rec.wt, hardcore_cube_root_prod, if_true, Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_cube_root_rho, hardcore_cube_root_e_gN, hardcore_cube_root_e_gN_dx, hardcore_cube_root_e_gN_da, hardcore_cube_root_e_gD, hardcore_cube_root_e_gD_dx, hardcore_cube_root_e_gD_da, hardcore_cube_root_e_hN, hardcore_cube_root_e_hN_dx, hardcore_cube_root_e_hN_da, hardcore_cube_root_e_hD, hardcore_cube_root_e_hD_dx, hardcore_cube_root_e_hD_da, hardcore_cube_root_e_pN, hardcore_cube_root_e_pN_dx, hardcore_cube_root_e_pD, hardcore_cube_root_e_pD_dx, hardcore_cube_root_e_mN, hardcore_cube_root_e_mD, hardcore_cube_root_e_kN, hardcore_cube_root_e_kD]
  have hres0xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hres0as : 0 ≤ a - (0 : ℝ) := by linarith
  have hres0at : 0 ≤ (1 : ℝ) - a := by linarith
  have hres0ks : 0 ≤ (k : ℝ) - (0 : ℝ) := by linarith
  linarith [mul_nonneg (mul_nonneg (pow_nonneg hres0xs 1) (mul_nonneg (pow_nonneg hres0as 0) (pow_nonneg hres0at 2))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 1) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 0) (pow_nonneg hres0at 2))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 2) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 3) (mul_nonneg (pow_nonneg hres0as 0) (pow_nonneg hres0at 2))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 3) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 3) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 3) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 4) (mul_nonneg (pow_nonneg hres0as 0) (pow_nonneg hres0at 2))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 4) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 4) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 4) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 5) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 0), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 5) (mul_nonneg (pow_nonneg hres0as 1) (pow_nonneg hres0at 1))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 5) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1), mul_nonneg (mul_nonneg (pow_nonneg hres0xs 6) (mul_nonneg (pow_nonneg hres0as 2) (pow_nonneg hres0at 0))) (pow_nonneg hres0ks 1)]

/-- Row 1: the child weight is `≥ 0` (`K1 ≥ 0`). -/
theorem hardcore_cube_root_K1 : ∀ x a, (0 : ℝ) ≤ x → hardcore_cube_root_R.inA a → 0 ≤ hardcore_cube_root_R.KN hardcore_cube_root_I 1 x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_cube_root_rho, hardcore_cube_root_e_gN, hardcore_cube_root_e_gN_dx, hardcore_cube_root_e_gN_da, hardcore_cube_root_e_gD, hardcore_cube_root_e_gD_dx, hardcore_cube_root_e_gD_da, hardcore_cube_root_e_hN, hardcore_cube_root_e_hN_dx, hardcore_cube_root_e_hN_da, hardcore_cube_root_e_hD, hardcore_cube_root_e_hD_dx, hardcore_cube_root_e_hD_da, hardcore_cube_root_e_pN, hardcore_cube_root_e_pN_dx, hardcore_cube_root_e_pD, hardcore_cube_root_e_pD_dx, hardcore_cube_root_e_mN, hardcore_cube_root_e_mD, hardcore_cube_root_e_kN, hardcore_cube_root_e_kD]
  have hK1xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK1as : 0 ≤ a - (0 : ℝ) := by linarith
  have hK1at : 0 ≤ (1 : ℝ) - a := by linarith
  linarith

/-- Row 1: the child weight is `≤ μ` (`A K1 ≤ μ`). -/
theorem hardcore_cube_root_K1le : ∀ x a, (0 : ℝ) ≤ x → hardcore_cube_root_R.inA a →
    a * hardcore_cube_root_R.KN hardcore_cube_root_I 1 x a ≤ p2 hardcore_cube_root_I.mN x 0 * hardcore_cube_root_R.Dg x a * hardcore_cube_root_R.Dh x a := by
  intro x a hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  simp only [Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_cube_root_rho, hardcore_cube_root_e_gN, hardcore_cube_root_e_gN_dx, hardcore_cube_root_e_gN_da, hardcore_cube_root_e_gD, hardcore_cube_root_e_gD_dx, hardcore_cube_root_e_gD_da, hardcore_cube_root_e_hN, hardcore_cube_root_e_hN_dx, hardcore_cube_root_e_hN_da, hardcore_cube_root_e_hD, hardcore_cube_root_e_hD_dx, hardcore_cube_root_e_hD_da, hardcore_cube_root_e_pN, hardcore_cube_root_e_pN_dx, hardcore_cube_root_e_pD, hardcore_cube_root_e_pD_dx, hardcore_cube_root_e_mN, hardcore_cube_root_e_mD, hardcore_cube_root_e_kN, hardcore_cube_root_e_kD]
  have hK1lexs : 0 ≤ x - (0 : ℝ) := by linarith
  have hK1leas : 0 ≤ a - (0 : ℝ) := by linarith
  have hK1leat : 0 ≤ (1 : ℝ) - a := by linarith
  linarith [mul_nonneg (pow_nonneg hK1lexs 0) (mul_nonneg (pow_nonneg hK1leas 0) (pow_nonneg hK1leat 2)), mul_nonneg (pow_nonneg hK1lexs 0) (mul_nonneg (pow_nonneg hK1leas 1) (pow_nonneg hK1leat 1)), mul_nonneg (pow_nonneg hK1lexs 0) (mul_nonneg (pow_nonneg hK1leas 2) (pow_nonneg hK1leat 0)), mul_nonneg (pow_nonneg hK1lexs 1) (mul_nonneg (pow_nonneg hK1leas 1) (pow_nonneg hK1leat 1)), mul_nonneg (pow_nonneg hK1lexs 1) (mul_nonneg (pow_nonneg hK1leas 2) (pow_nonneg hK1leat 0)), mul_nonneg (pow_nonneg hK1lexs 2) (mul_nonneg (pow_nonneg hK1leas 2) (pow_nonneg hK1leat 0))]

/-- Row 1: the cleared residual of the inductive step is `≥ 0`. -/
theorem hardcore_cube_root_res1 : ∀ x a (k : ℕ), (0 : ℝ) ≤ x → hardcore_cube_root_R.inA a →
    0 ≤ hardcore_cube_root_R.Q hardcore_cube_root_N hardcore_cube_root_I 1 x a (hardcore_cube_root_R.wt k a) := by
  intro x a k hx ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [Rec.Q, Rec.wt, hardcore_cube_root_prod, if_true, Rec.KN, Rec.Gx, Rec.Gq, Rec.Dg, Rec.Hx, Rec.Hq, Rec.Dh, Norm.Px, hardcore_cube_root_rho, hardcore_cube_root_e_gN, hardcore_cube_root_e_gN_dx, hardcore_cube_root_e_gN_da, hardcore_cube_root_e_gD, hardcore_cube_root_e_gD_dx, hardcore_cube_root_e_gD_da, hardcore_cube_root_e_hN, hardcore_cube_root_e_hN_dx, hardcore_cube_root_e_hN_da, hardcore_cube_root_e_hD, hardcore_cube_root_e_hD_dx, hardcore_cube_root_e_hD_da, hardcore_cube_root_e_pN, hardcore_cube_root_e_pN_dx, hardcore_cube_root_e_pD, hardcore_cube_root_e_pD_dx, hardcore_cube_root_e_mN, hardcore_cube_root_e_mD, hardcore_cube_root_e_kN, hardcore_cube_root_e_kD]
  have hres1xs : 0 ≤ x - (0 : ℝ) := by linarith
  have hres1as : 0 ≤ a - (0 : ℝ) := by linarith
  have hres1at : 0 ≤ (1 : ℝ) - a := by linarith
  have hres1ks : 0 ≤ (k : ℝ) - (0 : ℝ) := by linarith
  linarith

/-- The per-instance obligations, assembled. -/
theorem hardcore_cube_root_checks : hardcore_cube_root_R.Checks hardcore_cube_root_N hardcore_cube_root_I (0 : ℝ) where
  x0_nonneg := by norm_num
  good := hardcore_cube_root_good
  pos1 := hardcore_cube_root_pos1
  K0 := hardcore_cube_root_K0
  K0le := hardcore_cube_root_K0le
  K1 := hardcore_cube_root_K1
  K1le := hardcore_cube_root_K1le
  res0 := hardcore_cube_root_res0
  res1 := hardcore_cube_root_res1

/-- (1) The derivative prelude: `D` is the log-derivative of `T` on `λ ≥ λ0`. -/
theorem hardcore_cube_root_logderiv : ∀ b : RTree, ∀ x, (0 : ℝ) ≤ x →
    HasDerivAt (fun t => Real.log (hardcore_cube_root_R.T b t)) (hardcore_cube_root_R.D b x) x :=
  fun b x hx => hardcore_cube_root_R.hasDerivAt_log_T (hardcore_cube_root_good x hx) b

/-- (2) The derivative bound `λ D_b ≤ n_b c(λ)` on `λ ≥ λ0`. -/
theorem hardcore_cube_root_deriv_bound : ∀ b : RTree, ∀ x, (0 : ℝ) ≤ x →
    x * hardcore_cube_root_R.D b x ≤ b.size * hardcore_cube_root_N.C x :=
  fun b x hx => (Rec.invariant _ _ _ _ hardcore_cube_root_checks b x hx).1

/-- (2) `T_b / ψ^(ρ n_b)` is antitone on `λ ≥ λ0`. -/
theorem hardcore_cube_root_antitone : ∀ b : RTree,
    AntitoneOn (fun t => hardcore_cube_root_R.T b t / hardcore_cube_root_N.psi t ^ (hardcore_cube_root_N.rho * b.size)) (Set.Ici (0 : ℝ)) :=
  Rec.ratio_antitone _ _ _ _ hardcore_cube_root_checks

/-- The anchor node check at `λ0`: `g(λ0, A)^3 ≤ ψ(λ0)^1`. -/
theorem hardcore_cube_root_node : ∀ a, hardcore_cube_root_R.inA a → p2 hardcore_cube_root_R.gN (0 : ℝ) a ^ 3 * p2 hardcore_cube_root_N.pD (0 : ℝ) 0 ^ 1 ≤
    p2 hardcore_cube_root_N.pN (0 : ℝ) 0 ^ 1 * p2 hardcore_cube_root_R.gD (0 : ℝ) a ^ 3 := by
  intro a ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha1 := ha1 hardcore_cube_root_prod
  simp only [hardcore_cube_root_e_gN, hardcore_cube_root_e_gN_dx, hardcore_cube_root_e_gN_da, hardcore_cube_root_e_gD, hardcore_cube_root_e_gD_dx, hardcore_cube_root_e_gD_da, hardcore_cube_root_e_hN, hardcore_cube_root_e_hN_dx, hardcore_cube_root_e_hN_da, hardcore_cube_root_e_hD, hardcore_cube_root_e_hD_dx, hardcore_cube_root_e_hD_da, hardcore_cube_root_e_pN, hardcore_cube_root_e_pN_dx, hardcore_cube_root_e_pD, hardcore_cube_root_e_pD_dx, hardcore_cube_root_e_mN, hardcore_cube_root_e_mD, hardcore_cube_root_e_kN, hardcore_cube_root_e_kD]
  have hanchoras : 0 ≤ a - (0 : ℝ) := by linarith
  have hanchorat : 0 ≤ (1 : ℝ) - a := by linarith
  linarith

/-- (3) The anchor: `T_b(λ0) ≤ ψ(λ0)^(ρ n_b)` for every tree. -/
theorem hardcore_cube_root_anchor : ∀ b : RTree, hardcore_cube_root_R.T b (0 : ℝ) ≤ hardcore_cube_root_N.psi (0 : ℝ) ^ (hardcore_cube_root_N.rho * b.size) := by
  obtain ⟨hpN, hpD, -⟩ := hardcore_cube_root_pos1 (0 : ℝ) le_rfl
  exact Rec.anchor_of_node _ _ _ (hardcore_cube_root_good _ le_rfl) hpN hpD 1 3 (by norm_num) (by rw [hardcore_cube_root_rho]; norm_num) hardcore_cube_root_node

/-- (3) THE ANCHORED EXTENSION: `T_b(λ) ≤ ψ(λ)^(ρ n_b)` for every tree and every `λ ≥ λ0`. -/
theorem hardcore_cube_root : ∀ b : RTree, ∀ x, (0 : ℝ) ≤ x →
    hardcore_cube_root_R.T b x ≤ hardcore_cube_root_N.psi x ^ (hardcore_cube_root_N.rho * b.size) :=
  Rec.anchored_extension _ _ _ _ hardcore_cube_root_checks (0 : ℝ) le_rfl hardcore_cube_root_anchor

end AnchoredMonotoneExtension
