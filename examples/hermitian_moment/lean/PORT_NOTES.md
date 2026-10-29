# RHLinalg port notes

Verbatim port of the self-contained linear-algebra core of §3 of arXiv:2608.13637 from the public
repo `anthropics/zeta-23-lean` (path `zeta23/Zeta23/LinAlg/`), namespace `RHLinalg`. These eight
files have no upstream outside that project. This is the Lean prelude cited by the
`hermitian_moment` Telperion emitter family.

**Status: NOT built here.** No `lake`/`lean` toolchain is available in this worktree. The port is a
faithful text transcription; compilation is confirmed later in CI. Risks are flagged below.

## (a) Toolchain / Mathlib pin used

| | This port (target) | Source repo (`anthropics/zeta-23-lean`) |
|---|---|---|
| Lean | `leanprover/lean4:v4.32.0` | `v4.33.0-rc2` |
| Mathlib | `rev = "v4.32.0"` (commit `81a5d257c8e410db227a6665ed08f64fea08e997`) | commit `51e6992efd06` |

The pin was **copied exactly** from the sibling example
`telperion/examples/zero_free_bridge/lean/` — its `lean-toolchain` (`leanprover/lean4:v4.32.0`),
its `lakefile.toml` `[[require]] mathlib rev = "v4.32.0"`, and its `lake-manifest.json` mathlib
`rev`/`inputRev` (transitive dep pins copied verbatim from that manifest). This matches the Arda
repo's repo-wide v4.32.0 pin, NOT the source repo's v4.33.0-rc2.

## Files written (all under `.../hermitian_moment/lean/`)

```
lean-toolchain                 leanprover/lean4:v4.32.0
lakefile.toml                  name RHLinalg, defaultTargets [RHLinalg], require mathlib v4.32.0, lean_lib RHLinalg
lake-manifest.json             mathlib v4.32.0 (81a5d257...) + transitive pins (copied from zero_free_bridge)
RHLinalg.lean                  aggregator: imports all 7 modules
RHLinalg/PosIndex.lean         (imports Mathlib only)
RHLinalg/HermitianPosPart.lean (imports RHLinalg.PosIndex)
RHLinalg/Sylvester.lean        (imports RHLinalg.HermitianPosPart + Mathlib)
RHLinalg/Inertia.lean          (imports RHLinalg.Sylvester)
RHLinalg/VonNeumann.lean       (imports RHLinalg.PosIndex + Mathlib)
RHLinalg/RankTrace.lean        (imports RHLinalg.{PosIndex,VonNeumann,HermitianPosPart})
RHLinalg/Weyl.lean             (imports RHLinalg.{PosIndex,Sylvester} + Mathlib)
```

The ONLY edit to file bodies: inter-file `import Zeta23.LinAlg.X` → `import RHLinalg.X`. Every
lemma/theorem statement and proof body is byte-for-byte identical to the source (verified by diff
against the import-rewritten source). Mathlib import lines were left untouched.

## (b) Mathlib identifiers to confirm in CI (v4.32 vs v4.33 drift checklist)

Source compiled under v4.33.0-rc2; target is v4.32.0. Mathlib evolves fast, so any of these
identifiers may have been renamed/moved/re-signatured across the gap. None were guess-rewritten —
they are transcribed as-is and must be confirmed by the CI build. Ordered roughly by risk.

Higher risk (recent / actively churning API):
- [ ] `Matrix.IsHermitian.spectral_theorem` — exact statement form (some versions state
      `A = U * diag * Uᴴ` vs the `conjStarAlgAut` form used here via `conjStarAlgAut_apply`).
- [ ] `Unitary.conjStarAlgAut` and `Unitary.conjStarAlgAut_apply` (also referenced unqualified as
      `conjStarAlgAut`/`conjStarAlgAut_apply` under `open Unitary`). Namespace + `_apply` lemma name.
- [ ] `Matrix.IsHermitian.eigenvectorUnitary` (and its `.2` membership field) — name/shape.
- [ ] `Matrix.IsHermitian.eigenvalues`, `.eigenvalues₀`, `.eigenvalues₀_antitone` — the `₀`
      (sorted, `Fin (card n)`-indexed) API is comparatively new; confirm all three exist in v4.32.
- [ ] `Matrix.IsHermitian.eigenvalues_eq_eigenvalues₀`-style bridge is NOT used; instead the port
      `simp [Matrix.IsHermitian.eigenvalues, ...]` unfolds `eigenvalues` in terms of `eigenvalues₀`
      composed with an equiv (`eigenvalues_eigEquiv`, `hevA`/`hevB` in VonNeumann). This `simp`
      unfolding is fragile across versions — confirm the definitional shape of `.eigenvalues`.
- [ ] `Matrix.doublyStochastic`, `Matrix.mem_doublyStochastic_iff_sum`,
      `Matrix.exists_eq_sum_perm_of_mem_doublyStochastic`, `Matrix.reindex_mem_doublyStochastic`
      (Birkhoff–von Neumann API in `Mathlib.Analysis.Convex.Birkhoff`). Names + signatures.
- [ ] `Matrix.permMatrix_mulVec` and `Matrix.smul_mulVec` / `Matrix.sum_mulVec` (used in the
      Birkhoff averaging simp set in VonNeumann `bilinear_doublyStochastic_le_of_monovary`).
- [ ] `Matrix.IsHermitian.rank_eq_card_non_zero_eigs` — name and whether it returns a
      `Fintype.card` of a subtype (the port follows it with `Fintype.card_subtype`).
- [ ] `Matrix.PosSemidef.conjTranspose_mul_mul_same` and
      `Matrix.PosSemidef.mul_mul_conjTranspose_same` — orientation/name of the PSD congruence lemmas.
- [ ] `Matrix.isHermitian_conjTranspose_mul_mul` (used in the `posIndex_conj_le` statement itself —
      a signature change here changes the anchor type). Confirm argument order `B hQ`.

Medium risk (stable-ish but check):
- [ ] `RCLike` API: `RCLike.re`, `RCLike.ofReal`, `RCLike.star_def`, `RCLike.mul_conj`,
      `RCLike.conj_mul`, `RCLike.mul_re`, `RCLike.norm_ofReal`, `RCLike.ofReal_re`,
      `RCLike.ofReal_nonneg`, `RCLike.ofReal_ne_zero`, `RCLike.nonneg_iff`, `RCLike.ofReal_sub/mul`.
- [ ] `Module.finrank` (vs older `FiniteDimensional.finrank`), `LinearMap.finrank_range_of_inj`,
      `Submodule.finrank_mono`, `Submodule.finrank_add_le_finrank_add_finrank`,
      `Submodule.add_mem_sup`. finrank namespace moved historically — high-value to confirm.
- [ ] `Matrix.rank`, `Matrix.rank_mul_eq_left_of_isUnit_det`,
      `Matrix.rank_mul_eq_right_of_isUnit_det`, `Matrix.rank_diagonal`.
- [ ] `Matrix.UnitaryGroup.det_isUnit`, `Matrix.unitaryGroup`, `Unitary.star_mem`,
      `Unitary.mul_star_self_of_mem`, `Unitary.star_mul_self_of_mem`.
- [ ] posPart/negPart real API: `posPart_nonneg`, `negPart_nonneg`, `posPart_eq_zero`,
      `posPart_eq_self`, `posPart_sub_negPart`, `sub_nonpos`/`sub_nonneg` interplay.
- [ ] `Monovary`, `Monovary.sum_mul_comp_perm_le_sum_mul` (rearrangement, in
      `Mathlib.Algebra.Order.Rearrangement`). The port also adds a `_root_.Antitone.monovary_antitone`
      helper — confirm no name clash with a newer Mathlib `Antitone.monovary` variant.
- [ ] `sq_sum_le_card_mul_sum_sq` (Cauchy–Schwarz / Chebyshev, in `Mathlib.Algebra.Order.Chebyshev`).
- [ ] `Finset.card_nbij'` (used in `card_eigenvalues_reindex`) — the `nbij'` argument order/shape
      changed across recent Mathlib; medium-high risk.
- [ ] `nonneg_of_sum_ne_zero` → the port uses `nonempty_of_sum_ne_zero`; confirm name.
- [ ] `single_le_sum`, `sum_pos'`, `sum_le_sum_of_subset_of_nonneg`, `card_filter_le`,
      `sum_add_sum_compl`, `Finset.card_nbij'`, `Fintype.equivOfCardEq`.

Lower risk (very stable core): `Matrix.mulVec`, `dotProduct`, `Matrix.trace`, `trace_mul_comm`,
`trace_mul_cycle`, `diagonal_mul_diagonal`, `mulVec_diagonal`, `star_mulVec`, `dotProduct_mulVec`,
`conjTranspose_conjTranspose`, `noncomm_ring`, `nlinarith`, `linarith`, `positivity`, `abel`.

### Notation / pretty-printer note
The `·⁺` / `·⁻` posPart/negPart notation and `ᴴ` conjTranspose notation must be in scope. The files
rely on `open scoped ComplexOrder` and the default posPart/negPart notation being available at
v4.32 — confirm the notation scope names did not change.

## (c) The 9 anchor signatures (verbatim final types)

Emitters cite these by name. Signatures below are exactly as they appear in the ported files
(multi-line as written; `𝕜 : Type*` with `[RCLike 𝕜]`, `n`/`m`/`d : Type*` with the
`[Fintype _] [DecidableEq _]` instances declared at file scope via `variable`).

1. `RHLinalg.posIndex_conj_le` (Inertia.lean:51)
```lean
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) ≤ posIndex hQ
```

2. `RHLinalg.posIndex_add_le` (Inertia.lean:90)
```lean
theorem posIndex_add_le {Q₁ Q₂ : Matrix m m 𝕜}
    (hQ₁ : Q₁.IsHermitian) (hQ₂ : Q₂.IsHermitian) :
    posIndex (hQ₁.add hQ₂) ≤ posIndex hQ₁ + posIndex hQ₂
```

3. `RHLinalg.rank_trace_ineq` (RankTrace.lean:163)
```lean
theorem rank_trace_ineq {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (P + Q)
```

4. `RHLinalg.rank_trace_ineq_two` (RankTrace.lean:260)
```lean
theorem rank_trace_ineq_two {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * (b : ℝ) - frobSq (P + Q) ≤ (r : ℝ)
```

5. `RHLinalg.finrank_le_posIndex_of_posDefOn` (Sylvester.lean:82)
```lean
theorem finrank_le_posIndex_of_posDefOn {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {W : Submodule 𝕜 (n → 𝕜)} (hW : PosDefOn A W) :
    Module.finrank 𝕜 W ≤ posIndex hA
```

6. `RHLinalg.posDefOn_range_hermPosPart` (Sylvester.lean:123)
```lean
theorem posDefOn_range_hermPosPart {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    PosDefOn A (LinearMap.range (hermPosPart hA).mulVecLin)
```

7. `RHLinalg.vonNeumann_trace_ineq` (VonNeumann.lean:171)
```lean
theorem vonNeumann_trace_ineq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace
      ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i
```

8. `RHLinalg.weyl_posIndexAbove_le` (Weyl.lean:50)
```lean
theorem weyl_posIndexAbove_le {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {θ : ℝ}
    (hθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA
```

9. `RHLinalg.cauchySchwarz_count` (Weyl.lean:89)
```lean
theorem cauchySchwarz_count {R : Matrix n n 𝕜} (hR : R.IsHermitian)
    {θ : ℝ} (hθ : 0 ≤ θ) (htr : θ * Fintype.card n < rtrace R) :
    (rtrace R - θ * Fintype.card n) ^ 2 / frobSq R
      ≤ (posIndexAbove hR θ : ℝ)
```

### Supporting definitions the anchors reference (also in namespace `RHLinalg`)
- `posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ` (PosIndex.lean)
- `posIndexAbove {A : Matrix n n 𝕜} (hA : A.IsHermitian) (θ : ℝ) : ℕ` (PosIndex.lean)
- `rtrace (A : Matrix n n 𝕜) : ℝ` (PosIndex.lean)
- `frobSq (A : Matrix n n 𝕜) : ℝ` (PosIndex.lean)
- `hermForm (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ` (Sylvester.lean)
- `PosDefOn (A : Matrix n n 𝕜) (W : Submodule 𝕜 (n → 𝕜)) : Prop` (Sylvester.lean)
- `hermPosPart hA` / `hermNegPart hA : Matrix n n 𝕜` (HermitianPosPart.lean)
- `specMap {A} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n 𝕜` (HermitianPosPart.lean)
