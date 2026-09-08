# Second-pass emitter catalog — zeta-23-lean (2026-09-08)

Phase 5 of the HermitianMomentInertia build (see
`~/.claude/plans/elegant-toasting-cake.md`). A read-only dive over the parts of
`anthropics/zeta-23-lean` NOT covered by the planned families
(HermitianMomentInertia: rank_trace / Sylvester inertia / von Neumann trace /
Weyl+Cauchy-Schwarz count / TwoMomentCount; EnclosureGrid), cataloging additional
reusable Telperion certificate shapes. Every shape is grounded in a lemma read in
full; the large bespoke-analytic-glue majority (Taper Gevrey/Stirling machinery,
MainTerm/ThmD assembly, PrimeSideA/B shear-Fubini estimates, CountByIntegral
identities) was deliberately skipped — one-off derivations with no
generator-producible / kernel-checkable certificate boundary.

## Build decisions (main session)

- **Upgrade planned `EnclosureGrid` → `EnclosureIntervalFold` (#1).** The source
  is richer than a per-cell grid check: a certified running `foldl` accumulator
  carrying integer bounds on prefix sums, prefix-of-prefix sums (a second
  "integral"), and per-step running maxima. Build the fold form.
- **Build `ArgumentVariationCount` (#2)** next — self-contained, genuinely new
  (2π per Re-sign-cell), complements the existing argument-principle/winding family.
- **Then `ReflectionHalving` (#4)** — a clean NEW generic shape (involution folds a
  weighted count onto half its support); reusable well beyond ζ.
- **Confirm-before-build:** `WeightedArgumentPrinciple` (#3) and
  `HermitianKernelEigenBound` (#6) overlap the existing winding family and the
  HermitianMomentInertia family respectively; build only the novel sub-pieces
  (weighted-rectangle-with-poles; the antisymmetric→`M=iK`→polarization lift).
- All are kernel-internal EXCEPT `#1` (needs the external Arb/interval-arithmetic
  `EnclOK` trust boundary — the documented seam, same discipline as RH-in-a-box).

---

## Priority 1

### 1. `EnclosureIntervalFold` — running interval-propagation checker
- **Source:** `PairCeiling/NumericCert.lean` (`step`, `run`, `check`, `St`, `LoopInv`,
  `loopInv_init`); `PairCeiling/RowCert.lean` (`rowsOK`, `sumLo/sumHi`, `checkRows`,
  `rows_sound`, `sums_sound`).
- **Shape:** generator produces integer interval enclosures `[(lo_j,hi_j)]` of a scaled
  sequence `K·S(j)`; kernel folds a running state left-to-right, accumulating integer
  bounds on prefix sums, prefix-of-prefix sums, and running maxima of affine combos, then
  checks final integer inequalities `aX·d ≤ n·scale`. Soundness lifts the accepted integer
  fold to a real conclusion `|N·S(j) − target| ≤ tn/td` + grid-sup bounds on D, E.
- **Resembles:** planned EnclosureGrid, but adds the certified foldl accumulator +
  prefix-of-prefix sums + per-step maxima. Build the fold form.
- **Priority 1. External trust boundary: YES** (`EnclOK`, interval arithmetic).

### 2. `ArgumentVariationCount` — 2π-per-sign-cell argument bound
- **Source:** `RvM/Backlund.lean` (`im_integral_le_two_pi`, `im_integral_logDeriv_le_aux`,
  `im_integral_logDeriv_le`).
- **Shape:** given continuous complex `w` and a finite set covering the sign-changes of
  `Re w`, kernel checks (bisection induction on count) `|Im ∫ w'/w| ≤ 2π·(#P+1)`; base
  case IVT + `Complex.abs_arg_le_pi`.
- **Resembles:** argument-principle/winding + Sturm, but a *counting* bound on total
  argument variation via sign-cell decomposition — distinct mechanism.
- **Priority 1. External trust boundary: No.**

## Priority 2

### 3. `WeightedArgumentPrinciple` — rectangle residue / zero-count by contour
- **Source:** `Analytic/RectangleLogDeriv.lean` (`residueTheorem_finset`,
  `rectangleIntegral'_mul_logDeriv'`, `finite_zeros_rectangle`).
- **Shape:** rectangle + analytic `f` (+ weight `g`) + finite zero/pole list ⟹ kernel checks
  `(1/2πi)∮ g·f'/f = Σ g(ρ)·ord_ρ`.
- **Resembles:** existing argument-principle — strict generalization (weighted, rectangle,
  poles, self-contained residue form). **Confirm overlap;** build only the weighted-with-poles
  variant if not subsumed. Priority 2. No trust boundary.

### 4. `ReflectionHalving` — symmetry-orbit domination of a weighted count  [NEW SHAPE]
- **Source:** `RvM/Halving.lean` (`N_le_two_mul_half`, `reflect_injective`, `reflect_mem_window`).
- **Shape:** finite weighted multiset partitioned by a predicate + an involution that
  preserves the set and weight and maps the "small" part into the "large" part ⟹ kernel
  concludes `total ≤ 2·(large-part weight)` via `finsum` domination.
- **Reusable** wherever a symmetry halves a count (functional-equation zero counts,
  palindromic/reciprocal-polynomial roots). Priority 2. No trust boundary.

### 5. `SpacingTailBound` — separated-support inverse-power sum ≤ closed form  [NEW SHAPE]
- **Source:** `MV/Spacing.lean` (`spacing_sq` ≤ 9/δ_s, `spacing_four` ≤ 27/δ_s³,
  `integral_inv_sq_Icc`, `integral_inv_four_Icc`, `Adm`).
- **Shape:** centers with disjoint radius-`δ_i/2` intervals ⟹ kernel bounds `Σ δ_t/(f_s−f_t)²`
  (and quartic) by `C/δ_s^{k−1}` via exact tail-integral lemmas.
- **Reusable** for spacing/energy bounds over well-separated point configs. Priority 2. No boundary.

### 6. `HermitianKernelEigenBound` — antisymmetric-kernel spectral radius via `M = iK`
- **Source:** `MV/Duality.lean` (`kfun`, `Mmat := iK`, `Mmat_isHermitian`,
  `abs_eigenvalue_le`, `mvHilbert_of_eigenBound`), `MV/Quadratic.lean` (`Uform_le`),
  `MV/Eigen*.lean` (`eigen_identity`, Preissmann–Lévêque).
- **Shape:** antisymmetric real kernel `k` → Hermitian `M=iK`; a supplied eigenvalue bound
  (reduced via `eigen_identity` to a quadratic positivity `Uform ≤ 73 Σt²`) yields a
  Hilbert-type bilinear inequality by spectral expansion + polarization.
- **Resembles:** HermitianMomentInertia theme; the novel sub-piece is the
  antisymmetric→`M=iK`→polarization lift. **Confirm overlap** before building. Priority 2. No boundary.

## Priority 3

### 7. `AutocorrSupportComparison` — convolution triangle-envelope sandwich  [NEW SHAPE]
- **Source:** `Taper/Decay.lean` (`autocorr_le_of_support`, `le_autocorr_of_plateau`,
  `autocorr_eq_zero_of_support`, `volume_Icc_inter_shift`).
- **Shape:** box-support/plateau data on `0≤v≤1` ⟹ kernel sandwiches `v⋆v` between the
  triangle envelope `(2M−|y|)₊` on both sides. Priority 3. No boundary.

### 8. `GevreyDerivativeCert` — Cauchy-estimate iterated-derivative factorial bound  [NEW SHAPE]
- **Source:** `Taper/Gevrey.lean` (`GevreyProfile`, `norm_iteratedDeriv_G_le`,
  `pow_mul_exp_neg_le`), `Taper/GevreyRamps.lean` (`abs_iteratedDeriv_le_indicator`).
- **Shape:** analyticity on a disc + radius ⟹ `‖f^{(k)}‖ ≤ B·A^k·(k!)^s` via Cauchy estimate
  + `u^k e^{−u} ≤ (k/e)^k`. Reusable for smooth-bump / Beurling–Selberg majorants.
  Priority 3. No boundary.

## Priority 4–5 — noted, not worth a dedicated emitter
- `WindowAdditivity` (`RvM/NcountWindow.lean`) — counting-measure additivity/monotonicity;
  better as a helper inside #2/#4. P4.
- `AbelIBPStability` (`PairCeiling/Stability.lean`) — Abel-summation↔IBP; the analytic engine
  *behind* #1, already covered by `finite_decide`/`telescoping`. P5, skip.
- `SlitPlaneLogPrimitive` / `ConjugationFold` (`RvM/Fold.lean`, `GammaFacts/StirlingVert.lean`)
  — bespoke complex-analytic glue, no certificate boundary. Skip.
