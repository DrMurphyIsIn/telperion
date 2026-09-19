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

---

## Built after this catalog

### `weil_form_enclosure` — the E8 pairing itself, as a named-hypothesis trust seam  [BUILT 2026-09-18]
- **The gap it closed.** `bragg_floor` certifies finite Bragg amplitudes against an archimedean
  floor per Li order `n`, but NOTHING in Telperion evaluated the E8 pairing — the finite prime
  sum `Σ_{n ≤ e^R} Λ(n)/√n (g(log n) + g(−log n))`, the two pole terms `h(±i/2)`, the `−g(0) log π`
  term, and the digamma integral `(1/2π) ∫ h(r) Re ψ(1/4 + ir/2) dr` — for a concrete `C_c^∞` test
  function, nor the `k × k` Gram entries for cross-correlations. That is the right-hand side of the
  PROVED registry node `RH_limit_explicit_formula` (E8, `WeilExplicit`; `E6Bridge4.lean`, #560).
- **Backend.** `telperion/src/telperion/weil_form_eval.py` — python-flint (`acb`) evaluator over the
  bump family `g(u) = amp·P(t)·exp(−1/(1−t²))`, `t = (u−c)/w`. Rigour: interior-cut collars for the
  bump's non-analytic endpoints; the archimedean tail bounded (not truncated) by `|h(r)| ≤ ‖f^{(N)}‖₁/|r|^N`
  with `‖f^{(N)}‖₁` from a symbolic-derivative + Arb-ball-grid sup bound, and the explicit
  `|Re ψ(1/4+iy)| ≤ log(|y|+2) + 4.4` (derivation in the module docstring, re-verified on a dyadic
  Arb sweep as a refuse-to-emit anchor). Prime side exact and FINITE — the compact-support payoff.
  `G_i(z)G_j(−z)` collapses the pole terms and `h_i(r)h_j(−r)` keeps the archimedean integrand
  ENTIRE (writing `conj`/`.real` inside it would silently invalidate Arb's path integral).
- **Emitted Lean.** `emit_weil_form_enclosure.py`. The enclosure is the NAMED HYPOTHESIS `henc`
  (the `BraggDefect` `hexp` / Li-ladder `henc` discipline) and the kernel proves only its
  consequence, through two abstract lemmas whose numeric side goals are `norm_num`:
  `box_pos` (`0 < weilForm (autocorr g)`) and `box_minor_pos` (Sylvester: both leading principal
  minors of a `2 × 2` Weil-Gram block positive, i.e. the block is positive definite — the datum a
  Gram-inertia consumer wants). `weil_negative_refutes_rh` is the falsifiability face; its RH
  content is the UNDISCHARGED hypothesis `hpos : RiemannHypothesis → 0 ≤ …`.
- **Refusals.** non-compact support (the PNT growth trap, E8 memo 2.2); box wider than the declared
  threshold; inverted box; Hermitian-inconsistent `(i,j)`/`(j,i)` mirrors; `lo ≤ 0`; non-positive
  worst-case determinant.
- **Registry stance.** `CERTIFICATE_SENSITIVE` with a two-sided kernel adapter
  (`negctrl_adapters/adapter_weil_form_enclosure.py`): a forged off-diagonal box that exceeds
  Cauchy–Schwarz makes `max(c0², c1²) < a0·b0` FALSE and the kernel rejects; the true bump-pair
  block (worst-case determinant ≈ +6.19e−10) compiles.
- **Dogfood.** `examples/weil_form_enclosure/` (`generate.py --check` also gates the `WeilExplicit`
  vocabulary mirror against `E6Bridge4.lean` byte-for-byte); CI job `weil-form-enclosure-compiles`.
- **Honest scope.** Category-(b): finite, consistent with RH, PROVING NOTHING about it. A positive
  autocorrelation pairing is what RH PREDICTS; Weil positivity over EVERY admissible test function
  is RH-equivalent and no finite family approaches "every". Arb is a non-kernel trust seam.
  `conjecture1_proved = False`.
## Addendum 2026-09-18 -- shape BUILT, not just catalogued

### `DisjointDiscs` -- finite point bank -> explicit pairwise-disjoint discs inside the open strip
- **Source:** MIRRORMERE node `MM_offline_disjoint_discs` / `QC_RECURRENCE_MEMO.md` section 4.3;
  general lemma in `examples/quasicrystal/lean/OfflineDiscs.lean`.
- **Shape:** Gaussian-rational strip points + an explicit rational radius `r` ⟹ kernel proves each
  pair `Disjoint (closedBall z r) (closedBall w r)` from `(2r)^2 < dist^2` (square root eliminated
  by `Real.lt_sqrt` BEFORE any arithmetic, so the goal is pure rational `norm_num`) and each disc
  `⊆ {0 < re < 1}` from the 1-Lipschitz `abs_re_sub_le_dist`; assembly restates the registry node's
  existential at the concrete `Finset`.
- **Negative control:** an inflated `r` makes a pair theorem genuinely FALSE, so the kernel rejects
  it -- a real Layer-2 seam (`negctrl_adapters/adapter_disjoint_discs.py`, two-sided, passing).
  Layer 1 also refuses boundary-reaching radii, off-strip points, duplicates and `r <= 0`.
- **Status:** BUILT (kind `disjoint_discs`, `DisjointDiscsEmitter`). Distinct from
  `TwoScaleSeparation` (one centre, two radii, no containment) and from `SpacingTailBound` (1-D
  separated support, inverse-power sums). The consumer joint -- feeding a certified disc bank into
  `WindingCountEmitter` / `AnnulusCountEmitter` for the E5 Rouche count -- is NOT built.
- conjecture1_proved = False.
## Addendum 2026-09-18 -- MIRRORMERE ladder rung T2
- `twofreq_offline` (`TwoFreqOfflineEmitter`) -- certified OFF-line displacement of a
  two-frequency section: `|c1|^2 != |c2|^2` EXACTLY refutes real-rootedness via
  `TwoFreqRigidity.twoFreq_realRooted_iff`, and for the Euler-factor family
  `1 - p^(-s)` on `s = 1/2 + i x` it also certifies `Im x = 1/2` for EVERY zero.
  The exact COMPLEMENT of `selfinversive_rigidity`: the two partition the coefficient
  space, each refusing the other's regime.  Adds irrational coefficient literals
  (`inv_sqrt`, `real_sqrt`) and the `-(Real.log p)` frequency literal, which the
  Gaussian-rational-only rigidity emitter cannot express.  Kernel-gated negative-control
  adapter (equal-modulus forgery).  Full write-up: `EMITTER_MIRRORMERE_2026-09-18.md`.
  conjecture1_proved = False.
