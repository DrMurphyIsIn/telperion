# Telperion

**A certificate compiler for Lean 4 — it turns families of concrete mathematical
claims into kernel-checked Mathlib proofs by exact-arithmetic witness, not by
trust.**

You describe your problem as a parameterized *family* of statements. Telperion
certifies each instance in exact rational arithmetic, then emits Lean 4 that
Mathlib's kernel re-proves from scratch. **The generator is untrusted by
design** — a wrong certificate is a compile error, never a false theorem — so
you get machine-checked proofs without having to trust, or even read, the tool
that wrote them. That inversion (check the witness, don't trust the author) is
the whole point: it is exactly what makes an unreliable, heuristic, or
LLM-driven generator safe to build on.

Telperion was forged as the engine behind a hard research proof — the
Brualdi–Goldwasser Laplacian-ratio problem — but nothing in the engine is
specific to it. It is now a standalone, problem-agnostic artifact, battle-tested
across three very different campaigns:

- **Extremal combinatorics** — the Brualdi–Goldwasser proof, thousands of
  CI-green Mathlib theorems (`g1_floors` alone: 3,084).
- **Analytic number theory** — an *unconditional* Riemann-ζ zero-free region,
  the Borel–Carathéodory machinery, and sharp near-line growth bounds, all
  sorry-free (classical-analysis formalization, not a claim on RH itself).
- **Proof complexity** — sum-of-squares refutations of unsatisfiable systems and
  their pseudo-expectation-duality complement (no low-degree refutation exists).

The same `certify → emit → freeze` pipeline that discharges a 3,084-theorem
combinatorial floor table also proves a textbook inequality
([`examples/bernoulli`](examples/bernoulli/)) through identical machinery. Bring
your own inequality, identity, bound, enclosure, or positivity certificate, and
it will try to hand you a kernel-checked Lean proof of it.

## What you can prove with it

Telperion turns a problem into Lean whenever you can express it as a *certifiable
family* — a grid of instances, each reducible to one of its certificate shapes.
Fifty-plus shapes now span a broad slice of concrete mathematics:

- **Positivity & inequalities** — `0 ≤ f(x̄)` / `g ≤ h` for rational `f,g,h`
  (Pólya, two-variable box-corner), polynomial nonnegativity via exact rational
  sum-of-squares (interior equality cases included), Positivstellensatz
  certificates on polytopes and semialgebraic sets (Handelman, Putinar), and
  reverse/pairwise inequalities (Cauchy–Schwarz, tangent-line convex sums).
- **Exact identities, arithmetic & valuations** — integer/rational identities and
  powers, rational-function identities on a ray, p-adic valuations `v_p(n)=k`,
  hypergeometric/binomial sum identities (Wilf–Zeilberger), and ideal-membership
  equalities (Nullstellensatz).
- **Enclosures** — rigorous two-sided rational brackets of transcendentals
  (`lo ≤ exp(−θ) ≤ hi`) and of algebraic numbers (`lo ≤ √a ≤ hi`).
- **Infeasibility & duality** — a system has *no* real solution (a
  Positivstellensatz/SOS refutation), or its dual: *no low-degree SoS refutation
  exists* (pseudo-expectation / moment-relaxation feasibility).
- **Extremal & combinatorial facts** — integer maxima of unimodal and log-concave
  sequences, telescoping tree/potential bounds, lattice-box (`ℤ^d_{≥0}`) integer
  Positivstellensatz bounds, and finite argmax-with-margin extremality.
- **Complex analysis** — coordinate and magnitude bounds on disks, Cauchy
  derivative estimates, the Borel–Carathéodory half-plane→disk core,
  parametric-integral holomorphy, and the ζ zero-free-region assembly (product
  inequality + growth + pole → an explicit region gap).
- **Finite & assembled reasoning** — case dispatch over a bounded parameter,
  region subdivision and glue, `∀ K ≥ K₀` tails, and substitution/dichotomy
  assemblies of all of the above, expressed in the original variables.

If your statement fits one of these shapes — or a product/quantifier over a grid
of them — Telperion certifies it in exact arithmetic and emits the Lean. If it
needs a new shape, you add an emitter (see [Extending it](#extending-it)); the
trust model and the whole pipeline come for free.

### Certificate shapes

Each shape is an *emitter*; all flow through the same `certify → validate →
emit → freeze` workflow, and every one below has a worked, CI-compiled example
under [`examples/`](examples/).

| Emitter | Proves | Lean it writes |
|---|---|---|
| `DirectPolyaEmitter` | `0 ≤ f(x̄)`, `f` rational with an all-nonneg-numerator / positive-factored-denominator form | `f = num/den` by `field_simp`+`ring`, then `positivity` |
| `BilinearBoxEmitter` | `before ≤ after` on a box in two bound variables | bilinear decomposition + 4 Pólya corner certificates + assembly |
| `SOSEmitter` | `0 ≤ p` for a polynomial via an exact rational PSD-Gram sum-of-squares (reaches interior ties) | `p = Σ dᵢ·ℓᵢ² := by ring`, then `positivity` |
| `RationalSOSEmitter` | `0 ≤ p` for a NONNEGATIVE-but-NOT-SOS polynomial (e.g. Motzkin) via an Artin denominator `q·p = Σ dᵢℓᵢ²`, `q > 0` (Telperion FINDS `q` + SOS) | `positivity` (`0 < q`, and the SOS after `ring`) + `nlinarith`/`mul_pos` to divide out `q` |
| `ExactFactEmitter` / `IdentityEmitter` | exact integer/rational identities and powers | `norm_num` / `ring` |
| `PadicValuationEmitter` | p-adic valuation facts `v_p(n)=k` | `(p^k ∣ n) ∧ ¬(p^{k+1} ∣ n)` by `norm_num` |
| `IntervalBracketEmitter` | rigorous two-sided rational enclosure `lo ≤ exp(−θ) ≤ hi` | Taylor bound + convexity companion |
| `CaseDispatchAssemblyEmitter` | finite case dispatch over a bounded parameter | `interval_cases` fan-out |
| `SubdivisionGlueEmitter` | reconstruct a subdivided region's theorem from its leaf cells | `le_total` case-split glue |
| `TailNatEmitter` | symbolic tails — finite table + one `∀ K ≥ K₀` certificate | ℕ-quantified, induction-free |
| `ReparamAdapterEmitter` | recast a real-variable certificate over `Nat.cast_sub` casts | cast-rewrite adapter |
| `VarMapAdapterEmitter` | substitution glue expressed in the original variables | `MapSpec`-driven rewrite |
| `DichotomyGlueEmitter` | classification over declared thresholds | `le_total` splits |
| `ConeFarkasEmitter` | `0 ≤ target` as an exact nonnegative combination `Σ λᵢ·bᵢ` of a positivity-provable basis (a Farkas / linear-Positivstellensatz certificate) | `target = Σ λᵢ·bᵢ := by ring`, then `positivity` |
| `UnimodalMaxEmitter` | the integer maximum of a unimodal sequence is at the ratio's crossing `s*` | monotone-ratio (`positivity`) + crossing (`norm_num`) facts + the reusable `unimodal_peak` lemma |
| `TelescopingPotentialEmitter` | a recursive/tree bound `Σ local(v) ≤ P(root)` from a per-node super-solution | per-node margins (`positivity`) + the reusable rose-tree `RTree.telescope` lemma |
| `LatticeBoxEmitter` | `f(x) ≤ B` for all `x ∈ ℤ^d_{≥0}` (d-dim integer Positivstellensatz) | finite base box (`norm_num`) + per-axis monotone tail (`ring`/`positivity`) |
| `LogConcaveSinglePointEmitter` | `max_{k∈ℕ} F(k) ≤ B` reduced to a single point `k*` by log-concavity | single-point + per-step + neighbour facts (`norm_num`) |
| `MonotoneRatioTailEmitter` | `b(s) ≤ B` for all `s ≥ s₀` via a nonincreasing tail | tail step (`positivity`) + base (`norm_num`) + `Nat.le_induction` |
| `SturmPositiveEmitter` | `0 < p(x)` (STRICT) on a closed interval `[a,b]` — root exclusion via a Sturm sequence (the exact decision oracle) + a Bernstein certificate for `p−γ ≥ 0`, `γ>0` | Bernstein fold + `ring` + `linarith` (`0 < γ ≤ p`) |
| `BernsteinEmitter` | `0 ≤ p(x)` on a closed interval `[a,b]` via nonnegative Bernstein coefficients (Telperion FINDS them, elevating the degree; the univariate interval specialization of Handelman) | `mul_nonneg`/`pow_nonneg` fold over `0 ≤ x−a`, `0 ≤ b−x` + `ring` + `linarith` |
| `InterlacingEmitter` | Newton's inequalities (coefficient log-concavity) of a real-rooted polynomial | `norm_num` on exact rationals |
| `ConstrainedSOSEmitter` | `0 ≤ p` on a semialgebraic set `{gᵢ ≥ 0}` via a Putinar certificate `p = σ₀ + Σ σᵢ·gᵢ` (SOS multipliers) — supply the multipliers, or return `sigma0=None` and Telperion FINDS them (`find_putinar_certificate`, numeric SDP rounded to exact rationals) | `p = σ₀ + Σ σᵢ·gᵢ := by ring`; each `σⱼ` by `positivity`, paired with `gᵢ ≥ 0` by `mul_nonneg`, summed by `linarith` |
| `WZEmitter` | hypergeometric / binomial sum identities `Σ_k F(n,k) = rhs(n)` via a Wilf–Zeilberger mate `R(n,k)` | denominator-cleared WZ equation as an exact `ring` polynomial identity + the reusable `wz_row_invariant` telescoping-closure lemma |
| `HandelmanEmitter` | `0 ≤ p` on a polytope `{ℓᵢ ≥ 0}` via a nonnegative combination of PRODUCTS of the constraints `p = Σ c_α ∏ ℓᵢ^{αᵢ}` — supply the products, or return `terms=None` and Telperion FINDS them (`find_handelman_certificate`, exact) | `mul_nonneg`/`pow_nonneg` fold over the constraint hypotheses + `ring` + `linarith` |
| `NullstellensatzEmitter` | `p = 0` on a variety `V(g₁,…,gₘ)` via ideal-membership cofactors `p = Σ hᵢ·gᵢ` (an EQUALITY, computed by Gröbner reduction) | a single `linear_combination Σ hᵢ·(hyp_i)` |
| `InfeasibilityEmitter` | a system `{gⱼ = 0}` has NO solution (a certificate of NON-existence) via a computed Nullstellensatz refutation `1 = Σ λⱼ·gⱼ` | `linear_combination` ⟹ `1 = 0`, then `absurd … norm_num` ⟹ `False` |
| `ConsequenceEmitter` | an equation `lhs = rhs` FOLLOWS from hypotheses `{aᵢ = bᵢ}` (`lhs−rhs ∈ ⟨aᵢ−bᵢ⟩`, cofactors computed) | a single `linear_combination Σ cᵢ·(hyp_i)` |
| `SOSRefutationEmitter` | a semialgebraic system `{gᵢ ≥ 0, hⱼ = 0}` is unsatisfiable OVER ℝ via `−1 = σ₀ + Σσᵢgᵢ + Σλⱼhⱼ` (reaches positivity-only infeasibility like `x²+1=0`) — supply the certificate, or return `sigma0=None` and Telperion FINDS it (`find_sos_refutation`, SDP; auto-closes the ℝ-only gap) | `positivity`/`mul_nonneg` + `linear_combination` + `linarith` ⟹ `False` |
| `RealNullstellensatzEmitter` | `p = 0` on the REAL variety of `⟨gₖ⟩` via `p^{2m} + s ∈ ⟨gₖ⟩` (`s` a sum of squares, cofactors computed) | `positivity` + `linear_combination` + `linarith` + `pow_eq_zero_iff` |
| `CGRoundEmitter` | a linear goal over INTEGER variables from a Chvátal–Gomory derivation (VIPR-style): `lincomb` (nonnegative combination of prior facts) + `cg_round` (from an integer-coefficient fact `Σ cⱼxⱼ ≥ v`, the integer LHS rounds the bound up to `Σ cⱼxⱼ ≥ ⌈v⌉`); refuses non-integer or vacuous rounds, negative multipliers, undominated goals, and rounding-INSENSITIVE certificates | integer-cleared hypotheses discharged by `omega` (linear-integer decision procedure, which performs the CG rounding internally) |
| `TangentSumEmitter` | a symmetric-sum (combinatorial) inequality `B ≤ Σf(xᵢ)` for a convex polynomial `f` of any even degree with `Σxᵢ = S`, via the tangent line at `a = S/n` — the surplus `f−L` is an exact rational SOS (factored over ℚ; double root at `a`); refuses a non-convex `f` | per-term `have … = Σcⱼ·bⱼ² := by ring; positivity`, assembled by `linarith [h₁,…, hsum]` |
| `CauchySchwarzEmitter` | the (weighted) Cauchy–Schwarz / QM–AM inequality `(Σwᵢxᵢ)² ≤ (Σwᵢ)(Σwᵢxᵢ²)` (constraint-free) via the pairwise-difference SOS `Σ_{i<j} wᵢwⱼ(xᵢ−xⱼ)²`; refuses a non-positive weight | `have … = Σ wᵢwⱼ(xᵢ−xⱼ)² := by ring; positivity`, then `linarith` |
| `PSDFormEmitter` | `0 ≤ xᵀMx` for an explicit rational symmetric **positive-semidefinite** matrix `M` (definite or singular), via the exact rational completing-the-square congruence `xᵀMx = Σ cᵢ·(…)²` (`cᵢ > 0`, cvxpy-free — the moment-matrix / Gram-bridge PSD primitive); refuses an indefinite matrix | `have xᵀMx = Σ cᵢ·(…)² := by ring`, then `positivity` |
| `Xor3MomentPSDEmitter` | a degree-d SoS lower bound for an UNSAT 3-XOR (Tseitin) instance whose width-2d GF(2) closure is conflict-free — the moment matrix is **block-rank-one**, so `0 ≤ xᵀMx` emits as a compact SOS `Σ_class (Σ σ_S·x_S)²` (one square per derivability class); refuses a satisfiable instance, a width refutation, or a non-block-rank-one matrix | `have xᵀMx = Σ_class(…)² := by ring`, then `positivity` |
| `PolyaZerosEmitter` | `0 ≤ p` homogeneous on the simplex, TOLERATING zeros on faces (Castle–Powers–Reznick 2011): multiply by `(Σxᵢ)^N` until every coefficient is nonnegative, so boundary zeros are allowed (where the strict-interior Pólya certificate fails) | nonneg-coefficient expansion `p·(Σx)^N = Σ c_α x^α` (`c_α ≥ 0`) + `positivity` |
| `FwdTelescopeEmitter` | a forward-difference telescoping / contiguous (W2-type hypergeometric) sum identity `Σ_k F(n,k) = rhs` via a first-order certificate `G(n,k+1) − G(n,k) = F(n,k)` | the telescoping equation as a `ring` polynomial identity + a `Finset.sum_range_succ` collapse |
| `RationalIdentityEmitter` | a rational-function identity `lhs = rhs` over ℚ on a ray with rational-rooted denominators (the gauge / shift-factor tower identities) | `field_simp` (nonzero denominators) + `ring` |
| `FiniteDecideEmitter` | guarded universal facts over an explicit finite table `∀ i ∈ table, P i` (decidable predicate) | kernel `decide` over the enumerated table |
| `ZeroFreeCosineEmitter` | nonnegativity of a nonneg-coefficient cosine polynomial `Σ_{k} a_k cos(kθ) ≥ 0` (the 3-4-1 positivity kernel behind `ζ(1+it) ≠ 0` and the zero-free region) via a Fejér–Riesz / Handelman witness on `(1+x)^n` | Chebyshev substitution `cos(kθ)=T_k(x)` → `HandelmanEmitter`/`positivity` on the `(1+x)^n` cone |
| `DirichletReprEmitter` | the TRUNCATED Abel-summation / Euler–Maclaurin representation of a unit-coefficient Dirichlet series `ζ(s) = Σ_{n≤N} n^{-s} + N^{1-s}/(s-1) − s·∫_{x>N} {x}x^{-s-1}` (`Re s > 1`, `N ≥ 1`) — the finite-`N` companion of the fractional-part representation and the engine of the sharp near-line bound; certifies the symbolic equality of the two closed forms (boundary + tail correction) | finite Abel identity by `linear_combination`/`ring` + the `Ioc`/`Ioi` tail split |
| `DominatedIntegrabilityEmitter` | integrability of a bounded-factor-over-complex-power integrand `f(x) = b(x)/(x:ℂ)^p` (`‖b‖ ≤ B`) on a ray `Ioi c` (`c > 0`), gated by the decay `Re p > 1` | `Integrable.mono'` + a.e. pointwise `‖f‖ ≤ B·x^{−Re p}` + `integrableOn_Ioi_rpow_of_lt` |
| `PreconnectedCoverEmitter` | preconnectedness of a non-convex domain given as a finite union of convex cells glued along shared points (canonical: a convex open set minus one interior point — e.g. ζ's strip domain) | `IsPreconnected` via a pairwise-overlapping convex cover + `IsPreconnected.union` glue |
| `ZeroFreeRegionEmitter` | a zero-free region `Re s > 1 − c/\|t\|^{5θ}` for ζ from the 3-4-1 product inequality + pole bound + growth bound (exponent `θ`; crude `θ=1`, sharp `log` smaller) + Cauchy derivative bound; certifies the exact substitution identity `(c₁/(1−β))³·(2(1−β)c₄γ^θ)⁴·(c₂γ^θ) = 16c₁³c₂c₄⁴(1−β)γ^{5θ}` and refuses a wrong constant/exponent or a nonpositive coefficient | `gcongr` (bound the product) + `field_simp; ring` (the identity) + `nlinarith` |
| `BilinearCornerBoxEmitter` | `0 ≤ A + B·s + C·t + E·(s·t)` on a box `[s0,s1]×[t0,t1]` — a bilinear form is affine in each variable, so its minimum is at a CORNER; certifies from the four corner values (each ≥ 0) via the barycentric convex-combination identity `f = Σ λ_corner·f(corner)` (`λ ≥ 0`); refuses a negative corner or a degenerate box | a reusable `bilinear_corner_nonneg` lemma (two `le_total` slope-sign splits closed by `nlinarith [mul_nonneg …]`) applied per instance to four `by norm_num` corner facts |
| `AlgebraicBracketEmitter` | rigorous two-sided rational enclosure `lo ≤ √a ≤ hi` of a square root, certified by the exact rational facts `0 ≤ lo`, `lo² ≤ a`, `a ≤ hi²` (the algebraic-number companion to `IntervalBracketEmitter`'s `exp` bracket) | `Real.le_sqrt_of_sq_le` (lower) + `Real.sqrt_le_iff` (upper), the rational side-goals by `norm_num` |
| `HalfPlaneDiskEmitter` | the Borel–Carathéodory / Möbius–Schwarz half-plane→disk core: `Re w ≤ B` (`B > 0` rational) ⟹ `‖w/(2B−w)‖ ≤ 1`, via the Positivstellensatz identity `‖2B−w‖² − ‖w‖² = 4B(B−Re w) ≥ 0` (with optional inversion + reverse-triangle companions) | `norm_div` + `div_le_one` + `Complex.normSq_apply` expansion + `nlinarith [mul_nonneg …, sq_nonneg w.im]` — a B-parameterized copy of the proven `norm_div_two_mul_sub_le_one` |
| `MagnitudeSplitBoundEmitter` | triangle-inequality magnitude split: `‖A‖ ≤ α`, `‖B‖ ≤ β`, `‖C‖ ≤ γ` ⟹ `‖A + B − C‖ ≤ α + β + γ` (fully general; also a concrete-bounds and a general signed-sum `Σ ± termᵢ` variant); refuses a negative bound or an ill-formed shape | `have h1 := norm_sub_le (A+B) C`; `have h2 := norm_add_le A B`; `linarith` — the final assembly of the proven `zeta_log_bound` |
| `DiskCoordBoundsEmitter` | linear coordinate bounds `wr∓ρ ≤ z.re`, `wi∓ρ ≤ z.im` from disk membership `z ∈ closedBall (wr+wi·I) ρ` — a Farkas-style certificate: each bound follows from `\|(z−w).re\| ≤ ‖z−w‖ ≤ ρ` via `(z−w).re = z.re−wr`; refuses `ρ ≤ 0` | a `(wr,wi,ρ)`-parameterized copy of the `zeta_sphere_bound` geometry (`Complex.abs_re_le_norm`/`abs_im_le_norm` + `abs_le`, closed by `linarith`) |
| `CauchyDerivBoundEmitter` | Cauchy's derivative estimate: `f` holomorphic on `ball z0 R`, `‖f‖ ≤ M` on `sphere z0 R` (`R > 0`) ⟹ `‖deriv f z0‖ ≤ M/R`; plus the Borel–Carathéodory constant identity `(2(r+ρ')/(R−(r+ρ')))·(1/ρ') = 4(R+r)/(R−r)²` at `ρ'=(R−r)/2`; refuses `R ≤ 0` | direct `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`; the constant by `have (R−r) ≠ 0` + `field_simp; ring` |
| `LogDerivRegionCoreEmitter` | de la Vallée Poussin log-derivative region core: 3-4-1 positivity + pole/zero/double bounds ⟹ `4k/(σ−β) ≤ 3/(σ−1) + 3A + 5AL` and the cleared region gap; ports the kernel-checked `dlvp_core_estimate`/`dlvp_region_gap` (ζ log-derivatives abstracted to reals as hypotheses) | `linarith` + `field_simp; ring` + `nlinarith` |
| `FiniteArgmaxMarginEmitter` | finite extremality with a strict margin: a designated winner `p_w/q_w` (`q_w>0`) strictly beats every competitor `p_i/q_i` in a finite list, via the cross-multiplied INTEGER facts `p_i·q_w < p_w·q_i` (no division), plus an optional value-load `v_w < 1`; refuses a tie/beat, a nonpositive denominator, or an empty list | one `(p_i*q_w : ℤ) < p_w*q_i := by norm_num` per competitor — the proven `bgext_*_beats_runnerup` pattern |
| `PseudoExpectationDualityEmitter` | "**no degree-`d` SoS refutation** of `{gᵢ = 0}` exists": a pseudo-expectation `E` (`E 1 = 1`, `E(s²) ≥ 0` for `deg s ≤ d`, `E(p·gᵢ) = 0`) blocks every refutation `−1 = Σsⱼ² + Σpᵢgᵢ` (apply `E`: `−1 = (≥0)+0`) — the duality complement of `InfeasibilityEmitter`; 0/1 (`Xᵢ²−Xᵢ`, support-weighted) and ±1 (`Xᵢ²−1`, parity-weighted) modes, multilinear kill proved unconditionally, PSD leaf supplied; refuses `E 1 ≠ 1`, a non-vanishing kill, or a negative moment | `no_refutation` (`map_*` + `Finset.sum_nonneg` + `linarith`) + `pe_bool_kill` (`MvPolynomial.induction_on'` + `support_single_add`/`oddSet_add`) — the proven `KnapsackSOS.Duality`/`Xor3Duality` pattern |
| `OrderBalanceEmitter` | the integer zero/pole-order hinge at the 1-line (`ζ(1+it) ≠ 0`): nonneg-cosine weights `(a₀,…,a_m)` + integer zero orders `(k_j ≥ 1)`, pole giving `+a₀·1` and each order-`k_j` zero `−a_j·k_j`, forcing `a₀ ≥ Σ a_j·k_j` — contradicted by the certified `a₀ < Σ a_j·k_j`; generalizes the proven `zeta_boundary_contradiction` (residue limits as hypotheses); refuses a non-violated balance, order `< 1`, or a negative weight | abstract residue-limit hypotheses ⟹ `False` by `linarith` (+ `exact_mod_cast` for ℤ→ℝ orders) |
| `LFunctionProductEmitter` | the nonneg-cosine → L-product lower bound `1 ≤ ∏ₖ ‖ζ(σ+i·k·t)‖^{aₖ}` (`Re s>1`) from a Fejér-admissible cosine tuple `(a₀,…,a_m)` (`aₖ≥0`, `Σ aₖcos kθ ≥ 0`, re-checked via Chebyshev `x=cosθ` + a Handelman/Fejér–Riesz witness); refuses an inadmissible tuple. Emits the `(3,4,1)` instance for `riemannZeta` (the one Mathlib exposes) | mirrors `zeta_norm_product_ge_one`: `DirichletCharacter.norm_LFunction_product_ge_one` + `LFunction_modOne_eq` + `norm_mul`/`norm_pow` |
| `ParametricHolomorphyEmitter` | analyticity of a parametric tail integral `DifferentiableAt ℂ (fun w => ∫ x in Ioi c, {x}·(x)^{−(w+1)}) z` for `σ₀ < Re z` (`σ₀>0`, `c≥1`), gated by the exact decay inequalities `−σ₀−1 < −1`; the stronger companion to `DominatedIntegrabilityEmitter` (existence). NOTE: thin certificate / heavy fixed skeleton — a borderline emitter (natural home is the lemma pack) | a `(c,σ₀)`-parameterized copy of the proven `differentiableAt_fractIntegral` (`hasDerivAt_integral_of_dominated_loc_of_lip`) |
| `SymmetricQuadFormEmitter` | the level-1 subset-indexed moment form `Φ = f₀·A² + 2f₁·A·X + f₂·X² + (f₁−f₂)·Q ≥ 0` **symbolically in n** (the `subsetForm_d1` object — one certificate covers all n), given moments obeying the rank-collapse identity; d≥2 is future work | the exact completing-the-square + Cauchy–Schwarz congruence `Φ = f₀·(A+(f₁/f₀)X)² + cCS·(n·Q−X²)`: `field_simp; ring` identity + `div_nonneg`/`positivity` + `linarith` |
| `PolytopeMaxMonotoneEmitter` | `0 ≤ p(x)` for a **multi-affine** `p` (degree ≤ 1 per variable) on a box `∏[lᵢ,uᵢ]` — the general-`d` generalization of `BilinearCornerBoxEmitter`; certifies from all `2^d` corners via the barycentric convex-combination identity; refuses a negative corner or degenerate box (d=2,3 build-verified; d≥4 needs a higher heartbeat budget) | a reusable per-`d` `multiaffine_corner_nonneg_d` lemma (slice affinely in each variable — nested `le_total` splits closed by `nlinarith [mul_nonneg …]`) applied to `2^d` `by norm_num` corner facts |
| `SecondOrderRecurrenceEmitter` | a closed form `g(q)` for a second-order (three-term) linear recurrence `A(q)·f(q+2) + B(q)·f(q+1) + C(q)·f(q) = 0` (the Hahn/Krawtchouk/Jacobi generalization of `FwdTelescopeEmitter`); certificate = the exact ring identity + two base cases; refuses a `g` that fails the recurrence | strengthened-predicate two-step `Nat.le_induction`, the recurrence identity by `ring`, leading coefficient cancelled by `mul_left_cancel₀`, bases by `norm_num` |
| `IntegralityGateEmitter` | a strictness/integrality gate: a property holds except on a finite table, the exceptions occurring exactly where a prime `p ∣ n` (the BG 23-gate) | a p-adic tie pin `(p^k ∣ N) ∧ ¬(p^{k+1} ∣ N)` by `norm_num` (`PadicValuationEmitter`) + a finite exceptional table (`norm_num` per row + a guarded `∀ x ∈ table` by `decide`, `FiniteDecideEmitter`) |
| `RecursiveDominationRatioEmitter` | a rational domination ratio `r(params) = P/Q ≥ 1` (all-nonneg-coefficient `P,Q`, `Q > 0`) over a multivariate parameter box — the multivariate-envelope generalization of the finite-argmax margin; cross-multiplies to `P − Q ≥ 0` and certifies it for a multi-affine `D = P−Q` via the `k`-variable corner principle; refuses a sub-1 ratio or degenerate box | `mul_nonneg` corner products + the `ring` convex-combination identity + `mul_pos` denominator positivity, closed by `nlinarith` |
| `AchievabilityClosureEmitter` | replace a relaxed inequality (false on domain `D`) with its restriction to the **achievable** subset `A ⊆ D` where it holds (the cavity-message `μ = 1/(j+1+S) ≤ 1/2` pattern); certifies the restricted inequality *and* a load-bearing witness that it fails on `D∖A`; refuses a phantom or a non-load-bearing cap | the restricted inequality by `nlinarith [mul_nonneg (x−l) (b−x)]`; the achievability bound by `one_div_le_one_div_of_le` |
| `SeparableConvexExtremumEmitter` | separable-convex extremum on the fixed-sum box `{Σxᵢ=S, lᵢ≤xᵢ≤uᵢ}`: the **min** is the homogeneous point `n·φ(S/n) ≤ Σφ(xᵢ)` (Jensen) for convex `φ`, via the tangent line at `S/n`; refuses a non-convex `φ`. (The max/vertex direction is named-open — it needs the spreading-exchange induction.) | per-term `have … = Σcⱼ·bⱼ² := by ring; positivity`, assembled by `linarith [h₁,…, hsum]` |
| `ScaleInvarianceEmitter` | a rational objective `f` is invariant under scaling a parameter — degree-0 homogeneity `f(λ•args) = f(args)` (`λ>0`), or a parameter cancels entirely `f(p)=f(p')` (`∂f/∂p ≡ 0`); models the Arda trading system's leverage↔position_size degeneracy in the Sharpe objective (the algebraic reason `leverage` is a non-evolvable gene); refuses an objective that genuinely depends on the parameter | `field_simp` (nonzero denominators) + `ring` |
| `ConcaveStationaryMaxEmitter` | a stationary point of a strictly-concave objective is its unique maximizer — Kelly-fraction optimality for `g(f)=wr·ln(1+f·b)+(1−wr)·ln(1−f)` on `(0,1)`: ships the two load-bearing facts, the FOC `g'(f*)=0` and strict concavity `−g''(f)>0` on `(0,1)`, from which the unique max follows classically; refuses a non-stationary `f*`, `wr∉(0,1)`, or `b≤0` | FOC `(… : ℝ) = 0 := by norm_num` + `∀ f ∈ Ioo 0 1, 0 < −g''(f)` via denominator-positivity (`nlinarith`) then `positivity` |
| `CustomAssemblyEmitter` | escape hatch for a hand-designed assembly | your skeleton |

*Candidate (not-yet-built) shapes are tracked in the emitter roadmaps under
[`docs/`](docs/) — `EMITTER_ROADMAP_2026-08-21.md` (BG / P=NP backlog: `SymmetricQuadForm`,
`PolytopeMaxMonotone`, `SingularPSD`, …), `EMITTER_ROADMAP_2026-09-02_RH_CROSSCUT.md`
(RH cross-cutting, all 8 shipped), and `EMITTER_ROADMAP_2026-09-02_SWEEP2.md`
(second sweep, all 4 shipped). The two sweeps found the corpus close to
saturated; the remaining roadmap items are the 08-21 BG/P=NP backlog and a few
fold-in sub-modes (`HodgeRiemann`→`psd_form`, `DiscreteConcavity`→`logconcave`).*

Under the positivity shapes sits an automatic search: the Pólya engine
(`polya_lift` — multiply through by `(1+Σxᵢ)^N`, recursively subdivide the box,
solve the rationalizable subset by SOS) turns "true but not obviously in Pólya
form" into a certificate on its own, and `diagnose` tells you which case you are
in — certifiable, not-yet-Pólya (with remedy hints), or actually false (with an
exact rational counterexample).

## The trust model

**The generator is untrusted by design; the Lean kernel is the sole trusted
component.** A defective certificate becomes a compile failure, never a false
theorem — so the correctness guarantee is *independent* of how the certificate
was found. That is the load-bearing inversion: instead of trying to make the
generator trustworthy (hopeless for a heuristic search or an LLM), Telperion
makes its trustworthiness irrelevant. Finding a certificate is hard and can be
delegated to anything; *checking* one is a cheap, mechanical kernel computation.
The exact-arithmetic self-checks exist only to catch mistakes *before* you burn
a CI round-trip — not to establish truth. The corollary is a small, readable,
dependency-light engine (sympy only, a few thousand lines) a referee can audit
rather than trust.

**Why this matters for LLM-generated mathematics.** The defining failure of a
language model let loose on math is the confident *hallucination* — a
plausible-looking lemma, proof step, or numeric claim that is simply wrong, and
wrong in a way that survives casual review precisely because it *reads*
correctly. Telperion structurally forecloses that failure. An LLM (or any
heuristic search) may *propose* a certificate; it can never produce a false
theorem, because the only thing that counts as success is a witness the Lean
kernel re-checks from scratch. A hallucinated sum-of-squares decomposition, a
wrong Handelman multiplier, a fabricated constant — each becomes a red
`lake build`, not an accepted result. The failure mode is downgraded from
"silent false theorem" to "loud rejection," and the component doing the
rejecting is a small, fixed kernel that neither knows nor cares that an LLM wrote
the input — so the guarantee holds no matter how unreliable the generator is.
Hallucination is *contained*, not merely discouraged: the model may be as wrong
as it likes on the inside of the kernel boundary, and nothing false gets out.
(What the kernel does *not* police is whether you asked the right question — a
valid proof of a vacuous or mis-stated goal is still valid. That gap is the job
of the vacuity guard below, the Comparator's independent statement check, and
plain honesty about what you set out to prove.)

**The one thing the kernel cannot catch — vacuity.** The kernel rejects a
*false* theorem, but a *true-but-vacuous* one (`X = X`, `0 ≤ 0`) compiles green
while proving nothing — the defect lives in the *statement*, not the proof.
`nonvacuity.py` is Telperion turned on its own output: `emit()` refuses a
reflexive emitted statement (`check_nonvacuous`), and the identity emitters
additionally require the certificate to be *load-bearing* — corrupting the
certificate must break the claim (`assert_certificate_sensitive`). A family that
deliberately emits reference identities opts out with
`LeanProfile(allow_reflexive=True)`.

## Independent verification — the Comparator (a second opinion)

The kernel tells you *this is valid Lean*; `nonvacuity.py` tells you *the
statement isn't hollow*. But both still rest on a single implementation — Lean's
own kernel and elaborator — and neither can independently confirm that the proof
Telperion emitted proves the statement you actually *meant*. So Telperion can
hand its output to a **second opinion**: the
[Comparator](https://github.com/leanprover/comparator) from OpenAI's
[ten-proofs](https://github.com/openai/ten-proofs), an independent judge for Lean
proofs.

You give the Comparator two modules — a **challenge** (the intended statement) and
a **solution** (Telperion's emitted proof) — and it exports both with
`lean4export` and checks three things the ordinary build cannot:

- **Statement identity.** The solution must prove *exactly* the challenge
  statement, not something weaker — a generator-*independent* form of the vacuity
  guard: the reference statement is authored apart from the certificate, so a
  drifted or hollowed emission is caught by a type mismatch.
- **An axiom whitelist.** A per-theorem, machine-checked `#print axioms` — it
  admits only the axioms you list (the clean `[propext, Quot.sound,
  Classical.choice]`) and rejects anything else, including `native_decide`'s
  `ofReduceBool`, not merely `sorryAx`.
- **A second, non-Lean kernel.** With `enable_nanoda`, the exported proof is
  replayed through [nanoda](https://github.com/ammkrn/nanoda_lib) — a kernel
  written from scratch in Rust — *in addition to* Lean's own. A soundness bug
  would now have to fool two independently-implemented kernels.

`telperion.comparator` is the bridge. It turns an `EmitResult` into a Comparator
challenge config and scaffolds the challenge module for you:

```python
from telperion import (challenge_for_result, render_challenge_scaffold,
                       write_challenge_config)

res = emit(certify(fam), profile, [emitter], validation, file_name="MyFam.lean")
cfg = challenge_for_result(res, profile, challenge_module="MyFamChallenge")
write_challenge_config(out / "MyFam.comparator.json", cfg)
(out / "MyFamChallenge.lean").write_text(
    render_challenge_scaffold(res, profile, module_name="MyFamChallenge"))
```

Sharded (multi-file) emits get one config per shard via
`sharded_challenge_configs(...)`. A full, CI-green worked example — mathlib build,
both kernels, and all — lives in [`examples/bernoulli/lean`](examples/bernoulli/lean/)
(workflow `telperion-comparator.yml`).

**It has been pointed at real proofs, not just the examples.** The three anchor
theorems of the Brualdi–Goldwasser formalization (the `Φ ≤ 1` crux, the g-step /
master-inequality crux, and the conditional R7′ capstone) are re-verified in CI
through the full judge — both the Lean kernel *and* nanoda accept each,
axiom-clean. The analytic-number-theory campaign is guarded in the same spirit
at the kernel level: its unconditional anchors (the elementary and polylog ζ
zero-free regions, the sharp near-line growth bound, the strip representation)
carry a `#print axioms` guard in CI that fails on any hidden `sorryAx` — so a
green build cannot smuggle a gap past a docstring that merely *says* "no sorry".

Two honest notes. First, for verifying *your own* output the sandbox isn't the
point (the kernel replay is), so CI wraps the judge in a shim that sidesteps a
`--`-stripping quirk in landrun's argument parser; a real
[bubblewrap](https://github.com/containers/bubblewrap)-backed sandbox is provided
for the case that actually needs it — judging *untrusted third-party* solutions.
Second, when a statement genuinely can't be re-stated independently (a capstone
whose statement is *about* your own structures), the Comparator runs in
self-check mode — you still get the axiom whitelist and the second kernel, just
not independent statement authorship.

The full reference — the bridge API, the v4.32.0 pins, the sharded path, and the
landrun/nanoda operational notes — is [`docs/COMPARATOR.md`](docs/COMPARATOR.md).

## The workflow (enforced, not advisory)

```
define -> certify() -> validate -> emit() -> lake build (your CI) -> freeze()
              |            |          |
   CertificationError   loud assert   refuses without BOTH the CertifiedFamily
   names every failing  failure       witness AND a green ValidationReport
   (cell, corner)
```

There is no API path from a family definition to Lean text that skips
certification, and `emit()` refuses a red validation report. Emitted files are
stamped with the tool version and a SHA-256 input hash (canonical serialization
of every instance's expressions, the Lean profile, the templates, and the
emitters' own code — timestamps excluded), so `--check` / `diff_frozen()`
detects any drift byte-for-byte, and a change to emission logic can never ship
under a stale hash.

Before you burn a CI round-trip, `emit()` also runs two local gates: a
structural lint (unfilled holes, unbalanced delimiters, duplicate names) and a
**soundness lint** (`telperion lint-lean`) that refuses the "green build ≠
proved" classes — `sorry`/`admit`, smuggled `axiom`, empty `:= by`, missing
type ascription, `Prop := True` trivial stubs.

## Five-minute example

```python
import sympy as sp
from telperion import (GridSpec, InequalityFamily, LeanProfile,
                        DirectPolyaEmitter, ValidationReport, certify, emit)

u = sp.Symbol("u", nonnegative=True)
fam = InequalityFamily(
    name="Demo",
    symbols=(u,),
    grid=GridSpec([("a", [1, 2, 3])]),                       # one theorem per a
    lean_name=lambda pt: f"demo_a{pt['a']}",
    target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
)
res = emit(certify(fam), LeanProfile(namespace=("Demo",)),
           [DirectPolyaEmitter()], ValidationReport(checks=(("spot", True),)))
print(res.files["Demo.lean"])          # kernel-checkable Lean, one theorem per a
```

`telperion init myproof` scaffolds a complete new project — a family template, a
pinned Lean+Mathlib shell, a drift manifest, and a CI workflow — so you can go
from an idea to a CI-checked theorem without wiring any of it by hand. The
fully worked reference is [`examples/toy_box/`](examples/toy_box/) (compiled
against pinned Mathlib in this repo's CI); [`examples/bernoulli/`](examples/bernoulli/)
is the non-BG example, Bernoulli's inequality end-to-end through the core engine.

## Extending it

New kind of statement? Write an emitter. An `Emitter` is a small class that
turns a certified instance into Lean text; it inherits the entire pipeline —
enforcement, provenance hashing, drift net, soundness lint, byte-stability, and
all three agent surfaces — for free. The fifty-plus emitters in the table above
are the working examples: the newest were added by modelling each emitted proof
on a lemma already proven in the corpus, then verifying with a single
`lake build`. `docs/TACTIC_CONTRACT.md` documents the exact Mathlib tactics the
default templates assume; `docs/METHODOLOGY.md`, the discipline. Candidate
shapes still on the roadmap live in `docs/EMITTER_ROADMAP_*.md`.

## Honest scope — what it is and isn't

Telperion is a **certificate compiler, not an autoformalizer.** It proves what
reduces to certified inequalities, identities, valuations, brackets, positivity
certificates, and finite case analysis — a broad and growing class, but not
*every* Lean theorem. It will not invent a structural induction or a clever
lemma for you; it turns "I'm confident this concrete inequality / identity /
bound / certificate holds" into machine-checked Lean, fast and byte-reproducibly.
When a target is *outside* its shapes it says so — `diagnose` triages any refusal
into `FALSE` (with an exact rational counterexample), `NOT_POLYA` (with remedy
hints), or `CERTIFIABLE` — rather than emitting a plausible-but-wrong proof.

The same discipline governs the research campaigns. Telperion formalizes
*classical and certificate-shaped* mathematics: the analytic-number-theory work
is a kernel-checked, unconditional **zero-free region** and its supporting
bounds — classical results, formalized honestly — and carries
`conjecture1_proved = False` throughout; it is **not** progress on the Riemann
Hypothesis, and the Brualdi–Goldwasser and proof-complexity campaigns are held to
the same standard. The project names what it cannot do rather than paper over it.

## Search, when you don't know the certificate yet — `telperion.evolve`

An optional AlphaEvolve/OpenEvolve-style layer that *searches* for a certificate
when you can't write one by hand: it evolves candidate certificate genomes,
scored by the same exact `hunt → certify → parsimony → lake build` cascade, with
a hybrid mutator (a local open-source LLM proposes shapes; structured operators
refine). The trust model is unchanged — the loop only *proposes*; every survivor
still passes the identical kernel gate, and nothing is auto-frozen. It runs
LLM-free out of the box (structured search); the LLM arm is an opt-in extra.

## As a certificate backend for an LLM/RL prover — `telperion prove`

Beyond the family workflow, Telperion exposes a **single-goal front door**:
hand it one goal string (`0 ≤ <expr>` over given symbols) and it routes the
goal through a kind-router to the right emitter and returns a kernel-checkable
aux lemma — deterministic, CPU-cheap, and honest on failure (exact triage:
FALSE with a rational counterexample, or NOT_POLYA with hints). This is the
trust model applied to an LLM prover's inner loop: the model proposes the
subgoal, Telperion returns either a kernel-checked discharge or a clean refusal,
and it never fabricates a proof — so the certificate-shaped fraction of the
model's reasoning inherits the no-false-theorem guarantee for free. The
integration seam is one JSON request/response (`telperion.tactic::discharge`),
with a sketched Lean `telperion_discharge` tactic frontend and a lift harness +
certifiable benchmark for measuring what the backend adds — see
[`examples/backend_integration/`](examples/backend_integration/) and the
frontier-prover gap analysis in
`docs/COMPARISON_ALPHAPROOF_DEEPSEEK_PROVER_V2_2026-08-20.md`. A companion
`audit` verb (the proof-auditor) re-screens any Lean text for the
"green build ≠ proved" classes.

## Using it from LLM agents

Three surfaces, all on the same enforced workflow:

- **CLI** — `telperion <verb>`: `init` (scaffold a project), `certify`, `probe`,
  `prove` (the single-goal backend), `diagnose`, `verify` (regenerate +
  byte-diff the drift net), `lint-lean` (the soundness gate), `audit` (the
  proof-auditor), `benchmark`, plus analysis (`margins`, `ties`, `hunt`,
  `relax`, `sharpen`) and reporting (`latex`, `ledger`, `status`, `package`,
  `export-certs`, `recheck`). Every string-taking surface parses through a
  token whitelist — sympy's evaluating parser never sees raw input.
- **MCP server** — `pip install "telperion[mcp]"`, then
  `claude mcp add telperion -- telperion-mcp`. Tools mirror the workflow
  (`polya_probe`, `certify_family`, `emit_family`, `diff_family`,
  `read_manifest`); there is no path to Lean that skips certification.
- **Claude Code plugin / skill** — [`claude-plugin/`](claude-plugin/) bundles
  the MCP registration with a skill that teaches an agent the discipline (probe
  first, never hand-edit emitted files, never skip validation, compile in CI,
  diff on every change).

## Install

```bash
pip install -e "telperion"        # the engine — sympy only
pip install -e "telperion[dev]"   # + pytest, to run the tests
```

`sympy` is the only core dependency; `import telperion` and the whole
certify→emit pipeline need nothing else. Optional extras: `mcp` (agent server),
`sdp` (cvxpy, for the SOS emitter), `flint` (faster arithmetic). The
`telperion.evolve` search layer needs no extra — it is pure-stdlib, and its
optional LLM arm simply talks to a local [Ollama](https://ollama.com) server if
one is running. See [Origin](#origin) for the `bg` research-lab extra.

## Origin

Telperion was extracted clean-room from the Brualdi–Goldwasser (1984)
Laplacian-ratio proof campaign in [`../proof/`](../proof/), where the pattern
produced thousands of CI-green Mathlib theorems (a 36-cell bilinear certificate
table, 36 dispatch adapters, 72 vee/mirror branches, 42 leg and 55 shedding
certificates — most batches first-try green; `g1_floors` alone is 3,084). That
campaign is still the tool's largest single stress test: its frozen families are
re-certified and byte-diffed in CI, the biggest also compiled against pinned
Mathlib by the `telperion-production` gate.

Two further campaigns then drove the engine well past its origin — the
analytic-number-theory work (the ζ zero-free region, Borel–Carathéodory, the
sharp near-line bound) and the proof-complexity work (SoS refutations and
pseudo-expectation duality). Each contributed new certificate shapes, growing the
catalog to fifty-plus, and each is exercised in CI against pinned Mathlib. The
problem-specific research modules live in the opt-in `telperion.bg` subpackage —
`import telperion` loads **zero** of them (statically and dynamically enforced by
[`tests/test_core_boundary.py`](tests/test_core_boundary.py)), keeping the
general engine small and auditable. Install the `bg` extra (networkx, numpy) only
if you want the research lab.

The methodology — untrusted generator, trusted kernel, numeric-first discipline,
provenance-and-drift — is written up in [`docs/METHODOLOGY.md`](docs/METHODOLOGY.md).


## License

Telperion is source-available under the
[Business Source License 1.1](LICENSE): free for academic research,
teaching, and evaluation; commercial production use requires a license
from the Licensor; each version converts to Apache-2.0 three years after
release. Emitted Lean certificates are excluded from the Licensed Work —
your outputs are yours. The mathematical content elsewhere in this
repository is Apache-2.0/CC-BY-4.0 (see ../LICENSING.md). Engine
contributions require the [CLA](CLA.md).
