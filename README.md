# Telperion

**A general-purpose tool for proving families of mathematical statements in
Lean 4 — by exact-arithmetic certificate and kernel verification.**

You describe your problem as a parameterized *family* of statements; Telperion
certifies each instance in exact rational arithmetic, then emits Lean 4 that
Mathlib's kernel re-proves from scratch. The generator is untrusted by design —
a wrong certificate is a compile error, never a false theorem — so you get
machine-checked proofs without having to trust (or read) the tool that wrote
them.

It was forged as the engine behind a hard research proof (Brualdi–Goldwasser;
see [Origin](#origin)), where it produced 200+ CI-green Mathlib theorems. But
**nothing about the engine is specific to that problem** — the same pipeline
proves an unrelated textbook inequality
([`examples/bernoulli`](examples/bernoulli/)) through identical machinery.
Telperion is now a standalone, problem-agnostic artifact: bring your own
inequality, identity, or bound, and it will try to hand you a kernel-checked
Lean proof of it.

## What you can prove with it

Telperion turns a problem into Lean when you can express it as a *certifiable
family* — a grid of instances, each reducible to one of its certificate shapes.
That covers a large slice of concrete mathematics:

- **Rational-function inequalities** — `0 ≤ f(x̄)` or `g(x̄) ≤ h(x̄)` for
  rational `f,g,h` over nonnegative variables (Pólya positivity; box-corner
  reductions in two variables).
- **Polynomial nonnegativity** — `0 ≤ p(x̄)` via an exact rational
  sum-of-squares (reaches interior equality cases Pólya lifting cannot).
- **Exact identities and arithmetic** — integer/rational identities, powers,
  and closed-form equalities (`ring`/`norm_num` cores).
- **p-adic valuation facts** — `v_p(n) = k` as decidable divisibility.
- **Two-sided transcendental enclosures** — rigorous rational brackets
  `lo ≤ exp(−θ) ≤ hi` at a rational point.
- **Finite case analysis** — dispatch over a bounded parameter (`interval_cases`),
  subdivision of a region into cells and gluing the pieces back.
- **`∀ K ≥ K₀` tails** — a finite table plus one uniform certificate.
- **Assemblies of the above**, in the original variables (substitution glue,
  dichotomies, custom skeletons).

If your statement fits one of these shapes — or a product/quantifier over a grid
of them — Telperion will certify it in exact arithmetic and emit the Lean. If it
needs a new shape, you add an emitter (see [Extending it](#extending-it)); the
trust model and the whole pipeline come for free.

### Certificate shapes (v0.1.6)

Each shape is an *emitter*; all flow through the same `certify → validate →
emit → freeze` workflow.

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
| `CustomAssemblyEmitter` | escape hatch for a hand-designed assembly | your skeleton |

The Pólya engine underneath (`polya_lift`: multiply through by `(1+Σxᵢ)^N`;
recursive box subdivision; SOS for the rationalizable subset) turns "true but
not obviously in Pólya form" into a certificate automatically, and `diagnose`
tells you which case you're in (see below).

## The trust model

**The generator is untrusted by design.** The Lean kernel is the sole trusted
component: a defective certificate manifests as a compile failure, never a false
theorem. The exact-arithmetic self-checks exist to catch mistakes *before* a CI
round-trip, not to establish truth. The design corollary is that the generator
stays small, readable, and dependency-light (sympy only) — a referee can audit
the engine (~a few thousand lines) instead of trusting it.

**The one thing the kernel can't catch — vacuity.** The kernel rejects a *false*
theorem, but a *true-but-vacuous* one (`X = X`, `0 ≤ 0`) compiles green while
proving nothing about the certificate — the defect lives in the statement, not
the proof. `nonvacuity.py` is Telperion pointed at its own output: `emit()`
refuses a reflexive emitted statement (`check_nonvacuous`), and the identity
emitters additionally require the certificate to be *load-bearing* — a corrupted
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
master-inequality crux, and the conditional R7′ capstone) are re-verified this
way in CI: both the Lean kernel *and* nanoda accept each, axiom-clean.

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
enforcement, provenance hashing, drift net, soundness lint, byte-stability, all
three agent surfaces — for free. The existing emitters (thirty-plus, see the
table above) are the working examples; `docs/TACTIC_CONTRACT.md` documents the
exact Mathlib tactics the default templates assume, and `docs/METHODOLOGY.md`
the discipline.

## Honest scope — what it is and isn't

Telperion is a **certificate compiler, not an autoformalizer.** It proves what
reduces to certified inequalities, identities, valuations, brackets, and finite
case analysis — a broad and growing class, but not *every* Lean theorem. It will
not invent a structural induction or a clever lemma for you; it turns "I'm
confident this concrete inequality/identity/bound holds" into machine-checked
Lean, fast and byte-reproducibly. When a target is *outside* its shapes it says
so — `diagnose` triages any refusal into `FALSE` (with an exact rational
counterexample), `NOT_POLYA` (with remedy hints), or `CERTIFIABLE` — rather than
emitting a plausible-but-wrong proof. The project's discipline is to name what
it cannot do, not to paper over it.

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
FALSE with a rational counterexample, or NOT_POLYA with hints). The
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
produced 200+ CI-green Mathlib theorems (a 36-cell bilinear certificate table,
36 dispatch adapters, 72 vee/mirror branches, 42 leg and 55 shedding
certificates — most batches first-try green). That campaign is still the tool's
largest stress test: its frozen families are re-certified and byte-diffed in CI,
the biggest also compiled against pinned Mathlib by the `telperion-production`
gate (e.g. `g1_floors`: 3,084 theorems). Those problem-specific research modules
live in the opt-in `telperion.bg` subpackage — `import telperion` loads **zero**
of them (statically and dynamically enforced by
[`tests/test_core_boundary.py`](tests/test_core_boundary.py)), keeping the
general engine small and auditable. Install the `bg` extra (networkx, numpy)
only if you want the research lab.

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
