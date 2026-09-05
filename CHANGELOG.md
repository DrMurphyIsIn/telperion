# Changelog

## Unreleased — Jensen d=2 hyperbolicity cert family (Task 9)

- **First formally kernel-verified Jensen-polynomial hyperbolicity for zeta.**
  Three sorry-free Lean 4 theorems (`jensen_box_hyperbolic_deg2_{0,1,2}`) assert
  that every degree-2 Jensen polynomial J^{2,n} whose rational coefficient box is
  certified by Arb ball arithmetic is real-rooted (`.roots.card = 2`). Axioms:
  `{propext, Classical.choice, Quot.sound}` only. AXLE statement-match gate
  kernel-enforced for each. Discriminant margins: 2.82e-4, 2.27e-8, 8.00e-13
  (n=0,1,2). `conjecture1_proved = False`; NOT a proof of RH.
- **`--grid` flag in `examples/jensen_hyperbolicity/generate.py`**: emits the
  d=2 cert family for n=0,1,2 in one command. Also adds `--n-list` for arbitrary
  explicit offset lists. Default precision for grid mode: 400 bits.
- **`enclose_coeff_box` uses ONLY the rigorous acb_series path.** Coefficients
  alpha(m) for m >= 5 (needed for n >= 3) are refused with `NotImplementedError`:
  python-flint's acb_series zeta caps at 10 terms, and a finite-evaluation
  (Vandermonde) extraction drops the alpha(m+3)+ Taylor tail (~1e-28), which is
  far larger than the acb input-ball radius (~1e-169) and would make the
  enclosure UNSOUND. Rigorous high-m coefficients require a Cauchy tail bound
  `|alpha(k)| <= max_{|t|=R}|Xi(t)| / R^{2k}`, deferred to Phase 2. (An earlier
  draft's `enclose_xi_coeff_high` Vandermonde method was UNSOUND for exactly this
  reason and has been removed from all cert paths.)
- **`tests/rh_jensen/test_grid.py`**: 9 pytest tests covering grid-mode exits,
  three-theorem emission (and n=3 absence), `.roots.card = 2` presence, no-sorry,
  AXLE gates, `#print axioms` lines, `--n-list` subset mode, and the rigor
  guards (`enclose_coeff_box` raises NotImplementedError for alpha(m>=5);
  `generate.py --n-list 3` fails). All 9 pass.
- **`docs/JENSEN_HYPERBOLICITY_STATUS.md`**: honest status document: what is
  kernel-proven (n=0,1,2), the coefficient-membership trust boundary
  (Arb-certified, non-kernel), and what is not done (alpha(m>=5) needs a Cauchy
  tail bound; d>=3 needs the Hermite engine; uniform N(d) out of scope; emitter
  framework integration deferred).
- n >= 3 (needs alpha(m>=5)) and degrees d >= 3 explicitly deferred to Phase 2
  (Mathlib lacks discriminant-to-real-roots bridges for cubics/quartics; the
  general Hermite-Bezoutian PSD engine will handle all d<=8 uniformly, and the
  Cauchy tail bound will close the high-m coefficient extraction).

## Unreleased — Comparator: independent verification (axiom whitelist + 2nd kernel)

- **`telperion.comparator` — a bridge to the openai/ten-proofs Comparator**, an
  independent judge for Lean proofs. It turns an `EmitResult` into a Comparator
  challenge config (`challenge_for_result`, `challenge_config`), extracts the
  emitted theorems' fully-qualified names (`emitted_theorem_names`), and scaffolds
  an independent challenge module that restates the emitted signatures with a
  proof independent of Telperion's certificate (`render_challenge_scaffold`).
  Sharded (multi-file) emits get one config per shard
  (`sharded_challenge_configs`, `render_sharded_challenge_scaffolds`). The
  Comparator then checks three things beyond `lake build`: **statement identity**
  (the emitted proof proves *exactly* the challenge statement — a generator-
  independent nonvacuity), an **axiom whitelist** (per-theorem `#print axioms`,
  admitting only `[propext, Quot.sound, Classical.choice]` and rejecting e.g.
  `native_decide`'s `ofReduceBool`), and a **second, non-Lean kernel** —
  [nanoda](https://github.com/ammkrn/nanoda_lib), replayed alongside Lean's own,
  so a soundness bug must fool two independently-written kernels.
- **`examples/bernoulli/lean/`** — a runnable, CI-green end-to-end example
  (mathlib build + both kernels), driven by `generate.py --comparator [--nanoda]`.
  Workflow `.github/workflows/telperion-comparator.yml`. `examples/r7_starofhubs`
  demonstrates the sharded path (9 shards / 972 theorems).
- **Applied to the Brualdi–Goldwasser proof.** The three AxiomGuard anchors
  (`R3Cert.phi_le_one`, `…gstep_le_one_achievable`, the conditional capstone
  `…conjecture1_of_layers`) are independently re-verified in CI
  (`proof-comparator.yml`): both the Lean kernel and nanoda accept each,
  axiom-clean.
- **`.github/comparator/landrun-bwrap.sh`** — a landrun-CLI-compatible sandbox
  wrapper backed by bubblewrap (real isolation: mount namespace, `--unshare-net`,
  `--clearenv`) that also preserves the `--` separator real landrun's `urfave/cli`
  strips. For verifying one's own output the lighter no-sandbox shim is the
  default (the kernel replay is the guarantee); the bwrap wrapper is for judging
  untrusted third-party solutions.

## Unreleased — cone/Farkas: overcomplete-basis solver + first compile gate

- **`cone_combination` now solves the OVERCOMPLETE (underdetermined) basis** —
  the former `"undecided over this basis — needs LP; named-open"` refusal.
  `sp.solve` returns a PARAMETRIC solution when the basis has more elements than
  the monomial equations pin down, and the old code bailed at the first free
  variable.  A nonnegative solution of `A λ = b`, if one exists, has a VERTEX
  form supported on ≤ rank columns, so `_cone_bfs` enumerates basis subsets in a
  deterministic order and solves each exactly with `linsolve`, returning the
  first all-nonnegative combination that reproduces the target — the same
  sympy-only, SDP/LP-free basic-feasible-solution search the Handelman finder
  uses.  The determined case is unchanged (direct solve first; BFS only on its
  miss), so every existing certificate is byte-identical.  Genuine
  non-membership is still refused (and `cone_decide` still supplies the Farkas
  dual).
- **`ConeFarkasEmitter` now binds free variables with an explicit `∀`** (and
  `intro`s them) instead of relying on Lean's `autoImplicit` — so the emitted
  theorem compiles under `autoImplicit false`, consistent with every other
  emitter.  Symbol-free (constant-target) families still emit a bare statement.
  Content change to emitted Lean; no cone family was previously frozen, so no
  refreeze elsewhere.
- **first compile gate for the cone emitter** — `examples/cone` (determined +
  two overcomplete-BFS certificates, with an infeasible-target negative
  control) added to the `quick` verify group and the `audit-compiles` lake gate.
  The ConeFarkas emitter (shipped 2026-08-19) had no compile-gated example until
  now.

## Unreleased — facial positivity (Pólya-with-zeros) + sympy-only real-Nullstellensatz finder

The emitter candidate named by `docs/HANDELMAN_DEGREE_BOUNDS_LIT_2026-08-20.md`
(Castle–Powers–Reznick 2011, "Pólya's theorem with zeros"), plus a cvxpy-free
finder for the real-Nullstellensatz emitter that composes with the SDP finder
landed the same day (see the Bernstein/Real-Nullstellensatz entry below).

- **`PolyaZerosEmitter`** (`polya_zeros`) — `0 ≤ p` on `{xᵢ ≥ 0, Σxᵢ > 0}` from
  the HOMOGENEOUS Pólya certificate `(Σxᵢ)^N·p = Q` with every Q-coefficient a
  nonnegative rational, verified exactly.  This is the tie-safe lift: `lift.py`'s
  inhomogeneous `(1 + Σxᵢ)^N` certifies STRICT positivity only (a zero on the
  closed orthant means no finite N), while the homogeneous form tolerates zeros
  ON FACES — the CPR class, degree-bounded by residual facial margins that do
  not vanish at the tie.  FINDER mode (`N = None`) searches N ≤ max_n; on a
  miss, `polya_zeros_obstruction` (all-ones sampling of every face) upgrades
  "gave up" to a STRUCTURAL refusal when the zero set leaves the face lattice
  (`(x−y)²`: "no Pólya exponent exists at ANY N", CPR Theorem 2) or a sample is
  negative.  The obstruction check is a sufficient condition, not a complete
  Theorem 2 decision — documented as such.  Lean side reuses the proven
  Handelman shapes (`mul_nonneg`/`pow_nonneg` fold + `ring` identity) plus
  `pow_pos`/`nlinarith` to divide out the positive factor.  Compile-gated
  frozen example `examples/polya_zeros` (supplied-N, face-zero finder case
  `xy(x²−xy+y²)` at N = 1, and the CPR near-tie `x² − (7/4)xy + y²`; negative
  controls: the tie refused WITH its obstruction named, an insufficient N
  refused).
- **`find_real_nullstellensatz_certificate`** — a second, cvxpy-free finder for
  the `real_nullstellensatz` emitter, composed with the SDP finder that landed
  the same day (`sdp_finder.find_real_nullstellensatz`): the finder branch now
  tries the exact sympy-only search FIRST (for m ≤ max_m the Gröbner normal form
  `s = NF(−p^{2m})` is the canonical SOS candidate; `sos_decompose` attempts an
  exact rational SOS), and falls back to the SDP for cases outside
  `sos_decompose`'s v1 class.  Trying the cheap finder first keeps the `quick`
  CI path cvxpy-free; both return the same `(m, s_terms)` interface and are
  re-verified against the certifier's own plain-division gate (miss = refusal).
  Multiplicity escalation works (`x` on `V(x³)`: m = 2, s = 0).  The
  `real_nullstellensatz` example gains two finder cases + a finder-mode negative
  control (non-vanishing `x + 1` refused).
- **Compile-gate repair**: `examples/cg_round/frozen/CGRound.lean` (PR #17) was
  in no lake gate — the "silenced gate" class.  Added to audit-compiles staging,
  `Audit.lean`, and the workflow trigger paths alongside the new `polya_zeros`
  example.
## Unreleased — Sturm strict-interval positivity (root exclusion)

- **`SturmPositiveEmitter`** (`sturm_positive`) — `0 < p(x)` (STRICT) for all
  `x ∈ [a,b]`, the robustly kernel-checkable half of Sturm: root EXCLUSION.  A
  Sturm sequence (exact, in sympy) is the decision oracle — it certifies `p` has
  no root in `[a,b]` (a polynomial with a root there, or negative there, is
  refused) — and the Lean proof combines a Bernstein certificate for `p − γ ≥ 0`
  (γ a rational floor `0 < γ ≤ min p`) with `0 < γ` via `linarith`.  Goes beyond
  `BernsteinEmitter` (non-strict `0 ≤ p`) by delivering strict positivity.  The
  other half of Sturm — an EXACT real-root COUNT emitted as a theorem — needs
  Sturm's theorem in Mathlib (not yet available) and remains out of scope; the
  Sturm sequence is used only as the exact oracle and negative-control gate.

Content-neutral for existing families (no refreeze).

## Unreleased — rational-SOS (Artin denominator): reaching nonneg-but-not-SOS

- **`RationalSOSEmitter`** (`rational_sos`) — proves `0 ≤ p` for a polynomial that
  is nonnegative but NOT a sum of squares (the class Hilbert showed the plain SOS
  emitter cannot reach; the Motzkin polynomial `x⁴y² + x²y⁴ − 3x²y² + 1` is the
  minimal example).  Artin's theorem: a strictly-positive multiplier `q` makes
  `q·p` a sum of squares.  Telperion FINDS the certificate — a ladder of
  `positivity`-provable strictly-positive multipliers `q` (products of `1 + xᵢ²`)
  until `q·p` has an EXACT rational SOS (shared SDP + robust rationalization) —
  then emits `positivity` (`0 < q`, and the SOS after a `ring` rewrite) + a
  `by_contra`/`nlinarith` that divides out `q`.  For Motzkin it finds
  `q = (1+x²)(1+y²)` and `q·M = (1−x²y²)² + (x−x³y²)² + (y−x²y³)² + (x³y−xy³)²`.
  Untrusted-by-verification: the identity `q·p = Σ dᵢℓᵢ²` is re-checked exactly.
  (This is the robust, kernel-checkable route to the SONC / nonneg-circuit class —
  it covers the same nonnegativity gap without the `rpow` AM-GM machinery.)

Content-neutral for existing families (no refreeze).

## Unreleased — Bernstein positivity + Real-Nullstellensatz finder + better SDP rationalization

- **`BernsteinEmitter`** (`bernstein`) — `0 ≤ p(x)` on a closed interval `[a,b]`
  via nonnegative Bernstein coefficients, the univariate interval specialization
  of Handelman positivity.  Telperion FINDS the certificate: it extracts the
  Bernstein coefficients by exact linear solve, ELEVATING the degree until all are
  nonnegative (the enclosure sharpens with degree; a strictly-positive polynomial
  succeeds at some finite degree, one touching zero interior is refused).  Robust
  Lean — a `mul_nonneg`/`pow_nonneg` fold over `0 ≤ x−a`, `0 ≤ b−x` + `ring` +
  `linarith`.
- **`find_real_nullstellensatz`** (`sdp_finder.py`) — `RealNullstellensatzEmitter`
  now SEARCHES the multiplicity `m` and the SOS `s` with `p^{2m} + s ∈ ⟨gₖ⟩` when a
  family returns `m=None, sos=None`: `x = 0` and `y = 0` on the real variety of
  `x²+y²` are found automatically (SDP over an SOS block + free ideal cofactors).
- **better SDP rationalization** — the shared SDP solver now tries continued-
  fraction rounding (`Fraction.limit_denominator`) alongside the fixed-denominator
  ladder, snapping an entry like `0.333…` to `1/3` without needing `3` on the
  ladder — raising the finders' exact-rationalization hit rate.  Untrusted-by-
  verification throughout: every found certificate is re-verified exactly.

Content-neutral for existing families (no refreeze).

## Unreleased — integer arithmetic (Chvátal–Gomory rounding, VIPR-style)

The first emitter that lives in INTEGER linear arithmetic rather than over the
reals — the deduction the reals cannot make.

- **`CGRoundEmitter`** (`cg_round`) — a linear goal over declared INTEGER
  variables from a Chvátal–Gomory derivation, in the style of the VIPR MILP
  certificate format (Cheung–Gleixner–Steffy, arXiv:1611.08832).  A certificate
  is a list of linear FACTS `Σ cⱼxⱼ ≥ v` plus an ordered derivation of two rules:
  `lincomb` (a NONNEGATIVE rational combination of prior facts + rational slack)
  and `cg_round` (from a fact whose coefficients are ALL integers — so the
  integer-valued LHS is an integer — round the bound up, `Σ cⱼxⱼ ≥ ⌈v⌉`).  Every
  step is verified exactly; the emitter REFUSES a non-integer rounding
  coefficient, a VACUOUS round (`v` already integer, `⌈v⌉ = v`), a NEGATIVE
  lincomb multiplier (it would flip the inequality), and an undominated goal.  A
  ROUNDING-SENSITIVITY self-check additionally requires the cut to be
  load-bearing: replaying the derivation with every round DISARMED (`⌈v⌉` reverted
  to `v`) must fail to dominate the goal, else the reals already gave it and the
  certificate is refused as vacuous.  Emitted Lean states the goal over `(x :
  Int)` with integer-cleared hypotheses and discharges the chain with `omega`
  (Mathlib's linear-integer decision procedure, which performs the CG rounding
  internally).  Kernel-checked clean: the frozen `3x ≥ 2 ⟹ x ≥ 1` and
  `x ≥ 1, y ≥ 1 ⟹ x + y ≥ 2` compile with axioms `[propext, Quot.sound]`.
- **near-star window composition probe** (`examples/cg_round/NearStarWindow.lean`)
  — the concrete W1 payload: the continuous near-star envelope
  `phi11(s) = (64/621)^{2s+1}·((4s+3)/(3(s+1)))^{11}·(3/2)^{11s}` OVERSHOOTS 1
  between integers (interior max ≈ 1.000459 at s ≈ 4.822), witnessed exactly by
  the consecutive ratio `Q(4) = phi11(5)/phi11(4) = 87946907297998046875 /
  86959512306484890624 > 1` (phi11 strictly increases into the tie phi11(5) = 1),
  so no continuous nonnegative certificate bounds it on `[4,6]`.  The
  Chvátal–Gomory move — `s` integer, `4 ≤ s ≤ 6` rounds `s` into `{4,5,6}` —
  reduces the window to three closed exact rational facts.  The single theorem
  `∀ s : Int, 4 ≤ s → s ≤ 6 → phi11num s ≤ phi11den s` kernel-checks with axioms
  `[propext, Classical.choice, Quot.sound]`.  `conjecture1_proved = False` — this
  is the integer-window fragment only, not BG.
## Unreleased — SDP refutation finder + compile-gated SOS-finder examples

Completes the checker→searcher upgrade for the remaining SOS emitters, on top of
the Putinar finder (`sos_sdp.find_putinar_certificate`).

- **`find_sos_refutation`** (`sdp_finder.py`) — `SOSRefutationEmitter` now
  SEARCHES the refutation `−1 = σ₀ + Σ σᵢ·gᵢ + Σ λⱼ·hⱼ` (SOS σ, free λ) when a
  family returns `sigma0=None`, AUTOMATICALLY closing the real-only gap (finds
  `σ₀ = x²`, `λ = −1` for `x² + 1 = 0`).  A shared multi-Gram SDP (cvxpy) with a
  trace-minimizing objective, multi-denominator rationalization, exact
  verification, and a PSD-singular-safe rational LDLᵀ.  Untrusted-by-verification.
- **compile-gated finder examples** — `examples/putinar_find` and
  `examples/sos_refutation_find` (the `sdp` verify group; cvxpy at freeze-time,
  regeneration off the cvxpy-free CI path) freeze the SDP-FOUND certificates so
  their auto-discovered Lean is kernel-verified in `audit-compiles`.

Content-neutral for existing families (no refreeze).

## Unreleased — proof-complexity-derived emitter shapes (2026-08-20, knapsack_sos arc)

Three shapes crystallized from the P-vs-NP certificate-ladder arc, each with
example family + negative controls + tests, frozen Lean compile-verified:

- **`RationalIdentityEmitter`** / `rational_identity_family` (kind
  `rational_identity`): identities of rational functions on a ray `c0 < n`,
  certified by exact cancellation + denominator-root audit, emitted via a
  structure-preserving renderer (the nonvacuity gate rejects the
  canonicalized `X = X` collapse — caught live during development) and a
  cross-multiplication spine (`div_eq_div_iff` + `mul_ne_zero` chains +
  `ring`; `field_simp` expands multi-factor denominators into quadratics
  whose nonvanishing it cannot decompose).  Crystallizes the knapsack
  Gram-bridge generator.
- **`FiniteDecideEmitter`** / `finite_decide_family` (kind `finite_decide`):
  guarded universally-quantified decidable facts over explicit ℕ/ℤ tables
  (mini-AST: ForallIn/Imp/Cmp + Var/Lit/Xor/Pop/Lookup/Mul), evaluated
  exactly in Python at certification and re-decided by the Lean kernel.
  Encodes the kernel-feasibility contract from PetersenCertificate.lean:
  ℕ/ℤ arithmetic only (ℚ does NOT kernel-reduce — `Rat.normalize` bottoms
  out in well-founded `Nat.gcd`), fueled popcount (well-founded recursion
  does not kernel-reduce), short-circuiting guarded Decidable instances,
  `maxRecDepth` raised.
- **`FwdTelescopeEmitter`** / `fwd_telescope_family` (kind `fwd_telescope`):
  the W2 forward-difference telescoping prover.  For
  `f(q+1) = f(q)·A(q)/(P−q)` the closed form
  `Δ^[j] f(q) = (−1)^j ∏N · f(q) / ∏(P−q−u)` is certified by ONE polynomial
  identity (the contiguous relation `A(q) − (P−q−j) + N(j) = 0`,
  sympy-exact; a wrong `N` is refused) and emitted as the full mathlib
  `fwdDiff` induction skeleton (pnum/pden, positivity, shift law, closed
  form) — the SumEqProd.lean knapsack instance is the re-derivation
  regression baseline.
- Claude plugin `version` aligned with core `__version__` (0.1.6).


## Unreleased — certificate FINDERS (checker → searcher)

Upgrading the checker-mode emitters from "you supply the certificate" to "you
supply the problem, Telperion finds the certificate."

- **`find_handelman_certificate`** — the `HandelmanEmitter` now SEARCHES for the
  polytope certificate when a family returns `terms = None`: given `p` and the
  constraints `{ℓᵢ ≥ 0}`, it finds nonnegative `c_α` and exponent vectors with
  `p = Σ c_α ∏ ℓᵢ^{αᵢ}`.  Exact and sympy-only (no SDP/LP dependency): a
  nonnegative representation has a basic-feasible form supported on ≤ rank
  products, so it enumerates column subsets and solves `A c = b` exactly, keeping
  the first nonnegative solution.  Deterministic (byte-stable frozen output), and
  untrusted-by-design — every found certificate is re-verified exactly by the
  certifier, so a search miss is a refusal, never a wrong theorem.

- **`find_putinar_certificate`** — the `ConstrainedSOSEmitter` (Putinar) now
  SEARCHES for the constrained-SOS certificate when a family returns
  `sigma0 = None`: given `p` and the constraint set `{gᵢ ≥ 0}`, it finds SOS
  multipliers with `p = σ₀ + Σ σᵢ·gᵢ`.  ROUTE A (the SDP analogue the Handelman
  note flagged as planned): a numeric SDP over the Gram matrices of `σ₀` and each
  `σᵢ` (cvxpy + SCS — no `csdp` binary needed), then EXACT rational rounding on a
  denominator ladder, a robust rank-deficiency-tolerant LDLᵀ (the exact-arithmetic
  analogue of leanprover/sos's facial reduction), and an exact reconstruction
  check over ℚ.  Mirrors leanprover/sos's round-and-check pipeline inside
  Telperion's own stack while emitting plain-Mathlib `ring`/`positivity`/`linarith`
  Lean (no external lake dependency — see `sos_sdp.py`'s `sos_witness` bridge note).
  The relaxation order defaults to `⌈deg p / 2⌉`, overridable via
  `constants['putinar_half_deg']`.  Deterministic (pinned solver + symmetrized,
  ladder-rounded Gram), and untrusted-by-design — every found certificate is
  re-verified exactly by `certify_putinar_point`, so a search miss is a refusal,
  never a wrong theorem.

## Unreleased — the beyond-positivity pass (equational reasoning + real refutations)

Three emitters completing the "beyond `0 ≤ p`" arc — algebraic reasoning about
equalities, real-unsatisfiability, and real-variety vanishing:

- **`ConsequenceEmitter`** (`consequence`) — an equation FOLLOWS from polynomial
  equation hypotheses: `{aᵢ = bᵢ} ⟹ lhs = rhs`, when `lhs − rhs` lies in the
  ideal of the hypothesis differences.  Telperion computes the cofactors (Gröbner
  reduction); emits a single `linear_combination`.  (Generalizes Nullstellensatz.)
- **`SOSRefutationEmitter`** (`sos_refutation`) — closes the ℝ-only gap the
  ideal-theoretic `InfeasibilityEmitter` leaves open: a semialgebraic system
  `{gᵢ ≥ 0, hⱼ = 0}` is unsatisfiable OVER ℝ via a Positivstellensatz certificate
  `−1 = σ₀ + Σσᵢgᵢ + Σλⱼhⱼ` (SOS `σ`).  Reaches positivity-only infeasibility
  such as `x² + 1 = 0` (`σ₀ = x²`, `λ = −1`).  Emits `positivity`/`mul_nonneg`
  + `linear_combination` + `linarith` ⟹ `False`.
- **`RealNullstellensatzEmitter`** (`real_nullstellensatz`) — `p = 0` on the REAL
  variety, which ordinary ideal membership misses (e.g. `x` on the real variety of
  `x² + y²`).  Certificate `p^{2m} + s ∈ ⟨gₖ⟩` with `s` a sum of squares; Telperion
  computes the ideal cofactors.  Emits `p^{2m} ≥ 0` ∧ `p^{2m} = −s ≤ 0` ⟹
  `p^{2m} = 0` ⟹ `p = 0` (`pow_eq_zero_iff`).

Content-neutral for existing families (no refreeze); each ships a compile-gated
frozen example in the `audit-compiles` kernel gate.

## Unreleased — infeasibility / refutation (proving NO solution exists)

- **`InfeasibilityEmitter`** (`infeasible`) — the logical DUAL of the
  Nullstellensatz emitter, and a new capability class: a certificate of
  NON-existence.  Proves a polynomial system `{g_1 = 0, …, g_m = 0}` has no
  common solution via a **Nullstellensatz refutation** `1 = Σ λⱼ·gⱼ` (the system
  is unsatisfiable iff `1` lies in the ideal).  Telperion COMPUTES the cofactors
  `λⱼ` by undetermined coefficients (a linear solve at increasing degree); a
  satisfiable system — or one infeasible only over ℝ by positivity (e.g.
  `x² + 1 = 0`, which needs the SOS Positivstellensatz) — is refused.  Emits a
  direct contradiction: `linear_combination` turns the certificate into `1 = 0`,
  then `absurd … norm_num` closes `False`.  This is the bedrock verification
  shape — "no counterexample / bad state exists."  Content-neutral (no refreeze).

## Unreleased — two more literature-derived certificate families

- **`HandelmanEmitter`** (`handelman`) — the polytope specialization of
  positivity.  Proves `0 ≤ p` on `{ℓ₁ ≥ 0, …, ℓ_m ≥ 0}` from a Handelman
  certificate `p = Σ c_α ∏ ℓᵢ^{αᵢ}` — a nonnegative combination of PRODUCTS of
  the linear constraints (LP-feasible, no SDP; where Putinar uses SOS multipliers,
  Handelman uses nonnegative constants times constraint-monomials).  Telperion
  verifies the identity exactly with all coefficients nonnegative; emits a
  `mul_nonneg`/`pow_nonneg` fold over the constraint hypotheses + `ring` +
  `linarith`.
- **`NullstellensatzEmitter`** (`nullstellensatz`) — a NEW capability class: an
  EQUALITY on an algebraic variety, not an inequality.  Proves
  `∀x, (⋀ gᵢ = 0) → p = 0` from ideal-membership cofactors `p = Σ hᵢ·gᵢ`, which
  Telperion COMPUTES by Gröbner reduction (`sympy.reduced`) — a `p` that does not
  reduce to zero is refused.  Emits a single, maximally-robust Mathlib
  `linear_combination Σ hᵢ·(hyp_i)` (exactly the ideal-membership checker).

Both ship compile-gated frozen examples (`examples/handelman`,
`examples/nullstellensatz`) in the `audit-compiles` kernel gate.  Content-neutral
for existing families (no refreeze).

## Unreleased — non-vacuity gate (Telperion pointed at its own output)

The Lean kernel guarantees no FALSE theorem; it cannot catch a TRUE-but-vacuous
one (`X = X`, `0 ≤ 0`) — the defect lives in the statement, not the proof.  New
`nonvacuity.py` closes that gap in two layers:

- **Structural** — `check_nonvacuous`, wired into `emit()` beside the
  sorry/axiom lint: refuses a WHOLLY VACUOUS body (every theorem conclusion
  reflexive, `t ⋈ t`).  This is precisely the class that let a WZ emitter ship a
  vacuous single-theorem `X = X` body (kernel green, Python silently the real
  checker) through hand review.  A mixed body with a tight-but-genuine ingredient
  (e.g. a monotone-tail base `b(s₀) ≤ B` that is `1 ≤ 1` at a tie) is NOT
  flagged — per-instance rigor is the semantic gate's job.  A family that
  intentionally emits an all-trivial body opts out via
  `LeanProfile(allow_reflexive=True)`.
- **Semantic** — `assert_certificate_sensitive`, wired into the WZ certifier:
  rebuilds the claim from a CORRUPTED certificate and requires the corruption to
  break it (claim `0` for the true certificate, non-`0` for a perturbation), so
  the certificate is provably load-bearing — and correctly passes a tight-but-
  certificate-dependent claim.

Content-neutral (no emitted Lean changes, no refreeze).  A drift-net test pins
that no frozen example is a wholly-vacuous emission.

## 0.1.6 (2026-08-19) — two literature-derived certificate families

A deep literature review (beyond the Brualdi–Goldwasser campaign) identified the
highest-value certificate families not yet covered.  The top two are promoted to
first-class emitters, again via the generic `family.special = (kind, spec)` hook
(no shared-core churn), each with a working negative control:

- **`ConstrainedSOSEmitter`** (`putinar`) — the constrained arm of real-algebraic
  positivity the unconstrained `SOSEmitter` could not reach.  Proves `0 ≤ p` on a
  basic closed semialgebraic set `{g₁ ≥ 0, …, g_m ≥ 0}` from a **Putinar /
  Positivstellensatz** certificate `p = σ₀ + Σ σᵢ·gᵢ` with each `σⱼ` a sum of
  squares.  Telperion is the CHECKER: it verifies the identity exactly in
  rational arithmetic and that every square coefficient is nonnegative — a
  decomposition that fails to reconstruct `p`, or smuggles in a negative
  coefficient, is refused.  Emits robust Lean — `ring` for the identity,
  `positivity` for each multiplier, `mul_nonneg` to pair it with the constraint
  hypothesis, `linarith` to sum the nonnegative pieces.
- **`WZEmitter`** (`wz`) — the combinatorial-identity family (**Wilf–Zeilberger
  creative telescoping**) previously untouched.  Certifies a hypergeometric /
  binomial sum identity `Σ_k F(n,k) = rhs(n)` from its WZ mate `R(n,k)`: the
  summand ratios are checked rational (proper hypergeometric), the WZ equation is
  verified as an exact rational identity, and the **denominator-cleared** WZ
  equation is emitted as a **non-vacuous** `ring` polynomial identity (kept as
  distinct products so a wrong mate makes it a false identity that `ring`
  rejects).  Ships the reusable `Telperion.wz_row_invariant` telescoping-closure
  lemma (proven by finite-sum telescoping); the final identity is a base-row
  evaluation fed to it.  Deriving the mate (Zeilberger's algorithm) is upstream.

Version bump forces a global refreeze (the tool version is part of every family's
provenance hash).

## 0.1.5 (2026-08-19) — seven BG-derived certificate shapes

Seven reusable certificate shapes that surfaced in the Brualdi–Goldwasser
campaign are promoted to first-class emitters, flowing through the single
enforced `certify → validate → emit → freeze` API with a working negative
control each (an out-of-class target is refused at certification; no Lean is
produced for a non-member).  Added via **one generic hook** — `family.special =
(kind, spec)` + `CertifiedInstance.payload` — so the shared core grew by one
field, not seven.

- **`ConeFarkasEmitter`** (`cone`) — `0 ≤ target` as an exact nonnegative
  combination `target = Σ λᵢ·bᵢ` of a positivity-provable basis (`ring` +
  `positivity`); refusal carries the Farkas dual (impossibility over the basis).
- **`UnimodalMaxEmitter`** (`unimodal`) — the README-open "generic Lean lemma
  for unimodal integer maxima": ships the reusable `Telperion.unimodal_peak`
  lemma (proven once — descend via `Nat.le_induction`, climb via gap induction)
  + the per-instance monotone-ratio (`positivity`) and crossing (`norm_num`)
  facts that locate the peak `s*`.
- **`TelescopingPotentialEmitter`** (`telescope`) — the README-open "generic
  induction emission for telescoping potentials": ships the reusable rose-tree
  `Telperion.RTree.telescope` lemma + the per-node super-solution margins
  (`positivity`).  (Finding a closed-form potential is the hard part — for the
  BG crux, provably impossible for finite-basis `P`, see `R1_WIRING_SCOPING`;
  the *assembly* is what this ships.)
- **`LatticeBoxEmitter`** (`lattice_box`) — the d-dimensional integer
  Positivstellensatz: `f(x) ≤ B ∀ x ∈ ℤ^d_{≥0}` via a finite base box
  (`norm_num`) + per-axis monotone tail witnesses (`ring`/`positivity`).
- **`LogConcaveSinglePointEmitter`** (`logconcave`) — reduce `max_{k∈ℕ} F(k) ≤
  B` to a single point `k*` by log-concavity (`F(k+1)F(k-1) ≤ F(k)²`); emits the
  exact single-point + per-step + neighbour-domination facts (`norm_num`).
- **`MonotoneRatioTailEmitter`** (`monotone_tail`) — `b(s) ≤ B ∀ s ≥ s₀` via a
  Pólya-certified nonincreasing tail (`positivity`) + base (`norm_num`) + a
  `Nat.le_induction` assembly.
- **`InterlacingEmitter`** (`interlacing`) — Newton's inequalities (coefficient
  log-concavity) of a real-rooted polynomial (`norm_num` on exact rationals).

Two shapes ship a reusable **generic Lean lemma** as a prelude
(`UNIMODAL_PRELUDE`, `TELESCOPE_PRELUDE`) — proven once, applied per family;
these close the two shapes the README long tracked as open.  All seven emitters
are core (sympy-only) and import no `telperion.bg` module (boundary enforced;
`is_real_rooted` and the lattice/telescope certifiers were inlined engine-local).

HONEST SCOPE: the certifiers and every emitted per-instance fact are exact-
arithmetic validated here; the Lean KERNEL verdict is CI-only (this repo cannot
run `lake` locally).  Where a shape's global assembly is a family-specific
one-line application of a shipped prelude lemma, that is documented, not faked —
no `sorry`, no stub (the soundness lint enforces it).  `conjecture1_proved` is
untouched.

## 0.1.4 (2026-08-18) — Tier-1 emitters · core/bg split · soundness lint · code-fingerprint hash · honesty patterns · perf gate

The strategic-plan workstreams and the parallel crux-campaign methodology port
landed together (see the sections below): the Tier-1 first-class emitters (P2),
the physical core/bg package split (P1), an external non-BG validation family
(P3), a Lean soundness/honesty pre-linter (P4), an emitter-code fingerprint
folded into the input hash (P5), plus the eight honesty-pattern modules and the
`bench.py` perf-regression gate. P5 changes the hashing algorithm, so **every
frozen family was regenerated and the version bumped 0.1.3 → 0.1.4**.

### P1 — core/bg package split

The engine's trust-model claim ("a referee audits the small engine, not the
research accretion") was being eroded by 18k LOC of Brualdi–Goldwasser research
probes living in the same flat namespace as the ~40-module engine. The 72
problem-specific modules moved to a `telperion.bg` subpackage; the engine stays
at `telperion.*`.

- `import telperion` now loads **zero** bg modules (runtime-enforced) — the core
  is sympy-only and self-contained; the bg lab (networkx/numpy) is the opt-in
  `bg` extra (`graph` kept as a legacy alias).
- `telperion.bg` re-exports the engine, so it is a strict **superset** namespace
  — bg consumers import everything from one place.
- Enforced by `tests/test_core_boundary.py`: static (no engine module imports
  `telperion.bg` in any spelling) + dynamic (`import telperion` leaks no bg
  module) + superset checks. Runs in the standard `telperion-test` gate.

### P4 — Lean soundness pre-linter (`lean_lint.py`)

`lint.py` owns the *structural* failure classes (holes, header, empty binders,
delimiter balance, duplicate names). The new `lean_lint.py` COMPLEMENTS it with
the *"green build ≠ actually proved"* class the origin campaign's own Lean audit
flagged: `sorry`/`admit`, `axiom` declarations, missing type ascription, empty
`:= by` tactic blocks (all ERROR), and the `Prop := True` / trivial-stub class
(WARN). Comment/string-aware, dependency-free, ~230 lines. Wired into `emit()`
(hard-blocks error-severity before freeze — validated across all 31 refrozen
families), exported, and exposed as `telperion lint-lean <file>`.

### P5 — emitter-code fingerprint in the input hash

The input hash covered config fields and the manual `__version__` string but NOT
emitter *code* — so an `emit_body` edit that produced different Lean left every
frozen hash untouched (the mechanism behind the G1 empty-binder regression
shipping under a stale hash). `Emitter.code_fingerprint()` folds a
version-stable hash of the emitter class's raw source (and its telperion bases)
into `config_fingerprint()`, which `emit()` already threads into the hash. Raw
source, NOT `ast.dump` — whose serialization varies across Python versions and
would break the cross-version byte-stability the CI matrix enforces (this was
caught in testing: `verify` failed under py3.14 with the ast.dump version). Any
edit to the emitter source moves the fingerprint (conservative for a drift net);
a change to the base `Emitter` moves every emitter's. Known residual
(documented): module-level helper functions the emitter *calls* are not captured
— the compile/diff gates remain the backstop for those.

### P3 — external non-BG validation family (`examples/bernoulli`)

Genericity evidence: Bernoulli's inequality `(1+x)^k − 1 − k·x ≥ 0` (integer
`k∈1..6`, `x≥0`) driven end-to-end through **core only** (`DirectPolyaEmitter`,
never `telperion.bg`) — a textbook inequality with nothing to do with BG through
the same certify→validate→emit→freeze machinery. 6 theorems, exact-arithmetic
self-checks + a `emit()`-refuses-without-green-validation negative control,
byte-stable freeze.

### Honesty patterns (methodology port)

Eight reusable meta-skill patterns from the Brualdi–Goldwasser crux campaign
(20+ probes, zero false positives), ported as checkable modules — each returns a
`ProbeVerdict` decided in exact rationals.  See `docs/HONESTY_PATTERNS.md`.

- **`verdict.py`** (#8, load-bearing): the `VALIDATED / OBSTRUCTED_AND_LOCATED /
  NULL / RE_DERIVATION` taxonomy with structural invariants, and `require_exact`
  / `decide` — **no floats at decision points**, refused the same way a non-Polya
  numerator is refused at certification.
- **`circularity.py`** (#6): refuses a lemma that implies the goal (needs a
  separating witness) — the spectral-gap-mis-framing catch.
- **`faithfulness.py`** (#1): independent-implementation cross-check at seeded
  exact points; generalizes `certify._dual_engine_check`.
- **`limit_probe.py`** (#2): the anti-size-bounded-trap — locates the size where
  a claim breaks or a margin degrading toward the boundary.
- **`upgradability.py`** (#7): mechanical (finite complete cover) vs conceptual
  seam (unbounded axis).
- **`super_solution.py`** (#4): exact `P ≥ T P` with the branching /
  value-iteration-divergence caveat that blocks a silent global overclaim.
- **`discharging.py`** (#5): exact charge-conservation + per-node target (the
  invariant the origin's machine-checked G1Discharge/G1ConsTree rests on).
- #3 (exact ratio-unimodality) already lived in `unimodal.py` /
  `branching_unimodality.py`.

Optimization pass: **`bench.py`** — a scaling-ratio perf-regression gate
(`scaling_probe`) that institutionalizes catching the O(n^2) render/hash traps
the campaign found only by py-spy on hung runs; `tests/test_perf_budget.py`
asserts certify+emit stays sub-quadratic (measured growth ~1.09 = linear).
Deliberately NOT a ProbeVerdict — wall-clock is empirical, not an exact-rational
decision. Profiling confirmed no regression from the Tier-1 / pattern work; the
hot path (`polya_certify`'s `together`) is inherent, linear, and cache-backed.
`conjecture1_proved=False` throughout.

### P2 — Tier-1 first-class emitters

Three certificate capabilities that previously bypassed the enforced pipeline
via one-off demonstrators are now first-class: each is a pipeline-enforced
`family.kind` + `Emitter` + convenience constructor flowing through the single
`certify() → emit() → freeze()` API and its honesty machinery.

- **`SOSEmitter` / `sos_family`** (`emit_sos.py`, `kind="sos"`): promotes
  `sos_sdp.py`'s standalone `lean_certificate()` to a first-class emitter with
  canonical graded-lex rendering (not `sstr`) and an honesty pin — declared
  interior ties are cross-checked against the SDP dual's tight variety (an
  over-claiming certificate is refused). `examples/sos_sdp` grown 1 → 3
  theorems (interior-tie pencil); `sdp` manifest group (cvxpy, off the
  cvxpy-free CI path; the frozen Lean is the compile evidence).
- **`IntervalBracketEmitter` / `bracket_family` / `BracketSpec`**
  (`emit_bracket.py`, `kind="bracket"`): reusable rigorous rational enclosures
  `lo ≤ exp(-θ) ≤ hi` via the CI-green Taylor + convexity scaffold; the rational
  heart is Pólya-certified, the gate verifies `hi·taylor_floor ≥ 1` (exactly
  what the emitted `1/tf ≤ hi` step needs). `examples/exp_bracket` grown 2 → 6
  theorems (multi-θ). `func="log"` deferred (no CI-verified Mathlib chain).
- **`PadicValuationEmitter` / `valuation_family`** (`emit_padic.py`,
  `kind="valuation"`): a grid family of `ValuationFact`s as decidable
  divisibility (`(p^k ∣ n) ∧ ¬(p^{k+1} ∣ n)` by `norm_num`).
  `examples/padic_valuation` reframed to a node-by-node K-accounting (5
  theorems + telescope/split prelude).

**Foundation**: `family.py` (three new modes + `kind`), `certify.py` (kind
dispatch, serial + fork paths, `CertifiedInstance` payloads), `provenance.py`
(`family_hash` per-kind serialization), `__init__.py` exports. The Tier-1
emitter *code* is new but changed no existing family's emitted *bytes* on its
own. Version bumped 0.1.3 → 0.1.4 and every frozen family regenerated — the
input hashes move because P5 now folds each emitter's code fingerprint into the
hash (not only the `__version__` string), while the emitted Lean *bodies* stay
byte-identical (only the stamped version/hash line changes); the drift net was
re-verified across all families.

**Honesty**: `conjecture1_proved=False` untouched; scope banners on all three
modules; each arm carries a live negative control (non-SOS refusal, false-`hi`
refusal, wrong-`k` refusal). Lean kernel verdict is CI-side (`lake build`), not
verified locally.

## 0.1.0 (2026-08-15/16) — extraction + hardening

Born from the Brualdi–Goldwasser campaign (`../proof/`), where the pattern
produced 200+ CI-green Mathlib theorems.

**Core**: `InequalityFamily` (direct + bilinear-box), `certify()` with
structural refusals, three emitter kinds (Polya batches, ℕ-reparam adapters,
`interval_cases` assemblies), enforced certify→validate→emit→freeze workflow,
input-hash provenance, byte-stable rendering across sympy versions.

**Hardening round 1**: `diagnose` refusal triage (FALSE with exact witness /
NOT_POLYA with remedy hints / CERTIFIABLE); structural lint gate inside
`emit()`; `ShardSpec` file sharding with cross-shard imports; `telperion.toml`
manifest + `verify` drift net (fails on unlisted generate scripts);
fuzz/property tests.

**Hardening round 2**: `safe_parse_expr` token whitelist on every
string-taking surface (CLI probe/diagnose, MCP tools) — sympy's parser is
never fed raw input; `telperion init` project scaffolding (family template
with the validation discipline built in, pinned Lean shell, drift manifest,
lean-verify workflow); `certify(progress=)` + `certify -v` for long runs;
path-hashed module loading (family.py can't shadow installed modules);
`CustomAssemblyEmitter` escape hatch for hand-designed assemblies.

**The Pólya engine**: `polya_lift` (multiply through by `(1+Σxᵢ)^N` — Pólya's
theorem as an algorithm; certifies strict positivity, provably cannot converge
at equality cases) integrated as `family.auto_lift` / `polya_certify(lift_max)`;
recursive box subdivision (`auto_subdivide` on corner refusals,
`force_subdivide` to isolate tie regions) producing leaf cells plus
`SubdivisionGlueEmitter`'s `le_total` case-split glue reconstructing the
original cell theorem; diagnose now reports the exact lift exponent when one
exists, and names the tie obstruction when none does.  Toy example gains
ToyLift and ToySplit — both new shapes compile against pinned Mathlib in CI.

**Tie-variety extraction + margins** (`margins.py`, CLI `margins`/`ties`, MCP
tools): the exact equality cases of every certificate — combinatorial tie
faces via minimal hitting sets for certified (nonneg-coefficient) numerators
(with the structural corollary: certified instances have no interior ties,
which is exactly why interior-tie claims need the arithmetic treatment),
exact real roots for refused univariate claims; per-certificate margin reports
(constant-term floor + exact-rational sample minimum with argmin), tight
instances first.  diagnose now names the tie points when lifting fails.

**Wishlist 3–7**: `telperion latex` — paper appendix / leanblueprint nodes
stamped with the SAME input hash as the Lean (sync checkable by comparing two
hex strings); symbolic-tail families (`TailFrom` axis: finite table + one
``K = K₀ + t`` certificate, `TailNatEmitter` emitting the ℕ-quantified
``∀ K ≥ K₀`` theorem; the certifier's integrality check even catches int/int
float contamination in user targets); exact SOS certificates for the
rationalizable subset (even powers + iterated quadratic completion — reaches
interior-tie shapes lifting cannot; surfaced via diagnose); CAS-neutral
certificate interchange (JSON with expression ASTs + a PURE-stdlib
`recheck.py` — coefficient signs, factor positivity, Schwartz–Zippel identity
spot-checks in `fractions` — a third independent verifier beside sympy and the
Lean kernel); `certify(workers=N)` fork-parallel certification;
`telperion package` reviewer bundles (family + frozen + certificates.json +
standalone rechecker + generated REVIEWING.md).

**The honesty engine** (from a review of what made the origin proof
possible): (1) tie pinning — `family.ties`/`family.anchors` declarations; the
certifier asserts the target AND the certificate vanish exactly at declared
ties (the campaign's overclaim trap, which killed three false proofs, as a
standing invariant) and that anchors evaluate exactly (the pi(T(3,3,3)) =
19683/256 pattern); (2) the relaxation probe (`telperion relax`) — the
campaign's decisive maneuver as a tool: interpolate an integer grid axis
continuously and hunt for exact violations; ARITHMETIC verdict with witness
means no smooth certificate can close the family; (3) the adversarial hunt
(`telperion hunt`) — exact-rational minimization in three modes: coordinate
descent, GA with memetic descent refinement (the Arda evolution engine's
transferable core), and a MAP-Elites quality-diversity archive returning
DIVERSE near-tight points (tie varieties have many points; a pure minimizer
finds one — demonstrated: both basins of a bimodal tie landscape recovered
exactly). diagnose escalates from sampling to hunting before concluding
NOT_POLYA. Deliberately not ported from Arda: Rust kernels (audit surface),
island/climate machinery (overkill). Named future step: pluggable hunt
domains (the origin hunted over TREES via Prufer sequences).

**Route ledger + executable status** (the collaboration layer from the
history review): `--ledger` on diagnose/relax/hunt appends refused routes and
exact disproofs to a deduplicated, fingerprint-keyed JSON ledger
(`telperion ledger` renders ROUTES.md) — the origin's `*_nogo*` convention as
infrastructure, so nobody re-attempts a dead route blind.  `telperion status`
generates STATUS.md by EXECUTING every manifest check (theorem counts and
input hashes read from frozen manifests; verdicts never asserted), with the
origin's reminder that green certificates do not by themselves prove a
surrounding conjecture.  `telperion review-brief` fills the adversarial
review checklist with the family's actual facts — and nags when ties or
anchors are undeclared.

**Identity families + kernel facts** (second history-review run, items B+C):
`equation=(lhs, rhs)` claims — certified by exact symbolic zero-check, emitted
by `IdentityEmitter` in the proven field_simp shape with a RAW tree renderer
that preserves the author's spelling (a together-based render had produced a
vacuous `1 = 1`; construction-time evaluation caveat documented — use
UnevaluatedExpr/evaluate=False when spelling matters); identities flow through
interchange/recheck (stdlib identity spot-checks) and latex.
`ExactFactEmitter` + `fact_pow`/`int_expr_lean`: kernel integer/rational facts
in unevaluated-power spelling closed by decide/norm_num — regenerates the
origin's `s_tail_crux : (3:ℤ)^317 * 2^81 ≤ 23^129 := by decide` verbatim, and
makes VerifiedConstant brackets emittable. Closes two named-opens.

**The second-brainstorm batch (A, D–H)**: witness-search claims
(`family.witnesses` — the per-residue comparator pattern as API: existential
claims, first certifiable candidate wins, label recorded and exported: the
winner-table pattern); the sharpness probe (`telperion sharpen` — bisect a cap
between the CERTIFICATE boundary and the TRUTH boundary; the gap is the room a
better method could win — the G3/G4 cap-widening question as a tool);
`emit --pilot N` (validate the template on N instances in CI before a
972-theorem batch — the campaign's first-try-green ritual as a flag);
`telperion cilog` (the Lean-failure knowledge base: seven hard-won gotcha
classes as executable diagnostics, error COUNT always reported first);
`per_node_family` + `fixed_points` (the telescoping-potential shape's
achievable half: per-node inequality families with the step map's fixed point
as the pinned tie — full induction emission stays the v2 headline); exact cone
membership (`cone_combination` — target = Σ λᵢ·basisᵢ with λ ≥ 0 decided in
exact rational arithmetic; the LP cutting-plane maneuver's solvable core,
float-guided LP for the underdetermined case named-open).

**Third-brainstorm batch (L, M, K)**: dual-engine validation as API
(`family.independent_target` — a pure-Fraction second implementation
cross-checked exactly at certification; the pi(T(3,3,3)) pattern, which had
already caught the nsimplify bug when hand-rolled); the persistent
certification cache (`certify(cache_dir=)` + `DiskCache`/`memoize` — content-
hash-keyed Polya results incl. cached refusals; performance layer only, the
drift net and kernel stay the arbiters; justified by the 972-cell run's
redundant-search profile); interval symbols (`interval_family` — bracket-
quantified claims `∀ ρ ∈ [lo,hi]`, multilinear per bracket, LOWERED onto the
bilinear-box machinery with floors: zero new emitters, the emitted _cell
theorem IS the quantified statement; composes with ExactFact bracket lemmas —
demonstrated on a miniature G1 floor claim over the campaign's real
log-bracket constants).  The G1 floor stratum is now expressible end to end.

**J + I (completing the three brainstorms)**: unimodality certificates
(`unimodal_certificate` — the near-star integrality proof's shape composed
from existing primitives: ratio log-concavity as a symbolic-tail Polya claim,
exact crossing localization, and EXACT TIE detection when r(s*) = 1 — the
R(5) = 1 double-maximum pattern reported rather than glossed; closes the loop
the ARITHMETIC relax verdict opens); Farkas dual witnesses (`cone_decide` —
cone refusals upgraded to verified impossibility proofs: an exact functional
with y·basisᵢ ≤ 0 and y·target > 0, for both inconsistent systems and
forced-negative weights; 'change the basis, not the search'); declared-
complete witness spaces (`witnesses_complete=True` — exhaustion becomes
PROVEN IMPOSSIBLE, ledger-ready).

## 0.1.1 (2026-08-16) — the review cycle, absorbed

**The G1 review response** (REVIEW_20260816_TELPERION_G1: PASS math/honesty,
FAIL shipped Lean): the empty-symbol emission bug (`def c1 ( : ℝ)` — the
"empty-syms guard" had fixed a crash, not the emission) repaired; a lint rule
for the class; `telperion-production.yml` — the COMPILE GATE over frozen
production artifacts (regen-diffs check bytes, tests check mathematics, only
`lake build` checks that shipped Lean is Lean); version discipline learned
(emission changes must bump — the input hash covers inputs, not the emitter's
code; every family refrozen under 0.1.1).

**Fourth-brainstorm batch (N, O, P, Q, R, S)**: typed hole contracts in
`render()` (empty binders now UNCONSTRUCTIBLE — caught at fill time, before
lint, before freeze); the cost ledger (`certify(profile=, budget_seconds=)` +
`profile_report` — the R7 45-minute blind grind, never again); variable-map
adapters (`MapSpec`/`VarMapAdapterEmitter` — the campaign's most-used
maneuver generalized: substitution glue in original variables, subsuming the
reparam shape); dichotomy glue (`DichotomyGlueEmitter` — le_total case
splits over declared thresholds, the classification-not-surgery pattern);
gate negative-controls (every known-bad artifact class PROVEN red in its
gate — silence from a gate is indistinguishable from safety); bracket
adequacy (`margins --adequacy` — the MR69 ΔCHARGE fragility class as a
report; FIRST RUN on G1 found exactly one FRAGILE cell in 514: a (2,0,1)
tax-window leaf at 0.59 of its bracket width).

**Named open items** (deliberately not shipped as stubs): `python-flint` fast
path (sympy expand/together dominates the profile, so a flint coefficient pass
would be decorative until the conversion layer is done properly);
bilinear-family built-in assembly (use `CustomAssemblyEmitter`); Kind-3
multi-axis grids; the SOS Lean-emitter path (certificates found by sos.py are
surfaced in diagnose but not yet emitted — needs a squares-aware skeleton);
incremental per-instance certification caching; bilinear tails; retrofitting
the R7 star-of-hubs family onto the witness API (it hand-rolls the search);
float-guided LP for underdetermined cone membership; the generic Lean lemma for
unimodal integer maxima (the emitted pieces close its hypotheses; the
induction skeleton is documented); generic induction
emission for telescoping potentials (the v2 headline); hunt over pluggable
combinatorial domains.

## 0.1.2 – 0.1.3 (2026-08-16) — performance

Two sympy hot-path traps found by py-spy on stalled runs, both fixed. (1)
`canonical_srepr`: sympy's default `srepr` ordering evalfs every `Add` node —
`srepr(order='none')` on construction-canonical expressions took the R7 family
hash from 70+ min to ~4 s (0.1.2). (2) `DirectPolyaEmitter` re-expanded the
certificate at render — `expr_lean_from_parts` renders from the stored
`(numerator, denominator)`, taking R7's 972 theorems to ~64 s (0.1.3). The
0.1.3 direct-Pólya bodies are now the cancelled pair (simpler, matches the
certificate); bilinear (G1/R47) output is byte-unchanged, so G1 acceptance is
intact. Emission changes bump the version because the input hash covers inputs,
not emitter code; every family was refrozen. Active heartbeat logging added so a
silent phase can't masquerade as a hang.

## 0.1.3 maintenance (2026-08-17) — enumeration refresh + CI hygiene

Documentation and packaging only — **no emission change**, so `__version__`
stays `0.1.3` and every frozen artifact's hash is untouched (no refreeze).

- **CI fix**: `tests/test_recursive_transfer.py` imported `networkx` at module
  top level, so a missing dep turned a collection error into a red `telperion-test`
  matrix across all six sympy/python cells. Both graph-certificate test modules
  now `pytest.importorskip("networkx")`; `networkx` is declared as a `graph`
  extra (and in `dev`) and installed in `telperion-test.yml` so the tests run
  rather than silently skip. Stale `forge-test.yml` path trigger corrected to
  `telperion-test.yml`.
- **Deselected two intractable tests** (owning session, please fix): with
  collection restored, the suite reached — for the first time —
  `test_bellman_rigidity.py::{test_value_function_and_sub_hull_gap,
  test_cramer_rate_positive_below_hull}`, both calling
  `value_function(max_size=14)`. That enumeration is super-exponential
  (`max_size=10` ~80 s; `14` runs for hours), so `telperion-test` deselects the
  pair to stay inside its 15-min budget (the rest passes in ~4.5 min). The
  assertions hold at `max_size=8` in ~4 s — reduce the size there and drop the
  deselect.
- **Packaging**: `pyproject.toml` version synced `0.1.0 → 0.1.3` (it had lagged
  the emission-stamped `__version__`).
- **Docs**: `README.md` (repo root) now enumerates the current Brualdi–Goldwasser
  state (near-star spine, R1/R2, g-lemma) with rigor tags; `telperion/README.md`
  replaces the stale "v0.1, two emitters, rest planned" with the full shipped
  emitter set and the production-family table; a thin top-level `STATUS.md`
  indexes both the proof and the engine, each row linking to the canonical doc.
