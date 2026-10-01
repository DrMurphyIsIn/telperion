# New Telperion emitters (2026-09-02..03) — parallel-session skill reference

**Consolidated 2026-09-03.** The campaign grew past the original nineteen: **31 new
certificate emitters** now landed — the two RH+BG "emitter sweeps" + the 2026-08-21
BG/P=NP backlog (the 19 below), then **twelve more** (trading-derived, the two
open-fronts, and the BG-remaining-core / AxiomMath-ported / F\*-fold families — see
the **Consolidation** section). This is the quick reference so any session knows what
Telperion can now discharge without re-deriving it.

## Meta — read first
- **All are registered and CI-gated.** Each has an entry in `certify.py`
  (`_SPECIAL_KINDS` tuple + `_SPECIAL_DISPATCH` dict), an export in `__init__.py`,
  a worked `examples/<name>/` regeneration harness, a row in the README
  "Certificate shapes" table (now **75 rows**), a `<name>-compiles` CI job, and a
  `telperion.toml` `[[check]]` manifest entry.
- **Local Lean builds work again** (machine serviced; the Aug-9 "CI-only" rule is
  lifted). Verify an example with
  `cd examples/<name>/lean && PATH=$HOME/.elan/bin:$PATH lake exe cache get && lake build`
  (~5–40 s, mathlib cached).
- **To use one:** pick its `kind`, build via `<name>_family(...)` → `certify` →
  `emit`, or copy its `examples/<name>/generate.py` (all follow the same shape as
  `examples/finite_argmax/generate.py`).
- **On both `main` and `rh-research-artifacts`.** `conjecture1_proved = False`
  throughout — these are classical / certificate-shaped formalizations, not
  progress on RH, BG, or P vs NP.

## Positivity / box / extremal-combinatorics
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `BilinearCornerBoxEmitter` | `bilinear_corner` | `0 ≤ A+B·s+C·t+E·st` on a 2-var box, from the 4 corners (barycentric convex combination) | |
| `PolytopeMaxMonotoneEmitter` | `polytope_max` | general-`d`: multi-affine `0 ≤ p(x)` on `∏[lᵢ,uᵢ]` from the `2ᵈ` corners | d=2,3 build-verified; d≥4 needs a higher heartbeat budget |
| `FiniteArgmaxMarginEmitter` | `finite_argmax` | a designated winner beats every competitor in a finite list, cross-multiplied over ℤ (no division) | pure `norm_num` |
| `RecursiveDominationRatioEmitter` | `domination_ratio` | a rational ratio `P/Q ≥ 1` (nonneg-coeff, `Q>0`) on a multivariate box, via corner dispatch on multi-affine `P−Q` | caller supplies the extracted `P,Q` |
| `SeparableConvexExtremumEmitter` | `separable_convex` | `n·φ(S/n) ≤ Σφ(xᵢ)` (Jensen min) on a fixed-sum box for convex `φ`, via tangent-line SOS | **min/homogeneous face only**; max/vertex face is named-open |
| `AchievabilityClosureEmitter` | `achievability` | restrict a relaxed inequality (false on `D`) to its achievable subset `A⊆D`, with a load-bearing witness that it fails on `D∖A` | |

## Complex analysis / RH zero-free-region toolkit
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `HalfPlaneDiskEmitter` | `halfplane_disk` | Borel–Carathéodory core `Re w ≤ B ⟹ ‖w/(2B−w)‖ ≤ 1` (the `4B(B−Re w)≥0` identity) | |
| `CauchyDerivBoundEmitter` | `cauchy_deriv` | `‖deriv f z₀‖ ≤ M/R` from a sphere bound + the `ρ'=(R−r)/2` constant | |
| `DiskCoordBoundsEmitter` | `disk_coord` | disk membership → linear `Re/Im` coordinate bounds (Farkas) | |
| `MagnitudeSplitBoundEmitter` | `magnitude_split` | `‖A+B−C‖ ≤ α+β+γ` triangle assembly | |
| `LogDerivRegionCoreEmitter` | `logderiv_region` | the dVP region gap `4k/(σ−β) ≤ 3/(σ−1)+3A+5AL` (ζ'/ζ bounds as hypotheses) | |
| `OrderBalanceEmitter` | `order_balance` | the integer zero/pole-order hinge at `Re=1` (`ζ(1+it)≠0`) | |
| `LFunctionProductEmitter` | `lfunction_product` | `∏ₖ‖ζ(σ+ikt)‖^{aₖ} ≥ 1` from a Fejér-admissible cosine tuple | emits the (3,4,1) instance Mathlib exposes |
| `ParametricHolomorphyEmitter` | `parametric_holomorphy` | holomorphy of a parametric tail integral | thin/heavy — borderline; natural home is the lemma pack |

## Proof complexity / SoS
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `PseudoExpectationDualityEmitter` | `pe_duality` | **"no degree-`d` SoS refutation of `{gᵢ=0}` exists"** — the duality complement of `InfeasibilityEmitter`; bool + parity modes, PSD leaf as hypothesis | retires the ad-hoc `gen_xor3_duality.py` |
| `SymmetricQuadFormEmitter` | `symmetric_quad` | symbolic-in-`n` level-1 moment-matrix PSD (`subsetForm_d1`; one certificate, all n) | d=1; d≥2 open |

## Arithmetic / recurrence / enclosure
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `AlgebraicBracketEmitter` | `algebraic_bracket` | `lo ≤ √a ≤ hi` rational enclosure (algebraic companion to the `exp` bracket) | |
| `SecondOrderRecurrenceEmitter` | `second_order` | closed form for a 3-term recurrence `A·f(q+2)+B·f(q+1)+C·f(q)=0` (Hahn/Krawtchouk; generalizes `fwd_telescope`) | |
| `IntegralityGateEmitter` | `integrality_gate` | finite exceptional table + p-adic tie pin (the BG 23-gate); composes `padic`+`finite_decide` | |

## Consolidation — the twelve emitters shipped after the initial nineteen (2026-09-02..03)

Grouped by the front that motivated them. All kernel-green (local `lake build`),
`--check` byte-for-byte, negative controls firing.

### Trading-derived (exact-algebraic structures from the Arda trading system)
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `ScaleInvarianceEmitter` | `scale_invariance` | degree-0 homogeneity / parameter cancellation `f(λ•x)=f(x)` — models the leverage↔position_size Sharpe degeneracy (why leverage is a non-evolvable gene) | `field_simp; ring` |
| `ConcaveStationaryMaxEmitter` | `concave_stationary_max` | a stationary point of a strictly-concave objective is its unique max — Kelly-fraction optimality (FOC + `−g''>0`) | |

### Open fronts (the two named-open residuals, now CLOSED)
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `SymmetricQuadD2Emitter` | `symmetric_quad_d2` | the **degree-2** subset-form moment PSD, **symbolic in n** (three-piece completing-the-square + centered CS) — closes the `symmetric_quad` d≥2 front | scheme leaf facts as hypotheses |
| `SeparableConvexExtremumEmitter` (max mode) | `separable_convex` | adds the **max/vertex** face `Σφ ≤ (n−1)φ(u)+φ(S−(n−1)u)`, parameterizing the proven `VertexLemmaFull` push-chain | uniform box, even deg ≤ 6 |

### BG remaining-core (the verified open core: capstone conditional on Hnorm/Hdom, heart = SCLStep)
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `TightCapEnclosureEmitter` | `tight_cap_enclosure` | the BG g-step fixed-config closure `(baseOf l)¹¹·prodBcap l/(W(5/3)¹¹) ≤ 1` (concrete + single-symbolic-child faces) | models proven `single_child_le_one` |
| `AffineParamEndpointEmitter` | `affine_param_endpoint` | an affine-in-parameter gap `A+μB ≥ 0` on `[lo,hi]` ⟺ at the two endpoints — **collapses SCLStep's price interval `I=[456/3703,3/7]` to two rational checks** | RH-reusable |
| `RecursionClosureEmitter` | `recursion_closure` | tangent-majorant + per-child ceiling ⟹ node ceiling (fixed price); all-cherry = equality (composes with the `tight_cap` tie) | assembly only; all-cherry exchange is structural |
| `CavityExchangeEmitter` | `cavity_exchange` | Kelmans de-branch monotonicity: bilinear 4-corner reduction + all-nonneg-coeff Polya corners | generalizes `R47R4Kelmans*Cert` |
| `PerSizeDominanceSweepEmitter` | `per_size_dominance_sweep` | a finite per-size sweep aggregating `tight_cap` per-config certs | per-n, non-exhaustive by honest scope |

### AxiomMath-ported (from Lamzouri arXiv:2609.02882 / AxiomMath/ZetaZeros Lean certs)
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `CurvatureBoundaryEmitter` | `curvature_boundary` | a function with definite `f''` sign has its extremum at the boundary (concave→min, convex→max, affine→endpoints) — ports their `extremalG_const`, generalizes `affine_param_endpoint`, covers the BG concave-corner case | interval-aware curvature check |
| `TranscendentalEnclosureEmitter` | `transcendental_enclosure` | rational `L ≤ expr ≤ U` over a box — **log face** (`log(1+x)`, discharges the BG per-cell `log(1+S/d)`); Montgomery–Taylor `C₀` trig face deferred/refused | |

### MIRRORMERE exp seam (2026-09-18)
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `ExpEnclosureEmitter` | `exp_enclosure` | rational brackets of `Real.exp x` (`|x| ≤ 1`) from `Real.exp_bound`'s exact order-`n` Taylor box — plus the `exp_neg`, **deficit** (`e^x + e^{-x} - 2`) and `cosh` faces; the exp face that `transcendental_enclosure` (log only) and `log_combination` (internal degree-3 step) never exposed as a standalone certificate | **dogfooded**: discharges the Arb `hexp` of `BraggDefect.bragg_defect_witness` (→ `bragg_defect_witness_unconditional`, MM_bragg_defect_witness) and reproduces the `excess_bracket` / `ZooDH.cosh_bracket` constants. A finite arithmetic fact; conjecture1_proved = False |

### F\*-fold (cross-front dogfood)
| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `LogCombinationEmitter` | `log_combination` | `Σ cᵢ·log(rᵢ) ≤ q` by folding into a single `log(∏ rᵢ^{cᵢ})` — **tight at the tie**, no separate F\* lower bound. **Three routes**: monotone (`q=0`, `∏≤1`), tangent (`log x ≤ x−1`, any-sign `q`, any `k`), and **tight** (degree-3 exp, `log X ≤ Q ⟺ X ≤ exp Q` via `Real.exp_bound'` — for cells where the tangent overshoots). Handles negative fstar coefficient (`+F*`) | **dogfooded live**: regenerates the BG `log74_le_4fstar` / `log54_sub_fstar_le` byte-for-byte, AND the round-trip generated `log54_sub_fstar_le_40`, `log74_le_4fstar_broom`, `log119_sub_fstar`, `log79_add_fstar` — each built GREEN against the real `R3Cert.BGSCLInduction` |

## Where to look / follow-ups
- **Shape reference:** `README.md` "Certificate shapes" table.
- **Design + honest scope:** `docs/EMITTER_ROADMAP_2026-09-02_RH_CROSSCUT.md`,
  `docs/EMITTER_ROADMAP_2026-09-02_SWEEP2.md`, and
  `docs/EMITTER_ROADMAP_2026-08-21.md` (see its `STATUS UPDATE (2026-09-02)`
  section — the BG/P=NP backlog is now essentially complete).
- **The two residual open fronts are now CLOSED** — `symmetric_quad` d≥2 shipped as
  `SymmetricQuadD2Emitter`, and `separable_convex` max/vertex shipped as the
  `mode="max"` face (see Consolidation above).
- **BG live front (2026-09-03):** the ceiling was reframed from the refuted
  multiplicative cap to an **additive subaction** (`bg/scl-on-main`
  `BGSCLSubaction.lean`); the `curvature_boundary` + `transcendental_enclosure` +
  `log_combination` trio are the per-cell analytic tools, and `LogCombinationEmitter`
  is **dogfooded** against the two in-kernel BG cells. Remaining BG work is on the
  proof side (per-cell family, high-degree tail lemma, instantiating ρ).

## Building your own emitter (the recipe all 31 followed)
An emitter = `src/telperion/emit_<name>.py` (a frozen `Certificate` dataclass +
`<name>_certificate(...)` that exact-self-checks and RAISES on bad input +
`certify_<name>_point(family,pt,name)` + `<Name>Emitter(Emitter).emit_body` +
`<name>_family(...)`), registered in `certify.py`'s two structures + `__init__.py`,
plus `examples/<name>/{generate.py, lean/*}`, a README row, a CI job, and a
`telperion.toml` entry. **Model each emitted proof on a lemma already proven in
the corpus, then verify with one local `lake build`** — that near-eliminated build
failures. Gotcha: ℝ-ascribe bare rational literals in emitted Lean (`(0:ℝ)`,
`(<rat>:ℝ)`) or they default to ℤ and won't unify with ℝ lemmas.

---

## Session 2026-09-04..05 — direct-function emitters + pipelines (Kelmans/RH)

A separate style from the `<name>_family`/`certify` framework above: these are **direct
`str`-emitting functions** (no `CertifiedFamily`/`_SPECIAL_DISPATCH` registration) — call them,
get Lean text, kernel-check it. All in `src/telperion/`, all with unit tests. Landed on `main`.

| Capability | Entry point | Discharges / does |
|---|---|---|
| `emit_nonneg_orthant` | `nonneg_orthant_cert(name, poly, syms)` | `0 < p` on the nonneg orthant for an all-nonneg-coeff poly + positive constant; **auto-generates** per-monomial `mul_nonneg` hint chains (any arity). A specialized/optimized `emit_handelman`. |
| `emit_domain_to_orthant` | `domain_to_orthant_cert(name, poly, constraints)` | positivity on a **simplicial cone** (`var_i ≥ lower_i`, e.g. `pA ≥ pB ≥ 1`) via slack reparametrization; theorem stated in ORIGINAL vars, handles bodies with negative coeffs (positive only on the cone). |
| `emit_mt_cosine` | `fejer_riesz_sos(b)`, `mt_cosine_cert_lean(name, b)` | nonneg trig poly → exact **Fejér–Riesz constrained-SOS** `A²+(1−x²)B²` (a Putinar cert on `{1−x²≥0}`); flagship `MT_DEG4` beats the VP zero-free slice by 7.4% (F-functional). |
| `emit_spectral_factorization` | `spectral_factor(a)`, `emit_spectral_sos_cert(name, a)` | the `a→b` front-end (palindromic assoc-poly root-find) so ANY nonneg trig poly (given the tuple) gets the Fejér–Riesz SOS; `target='exact'` for perfect squares (VP), `'nearby'` otherwise. |
| `emit_order_residue` | `emit_order_residue_cert(name, n)` | packages the PROVEN `residue_logDeriv` — "residue of `f'/f` at an order-`n` point = `n`" — as a re-export at a fixed integer order (complex-analysis, upstreamable). |
| `cert_leaf` (pipeline) | `positivity_leaf(prefix, specs, module_doc, namespace)` | a family of cert specs (`kind=orthant/domain/rational`) → one **hazard-safe self-building Lean leaf**; `scan_hazards` RAISES on a `-/` in docstring prose (the `3-/4` bug, via stray-`-/`-in-code detection) or leaked `**`. Reproduces `R47R7KelmansTwoHubCert` byte-for-byte. |
| `mt_optimize` (pipeline) | `optimize_cosine(d, denom=…)` | discovers a VP-beating admissible cosine polynomial at any degree (scipy F-max over the Fejér cone with `a_k≥0, a₁≥a₀`, then robust rationalization); scipy lazy-imported. The F-functional saturates ~0.0286 by degree 4–6. |

| `emit_borel_caratheodory` | `emit_borel_caratheodory_cert(name, form=)` | wraps Mathlib's `Complex.borelCaratheodory`/`_zero` (value form is UPSTREAM as of v4.32) — packaging re-export; region gate gone. |
| `emit_reexport` | `reexport_cert(name, lemma, binders=, hyps=, conclusion=, args=)` | the general wrapper-emitter shape: package ANY proven/upstream theorem as a named re-export; reproduces `emit_order_residue` + `emit_borel_caratheodory`. |

**Applications (kernel-verified leaves on `main`):** the full Kelmans local merge table —
`R47R7Kelmans{TwoHub, AssistedMerge, GenEnv(100), Dichotomy(44)}Cert` (156 certs, all via
`emit_nonneg_orthant`) — plus the RH cosine leaves `mt_cosine_deg4_nonneg` / `vp_cosine_deg4_nonneg`
in `EmittedShapes.lean`. Exact-arithmetic BG probes use `python-flint` `fmpq` (~20× over `Fraction`);
`residual_flint_probe.pi_flint` is validated against `pi_loaded`.


## Session 2026-09-18 — `interval_gram_inertia` (the interval-matrix signature)

| Emitter | kind | Certifies | Scope note |
|---|---|---|---|
| `IntervalGramInertiaEmitter` | `interval_gram_inertia` | for a rational box `lo ≤ G ≤ hi`, EVERY real symmetric `G` inside it has signature exactly `(p, q)`: `RHLinalg.posIndex hG = p ∧ RHInertia.defect hG = q`. Exact rational congruence `BᵀMB = D` for the midpoint (the `psd_form` LDLᵀ primitive run to a full diagonalization, with symmetric pivoting), unit-abs-sum witness bases `X`/`Y`, and the interval absorbed by `\|xᵀ(G−M)x\| ≤ w(Σ\|xᵢ\|)²` + Cauchy-Schwarz; sound exactly when `w·S < δ` | **Island-pinned** to the ported RHLinalg block (v4.32.0, `hermitian_moment` island) — the emitted file imports `RHInertia`, not just Mathlib. **Real-symmetric only**: the complex `2n` real embedding is NOT built and a complex instance is refused, not faked. Refuses an asymmetric/empty box (the phantom), a singular midpoint, a definite box (`psd_form`'s shape), a wrong claimed signature, and any box wider than the pivot margin |

Fills the gap left by `psd_form` (one explicit matrix, definite only), `rayleigh_gram` (one
direction) and `hermitian_moment`/`rank_trace_scalar` (scalar shadows): the recurring D2/D3/T3
sentence "this Arb-enclosed Hermitian matrix has negative index exactly `q`". Replaces
`BraggDefect.lean`'s hand-written 2x2 / 4x4 blocks with a generic `n x n` instrument.

Design doc: [`INTERVAL_GRAM_INERTIA_EMITTER_DESIGN_2026-09-18.md`](INTERVAL_GRAM_INERTIA_EMITTER_DESIGN_2026-09-18.md).
Dogfood: `examples/gram_inertia/` (4 boxes: `(1,1)` 2x2, `(2,1)` 3x3, `(2,2)` 4x4 offline-pair
block, `(1,2)` fractional 3x3), CI job `gram-inertia-compiles`, axiom guard
`AxiomGuardGramInertia.lean`. Negative control: `adapter_interval_gram_inertia` (forged pivot below
the interval slack is kernel-rejected; separated-box twin compiles). `conjecture1_proved = False`.

## Session 2026-09-22 — `exp_threshold` (threshold to exponential domination)

`ExpThresholdEmitter` (kind `exp_threshold`), SHAPES_AUDIT_48H section 2 rank 5 (B N2, C 4.5):
from a threshold on the Gaussian width to the exponential bound by `1 + t <= e^t`. A bundle reads
the nested-max threshold hypothesis (the `eventual_threshold` witness with its `max 1` guard folded
in) and returns each consequence `Q <= K exp(s lam a)` -- linear (`div_le_iff0` +
`Real.add_one_le_exp` + `linarith`) or log (`Real.exp_log` + `Real.exp_le_exp`) -- plus the
product / inverse / shifted-rate atoms. Every quantity is independently a symbol or an exact
rational; refusals are exact (a rational `a <= 0`, a declared threshold not matching the
recomputation, strict log, an inverse bound below `1/x0`, a shifted-rate constant below
`max(c0, c1/(r-r'), 0)`, floats).

Design doc: [`EMITTER_EXP_THRESHOLD_DESIGN_2026-09-22.md`](EMITTER_EXP_THRESHOLD_DESIGN_2026-09-22.md).
Dogfood: `examples/rvm_bridge/lean/Probes/Dogfood_exp_threshold.lean` (generated by
`examples/rvm_bridge/dogfood_exp_threshold.py`; regenerates `E6Bridge7.lean:554-590` as one guarded
linear bundle and `E6Bridge14.lean:66-86` as a log step plus a guarded log bundle, with kernel
cross-checks against the originals). Negative control: `adapter_exp_threshold` (a hand-minted
`a = -1` instance, false at `lam = 0`, rejected at `positivity`; true twin `a = 1`).
Nothing here bears on RH; `conjecture1_proved = False`.

## Session 2026-09-22 — `enclosure_tree` (rational enclosures of expression trees)

`EnclosureTreeEmitter` (kind `enclosure_tree`), SHAPES_AUDIT_48H section 2 rank 1 (A N2/N3/N4, B C2,
C 4.7, D 4): a rational two-sided enclosure `lo <= E <= hi` of an expression tree over
`{+, -, *, /, ^, sqrt, log, exp, pi, arctan, rationals}`, each side `<` exactly when the exact fold
has slack or an open endpoint. One Mathlib fact per atom (`Real.pi_gt_dN` at the least ladder rung
that carries the claims, `log_two_gt_d9`, `abs_log_sub_add_sum_range_le` at the least fitting order
plus the backwards `Real.log_mul` fold, `Real.exp_bound`, `Real.sq_sqrt` against exact rational
squares, `|arctan t| <= |t|` and `t/2 <= arctan t` on `[0, 1]`); an exact interval fold for the
operations, linear nodes seen through by `linarith`, the four McCormick corner facts for products,
`le_div_iff0` for quotients; shared subtrees proved once per family. Faces: the `pi` rate corollary
`n <= cap -> (n + 1 : R) <= E` and the log/sqrt face `log (y + a) <= c sqrt y`. Refusals are exact
(a claim the fold does not imply at any node, strict without slack, radicand not `>= 0`, denominator
containing 0, `log` out of domain or out of radius without a factorisation, orders outside `1..64`,
`exp` at `|x| > 1`, an unreached rate cap, rational-only trees, floats).

Design doc: [`EMITTER_ENCLOSURE_TREE_DESIGN_2026-09-22.md`](EMITTER_ENCLOSURE_TREE_DESIGN_2026-09-22.md).
Dogfood: `examples/li_positivity/lean/Probes/Dogfood_enclosure_tree.lean` (generated by
`examples/li_positivity/dogfood_enclosure_tree.py`; the `LiLadderHeight` / `LiLadderSharp` pi-face
rate steps -- the search lands on d4 and d6 by itself -- with kernel cross-checks feeding the emitted
rate lemmas to the hand theorems, the nine `LeakageDictionary.lean:276-359` brackets with their
original claims, and route coverage; compiled on the island, 40 theorems axiom-clean) and
`examples/quasicrystal/lean/Probes/Dogfood_enclosure_tree.lean` (cross-checks both ways against the
nine originals; shadow-compiled on the li Mathlib, to be compiled on its own island). Negative
control: `adapter_enclosure_tree` (the pi-face instance hand-minted one past the truth, root lower
bound 18850 and cap 18849 against `6000 pi = 18849.55...`, rejected at the root `linarith`; the true
twin compiles). Nothing here bears on RH; `conjecture1_proved = False`.

## Session 2026-09-22 — `preordering_multiplier` (positivity on a semialgebraic set by a positive multiplier)

`PreorderingMultiplierEmitter` (kind `preordering_multiplier`), SHAPES_AUDIT_48H section 2 rank 3
(D 3.1 with its `li_box_rung` dogfood family D 3.3; B C3; C 5.3 item 1): `0 <= p` on
`{g_1 >= 0, ..., g_m >= 0}` for POLYNOMIAL generators from the exact identity
`M p = sum c_alpha prod g_i^{alpha_i}` with every `c_alpha >= 0` and `M = kappa g_j^e` (or a positive
constant), generators tagged `hyp` (a literal hypothesis) or `structural` (closed by `positivity`),
the zero set of a non-constant `M` certified as one point where `p >= 0`. An exact rational simplex
FINDS the certificate (outer loop over multiplier candidates, inner loop over the product degree);
the result is re-verified exactly and through `assert_certificate_sensitive` (the emitter is
CERTIFICATE_SENSITIVE and wired). Emitted proof: `obtain` per used generator, `generalize` the
target, `ring` for the identity, `positivity` for the cone, `eq_or_lt_of_le` into the locus branch
(`nlinarith only` + `norm_num`) or `mul_nonneg_iff_of_pos_left`. Refusals are exact: the LP
infeasible up to the cap (OBSTRUCTED_AND_LOCATED, with the exact witness and a `ProbeVerdict`,
when the grid scan finds `p < 0` on the set), any `c_alpha < 0`, a `hyp` generator that is not
literally a hypothesis, a `structural` one `positivity` cannot close, an uncertified multiplier
zero locus, a multiplier not in the cone, cost caps, floats, name collisions.

Design doc: [`EMITTER_PREORDERING_MULTIPLIER_DESIGN_2026-09-22.md`](EMITTER_PREORDERING_MULTIPLIER_DESIGN_2026-09-22.md).
Dogfood: `examples/li_positivity/lean/Probes/Dogfood_preordering_multiplier.lean` (generated by
`examples/li_positivity/dogfood_preordering_multiplier.py`; lean_lib `DogfoodPreorderingMultiplier`,
anchored in `AxiomGuardLiPositivity`): `LiBoxRungs.lean` `re_Q1..re_Q5_nonneg` regenerated (the
three hand certificates with multipliers `1`, `14 s`, `s^2` verbatim, plus LP-found `Q_4`/`Q_5`),
cross-checked against the originals and re-assembled into the island's termwise dispatch; `Q_6`
REFUSED as OBSTRUCTED_AND_LOCATED at the exact disk point `(4/5, -2/5)` (`Re Q_6 = -27772/15625`),
with the refutation `re_Q6_disk_claim_false` kernel-checked. All 15 theorems print
`[propext, Classical.choice, Quot.sound]`. Negative control: `adapter_preordering_multiplier`
(`p = d - B` on the disk, an exact identity with coefficient -1, false at `(1/2, 1/2)`; the kernel
rejects it at the `positivity` fold; true twin `p = d + B` compiles).
Nothing here bears on RH; `conjecture1_proved = False`.

## Session 2026-09-22 — `complex_re_im_split` (real / imaginary-part splits and the cast face)

`ComplexReImSplitEmitter` (kind `complex_re_im_split`), SHAPES_AUDIT_48H section 2 rank 4 (B N3,
B D7, C 2.10, D 2.2; "the smallest and most frequent shape in the cluster"): for a polynomial `p`
in a complex `z`, real atoms, natural-number atoms (the `zeroMult` casts of every B D7 site),
`Complex.I` and rationals, the faces `(p : C).re = P_re`, `(p : C).im = P_im`,
`‖p‖ ^ 2 = P_re^2 + P_im^2`, `‖exp p‖ = exp P_re`, and the cast face of a real-valued `p`
(`(p : C) = ((P : R) : C)` and its `.re`).  The claimed polynomial IS the statement; sympy's
split is re-verified three ways (symbolic identity, `as_real_imag`, an independent exact
`Fraction` evaluator) and a claim not ring-equal to it is refused (the forge case), as are a
non-polynomial `p` (division, transcendental, a symbolic exponent), the cast face on a `p` with
`z` or `I`, mis-declared atoms, floats, degree above 10, a degenerate bare variable / atom /
constant, and a `tie_to` that is not a Lean identifier.  Proofs are the frozen skeletons of the
hand proofs: `simp only [<component lemmas, restricted per instance>]` then `all_goals ring`;
`push_cast` then `all_goals ring` (then `Complex.ofReal_re`) for the cast face.

Design doc: [`EMITTER_COMPLEX_RE_IM_SPLIT_DESIGN_2026-09-22.md`](EMITTER_COMPLEX_RE_IM_SPLIT_DESIGN_2026-09-22.md).
Dogfood: `examples/rvm_bridge/lean/Probes/Dogfood_complex_re_im_split.lean` (generated by
`examples/complex_re_im_split/generate.py`, `--check` drift gate; 15 theorems, all
`[propext, Classical.choice, Quot.sound]`; registered as the island lean_lib
`DogfoodComplexReImSplit`, so `lake build` compiles it and `AxiomGuardRvMBridge.lean` guards it): `E6Bridge28.re_pow_two..five` with tie gates to the
hand lemmas; E6Bridge7's `norm_gaussTest` / `re_gaussTest` split `have`s, with consumer gates
re-proving both hand lemmas from the emitted splits (declared glue: `neg_mul` and three `ring`
reshapings); the five B D7 cast `have`s of `E6Bridge5` / `7` / `11` / `14`, each closed verbatim
by the emitted theorem at the island's atoms.  Negative control: `adapter_complex_re_im_split`
(the forged `Re ((a + b i)^2) = a^2 + b^2`, kernel-rejected with `a ^ 2 - b ^ 2 = a ^ 2 + b ^ 2`
unsolved; true twin `a^2 - b^2` compiles), plus an offline-pinned cast-face pair.  An
89-instance kernel stress run (all modes, random and edge cases) compiled clean and its 89
corrupted twins were all rejected.  Nothing here bears on RH; `conjecture1_proved = False`.

## Session 2026-09-22 — `zero_sum_majorant` (finite ordinate window + local-count tail)

`ZeroSumMajorantEmitter` (kind `zero_sum_majorant`), SHAPES_AUDIT_48H section 2 rank 2 (C 3.1
merged with B N5): a family supported on the nontrivial zeros is summable through a finite ordinate
window plus the local-count tail `m(rho) C/(1 + |gamma_rho|^2)`, the island atom
`RvMBridgeXi.zeroBoundAt`. Per instance the certificate is ONE strip inequality
`N/D <= C/(1 + |gamma_rho|^2)` on `h <= |Im rho - a|`, cleared to an exact nonnegative
Bernstein / Polya combination (the audit's `w^2 -> h^2 + t` shift, odd-part removal by a declared
square, degree elevation; exact sympy) that the emitted strip face states as `key` and closes by
`ring`, then `linarith only` over explicit `mul_nonneg` summands -- the coefficients are
load-bearing and certify runs `assert_certificate_sensitive` on the identity. The `_le` and
`_summable` faces compose it with the atom from the named hypotheses `hzero` / `hwin` / `hshape`
(optional size prefactor `K`); mode `tail_envelope` emits the B N5 envelope (Mathlib-only) and the
rate companion at a rational `P < 0`. Refusals are exact: a failed Polya check is reported FALSE
with a located rational point (the audit's `h = 0`, `1/|rho|^2` phantom) or OBSTRUCTED; `C < 0`,
`h` outside `{0, 1, 2}`, a non-ordinate window, a conditional support fact, `ordinate_sq` with
`h = 0`, a term list that is not the residual, `P >= 0`, floats, colliding names.

Design doc: [`EMITTER_ZERO_SUM_MAJORANT_DESIGN_2026-09-22.md`](EMITTER_ZERO_SUM_MAJORANT_DESIGN_2026-09-22.md).
Dogfood: `examples/rvm_bridge/lean/Probes/Dogfood_zero_sum_majorant.lean` (generated by
`examples/rvm_bridge/dogfood_zero_sum_majorant.py`; regenerates E6Bridge19 `zbound`, E6Bridge18
`polBound`, E6Bridge15 `liBound` and E6Bridge12 `tail_bound_window` under new names, with the
instance glue and kernel cross-checks proving the originals' statements VERBATIM; compiled on the
island, every theorem `[propext, Classical.choice, Quot.sound]`; registered as the island lean_lib
`DogfoodZeroSumMajorant` and anchored in `AxiomGuardRvMBridge.lean`, so CI re-checks it). Negative
control:
`adapter_zero_sum_majorant` (the 9/4 strip instance forged to `C = 1`, false at every point of the
strip, rejected at the `ring` identity; true twin `C = 9/4` compiles). Nothing here bears on RH;
`conjecture1_proved = False`.

## Session 2026-09-29 — `mobius_tangent_cell` (tangent-line cells with a Mobius term)

`MobiusTangentCellEmitter` (kind `mobius_tangent_cell`): `F(x) = a + b x + sum kappa_i log(alpha_i +
beta_i x) + sigma/(B + A x) <= 0` on a rational interval, `kappa_i > 0`, by tangent-line cells. Per
cell and rational tangent point `t`, each concave log is replaced by its tangent (with a rational
`H >= log u` from `Real.abs_log_sub_add_sum_range_le` plus `Real.log_two_{lt,gt}_d9`); the Mobius
term is kept when `sigma >= 0` (convex) or replaced by its tangent when `sigma < 0` (concave); the
convex majorant is checked at the two cell endpoints by `norm_num`. The generator bisects until
every cell passes; the union over the interval is a kernel-checked `le_or_gt` chain. The problem
can be given as two sides `lhs <= rhs` (exact `sp.apart` split; the original form is emitted as
`<name>_sides`). Technique: Lemma 3.3 of a draft communicated by J. L. Goldwasser (28 Sep 2026;
author his London colleague, name to be added). Refusals: convex logs (`kappa < 0`), sign changes
of a log argument or of `B + A x`, more than one simple pole, non-affine log arguments, floats,
tampered cells or tilings, and false or order-`>= 2`-tight claims at the bisection cap.

Design doc: [`EMITTER_MOBIUS_TANGENT_CELL_DESIGN_2026-09-29.md`](EMITTER_MOBIUS_TANGENT_CELL_DESIGN_2026-09-29.md).
Dogfood: `examples/mobius_tangent_cell/` (the [2/1] Pade bound `log(1 + x) <= x(6 + x)/(6 + 4x)` on
`[1/4, 1]` in 11 cells, the log-mean bound `log x <= 2(x - 1)/(x + 1)` on `[1/10, 1/2]`, and a
synthetic two-log concave-Mobius instance and a synthetic no-Mobius instance; 48 theorems, axiom
list pinned by `#guard_msgs`). Not
covered: the Pade bound near `x = 0` (tight to order 4; the tangent majorant loses a quadratic term,
refused) and `log(1 + x) >= 2x/(2 + x)` (convex log, refused). Negative control:
`adapter_mobius_tangent_cell` (the log-mean cell with its constant raised `-2 -> -19/10`, false at
`x = 1/2`, rejected at the cell `linarith`; the true twin compiles). Nothing here bears on RH;
`conjecture1_proved = False`.
## Session 2026-09-29 — concave-witness faces (fold-ins to existing kinds)

Three faces folded into existing kinds rather than new emitters. The certificate shapes (exact
cancellation, the piecewise-linear node condition, and the quadratic sign race pattern) are
distilled from a draft communicated by Prof. John L. Goldwasser ("The maximum Laplacian ratio of a
tree for all n >= 303: concave witnesses and one-variable certificates", 28 Sep 2026; author: his
London colleague). Only the generic shapes are used: no data from the draft, and nothing from its
Brualdi-Goldwasser sections is formalized. `conjecture1_proved = False`.

### `log_combination` — exact cancellation (routes `exact`, `mixed`)

The existing routes certify `Σ cᵢ·log rᵢ ≤ q` with a rational margin. At a tie point the value is
forced to be exactly zero (the motivating shape: `11·F* = 5·log(3/2) + log(23/18)` with
`F* = log(621/64)/11`, because `(3/2)^5·(23/18) = 621/64`), and every enclosure-based check fails
there at zero margin. The face adds:

* `exact`: `Σ cᵢ·log rᵢ = 0` for any number of terms with rational `cᵢ`, from the rational identity
  `∏ rᵢ^{D·cᵢ} = 1` (`D` = lcm of the coefficient denominators), split into two natural-power
  products `∏pos = ∏neg` and closed by `norm_num`; `Real.log_pow` / `Real.log_mul` expand both sides
  and `linarith` finishes.
* `mixed`: `lo ≤ V` and/or `V ≤ hi` for `V = (exact group) + (remainder logs) (+ R)`. The exact group
  cancels as above. The remainder folds to `log(X)/D'` and is enclosed by
  `1 − 1/X ≤ log X ≤ X − 1`. An optional opaque real `R` is carried with hypothesis bounds `R_lo ≤ R ≤ R_hi`,
  for the "bounded part" some other certificate supplies.

Entry points: `log_cancellation_certificate`, `LogCancellationCertificate`; the same `certify` / `emit`
path, dispatched by `spec["route"]`. Layer-1 refusals: a group that does not cancel exactly,
a nonpositive argument, a zero coefficient, a claimed bound that the tangent enclosure does not carry,
or no bound claimed. Dogfood: `examples/log_combination` instances 6-9 (`log 12 = 2 log 2 + log 3`,
`(1/2)log(9/4) + (1/3)log(8/27) = 0`, and two mixed instances, one with `R`), all
`[propext, Classical.choice, Quot.sound]`. Kernel negative controls live in
`tests/test_log_cancellation.py` (forged `log 12 = 2 log 2 + log 5`, and a mixed bound `≤ 1/200`
below the true `log 1.01`). Both are rejected and their true twins compile. They are face-specific adapters run through
`generic_negative_control`, not registered, because the registry keeps one adapter per emitter.
Limitation: the remainder enclosure is the degree-1 tangent pair only, and a remainder that needs the
`tight` degree-3 route is refused.

### `eventual_threshold` — quadratic sign race (`QuadraticSignRaceCert`)

For `P(m) = a·m² + b·m + c` with rational coefficients, this face certifies the exact sign pattern on the integers
`m ≥ m₀` with no hypotheses. Modes: `switch` (`a > 0`; `P < 0` on `[m₀, r]`, `P > 0` from `r+1`, so
the eventual threshold is sharp), `positive` (`a > 0`) and `negative` (`a < 0`, one sign
throughout). Each mode also proves the conjunct `P(m) ≠ 0` for every integer `m ≥ m₀`. The certificate is the vertex condition
`-b/(2a) ≤ m₀`, which makes `P` monotone on the range, plus the endpoint signs (`P(r) < 0 < P(r+1)`, or the sign of `P(m₀)`).
The kernel re-checks it with two `ring` identities that carry the certificate's literals. The first is the Taylor
expansion at the anchor `k`, `P(m) = a(m−k)² + P'(k)(m−k) + P(k)`, whose three summands are
sign-definite. The second, for the head of a switch, is `P(r) − P(m) = (r−m)(a(r+m)+b)`.

Why here: this is an eventual-threshold claim with an explicit, computed witness (and the
complementary sign below it). It does not fit `sturm_positive`, which is bounded-interval Bernstein root exclusion, or
`tails.py`, which is a Polya adapter over a shifted variable. `EventualThresholdEmitter`'s sensitivity stance is now
`CERTIFICATE_SENSITIVE`. The arity face still has no corruptible data, but this face does. The stance comes with a registered adapter
(`adapter_eventual_threshold`): the switch of `m² − 10m − 7` is forged one step late (`r = 11`, which claims
`P(11) < 0` although `P(11) = 4`). The kernel rejects that forgery, and the true `r = 10` twin compiles. Dogfood:
`examples/quadratic_sign_race` (new v4.32.0 project, generic instances: `m² − 10m − 7` switching
between 10 and 11; `C(m,2)` overtaking `3m + 20` between 10 and 11; `m² − 3m + 1 > 0` for `m ≥ 3`;
`−m² − 8m − 17 < 0` for `m ≥ −3`), all `[propext, Classical.choice, Quot.sound]`. Limitations: the
face covers degree 2 only, uses the sufficient vertex condition `-b/(2a) ≤ m₀` (not the weaker
integer condition `-b/(2a) ≤ m₀ + 1/2`), and proves `P ≠ 0` only on `m ≥ m₀`, not on all of ℤ.

### `monotone_tail` — piecewise-linear node-condition tail (`PLNodeTailPayload`)

This face closes a two-parameter family in one step: for all integers `m ≥ M+1` and all `y ∈ (0, 1]`,
`m·U(y) + L(y) ≤ 0`. Here `U ≤ 0` lies below a piecewise-linear function with rational nodes `(y_i, U_i)`
(`0 < y_0 < … < y_K = 1`, `U_0 = 0`, `U = 0` on `(0, y_0]`). `L ≤ 0` for `y ≤ y†` and
`L(y) ≤ s·(y − y†)` above. The certificate is the node condition `(M+1)·|U_i| ≥ s·(y_i − y†)` at every node
beyond `y†`. On each segment beyond `y†`, `h = m·U + s·(y − y†)` is linear and `≤ 0` at both ends, so it is
`≤ 0` throughout. The kernel checks this per segment through the exact identity
`(b − a)·h(y) = (b − y)·h(a) + (y − a)·h(b)` (`ring`), with `h(a), h(b) ≤ 0` from the node literals.

Why here: this is the ratio tail's monotone-plus-base shape with the roles moved. `m·U(y)` is nonincreasing in `m`
because `U ≤ 0`, and the node condition is the base case `m = M+1` for every `y` at once.
The core theorem takes `U`, `L` abstractly with their conditions as HYPOTHESES (the honest seam). With
`L = "log_tangent"` the emitter also discharges them for `L(y) = log(1+y) − log(1+y†)` (monotone below `y†`;
`log x ≤ x − 1` above, which needs `s ≥ 1/(1+y†)`). It then states a hypothesis-free corollary for the
concrete `U = min(0, segment lines)`, which lies below every segment line. `MonotoneRatioTailEmitter`'s stance is now
`CERTIFICATE_SENSITIVE` with a registered adapter (`adapter_monotone_tail`): `M` is forged from 1 to 0, and
the claim is genuinely false at `m = 1, y = 1` (`−1/5 + log(4/3) > 0`). The kernel rejects the forgery, and the
true twin compiles. Dogfood: `examples/pl_node_tail` (new v4.32.0 project; generic instances with
`y† = 1/2, s = 2/3, M = 1` and `y† = 1/3, s = 3/4, M = 14`, plus the abstract-`L` core), all
`[propext, Classical.choice, Quot.sound]`. Limitations: `U` enters only through the upper hypotheses
(or the min-of-lines instance). The only concrete `L` is the log tangent, and any other concave `L` must
supply `hL1`/`hL2` itself. `U_0 = 0` is required. The concrete corollary is for the min-of-lines `U`,
which equals the piecewise-linear interpolant only when the node sequence is concave.
## Session 2026-09-29 — `concave_pooled_induction` (tree-recursion bounds by a concave pooled-mean witness)

`ConcavePooledInductionEmitter` (kind `concave_pooled_induction`). **Method credit: concave-witness
induction, from the draft "The maximum Laplacian ratio of a tree for all n >= 303: concave witnesses
and one-variable certificates" (28 September 2026), communicated by Professor John L. Goldwasser
(author: his London colleague; name to be added).** For a branching recursion on finite rooted
trees -- message `y_v = h(m, R)`, profit `l(v) = sum l(c) + g(m, R)`, `R = sum y_c`, leaf pair
`(y_leaf, l_leaf)`, `h` and `g` rational -- it certifies `l(b) + alpha |b| <= U(y_b)` for every
tree, with `U` concave piecewise-linear (strictly decreasing slopes). In Lean `U` is the MINIMUM of
its affine pieces, so Jensen at the pooled mean is one generic lemma (`minPieces_jensen`), and the
induction is one generic theorem over `PTree` (`pooled_induction_core`; it also takes a carried
`U` below a pooling `V`, which this emitter instantiates as `U = V`). Per child count `m = 1..M`
and per cell of `R`, each piece of `U(h)` and the closure `lo <= h <= hi` is one polynomial
inequality with exact Bernstein coefficients, closed by `linarith` over the product facts; the
tail `m >= M + 1` (m-free `h`, `g`, `lo >= 0`) reduces to one variable through a piece with
`b_j <= 0` (`m b_j <= (M+1) b_j` or `m b_j <= (R/hi) b_j`), with a Taylor certificate on the
unbounded last cell. Without a tail the claim is stated for child count `<= M`. Not supported:
exempt "atom" children, a carried `U` different from `V` at the emitter level, non-rational
`g`/`h` (log cells are the sibling `mobius_tangent_cell` kind). The tail is our own sufficient
condition, not the draft's Lemma 3.4 node condition.

Design doc: [`EMITTER_CONCAVE_POOLED_INDUCTION_DESIGN_2026-09-29.md`](EMITTER_CONCAVE_POOLED_INDUCTION_DESIGN_2026-09-29.md).
Dogfood: `examples/concave_pooled_induction/` (`generate.py --check`; lake project on Mathlib
v4.32.0): the classical matching message `y_u = Z(T_u - u)/Z(T_u)` with `l = -sum_u y_u` and
`alpha = 3/5`, i.e. `sum_u y_u >= (3/5)|T|` for every finite rooted tree (the path shows the sharp
constant is `1/phi`), the same recursion on paths (bounded mode), and a clearly synthetic
m-dependent instance; 134 theorems, all `[propext, Classical.choice, Quot.sound]`. It is NOT the
Brualdi-Goldwasser problem; nothing from the draft's Sections 4-9 is used. Negative control:
`adapter_concave_pooled_induction` (the paths instance forged to `alpha = 13/20 > 1/phi`, a false
claim; its cells carry a negative Bernstein coefficient and the kernel rejects the `linarith`;
the true twin compiles). `conjecture1_proved = False`.
## Session 2026-09-29 — `gap_budget_multiplicity` (tangent-price gap budgets)

`GapBudgetMultiplicityEmitter` (kind `gap_budget_multiplicity`) prunes a multiset optimisation
with a gap budget. The value is `Phi = sum w(k)`, optionally plus `c log(sum y / M)` with `c > 0`,
under a normalisation `sum ell(k) = M`. A price `tau` and the log tangent give the per-atom gaps
`gamma(k) >= 0` and the budget `sum gamma <= theta = C - B` against a benchmark of value `B`. From
that budget the kernel checks the per-atom caps `floor(theta_hi / g_k)`, the exclusions, a tail
exclusion certified by convexity, and a knapsack over the surviving counts (`decide` over
naturals). Gap and budget bounds come from `enclosure_tree` (reused) or are exact. The generic core
(six lemmas) is emitted once per file. Each instance adds a benchmark lemma, which makes the main
theorem non-vacuous. The tangent-gap pricing pattern is from a draft communicated by Professor
John L. Goldwasser (28 Sep 2026).

Design doc: [`EMITTER_GAP_BUDGET_MULTIPLICITY_DESIGN_2026-09-29.md`](EMITTER_GAP_BUDGET_MULTIPLICITY_DESIGN_2026-09-29.md).
The dogfood is `examples/gap_budget_multiplicity/lean/GapBudgetMultiplicity.lean`, generated by
`generate.py`. It covers the classical maximum product of parts with sum `N = 3t, 3t+2, 3t+4`,
uniform in `t` (all 3s; at most one 2; at most two 2s or one 4 with the decided knapsack; no part
`>= 5`), plus a concave toy at two tangent points and a product-form cross-check. It has 59
theorems plus the cross-check, standard axioms only. Negative control: `adapter_gap_budget_multiplicity`
forges `gamma(2) >= 1/20` in the `N = 3t+2` budget, which claims `count 2 = 0`; the benchmark
refutes that claim and the kernel rejects it. Nothing here bears on RH or on the Laplacian-ratio
problem; `conjecture1_proved = False`.

## Session 2026-09-30 — `affine_hull_dominance` (exact tree maxima by convex-hull pruning of vector states)

`AffineHullDominanceEmitter` (kind `affine_hull_dominance`). For a positive multilinear tree
recursion -- an empty-bundle state `e`, a bilinear "bundle plus child" map `T`, a planting matrix
`P_c` depending on the child count, and a root covector `F_k`, all with nonnegative rational
coefficients -- it certifies, for every `n = 2..N`, the exact maximum `M_n` of the root value over
ALL trees on `n` vertices (`IsGreatest`), and that every maximizer has every branch state and every
partial bundle state on the kept hull points. The certificate is the exact hull dynamic program:
per class (size, child count) the kept points (hull vertices and hull-edge points, ties kept) and,
for every candidate in the Lean checker's own enumeration order, a `kept i` or `dom w` witness
(rational convex weights, componentwise domination, strict somewhere). `Cert.Valid` is closed by
one `decide +kernel`. The generic exchange induction states domination in dual form (every
nonnegative covector is at least as large at some kept point), so each recursion step is a
covector pull-back (`dot_mul_left`, `dot_mul_right`, `dot_plant`) and transitivity is immediate;
the strict form under the sign conditions (`Rec.Signs`) gives the maximizer theorem
`kept_of_pi_eq`.

Design doc: [`EMITTER_AFFINE_HULL_DOMINANCE_DESIGN_2026-09-30.md`](EMITTER_AFFINE_HULL_DOMINANCE_DESIGN_2026-09-30.md).
Dogfood: `examples/affine_hull_dominance/` (`generate.py --check`; lake project on Mathlib
v4.32.0): the Randic-weighted matching sum `sum_M prod_{uv in M} 1/(deg u deg v)` for n <= 14
(`M_14 = 9477/512`, unique maximizer at every n), one plus the Randic-type edge sum as a
3-dimensional recursion for n <= 12 (ties at n = 7, 8, 9), and a synthetic recursion with larger
hulls for n <= 12; 199 theorems, all `[propext, Classical.choice, Quot.sound]`, `lake build` 61 s.
Values and maximizer lists are cross-checked against brute force over every tree with at most 9
vertices. Negative control: `adapter_affine_hull_dominance` (the matching sum at N = 6 with every
maximizing root bundle removed and replaced by a non-dominating convex witness, claiming the
second-best value 7/2 as M_6 -- false, since 29/8 is attained; the decided checker rejects the
witness; the true twin compiles). Completeness of the maximizer list up to isomorphism is
generator-side, not a kernel theorem. `conjecture1_proved = False`.

## Session 2026-09-30 — `single_crossing_ladder` (single crossing, increasing breakpoints, best-member ladder)

`SingleCrossingLadderEmitter` (kind `single_crossing_ladder`) takes a parametric family of
log-sums `F_j(x) = sum kappa_i(j) log(1 + beta_i(j) x)` on `S = [0, X]` or `[0, oo)`, all tied at
`x = 0`. It certifies three things: (a) consecutive members cross EXACTLY ONCE, with the crossing
in a rational bracket, or one member dominates the other; (b) the breakpoints increase; (c) the
best-member ladder, where on `(lambda_{j-1}, lambda_j)` the member `F_j` is the unique maximum of
the window. The derivative of `D_j = F_j - F_{j+1}` is `N_j / P_j`, where `P_j` is a product of
the positive log arguments and `N_j` is a polynomial. Its single sign change `+ -> -` is certified
by Bernstein/Taylor cells (the `PolyCert` machinery of `concave_pooled_induction`) together with a
crossing cell on which `N_j' < 0`. The bracket values `D(lo) > 0 > D(hi)` use `enclosure_tree` log
atoms, Taylor only. A generic Lean core is emitted once per file: `single_crossing_core` (mean
value plus intermediate value), `dominated_core`, and `ladder_core` (`Nat.le_induction`). We added
a new kind, not a face, because the existing `unimodal` / `monotone_tail` / `eventual_threshold`
cores are about integer sequences and thresholds, and none states a real-parameter crossing (see
the design doc).

Design doc: [`EMITTER_SINGLE_CROSSING_LADDER_DESIGN_2026-09-30.md`](EMITTER_SINGLE_CROSSING_LADDER_DESIGN_2026-09-30.md).
Dogfood: `examples/single_crossing_ladder/` (`generate.py --check`; lake project on Mathlib
v4.32.0). The first instance is the arm ladder of the matching sum: the per-vertex log-weight
`F_j` of an arm with `j` cherries, members 1..7 on `[0, oo)`. Arms 1 and 2 are dominated, and arms
3..7 form the ladder with `lambda_3..lambda_6` in `(0.43050, 0.43051)`, `(0.87247, 0.87248)`,
`(1.19239, 1.19240)` and `(1.43559, 1.43560)`. The second is a synthetic bounded instance on
`[0, 2]`. The dogfood has 133 theorems, all `[propext, Classical.choice, Quot.sound]`.
Negative controls: `adapter_single_crossing_ladder` shifts the `lambda_3` bracket to
`(0.43052, 0.43053)`. That bracket is false, and the kernel rejects `_p3_vlo`. A double crossing
claimed single on `[0, oo)` is also rejected: its tail sign cell is false. Both true twins compile.
Scope: the ladder is proved for a finite window of members only. `conjecture1_proved = False`.

## Session 2026-10-01 — `typed_cavity_induction` (a type table as an inductive invariant over all trees)

`TypedCavityInductionEmitter` (kind `typed_cavity_induction`) works on a rational tree recursion
`y = h(m, R)`, `l = sum l(c) + g(m, R)`, `R = sum y(c)`. It certifies that a finite TYPE TABLE is
an inductive invariant over every finite rooted tree, or every tree of child count at most `D`.
A type is a predicate on (child count `m`, message sum `R`): consecutive degree groups, each
split into `R`-bins. Each type carries a bound `B` and a message interval; an exact atom pins its
message. The claim is `l(b) <= B[type b]` and `y(b) in [ylo, yhi][type b]`, with the corollary
`l <= max B` and an optional join that closes `K` trees at a root. Three devices reduce the
infinitely many parent steps to finitely many exact checks:

* enumeration over every multiset of child types for `m <= M_enum` (point cells by `norm_num`,
  interval cells by Bernstein coefficients);
* a tangent band for `M_enum < m <= M_tail`: a certified linear majorant of `g` makes the sum
  separable, leaving one inequality per degree and bin;
* an analytic tail for all `m > M_tail` at once: a two-variable certificate in `u = m - K0` and
  `R`, then `m mu_T <= K0 mu_T`.

The generic Lean core (`typed_induction_core`, `step_of_counts`, `separable_bound`) is emitted
once per file. We added a new kind, not a face: `concave_pooled_induction` carries one scalar
witness and no type table, and `affine_hull_dominance` is bounded in size (see the design doc).

Design doc: [`EMITTER_TYPED_CAVITY_INDUCTION_DESIGN_2026-10-01.md`](EMITTER_TYPED_CAVITY_INDUCTION_DESIGN_2026-10-01.md).
Dogfood: `examples/typed_cavity_induction/` (`generate.py --check`; lake project on Mathlib
v4.32.0).

* The first instance is published: the Balister-Bollobás-Gerke half-tree recursion (2) for the
  generalized Randić index `R_{-1}` (J. Graph Theory 56 (2007) 270-286), with types by root
  degree and the table `c_d` of their (4)-(5), at `beta_3 = 7/27` and `beta_4 = 139/528`. This is
  their Lemma 4. Through the join it gives their Theorem 6: `R_{-1}(T) <= (7/27) n + 5/27`
  (implying the printed `11/54`) and `R_{-1}(T) <= (139/528) n + 73/528`. A hand-written
  companion, `TypedCavityInductionRandic.lean`, restates both for `R_{-1}` itself.
* The second instance is synthetic: eight types with `R`-bins, interval messages, a band at
  `m = 3..4` and an `m`-dependent tail at `m >= 5`.

The dogfood has 585 + 11 theorems, all `[propext, Classical.choice, Quot.sound]`. Negative
control: `adapter_typed_cavity_induction` lowers `beta_3` by 1/1000 and recomputes the table. That
claim is false: starting from `[3, 2, 1]` and repeatedly joining two copies at a new root drives `c_T` past `c_3`. The
kernel rejects the degree-3 point cell, and the true twin compiles. v1 is rational only;
parameter boxes with Taylor enclosures are documented as v2. `conjecture1_proved = False`.
