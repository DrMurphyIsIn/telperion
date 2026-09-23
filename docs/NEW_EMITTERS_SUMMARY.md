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
