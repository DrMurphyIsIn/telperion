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
