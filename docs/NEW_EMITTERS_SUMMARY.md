# New Telperion emitters (2026-09-02) — parallel-session skill reference

Nineteen new certificate emitters landed across two RH+BG "emitter sweeps" and the
build-out of the 2026-08-21 BG/P=NP backlog. This is the quick reference so any
session knows what Telperion can now discharge without re-deriving it.

## Meta — read first
- **All 19 are registered and CI-gated.** Each has an entry in `certify.py`
  (`_SPECIAL_KINDS` tuple + `_SPECIAL_DISPATCH` dict), an export in `__init__.py`,
  a worked `examples/<name>/` regeneration harness, a row in the README
  "Certificate shapes" table (now **64 rows**), a `<name>-compiles` CI job, and a
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

## Where to look / follow-ups
- **Shape reference:** `README.md` "Certificate shapes" table.
- **Design + honest scope:** `docs/EMITTER_ROADMAP_2026-09-02_RH_CROSSCUT.md`,
  `docs/EMITTER_ROADMAP_2026-09-02_SWEEP2.md`, and
  `docs/EMITTER_ROADMAP_2026-08-21.md` (see its `STATUS UPDATE (2026-09-02)`
  section — the BG/P=NP backlog is now essentially complete).
- **Two residual open fronts** worth a session: **`symmetric_quad` d≥2** (harmonic
  completeness — the marquee P=NP moment-PSD generalization) and
  **`separable_convex` max/vertex** (`VertexLemmaFull.lean` spreading-exchange
  induction).
- **The two sweeps found the general certificate surface close to saturated** —
  the remaining roadmap is these two open fronts plus a couple of fold-in
  sub-modes (`HodgeRiemann`→`psd_form` signature-(1,n−1) mode,
  `DiscreteConcavity`→`logconcave` enclosure mode).

## Building your own emitter (the recipe these 19 followed)
An emitter = `src/telperion/emit_<name>.py` (a frozen `Certificate` dataclass +
`<name>_certificate(...)` that exact-self-checks and RAISES on bad input +
`certify_<name>_point(family,pt,name)` + `<Name>Emitter(Emitter).emit_body` +
`<name>_family(...)`), registered in `certify.py`'s two structures + `__init__.py`,
plus `examples/<name>/{generate.py, lean/*}`, a README row, a CI job, and a
`telperion.toml` entry. **Model each emitted proof on a lemma already proven in
the corpus, then verify with one local `lake build`** — that near-eliminated build
failures. Gotcha: ℝ-ascribe bare rational literals in emitted Lean (`(0:ℝ)`,
`(<rat>:ℝ)`) or they default to ℤ and won't unify with ℝ lemmas.
