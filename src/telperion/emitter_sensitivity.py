"""Emitter-wide certificate-sensitivity registry — Telperion pointed at its own
emitter set (Vector 2a of the self-application program).

`nonvacuity.assert_certificate_sensitive` proves an emitted identity is
LOAD-BEARING: corrupt the certificate and the claim must break.  It is the
semantic complement to the structural reflexive-statement check.  Today only the
WZ emitter invokes it — yet many emitters carry a corruptible identity
certificate (`linear_combination`/`ring` shapes: cone, Putinar, Handelman,
Nullstellensatz, consequence, …).

This module makes each emitter's stance EXPLICIT and ENFORCED, so the property
"every emitter has declared whether its certificate is load-bearing" becomes a
standing CI gate rather than tribal knowledge:

  * CERTIFICATE_SENSITIVE   — carries an identity certificate whose corruption
                              must break the claim; `assert_certificate_sensitive`
                              is the right guard.  `checked_in` names the module
                              that actually invokes it (truthfully verified), or
                              is None for "declared-but-not-yet-wired" — naming
                              the gap honestly instead of papering over it.
  * STRUCTURALLY_NONVACUOUS — a positivity / decidable / finite-cover / glue /
                              adapter shape with no separately-supplied
                              corruptible identity; the structural reflexive check
                              plus the kernel suffice.

No emitter file is modified: this is an additive meta-layer.  A newly-added
Emitter subclass fails `test_certificate_sensitivity` until its stance is
declared here.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .workflow import Emitter

CERTIFICATE_SENSITIVE = "certificate_sensitive"
STRUCTURALLY_NONVACUOUS = "structurally_nonvacuous"

# Negative-control declaration (the AXLE `disprove` layer): every emitter must
# declare whether it carries a Lean-backed generic negative control (an ADAPTER
# in negative_control_harness.ADAPTERS) or is NOT_APPLICABLE with a reason.
NEG_CONTROL_ADAPTER = "adapter"
NEG_CONTROL_NOT_APPLICABLE = "not_applicable"
# A CERTIFICATE_SENSITIVE emitter whose kernel-gated adapter has NOT been built
# yet.  The honest analogue of ``checked_in=None`` for the semantic wiring: the
# emitter is falsifiable in principle (a forged cert would be kernel-rejected),
# but no adapter exists in ``negative_control_harness.ADAPTERS`` — we NAME that gap
# rather than lie by claiming an adapter or mislabelling it not_applicable.
NEG_CONTROL_DECLARED_UNWIRED = "declared_unwired"

_NEG_CONTROL_KINDS = frozenset(
    {NEG_CONTROL_ADAPTER, NEG_CONTROL_NOT_APPLICABLE, NEG_CONTROL_DECLARED_UNWIRED}
)


@dataclass(frozen=True)
class NegControlStance:
    """One emitter's declared negative-control stance.

    ``kind`` is one of:

    * ``NEG_CONTROL_ADAPTER`` — a two-sided kernel control exists, keyed by the
      emitter name in ``negative_control_harness.ADAPTERS``;
    * ``NEG_CONTROL_NOT_APPLICABLE`` — no independent corruptible witness to
      falsify at the emission layer (a positivity/decidable/finite/glue shape);
    * ``NEG_CONTROL_DECLARED_UNWIRED`` — certificate-sensitive, so an adapter is
      POSSIBLE, but none is built yet (the honestly-named gap).

    ``reason`` is required for the not-applicable and declared-unwired cases.
    """

    kind: str
    reason: str = ""


@dataclass(frozen=True)
class SensitivityStance:
    """One emitter's declared certificate-sensitivity stance.

    ``checked_in`` is the module basename (e.g. ``emit_wz``) that invokes
    ``assert_certificate_sensitive`` for this emitter, or None when the semantic
    check is not (yet) wired through the generic primitive.

    ``neg_control`` is the negative-control declaration; when left None it is
    DERIVED from ``stance`` after the registry is built (see ``_derive_neg_control``):
    CERTIFICATE_SENSITIVE emitters carry an adapter, STRUCTURALLY_NONVACUOUS ones
    are not-applicable (their own ``reason`` is the not-applicable reason).
    """

    stance: str
    reason: str
    checked_in: str | None = None
    neg_control: "NegControlStance | None" = None


_S = SensitivityStance

# The 30 emitters and their stances.  CERTIFICATE_SENSITIVE = carries a
# corruptible identity certificate; STRUCTURALLY_NONVACUOUS = positivity /
# decidable / finite / glue / adapter shape.
REGISTRY: dict[str, SensitivityStance] = {
    # --- identity-carrying: a corrupted certificate must break the claim ---
    "WZEmitter": _S(CERTIFICATE_SENSITIVE,
                    "hypergeometric identity Σ_k F = rhs via a WZ mate; the mate "
                    "is load-bearing", checked_in="emit_wz"),
    "SOSEmitter": _S(CERTIFICATE_SENSITIVE,
                     "p = Σ dᵢ·ℓᵢ² ring identity; a corrupted Gram/multiplier "
                     "breaks the identity"),
    "ConeFarkasEmitter": _S(CERTIFICATE_SENSITIVE,
                            "target = Σ λᵢ·bᵢ Farkas combination; corrupt a λ and "
                            "the ring identity fails"),
    "ConstrainedSOSEmitter": _S(CERTIFICATE_SENSITIVE,
                                "Putinar p = σ₀ + Σ σᵢ·gᵢ; the SOS multipliers are "
                                "the corruptible certificate"),
    "HandelmanEmitter": _S(CERTIFICATE_SENSITIVE,
                           "p = Σ c_α ∏ ℓᵢ^{αᵢ} nonnegative product combination; "
                           "the coefficients are load-bearing"),
    "ZeroFreeCosineEmitter": _S(CERTIFICATE_SENSITIVE,
                                "same shape as HandelmanEmitter: p = Σ c_α ∏ ℓ^α "
                                "Fejér–Riesz/Handelman witness closed by `ring`; a "
                                "corrupted coefficient breaks the identity",
                                checked_in="emit_zero_free_cosine"),
    "NullstellensatzEmitter": _S(CERTIFICATE_SENSITIVE,
                                 "p = Σ hᵢ·gᵢ ideal-membership cofactors; a "
                                 "corrupted cofactor breaks linear_combination"),
    "InfeasibilityEmitter": _S(CERTIFICATE_SENSITIVE,
                               "1 = Σ λⱼ·gⱼ refutation; the multipliers are the "
                               "certificate of non-existence"),
    "ConsequenceEmitter": _S(CERTIFICATE_SENSITIVE,
                             "lhs−rhs = Σ cᵢ·(hyp_i) cofactors; corrupt a cofactor "
                             "and the consequence no longer follows"),
    "SOSRefutationEmitter": _S(CERTIFICATE_SENSITIVE,
                               "−1 = σ₀ + Σ σᵢ·gᵢ + Σ λⱼ·hⱼ; the multipliers are "
                               "the corruptible refutation certificate"),
    "RealNullstellensatzEmitter": _S(CERTIFICATE_SENSITIVE,
                                     "p^{2m} + s ∈ ⟨gₖ⟩ with SOS s; cofactors and "
                                     "SOS terms are load-bearing"),
    "CGRoundEmitter": _S(CERTIFICATE_SENSITIVE,
                         "Chvátal–Gomory derivation; carries a bespoke "
                         "rounding-sensitivity self-check in emit_cg_round "
                         "(disarming every round must fail to dominate the goal)"),
    "TelescopingPotentialEmitter": _S(CERTIFICATE_SENSITIVE,
                                      "Σ local(v) ≤ P(root) from a per-node "
                                      "super-solution; the potential P is the "
                                      "load-bearing certificate"),
    "IdentityEmitter": _S(CERTIFICATE_SENSITIVE,
                          "concrete rational/integer identity; a corrupted side "
                          "breaks ring/norm_num (may opt reflexive via "
                          "LeanProfile for reference identities)"),
    "ExactFactEmitter": _S(CERTIFICATE_SENSITIVE,
                           "concrete exact fact/power; corruption breaks norm_num"),
    # --- structurally non-vacuous: positivity / decidable / finite / glue ---
    "DirectPolyaEmitter": _S(STRUCTURALLY_NONVACUOUS,
                             "0 ≤ f via positivity on an all-nonneg form; the "
                             "reflexive-statement check + positivity suffice"),
    "TwoMomentCountEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                "(2−κ)N − err ≤ count from two moment-bound "
                                "hypotheses via nlinarith off Real.sqrt_le_sqrt; the "
                                "moment bounds are the analytic trust seam, the "
                                "arithmetic implication carries no corruptible identity",
                                # Structural, yet a statement-level kernel control exists:
                                # the Davenport–Heilbronn over-claim (concluded proportion
                                # inflated past what the moments support) is genuinely
                                # false and kernel-rejected.  See
                                # negctrl_adapters/adapter_two_moment_count.py.
                                neg_control=NegControlStance(NEG_CONTROL_ADAPTER)),
    "RankTraceScalarEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                 "integrality atom 2c·x−c² ≤ x² = (x−c)²≥0 via "
                                 "nlinarith [sq_nonneg]; a pure square-positivity fact"),
    "LiPositivityLadderEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                    "0 ≤ (taylorCoeff riemannXi n).re from a certified "
                                    "positive lower bound (hypothesis hlo = the Arb enclosure, "
                                    "the trust seam) via le_trans; positivity, no corruptible identity",
                                    # Structural, yet a kernel control exists: the in-proof
                                    # norm_num gate 0 ≤ lo makes a sign-corrupted lower bound
                                    # kernel-rejected.  See negctrl_adapters/adapter_li_positivity.py.
                                    neg_control=NegControlStance(NEG_CONTROL_ADAPTER)),
    "UnitModulusSOSEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                "0 ≤ (2 − u^m − conj(u^m)).re for |u|=1 via the manifest Hermitian "
                                "square ‖1 − u^m‖² (Complex.mul_conj + Complex.normSq_nonneg); the "
                                "|u|=1 side condition is a hypothesis, positivity is by structure with "
                                "no separately-supplied corruptible identity (the degenerate power "
                                "m<1 is refused at certify time — the negative control)"),
    "BraggFloorEmitter": _S(STRUCTURALLY_NONVACUOUS,
                            "Route P Brick D3 diffraction rung floorHi ≤ braggLo − tailHi: a concrete "
                            "rational inequality discharged by norm_num (the truncated von Mangoldt "
                            "Bragg amplitude net of its certified tail clears the explicit archimedean "
                            "floor).  braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the "
                            "documented trust seam; certify REFUSES a non-positive margin, so no "
                            "vacuous/false inequality ships.  Finite category-b; the passage to the "
                            "companion coefficient is the conditional RH-hard exhaustion seam, never "
                            "discharged (conjecture1_proved = False)",
                            # Structural, yet a kernel control exists: a sign/value-corrupted literal
                            # making floorHi ≤ braggLo − tailHi FALSE is kernel-rejected by norm_num.
                            # See negctrl_adapters/adapter_bragg_floor.py.
                            neg_control=NegControlStance(NEG_CONTROL_ADAPTER)),
    "EnclosureIntervalFoldEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                       "integer near-CUE row-band check rowsOK…=true by decide; "
                                       "the Arb enclosures are the input trust seam, the kernel "
                                       "decides only the ℤ band membership"),
    "ReflectionHalvingEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                   "finite symmetry-fold Σw ≤ 2·Σlarge by decide; a concrete ℤ "
                                   "inequality (true iff small≤large, which certify enforces)"),
    "SpacingTailBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                  "concrete separated-config Σ δ/(gap)² ≤ 9/δ_s by norm_num; an "
                                  "exact-rational inequality, refused unless it holds"),
    "AutocorrSupportEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                 "concrete (v⋆v)(y) ≤ (2M−|y|)₊ support-geometry bound by "
                                 "norm_num; exact-rational, no corruptible identity"),
    "RayleighGramEmitter": _S(STRUCTURALLY_NONVACUOUS,
                              "cᵀJc − θ·cᵀIc > 0 with BOTH Gram contractions spelled out "
                              "entry-wise and re-done by norm_num; certify refuses a failing "
                              "or degenerate (cᵀIc≤0) instance — no vacuous inequality ships"),
    "PolytopeMomentEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                "Σ coeff·simplexMoment(R,m,es) = q re-executed by norm_num "
                                "over the in-Lean closed form; integral semantics + "
                                "triangulation validity are the documented generator seam"),
    "AdmissibleTupleEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                 "admissibility re-decided over a non-empty derived prime list "
                                 "(p=2 always present) + concrete diameter equality, both by "
                                 "kernel decide; inadmissible tuples ({0,2,4} control) refused"),
    "LeeYangStablePairEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                   "Schur–Cohn/Jury chain positivity recomputed from coefficient "
                                   "literals by norm_num; certify cross-checks numeric roots and "
                                   "refuses borderline/mismatched verdicts — no knife-edge certs"),
    "EndpointGeomCapEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                 "geometric cap (R+z)/(R−z)² ≤ (R+1)/(R−1)² on the "
                                 "disk: an endpoint-maximum monotonicity bound, no "
                                 "separately-supplied corruptible identity (pre-existing "
                                 "origin/main gap; classified here to green the gate)"),
    "BilinearBoxEmitter": _S(STRUCTURALLY_NONVACUOUS,
                             "before ≤ after via 4 Pólya corner positivity certs "
                             "+ assembly; no separate corruptible identity"),
    "IntervalBracketEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                 "rigorous two-sided rational enclosure; the "
                                 "bracket facts are decided by norm_num"),
    "PadicValuationEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                "v_p(n)=k as decidable divisibility by norm_num"),
    "InterlacingEmitter": _S(STRUCTURALLY_NONVACUOUS,
                             "Newton inequalities decided by norm_num on exact "
                             "rational coefficients"),
    "UnimodalMaxEmitter": _S(STRUCTURALLY_NONVACUOUS,
                             "integer max at the ratio crossing s*; monotone-ratio "
                             "positivity + crossing norm_num facts"),
    "LogConcaveSinglePointEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                       "max reduced to a single point k* by "
                                       "log-concavity; per-step norm_num facts"),
    "MonotoneRatioTailEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                   "b(s) ≤ B via a nonincreasing tail; tail-step "
                                   "positivity + base norm_num + induction"),
    "LatticeBoxEmitter": _S(STRUCTURALLY_NONVACUOUS,
                            "f ≤ B on ℤ^d_{≥0}: finite base box + per-axis "
                            "monotone tail; no corruptible identity"),
    "TailNatEmitter": _S(STRUCTURALLY_NONVACUOUS,
                         "∀ K ≥ K₀ tail: finite table + one uniform certificate, "
                         "induction-free structural discharge"),
    "CaseDispatchAssemblyEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                      "finite interval_cases dispatch; sensitivity "
                                      "is inherited from the leaf certificates"),
    "SubdivisionGlueEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                 "le_total case-split glue of subdivided leaves; "
                                 "no independent identity"),
    "DichotomyGlueEmitter": _S(STRUCTURALLY_NONVACUOUS,
                               "le_total classification over declared thresholds"),
    "ReparamAdapterEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                "Nat.cast_sub cast-rewrite adapter over an "
                                "underlying certificate; no new identity"),
    "VarMapAdapterEmitter": _S(STRUCTURALLY_NONVACUOUS,
                               "MapSpec-driven substitution rewrite in the "
                               "original variables; no new identity"),
    "CustomAssemblyEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                "hand-designed escape-hatch skeleton; "
                                "load-bearingness is the author's responsibility "
                                "and covered by the structural reflexive check"),
    "TangentSumEmitter": _S(STRUCTURALLY_NONVACUOUS,
                            "convex-polynomial (any even degree) tangent-line bound "
                            "B ≤ Σf(xᵢ); the per-term surplus is an exact rational "
                            "SOS (ring+positivity) assembled by linarith, no "
                            "corruptible identity certificate"),
    "CauchySchwarzEmitter": _S(STRUCTURALLY_NONVACUOUS,
                               "(Σwᵢxᵢ)² ≤ (Σwᵢ)(Σwᵢxᵢ²) via the pairwise-difference "
                               "SOS Σwᵢwⱼ(xᵢ−xⱼ)² (ring+positivity+linarith); "
                               "positivity by structure, no corruptible identity"),
    "PSDFormEmitter": _S(STRUCTURALLY_NONVACUOUS,
                         "0 ≤ xᵀMx for a positive-semidefinite M via the exact "
                         "completing-the-square congruence xᵀMx = Σ cᵢ·baseᵢ² (ring+positivity); "
                         "positivity by structure, no corruptible identity"),
    "Xor3MomentPSDEmitter": _S(STRUCTURALLY_NONVACUOUS,
                               "3-XOR moment matrix PSD via GF(2) block-rank-one SOS "
                               "xᵀMx = Σ_class(Σ σ_S x_S)² (ring+positivity); positivity "
                               "by structure, no corruptible identity"),
    # --- emitters merged from main (runway + knapsack_sos arc) ---
    "FwdTelescopeEmitter": _S(CERTIFICATE_SENSITIVE,
                              "forward telescoping Σ = Π (SumEqProd); the "
                              "telescoping mate is the load-bearing identity"),
    "RationalIdentityEmitter": _S(CERTIFICATE_SENSITIVE,
                                  "an exact rational identity (Gram-bridge shape); "
                                  "a corrupted side breaks ring/norm_num"),
    "RationalSOSEmitter": _S(CERTIFICATE_SENSITIVE,
                             "Artin: q·p is SOS for nonneg-but-not-SOS p; the "
                             "denominator q and the SOS of q·p are load-bearing"),
    "BernsteinEmitter": _S(STRUCTURALLY_NONVACUOUS,
                           "interval positivity via nonnegative Bernstein "
                           "coefficients; positivity by structure"),
    "FiniteDecideEmitter": _S(STRUCTURALLY_NONVACUOUS,
                              "a finite proposition discharged by the Lean kernel "
                              "`decide` — decidable, no corruptible certificate"),
    "PolyaZerosEmitter": _S(STRUCTURALLY_NONVACUOUS,
                            "Castle–Powers–Reznick Pólya-with-zeros homogeneous "
                            "lift; positivity (zeros allowed on faces)"),
    "SturmPositiveEmitter": _S(STRUCTURALLY_NONVACUOUS,
                               "strict-interval positivity with a Sturm sequence "
                               "as the exact decision oracle (root exclusion)"),
    # --- 2026-09-04: classification of the previously-unclassified emitters
    #     (RH-region, BG-derived, and misc shapes). Evidence-based CS vs SN from
    #     per-emitter emit_body review. The CERTIFICATE_SENSITIVE ones without a
    #     negative-control adapter yet are declared NEG_CONTROL_DECLARED_UNWIRED
    #     (the honest gap, analogous to checked_in=None). ---
    "AchievabilityClosureEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "emit_body closes 0≤Q(x) on [l,b] by nlinarith over generic nonneg atoms (mul_nonneg (x-l)(b-x), sq_nonneg x, sq_nonneg (x-b)) + the two bound hyps"),
    "AffineParamEndpointEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Affine-in-parameter endpoint collapse: abstract core proved by nlinarith from the algebraic identity (hi-lo)(A+muB)=(hi-mu)(A+loB)+(mu-lo)(A+hiB)"),
    "AlgebraicBracketEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Rigorous-rational-enclosure shape: lo,a,hi ARE the statement, not a separate cofactor. norm_num decides the three pure-rational side-goals"),
    "BilinearCornerBoxEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Worst-corner box positivity: reusable affine-min-at-corners lemma closed by sign-cased mul_nonneg/nlinarith + 4 corner facts each norm_num-recomputed"),
    "BoxRobustEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Forall-box separable-quadratic 0<=target: nlinarith over generic nonneg atoms (sq_nonneg (v-lo)/(hi-v) per axis, 4 corner mul_nonneg per bilinear pair) + named box bounds; no separately-supplied corruptible cofactor -- the rigorous monomial-wise margin is recomputed by nlinarith as the nonneg combination"),
    "HyperbolicityEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Discriminant nonnegativity (b^2-4ac>=0) is recomputed by nlinarith from structural sq_nonneg/corner facts + the kernel bridge lemma; there is no separately-supplied corruptible cofactor"),
    "JensenPolynomialHyperbolicityEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Same shape as HyperbolicityEmitter for the d=2 Jensen polynomial: disc(c0,c1,c2)>=0 "
        "over Arb coefficient boxes via hyperbolic_deg2_of_discrim_nonneg + nlinarith off the "
        "named box hypotheses; the boxes enter as hypotheses (Arb trust seam), no "
        "separately-supplied corruptible identity.  Only discoverable when python-flint is "
        "importable (rh_jensen imports are flint-gated), which is why the flint-less CI unit "
        "job never surfaced the gap"),
    "CauchyDerivBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Both emitted shapes are structural: main wrapper is Mathlib's norm_deriv lemma specialized (R>0 via norm_num on a literal)"),
    "CavityExchangeEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Both emit paths discharge structurally: corner mode is `positivity` on an all-nonneg-coeff polynomial (reflexive nonneg form)"),
    "ConcaveStationaryMaxEmitter": _S(CERTIFICATE_SENSITIVE,
        "Ships a `_foc` theorem `g'(f*)=0` = an exact rational equation whose one side is the separately-supplied stationary point `fstar`"),
    "CurvatureBoundaryEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Convexity/positivity shape: nlinarith consumes the structural fact (x-a)(b-x)>=0 built from interval bounds, not a supplied cofactor"),
    "DiskCoordBoundsEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "\"Farkas-style\" is naming only: the cert (wr,wi,rho) is substituted into BOTH hypothesis and conclusion, so it parameterizes the statement, not a corruptible witness"),
    "FiniteArgmaxMarginEmitter": _S(CERTIFICATE_SENSITIVE,
        "Emits supplied concrete integer facts p_i*q_w < p_w*q_i (and p_w<q_w) closed by norm_num; the winner/competitor rationals are a separately-supplied payload (spec callback) whose"),
    "HalfPlaneDiskEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Payload carries only positive-rational B + 2 bools; the core 4B(B-Re w)>=0 is a product-of-nonnegatives closed by nlinarith from B>0 and Re w<=B"),
    # (BCSplit / JensenZeroCount / SphereBound stances live in the 2026-09-05
    #  entire-part batch below — earlier copies here were silently shadowed
    #  dict-literal duplicates, removed 2026-09-09; see
    #  test_registry_source_has_no_duplicate_keys.)
    "IntegralityGateEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "All emitted goals are concrete ℤ/ℕ literals: divisibility norm_num + per-row norm_num + a decide over a literal List(ℤ×ℤ). No separate multiplier/Gram/cofactor is consumed"),
    "LFunctionProductEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Emitted Lean discharges via a hard-coded Mathlib lemma (norm_LFunction_product_ge_one) + LFunction_modOne_eq + norm_mul/norm_pow + `exact h`"),
    "LogCombinationEmitter": _S(CERTIFICATE_SENSITIVE,
        "Log inequality folded to a rational-power/exp fact; every load-bearing step is norm_num/positivity recomputed from emitted literals + Mathlib log/exp lemmas glued by linarith"),
    "LogDerivRegionCoreEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "No separately-supplied corruptible witness. Per-instance A,L,k live inside BOTH the theorem hypotheses and goal, so linarith / field_simp;ring"),
    "MagnitudeSplitBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Triangle-inequality glue: linarith over Mathlib norm_sub_le/norm_add_le + the theorem's own magnitude hyps. No separately-supplied corruptible identity"),
    "OrderBalanceEmitter": _S(CERTIFICATE_SENSITIVE,
        "Emitter bakes a supplied rational-weight/integer-order tuple (a_j, k_j) into hpos/hb_j/hk_j hypotheses"),
    "ParametricHolomorphyEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Payload carries only (c, σ₀) numerals + derived gate values; emitted Lean re-derives every gate structurally via norm_num/linarith from 0<σ₀ and 1≤c"),
    "PerSizeDominanceSweepEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Per-config face is norm_num on a fully-closed concrete-rational LHS (baseOf L)^11*prodBcap L/(W*(5/3)^11)≤1"),
    "PolytopeMaxMonotoneEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Multi-affine box-positivity via worst-corner: emitted proof re-derives every corner value with norm_num and closes via structural affine-slice nlinarith+mul_nonneg on box hyps"),
    "PseudoExpectationDualityEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Payload is 4 scalars (name/n_vars/degree/mode); emitted Lean weights + kill lemmas are generated from these and proved by structural MvPolynomial algebra"),
    "RecursionClosureEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Emitted proof is pure transitivity glue: `exact recursion_closure_assembly` over abstract nodeVal with htan/hceil as ASSUMED theorem hypotheses"),
    "RecursiveDominationRatioEmitter": _S(CERTIFICATE_SENSITIVE,
        "Consumes cert.corners D-values as literal rationals baked into the emitted `hid ... := by ring` convex-combination identity and `hq_j := mul_nonneg hw_j (by norm_num)` nonneg witnesses"),
    "ScaleInvarianceEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "field_simp; ring closes f(lambda*args)=f(args) where both sides are the STATEMENT's own sympy-substituted shapes"),
    "SecondOrderRecurrenceEmitter": _S(CERTIFICATE_SENSITIVE,
        "Consumes a supplied three-term recurrence-satisfaction identity: A·g(q+2)+B·g(q+1)+C·g(q)=0 closed by `ring`, then fed to `linear_combination`"),
    "SeparableConvexExtremumEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Convex-φ extremum on fixed-sum box: MIN=tangent surplus φ−L is an exact rational SOS (ring+positivity, linarith), MAX=push-to-bound exchanges via nlinarith over structural"),
    "SymmetricQuadD2Emitter": _S(CERTIFICATE_SENSITIVE,
        "Load-bearing `hid` step is a completing-the-square rational identity (field_simp;ring) over separately-supplied exact rational functions t2_expr/n2_expr/pcoef/a/f0..f4 from the payload"),
    "SymmetricQuadFormEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "0 ≤ symbolic-in-N level-1 moment form via derived-and-exactly-rechecked completing-square congruence Φ=f0(A+(f1/f0)X)²+cCS(NQ−X²): positivity by structure + supplied CS hypothesis"),
    "TightCapEnclosureEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Both modes discharge structurally on exact ℚ: concrete = norm_num over unfolded W/Bcap/baseOf/prodBcap defs on a literal config (goal is a concrete rational)"),
    "TranscendentalEnclosureEmitter": _S(CERTIFICATE_SENSITIVE,
        "Consumes payload cert's supplied rational L (and U): _lower_box closes L≤log(1+x0) via Real.le_log_iff_exp_le reduced to concrete exp(L)≤1+x0 discharged by exp_bound' Taylor +"),
    # --- 2026-09-05: dVP zero-free-region atom emitters (bc_split/jensen_zero_count/
    #     sphere_bound from the 2026-09-02 batch, left unclassified there; and the
    #     2026-09-05 entire-part batch max_modulus/bc_deriv_re/entire_part_bound). All
    #     are wrapper / glue / disk-geometry shapes: the payload (radii, bounds) is
    #     substituted into BOTH hypotheses and goal, never a separately-supplied
    #     corruptible identity certificate — same stance as CauchyDerivBoundEmitter. ---
    "BCSplitEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Log-derivative combine w=Z+E, ‖E‖≤B ⟹ (-w).re ≤ B - Z.re (+ nonneg slack literal): "
        "linarith glue over Mathlib Complex.abs_re_le_norm + the theorem's own hyps; no supplied witness"),
    "JensenZeroCountEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Jensen zero-count for any analytic f: a concrete-(r,R) wrapper of Mathlib's "
        "AnalyticOnNhd.sum_divisor_le, r<R side-goals closed by norm_num on literals; the count IS the statement"),
    "SphereBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Strip-type growth ⟹ uniform sphere bound: disk-geometry gcongr/linarith from the hypotheses "
        "(‖z-c‖=R, |Re| ≤ ‖·‖), (c,R) parameterize the statement; no corruptible cofactor"),
    "MaxModulusEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Maximum-modulus propagation: a concrete-R wrapper of Mathlib's "
        "Complex.norm_le_of_forall_mem_frontier_norm_le (frontier_ball R≠0 via norm_num on a literal); "
        "the bound B is substituted into both hypothesis and goal"),
    "BCDerivReEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Real-part → derivative bound (Borel-Caratheodory + Cauchy): inline structural proof; (R,r,M') "
        "live in both hyps and goal, side-goals norm_num on literals, constant collapse by field_simp; no supplied identity"),
    "EntirePartBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Entire-part bound ‖logDeriv g c‖ ≤ 2M'/(R-r): self-contained 3-lemma preamble (log branch + "
        "BC-Cauchy + composition), wrapper feeds (R,r,M') via norm_num; the parameters parameterize the statement"),
    # --- 2026-09-06: zeta zero-localization (Stage 1) on-line zero-count emitter. ---
    "XiLineZerosEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "On-line nontrivial-zero existence for completedRiemannZeta: sign-change (lo>0 / hi<0 rational "
        "literals closed by norm_num) + Mathlib intermediate_value_Icc/Icc' through the kernel lemma "
        "ZetaZeroLocalization.completedZeta_im_eq_zero (Lambda real on the line). The enclosure boxes are "
        "carried as theorem HYPOTHESES (the documented Arb non-kernel input), not a baked-in corruptible "
        "fact -- a forged enclosure falsifies the hypothesis, leaving the IVT implication kernel-valid; "
        "no separately-supplied witness. conjecture1_proved = False"),
    # --- 2026-09-06: zeta-box-localization (Stage 2A) boundary winding-count emitter. ---
    "WindingCountEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Boundary log-derivative winding count Bd(Lambda'/Lambda)=2*pi*i*N. The enclosure boxes are "
        "documented Arb non-kernel input carried as theorem HYPOTHESES: in the toy z^2 (N=2) the winding "
        "is proven FROM SCRATCH via the segment/Complex.log branch-split primitive (clog_real + FTC-2 "
        "intervalIntegral.integral_eq_sub_of_hasDerivAt) with the two monodromy jumps log(-x)-log(x)=+-pi*i "
        "closed over norm_num-decided half-plane facts; in the Lambda [2/5,3/5]x[10,35] instance (N=5) the "
        "per-pole enclosure brackets (hin, strict rational interior bounds locating each zero) and the "
        "argument-principle residue decomposition enter as hypotheses, the per-pole winding is DISCHARGED "
        "from the same from-scratch interior-pole primitive, and Finset linearity telescopes the four "
        "sides -- a forged enclosure falsifies the hypothesis, leaving the argument-principle implication "
        "kernel-valid; no separately-supplied witness. conjecture1_proved = False"),
    # --- 2026-09-06: dVP Blaschke/two-scale atoms. All wrapper/glue/geometry shapes: the numeric data
    #     (radii R,R₀; σ,β,k) is substituted into BOTH hypotheses and goal, never a separately-supplied
    #     corruptible identity certificate — same stance as CauchyDerivBoundEmitter / TwoScale geometry. ---
    "TwoScaleSeparationEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Two-scale separation R-R₀ ≤ ‖z-ρ‖: reverse-triangle calc (norm_sub_norm_le + "
        "sub_sub_sub_cancel_right) from the sphere/closedBall membership hyps; radii parameterize the statement"),
    "FarPoleSumEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Far-pole sum ‖Σ (n u)conj u/(R²-conj u z)‖ ≤ (Σ|n u|)/(R-‖z‖): per-term reverse-triangle "
        "denom bound R²-‖u‖‖z‖ ≥ R(R-‖z‖) + norm_sum_le/Finset.sum_div; concrete R via norm_num, no supplied witness"),
    "HerglotzLowerEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Herglotz lower bound k/(σ-β) ≤ Re(Σ m/(z-ρ)): keep equal-height term (re_smul_inv_sub, real) + "
        "drop nonneg rest (re_inv_sub_nonneg via normSq_nonneg) over Finset.add_sum_erase; no corruptible cofactor"),
    "ArgumentPrincipleEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Argument principle ∮ Σ m/(z-ρ) = 2πi·Σ m: circleIntegral linearity (integral_fun_sum + integral_const_mul) over Mathlib per-pole residue integral_sub_inv_of_mem_ball; no separately-supplied witness"),
    "FullArgumentPrincipleEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Full argument principle ∮ (Σ m/(z-ρ) + E) = 2πi·Σ m: residue side (integral_sub_inv_of_mem_ball) + analytic side E vanishes by Cauchy (DiffContOnCl.circleIntegral_eq_zero); linearity via integral_add; no separately-supplied witness"),
    "RectArgumentPrincipleEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Rectangle Cauchy vanishing ∮_∂rect E = 0: direct over Mathlib integral_boundary_rect_eq_zero_of_differentiableOn with .re/.im reduction; no separately-supplied witness"),
    "AnnulusCountEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Annulus count ∮_R − ∮_r = 2πi·Σ_shell m: outer residue sum (integral_sub_inv_of_mem_ball) minus inner Cauchy-zero (poles outside ⟹ DiffContOnCl.circleIntegral_eq_zero); no separately-supplied witness"),
    "BoxLocalizationEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "RH-in-a-box localization counting step: a Finset exhaustion argument (Finset.sum_sdiff + sum_le_sum over T⊆s, each d≥1, ∑_s d = card T = n) forcing s = T and every Re = 1/2; the counting is structural (no corruptible identity certificate). The certificate REFUSES n_line > n_total and n_line != n_total (negative controls) — equality is the localization hypothesis"),
    "SlitLoopWindingZeroEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Winding-zero (Rouché heart) ∮ w'/w = 0 for a closed loop in ‖·-1‖<r≤1: w'/w = (log∘w)' via HasDerivAt.clog_real (slitPlane from Re>0) + FTC-2 integral_eq_sub_of_hasDerivAt collapsing to log(w b)-log(w a)=0; no separately-supplied witness"),
    "BoxResidueSumEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Box residue-sum Bd(Σ m/(z-ρ)) = 2πi·Σ m: Finset linearity (intervalIntegral.integral_finsetSum + integral_const_mul) over the four sides, conditional on the per-pole winding primitive Bd((z-ρ)⁻¹)=2πi (explicit hypothesis, the Mathlib gap); no separately-supplied witness"),
    "RectWindingEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Winding-nonzero primitive Bd((z-ρ)⁻¹)=2πi for ρ strictly inside: from-scratch segment/Complex.log branch-split — 3 sides in slitPlane via clog_real+FTC-2, left side via ρ-(·) branch, two log(-w)-log(w)=±iπ monodromy jumps (arg_neg_eq_arg_±pi) sum to 2πi; no separately-supplied witness"),
    "LogProductBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Two-scale log-product bound log‖P c‖-log‖P z‖ ≤ (Σ m)·(log R₀-log(R-R₀)): reverse-triangle separation ‖z-ρ‖≥R-R₀ (norm_sub_norm_le) + monotone Real.log_le_log + log-of-product (norm_prod/Real.log_prod/log_zpow) + Finset.sum_le_sum; geometry is the certificate, no separately-supplied witness"),
    # --- NS/Euler-derived emitters (2026-09-08) ---
    "AffineLedgerEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "threshold ≤/< affine form (or min of forms) on a parameter box via linarith (+ lt_min_iff/le_min_iff); the worst-corner margin is recomputed by linarith as the nonneg combination of the box hyps — no separately-supplied corruptible cofactor (cf. AffineParamEndpointEmitter/BoxRobustEmitter)"),
    "QuadraticIrrationalEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "ℤ[√d] conjugate-product identity + norm≥1 bound: the radicand d IS the statement (not a separate cofactor); the identity is recomputed by nlinarith off Real.sq_sqrt and the lower bound by Int.one_le_abs on the integer norm (cf. AlgebraicBracketEmitter)"),
    "GevreyMajorantEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Gevrey-2 factorial-majorant calculus: a FIXED self-contained lemma chain (Nat.choose/factorial + majorant laws + triangular-recurrence closure) with per-instance rational budget parameters that ARE the statement (side conditions re-decided by norm_num in-kernel); no separately-supplied corruptible cofactor — a violated budget is refused at certify time (negative control)"),
    "ContinuousBarrierEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "open-closed barrier bootstrap: fixed topological atom (compact least-hit + "
        "IVT from Mathlib) with per-instance rational budget (T,B,a) that IS the "
        "statement, side conditions re-decided by norm_num; violated budget B*T >= a "
        "refused at certify time (negative control); no corruptible cofactor"),
    "LogEpsOptimizeEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "log-eps cutoff witness optimization: the rational exponent theta and "
        "multiplier m=1/theta ARE the statement; the coefficient arithmetic "
        "(-m*log A)*theta = -log A is re-proved by ring in-kernel and theta out of "
        "(0,1] is refused at certify time; no separately-supplied cofactor"),
    "LogConvexInterpEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "zero-tolerant log-convexity interpolation: fixed cross/pair/between chain "
        "(induction + nlinarith on the hypothesis law) with per-instance index "
        "triples s<=a<=b re-decided by norm_num; violated ordering refused; no "
        "corruptible cofactor"),
    "FinitePrefixAbsorptionEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "eventually-bounded -> globally-bounded with the explicit Finset-sum "
        "witness C = A + sum |f n|/w n; a single fully-generic fixed atom, no "
        "per-instance data and no corruptible cofactor"),
    "GradedConvolutionEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "graded-convolution endpoint identities (congr-below / strict-congr / "
        "next-delta): fully-generic fixed exact identities over abstract modules, "
        "no per-instance data and no corruptible cofactor"),
    "PowerTowerEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "power-tower recurrence closure C q <= (9L)^(3^q): fully-generic fixed "
        "induction atoms over an abstract sequence; no corruptible cofactor"),
    "PartitionCompositionEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Faa di Bruno factorial-square partition-sum bound over Mathlib "
        "OrderedFinpartition (extendEquiv recursion): fully-generic fixed calculus, "
        "no corruptible cofactor"),
    "RegularWordEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "forbidden-factor word invariant 2*losses <= len+1 over List Bool: "
        "decidable structural recursion + omega; first discrete axis, no "
        "corruptible cofactor"),
    "LowOrderTailEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "low-order grades + doubled geometric tail hybrid: fully-generic fixed "
        "atoms (geometric sums <= 2 / <= 2q^a + the assembled bound); no "
        "corruptible cofactor"),
    "EventualThresholdEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "eventual scaling threshold with explicit nested-max-of-ratios witness: "
        "the arity IS the statement; witness assembly re-derived in-kernel by "
        "le_max chains + div_lt_iff0; no corruptible cofactor"),
    "ComparabilityEnvelopeEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "comparability/Lipschitz envelope atoms (rpow both-signs, sqrt "
        "conjugate-multiply, 1+x^2 denominator kill): fully-generic fixed atoms, "
        "no per-instance data and no corruptible cofactor"),
    "DiscreteMomentEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "discrete-sum moment atoms (simplex second moment, squareDecay telescope + "
        "antidiagonal convolution <= 8): fully-generic fixed atoms, no per-instance "
        "data and no corruptible cofactor"),
    "PolyExpAbsorptionEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "poly-exp absorption exp(-1/(2lam))/lam^m <= (4m)^m exp(-1/(4lam)): the "
        "power m and exact constant (4m)^m ARE the statement, re-decided in-kernel "
        "(add_one_le_exp + pow + norm_num); m=0 refused at certify time (negative "
        "control); no corruptible cofactor"),
    "TwoRowSolveEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "2x2 solution-entry bound from row-scale + ratio-gap hypotheses: a single "
        "fully-generic fixed atom (eq_div_iff/abs algebra + nlinarith), no per-instance "
        "data and no corruptible cofactor"),
    "RatioTelescopeEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "ratio-recurrence telescoping (factorial/geometric/index normal forms): three "
        "fully-generic fixed induction atoms over abstract sequences; no per-instance "
        "data and no corruptible cofactor"),
    "MonomialLadderEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "master-budget monomial rungs c*e*Theta^k <= b: the (Cm,Kmax,rung) rationals ARE "
        "the statement; each rung is re-derived in-kernel by pow_le_pow_right0 + "
        "mul_le_mul + linarith off the master hypothesis; violated rung budget refused "
        "at certify time (negative control); no corruptible cofactor"),
    "RpowBudgetEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "k-power product collapse with linarith at the exponent level: the exponent "
        "rationals ARE the statement; the collapse identity is re-proved by "
        "rpow_add/rpow_mul_natCast + ring and the margin by linarith; violated exponent "
        "margin refused at certify time (negative control); no corruptible cofactor"),
    "MultilinearPerturbationEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Leibniz telescoping product-perturbation envelope |prod F - prod G| <= C*eta: "
        "the arity and rational bounds ARE the statement; the envelope C = sum prod_{j!=i} M_j "
        "is recomputed in-kernel by the ring telescoping identity + mul_le_mul chains + linarith; "
        "no separately-supplied corruptible cofactor"),
    "PolyGeomClosureEmitter": _S(
        CERTIFICATE_SENSITIVE,
        "exact-invariant weighted-geometric closure: the SYNTHESIZED remainder polynomial q "
        "(solving q(N) = p(N) + rho*q(N+1)) is the load-bearing certificate -- a corrupted q "
        "breaks the induction's push_cast/ring step (and is refused at certify time by the "
        "exact sympy recurrence check)",
        neg_control=NegControlStance(
            NEG_CONTROL_DECLARED_UNWIRED,
            reason="certificate-sensitive (a forged remainder is kernel-rejectable via the "
                   "induction ring identity) but no adapter is registered in "
                   "negative_control_harness.ADAPTERS yet -- the honestly-named gap"),
    ),
    "TwoPointMomentEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "two-point moment feasibility: a FIXED explicit-witness calculus (symmetricPair / "
        "oneSidedPair, field_simp/ring/linarith) with per-instance rational (p1,p2,m,V) that "
        "ARE the statement, margin re-decided by norm_num; violated margin refused at certify "
        "time (negative control); no corruptible cofactor"),
    "CoefficientMassEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "l1-coefficient sup-envelope |p(x)| <= ||p||_1 * T^deg: the coefficient "
        "list and radius ARE the statement; the mass M and per-term |a_i| facts "
        "are re-decided in-kernel (sign-aware abs_of_nonneg/nonpos + norm_num + "
        "linarith); T < 1 / zero leading coeff refused at certify time"),
    "SqrtRootEliminationEmitter": _S(
        CERTIFICATE_SENSITIVE,
        "radical elimination v < E - u*sqrt(rad) <-> (v < E and 0 < Q): the "
        "separately-supplied eliminated form Q is the load-bearing certificate — "
        "a corrupted Q breaks the emitted `ring` identity (E-v)^2 - u^2*rad = Q "
        "(and is refused at certify time by the exact sympy identity check)",
        neg_control=NegControlStance(
            NEG_CONTROL_DECLARED_UNWIRED,
            reason="certificate-sensitive (a forged Q is kernel-rejectable via the "
                   "ring identity) but no adapter is registered in "
                   "negative_control_harness.ADAPTERS yet — the honestly-named gap"),
    ),
}


def _derive_neg_control(stance: SensitivityStance) -> NegControlStance:
    """Derive an emitter's negative-control stance from its sensitivity stance when
    it did not declare one explicitly.

    A CERTIFICATE_SENSITIVE emitter carries a corruptible identity/fact, so a
    forged FALSE instance is kernel-rejectable — it must have an ADAPTER (the
    ``neg_control_adapter_gap`` check then enforces one is actually registered).
    A STRUCTURALLY_NONVACUOUS emitter (positivity / decidable / finite / glue /
    adapter) has no independent numeric fact to falsify at the emission layer, so
    it is NOT_APPLICABLE and its own ``reason`` is the honest not-applicable reason.
    """
    if stance.neg_control is not None:
        return stance.neg_control
    if stance.stance == CERTIFICATE_SENSITIVE:
        return NegControlStance(NEG_CONTROL_ADAPTER)
    return NegControlStance(NEG_CONTROL_NOT_APPLICABLE, reason=stance.reason)


# Fill in the neg_control declaration for every entry (derive when unspecified).
REGISTRY = {
    name: SensitivityStance(
        stance=s.stance, reason=s.reason, checked_in=s.checked_in,
        neg_control=_derive_neg_control(s),
    )
    for name, s in REGISTRY.items()
}


def undeclared_neg_control_emitters() -> list[str]:
    """Registry emitters with no negative-control declaration — the completeness
    gate. (After derivation every entry is declared, so a stray None means a bug.)"""
    return sorted(n for n, s in REGISTRY.items() if s.neg_control is None)


def neg_control_adapter_gap() -> list[str]:
    """Emitters that DECLARE a neg-control adapter but have none registered in
    ``negative_control_harness.ADAPTERS`` — the registry cannot claim a control
    that does not exist (the analogue of ``wired_sensitive_emitters``' honesty)."""
    try:
        import telperion.negctrl_adapters  # noqa: F401  (import triggers register())
        from .negative_control_harness import registered_adapters
    except Exception:
        # Harness/adapters unavailable — report every declared adapter as a gap so
        # the honesty check fails loudly rather than silently passing.
        return sorted(
            n for n, s in REGISTRY.items()
            if s.neg_control and s.neg_control.kind == NEG_CONTROL_ADAPTER
        )
    live = set(registered_adapters())
    return sorted(
        n for n, s in REGISTRY.items()
        if s.neg_control and s.neg_control.kind == NEG_CONTROL_ADAPTER
        and n not in live
    )


def neg_control_unwired_emitters() -> list[str]:
    """Certificate-sensitive emitters declared ``NEG_CONTROL_DECLARED_UNWIRED`` — an
    adapter is possible but not built yet.  The honestly-named gap (analogue of a
    CERTIFICATE_SENSITIVE emitter with ``checked_in=None``); reported, not failed."""
    return sorted(
        n for n, s in REGISTRY.items()
        if s.neg_control and s.neg_control.kind == NEG_CONTROL_DECLARED_UNWIRED
    )


def discover_emitters() -> list[type]:
    """Every concrete SHIPPED Emitter subclass reachable from the base class.

    Governs only emitters defined in the ``telperion`` package — a test that
    defines or ``exec``s a throwaway ``Emitter`` subclass (e.g.
    ``test_provenance_code_fingerprint``'s ``ReplEmitter``, whose ``__module__``
    is ``builtins``) pollutes ``Emitter.__subclasses__()`` process-globally but is
    NOT a shippable emitter, so it is excluded from the completeness gate."""
    seen: dict[str, type] = {}

    def walk(cls: type) -> None:
        for sub in cls.__subclasses__():
            if sub.__module__.startswith("telperion."):
                seen[sub.__name__] = sub
            walk(sub)

    walk(Emitter)
    return list(seen.values())


def _emitter_names() -> set[str]:
    return {c.__name__ for c in discover_emitters()}


def unclassified_emitters() -> list[str]:
    """Discovered emitters with no declared stance — the completeness gate."""
    return sorted(_emitter_names() - set(REGISTRY))


def stray_registry_entries() -> list[str]:
    """Registry entries that no longer correspond to a real emitter."""
    return sorted(set(REGISTRY) - _emitter_names())


def wired_sensitive_emitters() -> set[str]:
    """CERTIFICATE_SENSITIVE emitters whose `checked_in` module truthfully invokes
    `assert_certificate_sensitive` — verified by reading the module source, so the
    registry cannot lie about what is actually wired."""
    src = Path(__file__).resolve().parent
    wired: set[str] = set()
    for name, stance in REGISTRY.items():
        if stance.stance != CERTIFICATE_SENSITIVE or not stance.checked_in:
            continue
        mod = src / f"{stance.checked_in}.py"
        if mod.is_file() and "assert_certificate_sensitive" in mod.read_text(encoding="utf-8"):
            wired.add(name)
    return wired


def sensitivity_report() -> str:
    """A human-readable stance table naming which sensitive emitters are wired."""
    wired = wired_sensitive_emitters()
    lines = ["Emitter certificate-sensitivity stances:"]
    for name in sorted(REGISTRY):
        st = REGISTRY[name]
        tag = st.stance
        if st.stance == CERTIFICATE_SENSITIVE:
            tag += " [wired]" if name in wired else " [declared, unwired]"
        lines.append(f"  {name}: {tag}")
    return "\n".join(lines)
