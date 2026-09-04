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
    "CauchyDerivBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Both emitted shapes are structural: main wrapper is Mathlib's norm_deriv lemma specialized (R>0 via norm_num on a literal)"),
    "CavityExchangeEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Both emit paths discharge structurally: corner mode is `positivity` on an all-nonneg-coeff polynomial (reflexive nonneg form)"),
    "ConcaveStationaryMaxEmitter": _S(CERTIFICATE_SENSITIVE,
        "Ships a `_foc` theorem `g'(f*)=0` = an exact rational equation whose one side is the separately-supplied stationary point `fstar`",
        neg_control=NegControlStance(NEG_CONTROL_DECLARED_UNWIRED,
            "certificate-sensitive; negative-control adapter not yet built")),
    "CurvatureBoundaryEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Convexity/positivity shape: nlinarith consumes the structural fact (x-a)(b-x)>=0 built from interval bounds, not a supplied cofactor"),
    "DiskCoordBoundsEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "\"Farkas-style\" is naming only: the cert (wr,wi,rho) is substituted into BOTH hypothesis and conclusion, so it parameterizes the statement, not a corruptible witness"),
    "FiniteArgmaxMarginEmitter": _S(CERTIFICATE_SENSITIVE,
        "Emits supplied concrete integer facts p_i*q_w < p_w*q_i (and p_w<q_w) closed by norm_num; the winner/competitor rationals are a separately-supplied payload (spec callback) whose",
        neg_control=NegControlStance(NEG_CONTROL_DECLARED_UNWIRED,
            "certificate-sensitive; negative-control adapter not yet built")),
    "HalfPlaneDiskEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Payload carries only positive-rational B + 2 bools; the core 4B(B-Re w)>=0 is a product-of-nonnegatives closed by nlinarith from B>0 and Re w<=B"),
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
        "Emitter bakes a supplied rational-weight/integer-order tuple (a_j, k_j) into hpos/hb_j/hk_j hypotheses",
        neg_control=NegControlStance(NEG_CONTROL_DECLARED_UNWIRED,
            "certificate-sensitive; negative-control adapter not yet built")),
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
        "Consumes cert.corners D-values as literal rationals baked into the emitted `hid ... := by ring` convex-combination identity and `hq_j := mul_nonneg hw_j (by norm_num)` nonneg witnesses",
        neg_control=NegControlStance(NEG_CONTROL_DECLARED_UNWIRED,
            "certificate-sensitive; negative-control adapter not yet built")),
    "ScaleInvarianceEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "field_simp; ring closes f(lambda*args)=f(args) where both sides are the STATEMENT's own sympy-substituted shapes"),
    "SecondOrderRecurrenceEmitter": _S(CERTIFICATE_SENSITIVE,
        "Consumes a supplied three-term recurrence-satisfaction identity: A·g(q+2)+B·g(q+1)+C·g(q)=0 closed by `ring`, then fed to `linear_combination`",
        neg_control=NegControlStance(NEG_CONTROL_DECLARED_UNWIRED,
            "certificate-sensitive; negative-control adapter not yet built")),
    "SeparableConvexExtremumEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Convex-φ extremum on fixed-sum box: MIN=tangent surplus φ−L is an exact rational SOS (ring+positivity, linarith), MAX=push-to-bound exchanges via nlinarith over structural"),
    "SymmetricQuadD2Emitter": _S(CERTIFICATE_SENSITIVE,
        "Load-bearing `hid` step is a completing-the-square rational identity (field_simp;ring) over separately-supplied exact rational functions t2_expr/n2_expr/pcoef/a/f0..f4 from the payload",
        neg_control=NegControlStance(NEG_CONTROL_DECLARED_UNWIRED,
            "certificate-sensitive; negative-control adapter not yet built")),
    "SymmetricQuadFormEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "0 ≤ symbolic-in-N level-1 moment form via derived-and-exactly-rechecked completing-square congruence Φ=f0(A+(f1/f0)X)²+cCS(NQ−X²): positivity by structure + supplied CS hypothesis"),
    "TightCapEnclosureEmitter": _S(STRUCTURALLY_NONVACUOUS,
        "Both modes discharge structurally on exact ℚ: concrete = norm_num over unfolded W/Bcap/baseOf/prodBcap defs on a literal config (goal is a concrete rational)"),
    "TranscendentalEnclosureEmitter": _S(CERTIFICATE_SENSITIVE,
        "Consumes payload cert's supplied rational L (and U): _lower_box closes L≤log(1+x0) via Real.le_log_iff_exp_le reduced to concrete exp(L)≤1+x0 discharged by exp_bound' Taylor +",
        neg_control=NegControlStance(NEG_CONTROL_DECLARED_UNWIRED,
            "certificate-sensitive; negative-control adapter not yet built")),
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
