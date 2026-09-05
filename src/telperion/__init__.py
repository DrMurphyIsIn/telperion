"""telperion: certify rational-inequality families in sympy, validate them in
exact arithmetic, and batch-emit kernel-checked Lean 4.

Trust model: the generator is UNTRUSTED by design — the Lean kernel is the sole
trusted component.  A defective certificate manifests as a compile failure,
never a false theorem.  See docs/METHODOLOGY.md.
"""

__version__ = "0.1.6"

from .certify import (  # noqa: F401
    CertificationError,
    CertifiedFamily,
    PolyaCertificate,
    certify,
    polya_certify,
)
from .emit import BilinearBoxEmitter, DirectPolyaEmitter  # noqa: F401
from .emit_facts import ExactFactEmitter, IdentityEmitter, fact_pow, int_expr_lean  # noqa: F401
from .emit_adapters import (  # noqa: F401
    CaseDispatchAssemblyEmitter,
    CustomAssemblyEmitter,
    SubdivisionGlueEmitter,
    Reparam,
    ReparamAdapterEmitter,
)
from .parsing import UnsafeExpressionError, safe_parse_expr  # noqa: F401
from .tails import TailFrom, TailNatEmitter, tail_family  # noqa: F401
from .cache import DiskCache, memoize  # noqa: F401
from .cone import ConeCombination, FarkasDual, cone_combination, cone_decide  # noqa: F401
from .unimodal import UnimodalityCertificate, unimodal_certificate  # noqa: F401
from .interval import interval_family  # noqa: F401
from .varmap import MapSpec, VarMapAdapterEmitter  # noqa: F401
from .dichotomy import DichotomyGlueEmitter  # noqa: F401
from .certify import profile_report, restrict_instances  # noqa: F401
from .padic import (  # noqa: F401
    ADELIC_NOTE,
    SPLIT_LEMMA,
    TELESCOPE_LEMMA,
    ValuationFact,
    padic_decompose,
    padic_val,
    padic_val_frac,
    valuation_facts_lean,
)
from .verdict import (  # noqa: F401
    FloatAtDecisionPoint, ProbeVerdict, Verdict, decide, null, obstructed,
    probe, re_derivation, require_exact, validated,
)
from .faithfulness import faithfulness_check, seeded_rational_points  # noqa: F401
from .circularity import circularity_check  # noqa: F401
from .upgradability import UNBOUNDED, upgradability_check, upgradability_of_family  # noqa: F401
from .limit_probe import limit_probe  # noqa: F401
from .super_solution import super_solution_check  # noqa: F401
from .discharging import discharging_check  # noqa: F401
from .witnessed_bound import witnessed_bound_check  # noqa: F401
from .bench import ScalingResult, scaling_probe, time_op  # noqa: F401
from .emit_sos import SOSEmitter, sos_family  # noqa: F401
from .emit_bracket import BracketSpec, IntervalBracketEmitter, bracket_family  # noqa: F401
from .emit_padic import PadicValuationEmitter, valuation_family  # noqa: F401
# BG-derived first-class emitters (2026-08-19).
from .emit_cone import ConeFarkasEmitter, cone_family  # noqa: F401
from .emit_tangent import TangentSumEmitter, tangent_certificate, tangent_sum_family  # noqa: F401
from .emit_cs import CauchySchwarzEmitter, cauchy_schwarz_family, cs_certificate  # noqa: F401
from .emit_psd_form import PSDFormEmitter, psd_certificate, psd_form_family  # noqa: F401
from .emit_xor3 import Xor3MomentPSDEmitter, xor3_certificate, xor3_family  # noqa: F401
from .emit_bilinear_corner import (  # noqa: F401
    BilinearCornerBoxEmitter, bilinear_corner_certificate, bilinear_corner_family,
)
from .emit_algebraic_bracket import (  # noqa: F401
    AlgebraicBracketEmitter, algebraic_bracket_certificate, algebraic_bracket_family,
)
from .emit_halfplane_disk import (  # noqa: F401
    HalfPlaneDiskEmitter, halfplane_disk_certificate, halfplane_disk_family,
)
from .emit_finite_argmax import (  # noqa: F401
    FiniteArgmaxMarginEmitter, finite_argmax_certificate, finite_argmax_family,
)
from .emit_magnitude_split import (  # noqa: F401
    MagnitudeSplitBoundEmitter, magnitude_split_certificate, magnitude_split_family,
)
from .emit_disk_coord import (  # noqa: F401
    DiskCoordBoundsEmitter, disk_coord_certificate, disk_coord_family,
)
from .emit_cauchy_deriv import (  # noqa: F401
    CauchyDerivBoundEmitter, cauchy_deriv_certificate, cauchy_deriv_family,
)
from .emit_logderiv_region import (  # noqa: F401
    LogDerivRegionCoreEmitter, logderiv_region_certificate, logderiv_region_family,
)
from .emit_pe_duality import (  # noqa: F401
    PseudoExpectationDualityEmitter, pe_duality_certificate, pe_duality_family,
)
from .emit_order_balance import (  # noqa: F401
    OrderBalanceEmitter, order_balance_certificate, order_balance_family,
)
from .emit_lfunction_product import (  # noqa: F401
    LFunctionProductEmitter, lfunction_product_certificate, lfunction_product_family,
)
from .emit_parametric_holomorphy import (  # noqa: F401
    ParametricHolomorphyEmitter, parametric_holomorphy_certificate, parametric_holomorphy_family,
)
from .emit_symmetric_quad import (  # noqa: F401
    SymmetricQuadFormEmitter, symmetric_quad_certificate, symmetric_quad_family,
)
from .emit_polytope_max import (  # noqa: F401
    PolytopeMaxMonotoneEmitter, polytope_max_certificate, polytope_max_family,
)
from .emit_second_order import (  # noqa: F401
    SecondOrderRecurrenceEmitter, second_order_certificate, second_order_family,
)
from .emit_integrality_gate import (  # noqa: F401
    IntegralityGateEmitter, integrality_gate_certificate, integrality_gate_family,
)
from .emit_domination_ratio import (  # noqa: F401
    RecursiveDominationRatioEmitter, domination_ratio_certificate, domination_ratio_family,
)
from .emit_achievability import (  # noqa: F401
    AchievabilityClosureEmitter, achievability_certificate, achievability_family,
)
from .emit_separable_convex import (  # noqa: F401
    SeparableConvexExtremumEmitter, separable_convex_certificate, separable_convex_family,
)
from .emit_scale_invariance import (  # noqa: F401
    ScaleInvarianceEmitter, scale_invariance_certificate, scale_invariance_family,
)
from .emit_concave_stationary_max import (  # noqa: F401
    ConcaveStationaryMaxEmitter, concave_stationary_max_certificate, concave_stationary_max_family,
)
from .emit_symmetric_quad_d2 import (  # noqa: F401
    SymmetricQuadD2Emitter, symmetric_quad_d2_certificate, symmetric_quad_d2_family,
)
from .emit_tight_cap_enclosure import (  # noqa: F401
    TightCapEnclosureEmitter, tight_cap_enclosure_certificate,
    tight_cap_enclosure_family, certify_tight_cap_enclosure_point,
)
from .emit_affine_param_endpoint import (  # noqa: F401
    AffineParamEndpointEmitter, affine_param_endpoint_certificate,
    affine_param_endpoint_family, certify_affine_param_endpoint_point,
)
from .emit_recursion_closure import (  # noqa: F401
    RecursionClosureEmitter, recursion_closure_certificate,
    recursion_closure_family, certify_recursion_closure_point,
)
from .emit_cavity_exchange import (  # noqa: F401
    CavityExchangeEmitter, cavity_exchange_certificate,
    cavity_exchange_family, certify_cavity_exchange_point,
)
from .emit_per_size_dominance_sweep import (  # noqa: F401
    PerSizeDominanceSweepEmitter, per_size_dominance_sweep_certificate,
    per_size_dominance_sweep_family, certify_per_size_dominance_sweep_point,
)
from .emit_curvature_boundary import (  # noqa: F401
    CurvatureBoundaryEmitter, curvature_boundary_certificate,
    curvature_boundary_family, certify_curvature_boundary_point,
)
from .emit_transcendental_enclosure import (  # noqa: F401
    TranscendentalEnclosureEmitter, transcendental_enclosure_certificate,
    transcendental_enclosure_family, certify_transcendental_enclosure_point,
)
from .emit_log_combination import (  # noqa: F401
    LogCombinationEmitter, log_combination_certificate,
    log_combination_family, certify_log_combination_point,
)
# dVP zero-free-region frontier atoms (2026-09-05).
from .emit_bc_split import (  # noqa: F401
    BCSplitEmitter, bc_split_certificate, bc_split_family, certify_bc_split_point,
)
from .emit_jensen_zero_count import (  # noqa: F401
    JensenZeroCountEmitter, jensen_zero_count_certificate,
    jensen_zero_count_family, certify_jensen_zero_count_point,
)
from .emit_sphere_bound import (  # noqa: F401
    SphereBoundEmitter, sphere_bound_certificate,
    sphere_bound_family, certify_sphere_bound_point,
)
from .emit_max_modulus import (  # noqa: F401
    MaxModulusEmitter, max_modulus_certificate,
    max_modulus_family, certify_max_modulus_point,
)
from .emit_bc_deriv_re import (  # noqa: F401
    BCDerivReEmitter, bc_deriv_re_certificate,
    bc_deriv_re_family, certify_bc_deriv_re_point,
)
from .emit_entire_part_bound import (  # noqa: F401
    EntirePartBoundEmitter, entire_part_bound_certificate,
    entire_part_bound_family, certify_entire_part_bound_point,
)
from .emit_unimodal import (  # noqa: F401
    UNIMODAL_PRELUDE, UnimodalMaxEmitter, unimodal_max_family,
)
from .emit_telescope import (  # noqa: F401
    TELESCOPE_PRELUDE, TelescopingPotentialEmitter, telescope_family,
)
from .emit_lattice_box import LatticeBoxEmitter, lattice_box_family  # noqa: F401
from .emit_logconcave import LogConcaveSinglePointEmitter, logconcave_family  # noqa: F401
from .emit_monotone_tail import MonotoneRatioTailEmitter, monotone_tail_family  # noqa: F401
from .emit_interlacing import InterlacingEmitter, interlacing_family  # noqa: F401
# Tier-2 literature-derived first-class emitters (2026-08-19).
from .emit_constrained_sos import ConstrainedSOSEmitter, putinar_family  # noqa: F401
from .sos_sdp import find_putinar_certificate  # noqa: F401
from .emit_wz import WZ_PRELUDE, WZEmitter, wz_family  # noqa: F401
# Tier-3 literature-derived first-class emitters (2026-08-20).
from .emit_handelman import (  # noqa: F401
    HandelmanEmitter, find_handelman_certificate, handelman_family,
)
from .emit_nullstellensatz import (  # noqa: F401
    NullstellensatzEmitter, nullstellensatz_family,
)
# Tier-4 refutation emitter (2026-08-20).
from .emit_infeasible import (  # noqa: F401
    InfeasibilityEmitter, find_refutation, infeasible_family,
)
# Tier-5 beyond-positivity emitters (2026-08-20).
from .emit_consequence import ConsequenceEmitter, consequence_family  # noqa: F401
from .emit_rational_identity import RationalIdentityEmitter, rational_identity_family  # noqa: F401
from .emit_finite_decide import (FiniteDecideEmitter, finite_decide_family,  # noqa: F401
    ForallIn, Imp, Cmp, Var, Lit, Xor, Pop, Lookup, Mul, NatTable, PairTable)
from .emit_fwd_telescope import FwdTelescopeEmitter, fwd_telescope_family  # noqa: F401
from .emit_sos_refutation import (  # noqa: F401
    SOSRefutationEmitter, sos_refutation_family,
)
from .emit_real_nullstellensatz import (  # noqa: F401
    RealNullstellensatzEmitter, find_real_nullstellensatz_certificate,
    real_nullstellensatz_family,
)
# Tier-6 integer-arithmetic emitter (2026-08-20): VIPR-style Chvatal-Gomory.
from .emit_cg_round import (  # noqa: F401
    CGRoundEmitter, certify_cg_round_point, cg_round_family,
)
# SOS-refutation + real-Nullstellensatz SDP finders (Putinar finder lives in
# sos_sdp; 2026-08-20).
from .sdp_finder import find_real_nullstellensatz, find_sos_refutation  # noqa: F401
# Tier-7 runway emitters (2026-08-20).
from .emit_bernstein import (  # noqa: F401
    BernsteinEmitter, bernstein_family, find_bernstein_certificate,
)
from .emit_rational_sos import (  # noqa: F401
    RationalSOSEmitter, find_rational_sos, rational_sos_family,
)
# Facial-positivity emitter (2026-08-20): Castle-Powers-Reznick Polya-with-zeros
# — the tie-safe homogeneous lift (zeros allowed on faces; cf. lift.py's
# strict-only inhomogeneous lift).
from .emit_polya_zeros import (  # noqa: F401
    PolyaZerosEmitter, find_polya_zeros_certificate, polya_zeros_family,
    polya_zeros_obstruction,
)
from .emit_sturm_positive import (  # noqa: F401
    SturmPositiveEmitter, sturm_positive_family,
)
# Non-vacuity gate — Telperion pointed at its own emitted output (2026-08-19).
from .nonvacuity import (  # noqa: F401
    NonVacuityError, assert_certificate_sensitive, check_nonvacuous,
)
from .family import BoxAxis, GridSpec, InequalityFamily  # noqa: F401
from .lean import LeanProfile, TemplateError  # noqa: F401
from .provenance import DiffReport, EmitResult, diff_frozen, family_hash, freeze  # noqa: F401
from .comparator import (  # noqa: F401
    CLEAN_AXIOMS, challenge_config, challenge_for_result, emitted_theorem_names,
    emitted_theorem_names_by_file, render_challenge_scaffold,
    render_sharded_challenge_scaffolds, sharded_challenge_configs,
    solution_module_of, write_challenge_config,
)
from .workflow import ValidationReport, WorkflowError, emit  # noqa: F401
from .prove import ProofResult, prove_goal  # noqa: F401
from .backend_lift import (  # noqa: F401
    LiftOutcome, LiftProblem, LiftReport, lift_report, run_backend,
)
from .benchmark import (  # noqa: F401
    BenchmarkEntry, BenchmarkReport, EntryResult,
    certifiable_seed_corpus, run_benchmark,
)
from .audit import (  # noqa: F401
    AuditFinding, AuditReport, audit_lean_file, audit_lean_text,
)
from .formalize import (  # noqa: F401
    FormalizeResult, Proposer, formalize, ollama_proposer,
)
from .tactic import discharge, discharge_json  # noqa: F401
from .hinge import (  # noqa: F401
    HingeFloorCertificate, hinge_floor_certificate, hinge_floor_module,
    hinge_floor_theorem, verify_hinge_floor,
)
from .sonc import (  # noqa: F401
    SONCCertificate, find_circuit_certificate, verify_circuit_certificate,
)
from .psd import (  # noqa: F401
    PSDCertificate, find_psd_certificate, verify_psd_certificate,
)
from .pratt import (  # noqa: F401
    PrattCertificate, find_pratt_certificate, verify_pratt_certificate,
)
from .emit_primality import primality_module, primality_theorem  # noqa: F401
from .lean_lint import (  # noqa: F401
    LeanLintError,
    LeanLintIssue,
    check_lean_text,
    lint_lean_file,
    lint_lean_text,
)
# VDB-weighted matching generating polynomial (2026-08-30): the coefficient vector Z_k for the
# combinatorial extremality program (weight 1/(d_u d_v)); extends matching_free_energy.rho.
from .weighted_matching import (  # noqa: F401
    CoefficientwiseDomination, matching_generating_poly, weighted_Z,
)
# Caterpillar transfer recurrence (Pant) + Perron free energy, and majorization/Schur-convexity
# (2026-08-30): combinatorial-program skills S0b, S1a.
from .transfer_caterpillar import (  # noqa: F401
    SpiderBeatsCaterpillarCertificate, TransferCaterpillarCertificate, Z_recurrence,
    arm_balance_delta_g, caterpillar_edges, free_energy, perron_eigenvalue, two_hub_Z,
    uniform_transfer_matrix,
)
from .majorization import (  # noqa: F401
    SchurConvexityCertificate, SchurVerdict, TTransform,
    is_schur_concave, is_schur_convex, majorization_chain, majorizes, recompose,
)
# VDB-weighted leaf-exchange / arm-balancing operator + ΔZ sign certificate (2026-08-30): skill S1b,
# the local move whose exact ΔZ drives the (corrected) reduction step.
from .vdb_exchange import (  # noqa: F401
    LeafExchangeCertificate, apply_move, delta_Z, delta_Zk, local_delta_from_pairs,
)
# Star-of-cherry-brooms S(k,c) (2026-08-31): the family that beats Pant's caterpillars for the Laplacian ratio;
# exact closed form + the c=5 branch-rate optimum (cross-exponentiated rational certificate).
from .spider_broom import (  # noqa: F401
    BroomOptimumCertificate, SmoothNoGoCertificate, broom_argmax_c, broom_free_energy, broom_ratio,
    broom_rate, broom_total, c5_unimodal_witness, rate_dominates, spider_Z, spider_edges,
)
# Branch potential ell(B) = log total(B) - |B| F* (2026-08-31): the additive form of the BG upper bound;
# the branch-ceiling reduces to broom-dominance per size + the proven broom c=5 optimum.
from .branch_potential import (  # noqa: F401
    F_STAR, branch_ell, branch_ell_by_vertex, branch_total, broom_dominance_holds,
    broom_edges, broom_optimum_prime,
)
# Tie-regime campaign (2026-08-31): uniform-hub potential + the arithmetic cherry-worst reduction.
from .tie_regime import (  # noqa: F401
    CHERRY, ExtremalityPriceMapCertificate, HighDegreeTailCertificate, MdGeometricTailCertificate,
    MdStepCertificate, MixedHubKKTCertificate, FreeClosureCertificate, MonotoneTailCertificate,
    NearBroomUnimodalityCertificate, TieCherryWorstCertificate, TieSlackCertificate, binding_j, broom_child,
    cherry_is_kkt_argmax, cherry_vs_broom_ratio, child_value, child_x, envelope_tail_case,
    mixed_lambda, slack_g, slack_hub_bound, slack_linobj, small_degree_threshold, uniform_hub_ell,
    y_floor,
)
# AXLE-inspired infrastructure (2026-09-03): structured Lean verification against a
# persistent pre-built environment, and a gap-driven emitter loop (sorry -> extract
# goal -> route-match -> fill).  See docs/VERIFY_AND_GAPFILL.md.
from .verify import VerifyResult, verify_lean  # noqa: F401
from .repair import repair_lean, verify_with_repair  # noqa: F401
from .gap_fill import (  # noqa: F401
    Gap, EnclosureSpec, FillResult, extract_gaps, extract_sorry_goals,
    match_log_enclosure, pick_route, fill_gap, register_matcher,
)
from .bundle import parse_theorems, merge_bundle, bundle_stats, topo_sort_blocks  # noqa: F401
from .cert_deps import extract_deps, DepGraph, minimal_snippet  # noqa: F401
from .normalize import normalize_lean, canonical_statement, theorem2sorry  # noqa: F401
from .cert_meta import (  # noqa: F401
    CertIndex, CertMeta, extract_cert_meta, measure_heartbeats, type_hash,
)
from .statement_match import (  # noqa: F401
    StatementMatchResult, statement_match_check, def_identity_check,
)
# AXLE third-tour #5/#6 (parallel-integration): the first-class environment registry
# and the mechanical verify-guarded proof simplifier.  Additive new modules.
from .environment import (  # noqa: F401
    Environment, UnknownEnvironmentError, discover_environments, get_environment,
    list_environments, clear_environments, register_environment, resolve,
    mathlib_built, default_examples_root,
)
from .simplify import (  # noqa: F401
    HaveStep, SimplifyResult, SimplifyStep, simplify_proof, remove_unused_haves,
    find_have_steps, unused_have_steps,
)
from .negative_control import (  # noqa: F401
    NegativeControlResult, assert_kernel_rejects, log_combination_negative_control,
)
from .signature_gate import (  # noqa: F401
    SignatureMatch, SignatureResult, build_sig_guards, check_signatures,
    forall_type, sig_guard_name,
)
# Generic kernel-gated negative control (AXLE `disprove`, generalized to every
# emitter): the engine + the per-emitter adapter registry.  Importing the adapters
# package runs each adapter's register(...) so ADAPTERS is populated on `import
# telperion` (the emitter-sensitivity gate relies on this).  See docs.
from .negative_control_harness import (  # noqa: F401
    NegativeControlAdapter, GenericNegativeControlResult, generic_negative_control,
    assert_kernel_accepts, build_single_instance_family, emit_via_single_instance_family,
    register, registered_adapters, ADAPTERS,
)
from . import negctrl_adapters  # noqa: F401  (registers all first-party adapters)

# The Brualdi-Goldwasser research lab lives under telperion.bg (opt-in).  The bg-named modules
# `bg_bulk_discharge` and `bg_upper_bound` (composed reduction skeleton) are opt-in too -- import them
# directly (`from telperion.bg_upper_bound import UpperBoundReduction`), not via `import telperion`, so the
# core/bg boundary (test_core_boundary) stays clean.
