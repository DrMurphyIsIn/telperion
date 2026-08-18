"""telperion: certify rational-inequality families in sympy, validate them in
exact arithmetic, and batch-emit kernel-checked Lean 4.

Trust model: the generator is UNTRUSTED by design — the Lean kernel is the sole
trusted component.  A defective certificate manifests as a compile failure,
never a false theorem.  See docs/METHODOLOGY.md.
"""

__version__ = "0.1.3"

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
from .potential import fixed_points, per_node_family  # noqa: F401
from .uniform_tail import ArmDominanceCertificate, UniformArmDominanceCertificate, arm_dominance_uniform, uniform_arm_dominance  # noqa: F401
from .lattice_box import LatticeBoxCertificate  # noqa: F401
from .gauge_lift import (  # noqa: F401
    ARM, ARM2, CHERRY, LEAF, TIE,
    ChildType, GaugeLiftCertificate, per_step_multiplier_limit,
)
from .permanent_tie import (  # noqa: F401
    QuantizedPermanentTieCertificate, near_star_permanent, near_star_prod_deg,
)
from .quantization import QuantizationCertificate, continuous_overshoot, continuous_phi11  # noqa: F401
from .fermion_dof import (  # noqa: F401
    FermionDOFCertificate, degrees, fermion_dof_count, laplacian_ratio_as_fermion_sum,
    matchings, pauli_decompose, pauli_exclusion_holds, perfect_matching_count,
)
from .immanant import (  # noqa: F401
    determinant, immanant, normalized_immanant, parastatistics_spectrum,
    permanent, permanental_dominance_holds,
)
from .amplitude import (  # noqa: F401
    amplitude_gap, amplitude_product11, bg_amplitude_holds,
    cavity_potential_residual, vertex_amplitudes,
)
from .benchmark_factor import (  # noqa: F401
    BenchmarkFactorCertificate, benchmark, phi11, rho,
)
from .telescope_product import TelescopeCertificate, q as telescope_q  # noqa: F401
from .perm_dominance import (  # noqa: F401
    PermanentalDominanceCertificate, char_involution, dim as irrep_dim,
)
from .scope import (  # noqa: F401
    TermwiseScopeCertificate, is_forest, shortest_cycle,
)
from .matching_free_energy import (  # noqa: F401
    CompetitorExtremalityCertificate, near_star_edges, rho as matching_rho,
)
from .tree_search import TreeLandscapeSearch  # noqa: F401
from .density_decay import (  # noqa: F401
    classify_decay_regime, default_family_zoo, laplace_surface_tension, density_decay_fit, is_linear_in_inverse_s,
    near_star_family, path_family, power_law_fit, spider_family,
    scout_disorder, stretched_exponential_fit,
)
from .counterexample_hunt import (  # noqa: F401
    CounterexampleHunt, near_star_seeds, probe_monotonicity, scaled_hunt,
)
from .rectification import (  # noqa: F401
    RectificationCertificate, canonical_form, is_canonical,
    rectify_moves, spider_edges, spider_phi11,
)
from .fractal_eigenvalue import (  # noqa: F401
    FractalEigenvalueCertificate, arm_transfer_eigenvalue_closed_form,
    arm_transfer_factor, density_at, near_star_edges,
)
from .girardeau import (  # noqa: F401
    GirardeauDualityCertificate, free_fermion_product,
    functional_determinant, hard_core_boson_partition,
)
from .bosonic import (  # noqa: F401
    BoseEinsteinStatisticsCertificate, BosonicReadingCertificate, BosonicToolkitCertificate,
    arm_condensate, bose_einstein_occupation, bosonic_permanent, coherent_state_occupation,
    condensate_density, fermion_vacuum_det, gross_pitaevskii_bethe, hafnian,
    per_from_hafnian, van_der_waerden_bound,
)
from .branching_unimodality import (  # noqa: F401
    BranchingUnimodalityCertificate, boost as gstep_boost,
)
from .multihub_submultiplicative import (  # noqa: F401
    MultiHubSubmultiplicativeCertificate, cut_components,
)
from .r2_submultiplicative import (  # noqa: F401
    R2SubmultiplicativeCertificate, a_bigroot, a_hub as dn_a_hub, double_near_star,
)
from .gibbs_free_energy import (  # noqa: F401
    GibbsFreeEnergyCertificate, matching_counts, monomer_dimer_free_energy,
    matching_measure, monomer_dimer_Z, unimodular_free_energy_limit,
)
from .collective_cancellation import (  # noqa: F401
    CollectiveCancellationNote, arm_factor, hub_factor,
    near_star_balance, per_vertex_factor,
)
from .sporadic_tie import (  # noqa: F401
    IntegralityStrictnessCertificate, SporadicTieConstraintCertificate,
    amp_product, deficit_lower_bound, tie_forces_divisibility,
)
from .near_star_tail import (  # noqa: F401
    NearStarTailCertificate, a_hub, phi11, ratio,
)
from .transfer_tail import (  # noqa: F401
    TransferTailBound, default_families, density_limit, phi_density,
)
from .parallel_map import (  # noqa: F401
    IslandModel, max_rho_for_n, parallel_sweep,
)
from .rooted_phi import (  # noqa: F401
    BGExtremalityCertificate, all_roots_phi11, bg_phi11, bg_phi11_argmax_root,
    bg_phi11_fast, phi11_rooted,
)
from .levinson import LevinsonAnalysis, tree_levinson  # noqa: F401
from .spectral import (  # noqa: F401
    free_fermion_modes, friedel_phase_shift, friedel_response, host_green_diagonal,
    impurity_determinant_phi11, normalized_adjacency_spectrum, orbital_free_energy_density, resonant_impurity_site,
    spectral_rho,
)
from .bridge import NearStarBridgeCertificate, near_star_R, near_star_tail_poly  # noqa: F401
from .zerofree import ZeroFreeDiskCertificate, dominant_term_margin  # noqa: F401
from .entropy import (  # noqa: F401
    BregmanCertificate, bregman_bound, permanent01, shearer_holds,
)
from .ehrhart import is_quasi_polynomial, minimal_period  # noqa: F401
from .graphlimit import (  # noqa: F401
    free_energy_density, matching_polynomial, near_star_limit_density,
)
from .mconvex import (  # noqa: F401
    MConvexityCertificate,
    is_m_concave,
    is_m_convex,
    separable_concave_on_base,
)
from .bellman import (  # noqa: F401
    concave_hull,
    cramer_rate,
    fenchel_transform,
    sub_hull_gap,
    value_function,
)
from .rigidity import (  # noqa: F401
    ArithmeticRigidityCertificate,
    near_star_R,
)
from .lorentzian import (  # noqa: F401
    HodgeRiemannCertificate,
    is_lorentzian_form,
    real_sign,
    signature,
)
from .heights import (  # noqa: F401
    displacement_convex,
    global_height_nonneg,
    local_heights,
    product_formula_residual,
    wasserstein1,
)
from .interlacing import (  # noqa: F401
    InterlacingCertificate,
    interlaces,
    is_real_rooted,
    sos_decompose,
    wronskian,
)
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
from .emit_sos import SOSEmitter, sos_family  # noqa: F401
from .emit_bracket import BracketSpec, IntervalBracketEmitter, bracket_family  # noqa: F401
from .emit_padic import PadicValuationEmitter, valuation_family  # noqa: F401
from .family import BoxAxis, GridSpec, InequalityFamily  # noqa: F401
from .lean import LeanProfile, TemplateError  # noqa: F401
from .provenance import DiffReport, EmitResult, diff_frozen, family_hash, freeze  # noqa: F401
from .workflow import ValidationReport, WorkflowError, emit  # noqa: F401
from .mahler import (  # noqa: F401
    LEHMER_CONSTANT,
    MahlerLehmerProbe,
    dpa_charpoly,
    is_cyclotomic_product,
    mahler_measure,
    matching_poly,
    matching_poly_from_counts,
)
from .ehrhart_bg import (  # noqa: F401
    EhrhartBGProbe,
    matching_polytope_ehrhart,
    matching_polytope_ehrhart_bruteforce,
)
from .resonance_carrier import (  # noqa: F401
    ResonanceCarrierCertificate,
    adelic_product,
    phi11_23adic_size,
    phi11_23adic_valuation,
)
from .frustration_free import (  # noqa: F401
    FrustrationFreeGapProbe,
    monomer_dimer_partition,
    tie_recursive_edges,
    transfer_density,
)
from .family_martingale import (  # noqa: F401
    TieRecursiveMartingaleCertificate,
    family_ceiling,
    per_block_factor,
    phi11_hub,
    root_amplitude,
)
from .mixed_block_martingale import (  # noqa: F401
    MixedBlockMartingaleCertificate,
    block_amplitude_and_message,
    block_factor,
    build_hub_tree,
    classify_block,
    homogeneous_family_phi11,
    homogeneous_family_sup,
    hub_phi11,
)
from .recursive_transfer import (  # noqa: F401
    RecursiveTransferCertificate,
    is_safe_vertex,
    transfer_factor,
    vertex_amplitudes,
)
from .envelope import (  # noqa: F401
    EnvelopeCertificate,
    empirical_envelope,
)
from .sibling_coupling import (  # noqa: F401
    RHO_B_11,
    SiblingCouplingCertificate,
    amplitude_product,
    parent_amplitude,
)
from .gaussian_invariant import (  # noqa: F401
    GaussianInvariantCertificate,
    continuum_minimum,
    near_star_energy,
)
from .matching_lorentzian import (  # noqa: F401
    MatchingLorentzianProbe,
    bivariate_matching_is_lorentzian,
    matching_support_vectors,
    matchings,
    support_is_m_convex,
)
from .susy_index import (  # noqa: F401
    SusyIndexProbe,
    adjacency_nullity,
    signed_matching_index,
    signed_perfect_matchings,
)
from .determinantal_kernel import (  # noqa: F401
    DeterminantalKernelProbe,
    girardeau_determinant,
    near_star_determinant_closed_form,
    normalized_spectrum_multiplicities,
)
from .dirac_index import (  # noqa: F401
    DiracIndexProbe,
    bipartition,
    dirac_chiral_index,
)
from .gate_strictness import (  # noqa: F401
    GateStrictnessCertificate,
    deficit_23_valuation,
    deficit_integer,
    rho_b_power_is_rational,
    strictness_bound,
)
from .irrationality_ceiling import (  # noqa: F401
    IrrationalityCeilingCertificate,
    le_half_holds,
    liouville_lower_bound,
    rho_b_power_11,
)
from .block_family_positivity import (  # noqa: F401
    SafeHubFamilyCertificate,
    block_is_safe_hub,
    family_phi,
    is_safe_message,
    safe_hub_ceiling,
)
from .interior_max import (  # noqa: F401
    InteriorMaxCertificate,
    is_large_message,
    log_concave_in_k,
    single_copy_value,
)
from .residual_foc import (  # noqa: F401
    ResidualFOCCertificate,
    family_argmax,
    family_phi_closed,
    foc_threshold,
    foc_upper_bound,
)
from .arm_maximal import (  # noqa: F401
    ArmMaximalCertificate,
    master_upper_bound,
    satisfies_master,
)
from .arm_monotone import (  # noqa: F401
    ArmMonotoneCertificate,
    chain_link_factor,
    path_F,
    rooted_path,
)
from .multi_hub_extremality import (  # noqa: F401
    MultiHubExtremalityCertificate,
    is_near_star,
    phi_maximizer,
)
from .double_near_star import (  # noqa: F401
    DoubleNearStarCertificate,
    double_near_star_edges,
    dns_phi11,
    multi_hub_peak,
)
from .arm_lean_certificates import (  # noqa: F401
    ArmLeanCertificate,
    B as arm_B,
    TAIL_P_COEFFS,
    final_rational_certificate,
    per_step_holds,
    tail_identity_holds,
)
from .gstep_reduction import (  # noqa: F401
    GStepReductionCertificate,
    MU_STAR,
    boost_le_four_thirds_when_small,
    descent_engine_holds,
    f_sym,
    g_bound,
    leaf_W_four_thirds_lt_gamma,
    leaf_mu_star_lt_third,
)
