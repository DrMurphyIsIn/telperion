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
from .quantization import QuantizationCertificate, continuous_overshoot, continuous_phi11  # noqa: F401
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
    impurity_determinant_phi11, normalized_adjacency_spectrum, resonant_impurity_site,
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
from .family import BoxAxis, GridSpec, InequalityFamily  # noqa: F401
from .lean import LeanProfile, TemplateError  # noqa: F401
from .provenance import DiffReport, EmitResult, diff_frozen, family_hash, freeze  # noqa: F401
from .workflow import ValidationReport, WorkflowError, emit  # noqa: F401
