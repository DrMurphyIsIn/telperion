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

# The Brualdi-Goldwasser research lab lives under telperion.bg (opt-in).
