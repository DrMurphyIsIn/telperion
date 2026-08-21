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


@dataclass(frozen=True)
class SensitivityStance:
    """One emitter's declared certificate-sensitivity stance.

    ``checked_in`` is the module basename (e.g. ``emit_wz``) that invokes
    ``assert_certificate_sensitive`` for this emitter, or None when the semantic
    check is not (yet) wired through the generic primitive.
    """

    stance: str
    reason: str
    checked_in: str | None = None


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
                            "convex-quadratic tangent-line bound B ≤ Σf(xᵢ); the "
                            "surplus is an exact sum of squares (nlinarith over "
                            "sq_nonneg + the sum constraint), no corruptible "
                            "identity certificate"),
}


def discover_emitters() -> list[type]:
    """Every concrete Emitter subclass reachable from the base class."""
    seen: dict[str, type] = {}

    def walk(cls: type) -> None:
        for sub in cls.__subclasses__():
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
