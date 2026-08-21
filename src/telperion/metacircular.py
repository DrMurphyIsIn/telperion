"""Meta-circular / trusted-floor study — the audit calculus pointed at itself.

Vector 4 of the self-application program.  The reflexive layer
(`nonvacuity`, `circularity`, …) catches meaning-level defects the kernel is
blind to.  This module asks the fixed-point question — *is the layer itself
faithful, and where is the irreducible trusted floor?* — and answers it in the
same exact, verdict-closed discipline every other probe uses.

Three findings, each honest:

1. **The structural non-vacuity check has a LOCATED gap.**  `check_nonvacuous`
   is syntactic — it refuses `t ⋈ t`.  A ring identity `lhs = rhs` with distinct
   sides (`(a+b)² = a²+2ab+b²`) is universally true — hence vacuous as a
   certificate of anything specific — yet slips past it.  We exhibit the
   witnesses rather than hide the boundary.  This is exactly the class the
   SEMANTIC layer (`assert_certificate_sensitive`) exists to cover.

2. **The structural and semantic checks are non-circular.**  A separating witness
   (a statement the structural check accepts but that is semantically vacuous)
   proves the semantic layer is not redundant with the structural one.

3. **The trusted base is small, named, and has an undecidable floor.**  Self-
   application shrinks and *locates* what must be trusted — but Löb/Gödel put a
   floor under it: whether a formal statement *means* the informal claim is
   undecidable in general.  `trusted_base()` names the residue.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

import sympy as sp

from .circularity import circularity_check
from .nonvacuity import NonVacuityError, check_nonvacuous
from .verdict import ProbeVerdict, Verdict


@dataclass(frozen=True)
class Probe:
    """A single meta-probe: an equality claim `lhs = rhs` over `symbols`."""

    name: str
    lhs: sp.Expr
    rhs: sp.Expr
    symbols: tuple[sp.Symbol, ...]

    @property
    def lean(self) -> str:
        """The claim as a Lean-shaped statement string (what the checker reads)."""
        return f"{sp.sstr(self.lhs)} = {sp.sstr(self.rhs)}"


@dataclass(frozen=True)
class MetaVerdict:
    """A verdict from a meta-probe, carrying the exhibited witnesses."""

    verdict: Verdict
    claim: str
    witnesses: tuple[str, ...] = ()
    detail: str = ""


_a, _b = sp.symbols("a b", real=True)


def tautology_probes() -> list[Probe]:
    """Ring identities `lhs = rhs` (lhs − rhs ≡ 0): universally true, hence
    vacuous as a certificate — the adversarial battery against the checker."""
    return [
        Probe("square_of_sum", (_a + _b) ** 2, _a**2 + 2 * _a * _b + _b**2, (_a, _b)),
        Probe("commute_add", _a + _b, _b + _a, (_a, _b)),
        Probe("add_zero", _a + 0, _a, (_a,)),
        Probe("diff_of_squares", (_a - _b) * (_a + _b), _a**2 - _b**2, (_a, _b)),
        Probe("distribute", _a * (_a + _b), _a**2 + _a * _b, (_a, _b)),
    ]


def substantive_probes() -> list[Probe]:
    """Non-identity equalities: genuine claims (lhs − rhs ≢ 0) — the control set
    where structural acceptance and semantic non-vacuity agree."""
    return [
        Probe("a_eq_b", _a, _b, (_a, _b)),
        Probe("a_eq_twob", _a, 2 * _b, (_a, _b)),
        Probe("prod_eq_sum", _a * _b, _a + _b, (_a, _b)),
    ]


def is_ring_identity(p: Probe) -> bool:
    """True iff the claim holds for ALL values — `lhs − rhs` expands to 0 —
    i.e. it is semantically vacuous as a certificate."""
    return sp.expand(p.lhs - p.rhs) == 0


def structural_accepts(p: Probe) -> bool:
    """True iff the STRUCTURAL non-vacuity check green-lights the probe's
    statement (does not raise) — i.e. it is not syntactically reflexive."""
    body = f"theorem probe : {p.lean} := by sorry"
    try:
        check_nonvacuous(body)
        return True
    except NonVacuityError:
        return False


def probe_structural_nonvacuity() -> MetaVerdict:
    """Search for statements the structural check accepts yet are semantically
    vacuous (ring identities).  Returns OBSTRUCTED_AND_LOCATED with the witnesses
    (the located scope boundary), or VALIDATED if the structural check happens to
    catch them all."""
    witnesses = [
        p.name for p in tautology_probes()
        if structural_accepts(p) and is_ring_identity(p)
    ]
    if witnesses:
        return MetaVerdict(
            verdict=Verdict.OBSTRUCTED_AND_LOCATED,
            claim="structural non-vacuity catches every semantic tautology",
            witnesses=tuple(witnesses),
            detail=(
                "the syntactic reflexive-check accepts these universally-true "
                "ring identities; catching them is the SEMANTIC layer's job "
                "(assert_certificate_sensitive), and beyond it lies the "
                "undecidable floor"
            ),
        )
    return MetaVerdict(
        verdict=Verdict.VALIDATED,
        claim="structural non-vacuity catches every semantic tautology",
    )


def check_metachecker_noncircular() -> ProbeVerdict:
    """Is the structural check a proper, independent layer relative to the
    semantic notion of non-vacuity — or does it already subsume it (circular)?

    lemma = 'structural check accepts the statement';
    goal  = 'the statement is genuinely (semantically) non-vacuous'.
    A separating witness (lemma holds, goal fails) — a ring identity the
    structural check accepts — proves the semantic layer is not redundant."""
    probes = tautology_probes() + substantive_probes()
    points = [{"i": i} for i in range(len(probes))]

    def lemma(pt):
        return structural_accepts(probes[pt["i"]])

    def goal(pt):
        return not is_ring_identity(probes[pt["i"]])

    return circularity_check(
        lemma, goal, points, label="structural-check vs semantic-non-vacuity"
    )


def trusted_base() -> list[str]:
    """The irreducible trusted residue after all self-application.  Named and
    located — the honest version of 'trust me'."""
    return [
        "Lean 4 kernel — the sole arbiter of proof validity; a false theorem "
        "never compiles",
        "exact-arithmetic decision primitives (require_exact / decide) — no "
        "float decides a verdict, so the meta-checks cannot be fooled by "
        "rounding",
        "the statement-intent match — whether a formal statement MEANS the "
        "informal claim is UNDECIDABLE in general (the Löb/Gödel floor): "
        "self-application shrinks and locates the trusted base but cannot "
        "eliminate this residue",
    ]
