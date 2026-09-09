"""Li positivity-ladder emitter — the RH-roadmap Track-2 showcase.

Li's criterion (Xian-Jin Li 1997), formalized upstream in
`nicholasbulka/li-criterion-rh-equivalence-lean` as

    LiCriterion.li_criterion_rh_iff :
      RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)

i.e. RH ⟺ every Li–Keiper coefficient of the Riemann ξ has nonnegative real
part.  This emitter certifies a FINITE PREFIX of that ladder: for a chosen `n`,
`0 ≤ (taylorCoeff riemannXi n).re` — the n-th rung — from a rigorous positive
rational lower bound on the coefficient.

HONESTY SEAM (identical discipline to RH-in-a-box / the effective dVP region): the
lower bound `lo ≤ (taylorCoeff riemannXi n).re` is an EXTERNAL numeric input (Arb /
mpmath interval arithmetic on ξ's Taylor coefficient at 0), carried as the theorem
HYPOTHESIS `hlo`.  The kernel proves only the trivial `0 ≤ lo ⟹ 0 ≤ coeff` step;
it does NOT evaluate the transcendental coefficient.  Certifying the n-th rung is
NOT progress toward RH: the uniform `∀ n` is exactly `li_criterion_rh_iff`'s RHS,
which IS RH.  `conjecture1_proved = False`.

Emitted per rung (`import`s the upstream `LiCriterion` library for `riemannXi` /
`taylorCoeff` — CI-wired via the lakefile `require`, see LI_POSITIVITY_LADDER.md):

    theorem <name> (hlo : (lo : ℝ) ≤ (taylorCoeff riemannXi n).re) :
        0 ≤ (taylorCoeff riemannXi n).re :=
      le_trans (by norm_num : (0:ℝ) ≤ lo) hlo

The claim is load-bearing (about the ACTUAL ξ coefficient, not an abstract real);
`hlo` is the documented trust boundary.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class LiRungCert:
    """The n-th Li ladder rung: a positive rational lower bound `lo` on
    `(taylorCoeff riemannXi n).re`."""

    n: int
    lo: sp.Rational


def li_rung_certificate(n, lo) -> LiRungCert:
    """Build (and exactly re-check) an n-th-rung certificate.  Refuses `n < 0`
    and a non-positive lower bound (a `lo ≤ 0` cannot witness positivity — that is
    an honest refusal, not a false theorem)."""
    n = int(n)
    lo = sp.Rational(sp.nsimplify(lo))
    if n < 0:
        raise ValueError(f"li_positivity REFUSED: need n ≥ 0 (got {n})")
    if lo <= 0:
        raise ValueError(
            f"li_positivity REFUSED: need a POSITIVE lower bound to witness "
            f"positivity of rung {n} (got lo = {lo})")
    return LiRungCert(n=n, lo=lo)


def certify_li_positivity_point(family, pt, name):
    """Certify one Li-ladder rung: ``(CertifiedInstance, 1)``.  Reads
    ``(n, lo) = family.special[1](pt)``."""
    n, lo = family.special[1](pt)
    cert = li_rung_certificate(n, lo)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class LiPositivityLadderEmitter(Emitter):
    """Emit the n-th Li-criterion rung `0 ≤ (taylorCoeff riemannXi n).re` from a
    positive rational lower bound (the Arb enclosure enters as hypothesis `hlo`).
    Deterministic `le_trans (by norm_num) hlo`.  Feeds the upstream
    `LiCriterion.li_criterion_rh_iff` (a finite prefix of its RHS)."""

    # The emitted Lean CALLS these upstream names; the profile/lakefile must supply
    # the LiCriterion library (riemannXi, taylorCoeff). Declared so emit() checks it.
    requires_prelude: tuple[str, ...] = ("riemannXi", "taylorCoeff")

    def __post_init__(self):
        self.kind = "li_positivity"
        self.requires_prelude = ("riemannXi", "taylorCoeff")

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: LiRungCert = inst.payload  # type: ignore[assignment]
            lo = rat_lean(cert.lo)
            coeff = f"(taylorCoeff riemannXi {cert.n}).re"
            nm = inst.lean_name
            lines.append(
                f"-- {nm}: Li-criterion rung n={cert.n} — 0 ≤ (taylorCoeff riemannXi {cert.n}).re, "
                f"witnessed by the certified lower bound lo={cert.lo}.\n"
                f"-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.\n"
                f"-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.\n"
                f"theorem {nm} (hlo : ({lo} : ℝ) ≤ {coeff}) : 0 ≤ {coeff} :=\n"
                f"  le_trans (by norm_num : (0:ℝ) ≤ {lo}) hlo\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def li_refutation_atom_lean() -> str:
    """The ladder's falsifiability face, emitted ONCE per generated file.

    Through the upstream equivalence, a certified NEGATIVE upper bound on ANY
    rung refutes RH outright: if ``(taylorCoeff riemannXi n).re ≤ hi < 0`` then
    ``¬RiemannHypothesis``.  Term-mode (no tactic fragility): the upstream
    ``li_criterion_rh_iff.mp`` hands ``0 ≤ coeff`` from RH, contradicted by
    ``coeff ≤ hi < 0``.  This theorem is NEVER expected to fire (every computed
    enclosure so far is positive); it is the honest contrapositive that makes
    the ladder falsifiable rather than confirmation-only.  Its hypotheses carry
    the same Arb trust seam as the rungs.  conjecture1_proved = False."""
    return (
        "-- li_neg_refutes_rh: the falsifiability face of the ladder.  A certified\n"
        "-- NEGATIVE upper bound on any rung would refute RH via the upstream\n"
        "-- equivalence.  Not expected to fire; emitted so the ladder is falsifiable,\n"
        "-- not confirmation-only.  hhi carries the same Arb trust seam as hlo.\n"
        "theorem li_neg_refutes_rh (n : ℕ) (hi : ℝ)\n"
        "    (hhi : (taylorCoeff riemannXi n).re ≤ hi) (hneg : hi < 0) :\n"
        "    ¬RiemannHypothesis :=\n"
        "  fun hRH => absurd (li_criterion_rh_iff.mp hRH n)\n"
        "    (not_le.mpr (lt_of_le_of_lt hhi hneg))\n"
    )


def li_positivity_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Li positivity-ladder family (kind ``li_positivity``).
    ``spec: pt -> (n, lo)`` — the rung index and its positive rational lower bound."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("li_positivity", spec),
        constants=dict(constants or {}),
    )
