"""Bragg-floor emitter — Route P Brick D3 part 2 (the Dyson-quasicrystal diffraction certificate).

Route P (`RvMWeierstrass.rh_iff_companion_ge`, #465) relocates RH onto one explicit inequality per
order `n`:

    RH ↔ ∀ n, −(1 + (taylorCoeff Γℝ n).re) ≤ (taylorCoeff zetaPoleCompanion n).re,

the right side being the arithmetic companion coefficient, the left the EXPLICIT archimedean floor
(the polygamma-at-½ capstone, #464).  Brick D1 (`logDeriv_zetaPoleCompanion_eq_vonMangoldt`) exposes
the companion's log-derivative on `Re s > 1` as the von Mangoldt log-prime (Bragg) spectrum
`−Σ_m Λ(m) m^{−s} + (s−1)⁻¹`.  This emitter certifies, per `n`, the FINITE diffraction inequality

    (truncated log-prime Bragg amplitude at s₀, over p^k ≤ N)  −  (certified tail)  ≥  floor(n),

a pure rational inequality discharged by `norm_num`.  The truncated amplitude lower bound, the tail
upper bound, and the floor upper bound are Arb-enclosed numeric inputs (python-flint) — the documented
trust seam, identical to the Li ladder.

WHAT THE CERTIFICATE CERTIFIES (read this before citing it)
-----------------------------------------------------------
The emitted theorem certifies ONLY the finite, Arb-enclosed rational inequality above.  It is
category-(b): finite, kernel-checkable, consistent with RH, and PROVES NOTHING about RH.

It does NOT assert that the truncated Bragg amplitude equals `(taylorCoeff zetaPoleCompanion n).re`.
That passage — from the finite Bragg datum at a fixed `s₀ > 1` to the companion coefficient at the Li
base point `s = 1`, and thence to the Route-P falsifiability atom — runs ENTIRELY through the
CONDITIONAL reduction `taylorCoeff_companion_bragg_of_exhaustion_limits` (RvMCompanionBraggLimit),
whose `T → ∞` exhaustion and archimedean-main-term-extraction hypotheses are the NAMED, UNBUILT,
RH-HARD frontier (the von Mangoldt series DIVERGES at `s = 1`).  This emitter neither discharges nor
approaches those hypotheses; the falsifiability atom carries them as explicit, undischarged Lean
hypotheses so nothing is overclaimed.

HONEST REFUSAL (the built-in forge / negative control)
------------------------------------------------------
Because the amplitude is evaluated at a FIXED `s₀` (so it is the order-0 datum, not an order-`n`
moment — expanding the comb at the Li base point is the RH-hard step we refuse to fake), the finite
inequality genuinely holds only for the `n` whose floor it clears.  `bragg_floor_certificate` REFUSES
any instance with a non-positive margin `(bragg_lo − tail_hi) − floor_hi ≤ 0` — an honest refusal,
never a false theorem.  Perturbing an amplitude/tail/floor so the margin vanishes triggers that
refusal (the forge test); a sign-corrupted literal is kernel-rejected (the negative control).

conjecture1_proved = False — this is a re-coordinatization of Route P onto the prime side and a real
finite certificate family, not a step toward RH.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .bragg_coeff import BraggFloorData
from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class BraggFloorCert:
    """One order-`n` Bragg-floor certificate: the truncated amplitude lower bound `bragg_lo`, the
    tail upper bound `tail_hi`, and the archimedean floor upper bound `floor_hi`, all rational
    (Arb-enclosed).  The certified claim is the finite inequality `bragg_lo − tail_hi ≥ floor_hi`."""

    n: int
    s0: sp.Rational
    cutoff: int
    bragg_lo: sp.Rational
    tail_hi: sp.Rational
    floor_hi: sp.Rational

    @property
    def margin(self) -> sp.Rational:
        return sp.Rational((self.bragg_lo - self.tail_hi) - self.floor_hi)


def bragg_floor_certificate(data: BraggFloorData) -> BraggFloorCert:
    """Build (and exactly re-check) a Bragg-floor certificate from Arb-enclosed data.

    REFUSES a non-positive margin: the truncated amplitude (net of its certified tail) must strictly
    clear the archimedean floor, else the finite inequality is false and we do NOT emit it (an honest
    refusal — the fixed-`s₀` order-0 amplitude does not dominate every mid-range floor; see the module
    docstring).  REFUSES `s0 ≤ 1` (the tail diverges) and `cutoff < 2`.
    """
    s0 = sp.Rational(data.s0)
    if s0 <= 1:
        raise ValueError(f"bragg_floor REFUSED: need base point s0 > 1, got {s0}")
    if data.cutoff < 2:
        raise ValueError(f"bragg_floor REFUSED: need prime-power cutoff ≥ 2, got {data.cutoff}")
    cert = BraggFloorCert(
        n=int(data.n), s0=s0, cutoff=int(data.cutoff),
        bragg_lo=sp.Rational(data.bragg_lo),
        tail_hi=sp.Rational(data.tail_hi),
        floor_hi=sp.Rational(data.floor_hi),
    )
    if cert.margin <= 0:
        raise ValueError(
            f"bragg_floor REFUSED at n={cert.n}: margin (bragg_lo − tail_hi) − floor_hi = "
            f"{cert.margin} ≤ 0 — the truncated Bragg amplitude does not clear the floor at this "
            f"order (raise the cutoff or this n is not finitely certifiable at s0={s0})")
    return cert


def certify_bragg_floor_point(family, pt, name):
    """Certify one Bragg-floor rung: ``(CertifiedInstance, 1)``.  Reads the ``BraggFloorData``
    payload from ``family.special[1](pt)`` and re-checks it via :func:`bragg_floor_certificate`."""
    data = family.special[1](pt)
    cert = bragg_floor_certificate(data)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class BraggFloorEmitter(Emitter):
    """Emit the order-`n` diffraction inequality `bragg_lo − tail_hi ≥ floor(n)` from Arb-enclosed
    rationals (the finite Bragg partial sum net of its tail clears the explicit archimedean floor).
    Deterministic `norm_num`.  The emitted theorem is the honest finite certificate; its connection
    to `companion_below_floor_refutes_rh` is the conditional seam, stated but not discharged."""

    def __post_init__(self):
        self.kind = "bragg_floor"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: BraggFloorCert = inst.payload  # type: ignore[assignment]
            blo = rat_lean(cert.bragg_lo)
            thi = rat_lean(cert.tail_hi)
            flo = rat_lean(cert.floor_hi)
            nm = inst.lean_name
            lines.append(
                f"-- {nm}: Route P Brick D3 diffraction rung, order n={cert.n}.  At base point "
                f"s0={cert.s0} the truncated log-prime (von Mangoldt / Bragg) amplitude over "
                f"p^k ≤ {cert.cutoff},\n"
                f"-- bounded below by braggLo={cert.bragg_lo}, net of the certified tail "
                f"tailHi={cert.tail_hi}, clears the explicit archimedean floor "
                f"floorHi={cert.floor_hi} ≥ -(1+Re taylorCoeff Γℝ {cert.n}).\n"
                f"-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the "
                f"documented non-kernel input.\n"
                f"-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage "
                f"to (taylorCoeff zetaPoleCompanion {cert.n}).re runs through the CONDITIONAL, "
                f"RH-hard\n"
                f"-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  "
                f"conjecture1_proved = False.\n"
                f"theorem {nm} : ({flo} : ℝ) ≤ {blo} - {thi} := by norm_num\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def bragg_below_floor_refutes_rh_lean() -> str:
    """The diffraction ladder's falsifiability face, emitted ONCE per generated file.

    A certified Bragg amplitude (net of its tail) falling strictly BELOW the archimedean floor would,
    THROUGH THE CONDITIONAL seam, refute RH via Route P.  The seam is made explicit: the theorem takes
    as an UNDISCHARGED hypothesis `hcomp` that the conditional reduction
    `taylorCoeff_companion_bragg_of_exhaustion_limits` has identified `(taylorCoeff zetaPoleCompanion
    n).re` with the finite Bragg datum `braggVal`; GIVEN that identification and a certified strict
    sub-floor `braggVal < floor`, the Route-P atom `companion_below_floor_refutes_rh` fires.

    `hcomp` is the quarantined RH-hard content (the `T → ∞` exhaustion + archimedean extraction); it
    is NEVER discharged here, and its provision is exactly the analytic core of RH.  This atom is NOT
    expected to fire (every computed Bragg rung clears the floor); it is emitted so the diffraction
    ladder is an experiment that could have falsified, not confirmation-only.  The arithmetic is
    trivial (`lt_of_lt_of_eq`/`not_le`); the entire load sits in the hypotheses.  Its Arb trust seam
    is the same as the rungs.  conjecture1_proved = False."""
    return (
        "-- bragg_below_floor_refutes_rh: the falsifiability face of the diffraction ladder.  Through\n"
        "-- the CONDITIONAL reduction taylorCoeff_companion_bragg_of_exhaustion_limits (hypothesis\n"
        "-- hcomp, the RH-hard exhaustion/extraction seam — NEVER discharged), a certified Bragg\n"
        "-- datum strictly below the archimedean floor refutes RH via companion_below_floor_refutes_rh.\n"
        "-- Not expected to fire; emitted so the ladder is falsifiable, not confirmation-only.\n"
        "-- conjecture1_proved = False.\n"
        "theorem bragg_below_floor_refutes_rh (n : ℕ) (braggVal : ℝ)\n"
        "    (hcomp : (LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n).re = braggVal)\n"
        "    (hbelow : braggVal < -(1 + (LiCriterion.taylorCoeff Complex.Gammaℝ n).re)) :\n"
        "    ¬RiemannHypothesis :=\n"
        "  companion_below_floor_refutes_rh n (hcomp ▸ hbelow)\n"
    )


def bragg_floor_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Bragg-floor family (kind ``bragg_floor``).  ``spec: pt -> BraggFloorData`` — the
    Arb-enclosed order-`n` data (amplitude lower bound, tail upper bound, floor upper bound)."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("bragg_floor", spec),
        constants=dict(constants or {}),
    )
