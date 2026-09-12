"""Rigorous rational enclosures for the Route-P Bragg-floor certificate (bragg_floor backend).

conjecture1_proved = False.  This module does NOT prove RH.  It produces certified
rational data for a FINITE, Arb-enclosed numeric inequality of the shape

    (truncated log-prime Bragg amplitude, order n)  −  (certified tail)  ≥  (archimedean floor n)

where

  * the **archimedean floor** of order ``n`` is ``-(1 + Re taylorCoeff Γℝ n)`` — fully explicit
    (the polygamma-at-½ capstone ``taylorCoeff_Gammaℝ_polygamma``, #464); numerically
    ``taylorCoeff Γℝ n = (n+1)·a_{n+1}`` with ``a_j = [z^j] log Γℝ(1/(1−z))``,
    ``Γℝ(s) = π^{−s/2} Γ(s/2)`` — the SAME object the Li ladder's archimedean side uses, here
    validated against its closed-form trend ``(n/2)(log n + γ − 1 − log 2π)``;
  * the **log-prime (von Mangoldt / Bragg) amplitude** is read off the companion's log-derivative
    on ``Re s > 1`` (Brick D1, ``logDeriv_zetaPoleCompanion_eq_vonMangoldt``):
    ``logDeriv zetaPoleCompanion s = −Σ_m Λ(m) m^{−s} + (s−1)⁻¹`` — the Bragg comb supported on
    ``{log p^k}`` with amplitude ``Λ(p^k) = log p``.  We work at a fixed real base point ``s₀ > 1``
    (``BASE_S0``) where this series converges, truncate the comb to prime powers ``m ≤ N``, and
    bound the tail ``Σ_{m>N} Λ(m) m^{−s₀}`` rigorously from above.

HONESTY SEAM — WHAT THIS CERTIFIES AND WHAT IT DOES NOT
------------------------------------------------------
The certified object is ONLY the finite rational inequality above: a truncated Bragg partial sum
(with a certified tail slack) clears the explicit archimedean floor.  It is category-(b): finite,
Arb-checkable, consistent with RH, PROVING NOTHING about RH.

The connection from this finite Bragg datum to ``taylorCoeff zetaPoleCompanion n`` — and hence to
the Route-P falsifiability atom ``companion_below_floor_refutes_rh`` — runs ENTIRELY through the
CONDITIONAL reduction ``taylorCoeff_companion_bragg_of_exhaustion_limits`` (RvMCompanionBraggLimit),
whose ``T→∞`` exhaustion + archimedean-main-term-extraction hypotheses are the NAMED, UNBUILT,
RH-HARD frontier (the von Mangoldt series diverges at the Li base point ``s = 1``).  This module
NEITHER discharges NOR approaches those hypotheses; the emitter states them explicitly as the seam.

The Arb ball arithmetic (python-flint) is the documented non-kernel trust boundary, IDENTICAL to the
Li ladder (see ``li_coeff`` / ``rh_jensen.coefficients``): every ball rigorously encloses the true
value via directed-rounded radii read out exactly as ``fractions.Fraction`` via ``man_exp()``.

EXTERNAL ANCHOR (refuse-to-emit gate)
-------------------------------------
Before any box is handed out, the archimedean coefficients are self-checked against the published
Li–Keiper-adjacent trend and the von Mangoldt amplitudes against ``Λ(2),Λ(3),Λ(4) = log2,log3,log2``
— a normalization or index bug ABORTS here rather than emitting (mirrors ``li_coeff``'s published-
value anchor).

Dependency: python-flint (Arb/FLINT).  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from .rh_jensen.coefficients import _arb_ball_to_fractions

# The fixed real base point s₀ > 1 at which the von Mangoldt Bragg series converges (Brick D1's
# Re s > 1 domain).  s₀ = 2 keeps the series geometric-fast and the tail small; any rational > 1
# works and is recorded in the certificate so the Lean statement is self-describing.
BASE_S0 = Fraction(2, 1)

# Published archimedean-trend anchor: Re taylorCoeff Γℝ n agrees with the LEADING term
# (n/2)(log n + γ − 1 − log 2π) to within this RELATIVE tolerance for the checked orders.  The
# trend is only a leading-order approximation (the measured residual (coeff−trend)/n ≈ 0.02–0.03,
# so the absolute gap grows ~0.03·n); a relative window catches a normalization/index bug (which
# would be off by an O(1) factor or a sign) without flagging the benign sub-leading drift.
_ARCH_TREND_REL = Fraction(1, 5)

# Small von Mangoldt values for the prime-side anchor: Λ(2)=log2, Λ(3)=log3, Λ(4)=log2 (= Λ(2)).
# Checked in mantissa against mpmath-free rational windows around the true logs.
_LOG2_LO, _LOG2_HI = Fraction("0.6931"), Fraction("0.6932")
_LOG3_LO, _LOG3_HI = Fraction("1.0986"), Fraction("1.0987")


def _is_prime_power(m: int) -> int | None:
    """Return the base prime ``p`` if ``m = p^k`` (k ≥ 1), else ``None``."""
    if m < 2:
        return None
    # smallest prime factor
    p = 2
    while p * p <= m:
        if m % p == 0:
            break
        p += 1
    else:
        p = m  # m is prime
    q = m
    while q % p == 0:
        q //= p
    return p if q == 1 else None


def enclose_arch_floors(count: int, prec_bits: int = 256) -> list[tuple[Fraction, Fraction]]:
    """Rigorous outward enclosures of the archimedean FLOOR ``-(1 + Re taylorCoeff Γℝ n)`` for
    ``n < count`` (the explicit Route-P floor).  One ``acb_series`` computation yields the whole
    prefix.  Raises ``ValueError`` if the leading-trend self-check fails.
    """
    import mpmath as mp
    from flint import acb, acb_series, ctx

    if count <= 0:
        raise ValueError(f"enclose_arch_floors: need count >= 1, got {count}")

    old_prec, old_cap = ctx.prec, ctx.cap
    try:
        ctx.prec = prec_bits
        ctx.cap = count + 2  # taylorCoeff Γℝ n = (n+1)·a_{n+1}, need one extra order
        z = acb_series([0, 1])
        one = acb_series([1])
        s = (one - z).inv()                       # s = 1/(1−z)
        pi_log = acb.pi().log()
        log_gammaR = (-(s / 2) * pi_log) + (s / 2).lgamma()   # log Γℝ(s) = −(s/2)logπ + logΓ(s/2)
        a = log_gammaR.coeffs()                   # a_j = [z^j] log Γℝ(1/(1−z))
    finally:
        ctx.prec, ctx.cap = old_prec, old_cap

    floors: list[tuple[Fraction, Fraction]] = []
    for n in range(count):
        # taylorCoeff Γℝ n = (n+1)·a_{n+1}; its enclosure as a real ball.
        coeff_lo, coeff_hi = _arb_ball_to_fractions(a[n + 1].real)
        coeff_lo, coeff_hi = (n + 1) * coeff_lo, (n + 1) * coeff_hi
        # floor = -(1 + Re coeff); order reverses under negation.
        floor_lo = -(1 + coeff_hi)
        floor_hi = -(1 + coeff_lo)
        floors.append((floor_lo, floor_hi))

    # External anchor: the Re taylorCoeff Γℝ n leading trend (n/2)(log n + γ − 1 − log 2π).
    mp.mp.dps = 40
    for n in (16, 24):
        if n < count:
            # recover Re coeff from floor: Re coeff = -1 - floor_hi .. -1 - floor_lo
            lo_c, hi_c = -1 - floors[n][1], -1 - floors[n][0]
            trend = (mp.mpf(n) / 2) * (mp.log(n) + mp.euler - 1 - mp.log(2 * mp.pi))
            trend = Fraction(mp.nstr(trend, 20))
            tol = abs(trend) * _ARCH_TREND_REL
            if not (lo_c - tol <= trend <= hi_c + tol):
                raise ValueError(
                    f"bragg_coeff ARCH SELF-CHECK FAILED at n={n}: Re taylorCoeff Γℝ enclosure "
                    f"[{float(lo_c)}, {float(hi_c)}] differs from the leading trend "
                    f"{float(trend)} by more than {float(_ARCH_TREND_REL)*100:.0f}% — "
                    f"normalization/index bug; refusing to emit")
    return floors


def enclose_bragg_truncation(
    n_support: int, prec_bits: int = 256, s0: Fraction = BASE_S0
) -> tuple[Fraction, Fraction, Fraction]:
    """Rigorous data for the truncated log-prime Bragg amplitude at base point ``s0 > 1``,
    truncated to prime powers ``m ≤ n_support``.

    Returns ``(bragg_lo, bragg_hi, tail_hi)``:

      * ``[bragg_lo, bragg_hi]`` encloses the truncated partial sum ``Σ_{p^k ≤ n_support} Λ(p^k) p^{−k·s0}``
        (Arb ball arithmetic; outward-rounded rationals);
      * ``tail_hi`` is a rigorous UPPER bound on the omitted tail ``Σ_{m > n_support} Λ(m) m^{−s0}``,
        via ``Λ(m) ≤ log m`` and the integral majorant
        ``∫_{n_support}^∞ (log x) x^{−s0} dx = n_support^{1−s0}(log n_support/(s0−1) + 1/(s0−1)²)``.

    The truncated partial sum is a rigorous LOWER proxy for the full Bragg amplitude; the certificate
    uses ``bragg_lo − tail_hi`` as a rigorous lower bound on ``(full amplitude − tail)``.  Raises
    ``ValueError`` on ``s0 ≤ 1`` (tail diverges) or a failed small-prime anchor.
    """
    from flint import acb, arb, ctx

    if s0 <= 1:
        raise ValueError(f"enclose_bragg_truncation: need s0 > 1 (convergence), got {s0}")
    if n_support < 2:
        raise ValueError(f"enclose_bragg_truncation: need cutoff ≥ 2, got {n_support}")

    old_prec = ctx.prec
    try:
        ctx.prec = prec_bits
        s0_arb = arb(s0.numerator) / arb(s0.denominator)
        total = acb(0)
        log2_ball = log3_ball = None
        for m in range(2, n_support + 1):
            p = _is_prime_power(m)
            if p is None:
                continue
            amp = arb(p).log()                      # Λ(p^k) = log p
            total = total + amp * (arb(m) ** (-s0_arb))
            if m == 2:
                log2_ball = amp
            if m == 3:
                log3_ball = amp
        bragg_lo, bragg_hi = _arb_ball_to_fractions(total.real)

        # Rigorous tail: Σ_{m>N} Λ(m) m^{−s0} ≤ ∫_N^∞ (log x) x^{−s0} dx, evaluated in Arb and
        # rounded UP to a rational.
        N = arb(n_support)
        a_exp = s0_arb - 1
        tail_ball = (N ** (-a_exp)) * (N.log() / a_exp + arb(1) / (a_exp * a_exp))
        _tlo, tail_hi = _arb_ball_to_fractions(tail_ball)
    finally:
        ctx.prec = old_prec

    # External small-prime anchor: Λ(2)=log2, Λ(3)=log3 inside their rational windows.
    if log2_ball is not None:
        l2lo, l2hi = _arb_ball_to_fractions(log2_ball)
        if not (l2lo >= _LOG2_LO - Fraction(1, 10**3) and l2hi <= _LOG2_HI + Fraction(1, 10**3)):
            raise ValueError(
                f"bragg_coeff PRIME ANCHOR FAILED: Λ(2) enclosure [{float(l2lo)},{float(l2hi)}] "
                f"outside log2 window — refusing to emit")
    if log3_ball is not None:
        l3lo, l3hi = _arb_ball_to_fractions(log3_ball)
        if not (l3lo >= _LOG3_LO - Fraction(1, 10**3) and l3hi <= _LOG3_HI + Fraction(1, 10**3)):
            raise ValueError(
                f"bragg_coeff PRIME ANCHOR FAILED: Λ(3) enclosure [{float(l3lo)},{float(l3hi)}] "
                f"outside log3 window — refusing to emit")

    return bragg_lo, bragg_hi, tail_hi


@dataclass(frozen=True)
class BraggFloorData:
    """The numeric inputs for one order-``n`` Bragg-floor certificate (all Arb-enclosed rationals).

    ``bragg_lo`` — a rigorous lower bound on the truncated log-prime amplitude at ``s0`` over
    ``p^k ≤ cutoff``; ``tail_hi`` — a rigorous upper bound on the omitted tail; ``floor_hi`` — a
    rigorous upper bound on the archimedean floor ``-(1 + Re taylorCoeff Γℝ n)``.  The certifiable
    claim is the pure rational inequality ``bragg_lo − tail_hi ≥ floor_hi ≥ floor(n)``.
    """

    n: int
    s0: Fraction
    cutoff: int
    bragg_lo: Fraction
    tail_hi: Fraction
    floor_hi: Fraction

    @property
    def margin(self) -> Fraction:
        """The certified slack ``(bragg_lo − tail_hi) − floor_hi`` (> 0 for a genuine certificate)."""
        return (self.bragg_lo - self.tail_hi) - self.floor_hi


def enclose_bragg_floor(
    n: int, cutoff: int, prec_bits: int = 256, s0: Fraction = BASE_S0,
    _floors: list[tuple[Fraction, Fraction]] | None = None,
) -> BraggFloorData:
    """Assemble the order-``n`` Bragg-floor data: truncated amplitude lower bound, tail upper bound,
    and archimedean floor upper bound.  ``_floors`` optionally reuses a precomputed floor prefix
    (the batch path computes it once).  Every value is a rigorous Arb-enclosed rational; the self-
    checks inside the two ``enclose_*`` calls are the refuse-to-emit anchors.
    """
    if _floors is not None:
        floor_lo, floor_hi = _floors[n]
    else:
        floor_lo, floor_hi = enclose_arch_floors(n + 1, prec_bits=prec_bits)[n]
    bragg_lo, _bragg_hi, tail_hi = enclose_bragg_truncation(cutoff, prec_bits=prec_bits, s0=s0)
    return BraggFloorData(
        n=n, s0=s0, cutoff=cutoff,
        bragg_lo=bragg_lo, tail_hi=tail_hi, floor_hi=floor_hi,
    )
