"""Arb transcendental-constant enclosure provider.

Provides a certified rational box [lo, hi] (as fractions.Fraction) that
rigorously contains a transcendental constant (pi, e, zeta(q), gamma(q))
computed via python-flint / Arb ball arithmetic.

CERTIFICATION STATUS
--------------------
This module is a certified rational-box provider.  Box MEMBERSHIP is a
documented NON-KERNEL input: Arb ball arithmetic (via python-flint) is
internally certified (interval arithmetic with outward rounding), but Lean
does not independently verify the constant's value.  The rational endpoints
lo, hi are exact fractions.Fraction derived via outward-rounded dyadic
arithmetic from the Arb ball's mid and rad fields (man_exp extraction).

conjecture1_proved = False.

TECHNIQUE: man_exp outward rounding
------------------------------------
An arb ball b has a midpoint mid and radius rad, both exact dyadic
rationals representable as  man * 2**exp  (SIGNED mantissa, signed
exponent).  man_exp() returns (man, exp) with  man * 2**exp == exact value.

    _dyadic(a): man, exp = a.man_exp(); return Fraction(man) * Fraction(2)**exp

The radius rad is a certified UPPER bound of the true radius, so
    lo = mid - rad
    hi = mid + rad
are exact fractions.Fraction that rigorously contain the true value.

No float arithmetic appears in the returned endpoints.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Union

try:
    import flint as _flint
    from flint import acb as _acb
    from flint import arb as _arb
    from flint import ctx as _ctx
    _FLINT_AVAILABLE = True
except ImportError:
    _FLINT_AVAILABLE = False

# ──────────────────────────────────────────────────────────────────────────────
# Internal dyadic helpers
# ──────────────────────────────────────────────────────────────────────────────

def _dyadic(a) -> Fraction:
    """Convert an Arb scalar (arb, no imaginary part) to an exact Fraction.

    Uses man_exp(): value = man * 2**exp, where man is the signed mantissa.
    Works for both positive and negative exponents without any float conversion.
    """
    man, exp = a.man_exp()
    man = int(man)
    exp = int(exp)
    if exp >= 0:
        return Fraction(man) * Fraction(2) ** exp
    else:
        # Fraction(man, 2**(-exp)) is exact for negative exponents
        return Fraction(man, 2 ** (-exp))


def _arb_ball_to_fractions(ball) -> tuple[Fraction, Fraction]:
    """Convert an Arb ball to an outward-rounded rational enclosure (lo, hi).

    Returns (mid - rad, mid + rad) as exact fractions.Fraction, where rad is
    a certified UPPER bound of the true radius.  The interval [lo, hi]
    rigorously contains the true value represented by the ball.

    No float arithmetic is used.
    """
    mid = _dyadic(ball.mid())
    rad = _dyadic(ball.rad())
    return mid - rad, mid + rad


# ──────────────────────────────────────────────────────────────────────────────
# Spec parsing and evaluation
# ──────────────────────────────────────────────────────────────────────────────

_ZETA_RE = re.compile(r"^zeta\((.+)\)$")
_GAMMA_RE = re.compile(r"^gamma\((.+)\)$")


def _parse_rational_arg(inner: str) -> Fraction:
    """Parse a rational string like '1/2' or '1/4' into a Fraction."""
    inner = inner.strip()
    return Fraction(inner)


def _eval_spec(spec: Union[str, Callable], prec_bits: int):
    """Evaluate spec at the given precision, returning an acb.

    spec can be:
      "pi"           -> acb.pi()
      "e"            -> acb(1).exp()
      "zeta(q)"      -> acb(str(q)).zeta()  where q is a rational
      "gamma(q)"     -> acb(str(q)).gamma() where q is a rational
      callable       -> spec(_flint)   (receives the flint module)

    Sets ctx.prec = prec_bits (save/restore around call).
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    old_prec = _ctx.prec
    try:
        _ctx.prec = prec_bits

        if callable(spec):
            result = spec(_flint)
        elif spec == "pi":
            result = _acb.pi()
        elif spec == "e":
            result = _acb(1).exp()
        else:
            m = _ZETA_RE.match(spec)
            if m:
                q = _parse_rational_arg(m.group(1))
                result = _acb(str(q)).zeta()
            else:
                m = _GAMMA_RE.match(spec)
                if m:
                    q = _parse_rational_arg(m.group(1))
                    result = _acb(str(q)).gamma()
                else:
                    raise ValueError(
                        f"Unknown spec {spec!r}. "
                        "Supported: 'pi', 'e', 'zeta(<rational>)', 'gamma(<rational>)', "
                        "or a callable(flint_module) -> acb."
                    )
    finally:
        _ctx.prec = old_prec

    return result


# ──────────────────────────────────────────────────────────────────────────────
# Public API
# ──────────────────────────────────────────────────────────────────────────────

def enclose_constant(
    spec: Union[str, Callable],
    prec_bits: int,
) -> tuple[Fraction, Fraction]:
    """Return a certified outward-rounded rational enclosure (lo, hi) for a
    transcendental constant.

    Parameters
    ----------
    spec : str or callable
        "pi"           -- the constant pi
        "e"            -- Euler's number e
        "zeta(q)"      -- Riemann zeta function at rational q (e.g. "zeta(1/2)")
        "gamma(q)"     -- Euler gamma function at rational q (e.g. "gamma(1/4)")
        callable       -- receives the flint module, must return an acb value

    prec_bits : int
        Working precision in bits for Arb computation.  Higher gives tighter
        enclosure.

    Returns
    -------
    (lo, hi) : tuple[Fraction, Fraction]
        Exact fractions.Fraction endpoints such that lo <= true_value <= hi.
        The interval is outward-rounded: lo may be slightly below and hi
        slightly above the best Arb approximation, by at most the certified
        radius of the Arb ball.  No float arithmetic is used in the return
        values.

    Raises
    ------
    RuntimeError
        If python-flint is not installed.
    ValueError
        If spec is not recognized.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    result_acb = _eval_spec(spec, prec_bits)
    # Take real part (arb ball)
    real_ball = result_acb.real
    return _arb_ball_to_fractions(real_ball)


# ──────────────────────────────────────────────────────────────────────────────
# EnclosureRecord
# ──────────────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class EnclosureRecord:
    """A certified rational enclosure record for a transcendental constant.

    Fields
    ------
    spec : str
        The constant specification (e.g. "pi", "e", "zeta(1/2)").
    prec_bits : int
        Arb working precision used to produce the enclosure.
    lo : Fraction
        Exact rational lower bound; true value >= lo.
    hi : Fraction
        Exact rational upper bound; true value <= hi.
    radius : Fraction
        Half-width of the enclosure (hi - lo) / 2.  A certified upper bound
        on the distance from the midpoint to the true value.

    CERTIFICATION NOTE: box membership is a documented non-kernel input.
    Arb ball arithmetic is certified; Lean does not verify the constant's
    value.  conjecture1_proved = False.
    """

    spec: str
    prec_bits: int
    lo: Fraction
    hi: Fraction
    radius: Fraction

    def to_dict(self) -> dict:
        """Serialize to a plain dict with string-encoded Fractions.

        All Fraction fields are stored as 'numerator/denominator' strings
        (or just 'numerator' for integers) to preserve exactness across
        JSON serialization.
        """
        def _frac_str(f: Fraction) -> str:
            if f.denominator == 1:
                return str(f.numerator)
            return f"{f.numerator}/{f.denominator}"

        return {
            "spec": self.spec,
            "prec_bits": self.prec_bits,
            "lo": _frac_str(self.lo),
            "hi": _frac_str(self.hi),
            "radius": _frac_str(self.radius),
        }
