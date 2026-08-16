"""The exact-numeric validation layer: rational interval kernel, verified
constants, adaptive bisection, and grid harnesses.

Everything here is `fractions.Fraction` — floats may GUIDE (e.g. picking a
dyadic anchor) but every accepted bound is verified rationally.  This layer is
validation-only: its facts gate emission (via ValidationReport) but are not
themselves emitted to Lean.  Generalized from the origin campaign's
g1_floor_certificates.py kernel.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr
from typing import Callable, Iterable, Sequence

from .workflow import ValidationReport


# ------------------------------------------------------------- exp/log kernel
def exp_lower(x: Fr, K: int = 30) -> Fr:
    """Rational lower bound for e^x, x >= 0: the Taylor partial sum."""
    if x < 0:
        raise ValueError("exp_lower requires x >= 0")
    s, term = Fr(0), Fr(1)
    for k in range(K + 1):
        s += term
        term = term * x / (k + 1)
    return s


def exp_upper(x: Fr, K: int = 30) -> Fr:
    """Rational upper bound for e^x on 0 <= x < K+1: partial sum + geometric tail."""
    if not 0 <= x < K + 1:
        raise ValueError("exp_upper requires 0 <= x < K + 1")
    s, term = Fr(0), Fr(1)
    for k in range(K + 1):
        s += term
        term = term * x / (k + 1)
    return s + term / (1 - x / (K + 2))


@dataclass(frozen=True)
class VerifiedConstant:
    """A rationally verified bracket lo <= value <= hi.

    Construct via `verify_log`: brackets log(target)/divisor by checking
    exp_upper(divisor*lo) <= target <= exp_lower(divisor*hi) in exact
    arithmetic.  The bracket, not the transcendental value, is what downstream
    bounds consume.
    """

    name: str
    lo: Fr
    hi: Fr

    @staticmethod
    def verify_log(name: str, target: Fr, lo: Fr, hi: Fr, divisor: int = 1) -> "VerifiedConstant":
        if not (exp_upper(divisor * lo) <= target <= exp_lower(divisor * hi)):
            raise ValueError(f"bracket [{lo}, {hi}] does not verify for log({target})/{divisor}")
        return VerifiedConstant(name, lo, hi)


class Log1pUpper:
    """Verified rational upper bound for log(1+u), u >= 0, via concavity anchors
    at dyadic points (float-guided anchor choice, rational verification)."""

    def __init__(self, grid: int = 512, slop: int = 2, prec: int = 10**9):
        self.grid, self.slop, self.prec = grid, slop, prec
        self._anchors: dict[Fr, Fr] = {}

    def __call__(self, u: Fr) -> Fr:
        if u < 0:
            raise ValueError("log1p_upper requires u >= 0")
        if u == 0:
            return Fr(0)
        u0 = Fr(int(u * self.grid), self.grid)
        if u0 not in self._anchors:
            q = Fr(int(math.log(1 + float(u0)) * self.prec) + self.slop, self.prec)
            if exp_lower(q) < 1 + u0:  # verify log(1+u0) <= q rationally
                raise ValueError(f"anchor verification failed at u0={u0}")
            self._anchors[u0] = q
        u0q = self._anchors[u0]
        return u0q + (u - u0) / (1 + u0)


# ------------------------------------------------------------------ bisection
def certify_floor(
    f_lower: Callable[[Fr, Fr], Fr],
    floor: Fr,
    lo: Fr,
    hi: Fr,
    *,
    max_depth: int = 22,
) -> bool:
    """Adaptive bisection: f(y) >= floor for all y in [lo, hi], where
    f_lower(y0, y1) is a rational lower bound of f over [y0, y1].

    Returns False (refusal, not error) if max_depth subdivisions cannot close
    the interval — the caller decides whether that is fatal.
    """
    if f_lower(lo, hi) >= floor:
        return True
    if max_depth <= 0:
        return False
    mid = (lo + hi) / 2
    return certify_floor(f_lower, floor, lo, mid, max_depth=max_depth - 1) and certify_floor(
        f_lower, floor, mid, hi, max_depth=max_depth - 1
    )


# ------------------------------------------------------------- harness shapes
def exact_grid_check(
    name: str,
    points: Iterable,
    claim: Callable[[object], bool],
) -> tuple[str, Callable[[], None]]:
    """A named check asserting claim(pt) for every point, exactly.  Feed the
    result list to ValidationReport.from_asserts / build_report."""

    def run() -> None:
        for pt in points:
            assert claim(pt), f"{name}: claim failed at {pt}"

    return (name, run)


def build_report(checks: Sequence[tuple[str, Callable[[], None]]]) -> ValidationReport:
    """Run all named checks (loud on failure) and return the green report."""
    return ValidationReport.from_asserts(checks)
