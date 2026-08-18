"""Generate the Bernoulli example's Lean file: certify -> validate -> emit -> write.

Usage:  python3 examples/bernoulli/generate.py [--check]

This example exercises the GENERAL telperion core (never telperion.bg) on a
textbook inequality with nothing to do with Brualdi-Goldwasser:

    Bernoulli's inequality (integer form): for integer k >= 1 and real x >= 0,

        (1 + x)^k - 1 - k*x >= 0.

Expanded, (1+x)^k = sum_{j=0}^k C(k,j) x^j; the degree-0 (=1) and degree-1
(= k*x) terms cancel against the subtracted -1 - k*x, leaving

        sum_{j=2}^k C(k,j) x^j,

a polynomial with all-nonnegative INTEGER coefficients (binomial coeffs) and
trivial denominator 1.  That is exactly a Polya certificate, so
`DirectPolyaEmitter` closes each instance by `positivity`.  We drive the whole
grid k in {1,2,3,4,5,6} through the enforced certify -> validate -> emit ->
freeze pipeline.

Without --check: writes frozen/Bernoulli.lean (and frozen/manifest.json).
With --check: regenerates in memory and diffs against the frozen copy —
nonzero exit on any drift.
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from math import comb
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    DirectPolyaEmitter,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)

HERE = Path(__file__).resolve().parent

# The single nonnegative real variable of Bernoulli's inequality.
x = sp.Symbol("x", nonnegative=True)

# The grid: integer exponents k = 1..6.
KS = [1, 2, 3, 4, 5, 6]


def bernoulli_target(pt) -> sp.Expr:
    """(1 + x)^k - 1 - k*x, expanded to its all-nonneg-coefficient form."""
    k = pt["k"]
    return sp.expand((1 + x) ** k - 1 - k * x)


def bernoulli_family():
    from telperion import GridSpec, InequalityFamily

    return InequalityFamily(
        name="Bernoulli",
        symbols=(x,),
        grid=GridSpec([("k", KS)]),
        lean_name=lambda pt: f"bernoulli_k{pt['k']}",
        target=bernoulli_target,
    )


def bernoulli_profile() -> LeanProfile:
    return LeanProfile(namespace=("Bernoulli",))


def _exact_spot_checks() -> ValidationReport:
    """The numeric-first discipline in miniature: BEFORE formalizing, verify in
    exact arithmetic (fractions.Fraction / sympy.Rational — no floats) that

      (a) the expanded target has all-nonnegative integer coefficients equal to
          the binomial coefficients C(k, j) for j >= 2 (and zero below), and
      (b) the claim (1+x)^k - 1 - k*x >= 0 holds at several exact rational
          sample points x >= 0.
    """

    def coeffs_are_nonneg_binomials():
        for k in KS:
            poly = sp.Poly(bernoulli_target({"k": k}), x)
            # Every coefficient is a nonnegative integer.
            for c in poly.all_coeffs():
                assert c == int(c) and int(c) >= 0, (k, c)
            # And they are exactly the binomials C(k, j) for j >= 2, 0 below.
            for j in range(0, k + 1):
                got = poly.coeff_monomial(x**j) if j > 0 else poly.coeff_monomial(1)
                want = comb(k, j) if j >= 2 else 0
                assert sp.Integer(got) == sp.Integer(want), (k, j, got, want)

    def value_nonneg_at_rationals():
        samples = [
            Fraction(0),
            Fraction(1, 7),
            Fraction(3, 4),
            Fraction(1),
            Fraction(5, 2),
            Fraction(37, 3),
        ]
        for k in KS:
            for xf in samples:
                xr = sp.Rational(xf.numerator, xf.denominator)
                val = bernoulli_target({"k": k}).subs({x: xr})
                assert val >= 0, (k, xf, val)
                # Cross-check against the unexpanded closed form in exact arith.
                closed = (1 + xr) ** k - 1 - k * xr
                assert sp.simplify(val - closed) == 0, (k, xf, val, closed)

    return ValidationReport.from_asserts(
        [
            ("bernoulli_nonneg_binomial_coeffs", coeffs_are_nonneg_binomials),
            ("bernoulli_value_nonneg_at_rationals", value_nonneg_at_rationals),
        ]
    )


def build():
    validation = _exact_spot_checks()
    res = emit(
        certify(bernoulli_family()),
        bernoulli_profile(),
        [DirectPolyaEmitter()],
        validation,
        file_name="Bernoulli.lean",
    )
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        ok = True
        rep = diff_frozen(res, HERE / "frozen")
        if not rep.ok:
            ok = False
            print("DRIFT:", *rep.details, sep="\n  ")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    freeze(res, HERE / "frozen")
    print(f"wrote Bernoulli({res.n_theorems}) theorems; input hash {res.input_hash}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
