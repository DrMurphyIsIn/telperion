"""Rational-identity EXTENSION example (2026-10-01): multivariate identities and identities
modulo a minimal polynomial, compile-gated.

    python examples/rational_identity/generate_ext.py           # write lean/RationalIdentityExt.lean
    python examples/rational_identity/generate_ext.py --check    # drift check (no write)

The univariate ray form keeps its own frozen example (``generate.py`` -> ``frozen/``); this
file exercises the two extension modes:

* MULTIVARIATE (``∀ x y : ℚ, c_x < x → c_y < y → lhs = rhs``, `field_simp; ring`):
  classical partial fractions -- 1/((x+1)(x+2)) = 1/(x+1) - 1/(x+2) on x > -1,
  1/(x(x^2+1)) = 1/x - x/(x^2+1) on x > 0, the two-variable
  1/((x+y)(x+2y)) = (1/(x+y) - 1/(x+2y))/y and 1/(x(x+y)) + 1/(y(x+y)) = 1/(xy) on x, y > 0.
* MODULO A MINIMAL POLYNOMIAL (``∀ t : ℝ, t^2 - t - 1 = 0 → lhs = rhs`` by
  `linear_combination q * h`, plus the instance at the real root (1 + √5)/2): classical
  Fibonacci / Lucas identities in Q(√5) = Q[t]/(t^2 - t - 1):
  t^2 = t + 1, t^n = F_n t + F_(n-1) (n = 3..8), t^n + (1 - t)^n = L_n (n = 2..6), and
  (2t - 1)^2 = 5.

NEGATIVE CONTROLS (Layer 1, self-checked below; the kernel controls live in
negctrl_adapters/adapter_rational_identity.py): a partial fraction off by 1/1000 is refused,
a Fibonacci power with F_(n-1) + 1 is refused (nonzero remainder), and a reducible modulus
is refused.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, RationalIdentityEmitter, ValidationReport,
    certify, emit, rational_identity_family,
)

x, y, t = sp.symbols("x y t")
PHI_MINPOLY = t ** 2 - t - 1


def _fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _lucas(n):
    return _fib(n - 1) + _fib(n + 1)


CASES = {
    "partial_fraction_two_linear": dict(
        symbols=(x,), lhs=1 / ((x + 1) * (x + 2)), rhs=1 / (x + 1) - 1 / (x + 2),
        domain={"x": -1}),
    "partial_fraction_quadratic_factor": dict(
        symbols=(x,), lhs=1 / (x * (x ** 2 + 1)), rhs=1 / x - x / (x ** 2 + 1),
        domain={"x": 0}),
    "partial_fraction_two_variable": dict(
        symbols=(x, y), lhs=1 / ((x + y) * (x + 2 * y)),
        rhs=(1 / (x + y) - 1 / (x + 2 * y)) / y, domain={"x": 0, "y": 0}),
    "harmonic_pair_two_variable": dict(
        symbols=(x, y), lhs=1 / (x * (x + y)) + 1 / (y * (x + y)), rhs=1 / (x * y),
        domain={"x": 0, "y": 0}),
    "phi_square": dict(symbols=(t,), lhs=t ** 2, rhs=t + 1, modulus=PHI_MINPOLY),
    "sqrt5_from_root": dict(symbols=(t,), lhs=(2 * t - 1) ** 2, rhs=5, modulus=PHI_MINPOLY),
}
for _n in range(3, 9):
    CASES[f"fibonacci_power_{_n}"] = dict(symbols=(t,), lhs=t ** _n,
                                         rhs=_fib(_n) * t + _fib(_n - 1), modulus=PHI_MINPOLY)
for _n in range(2, 7):
    CASES[f"lucas_sum_{_n}"] = dict(symbols=(t,), lhs=t ** _n + (1 - t) ** _n,
                                    rhs=_lucas(_n), modulus=PHI_MINPOLY)

_KEYS = list(CASES)
_OUT = Path(__file__).resolve().parent / "lean" / "RationalIdentityExt.lean"


def _family():
    return rational_identity_family(
        "RationalIdentityExt", (x,), GridSpec([("i", list(range(len(_KEYS))))]),
        lambda pt: _KEYS[pt["i"]], lambda pt: CASES[_KEYS[pt["i"]]])


def _validation():
    def off_by_a_thousandth():
        bad = rational_identity_family(
            "Bad", (x,), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: dict(lhs=1 / ((x + 1) * (x + 2)),
                            rhs=1 / (x + 1) - 1 / (x + 2) + sp.Rational(1, 1000),
                            domain={"x": -1}))
        try:
            certify(bad)
            raise AssertionError("partial fraction off by 1/1000 not refused")
        except CertificationError:
            pass

    def wrong_fibonacci():
        bad = rational_identity_family(
            "Bad2", (t,), GridSpec([("i", [0])]), lambda pt: "bad2",
            lambda pt: dict(lhs=t ** 5, rhs=5 * t + 4, modulus=PHI_MINPOLY))
        try:
            certify(bad)
            raise AssertionError("t^5 = 5t + 4 mod t^2 - t - 1 not refused")
        except CertificationError:
            pass

    def reducible_modulus():
        bad = rational_identity_family(
            "Bad3", (t,), GridSpec([("i", [0])]), lambda pt: "bad3",
            lambda pt: dict(lhs=t ** 2, rhs=1, modulus=t ** 2 - 1))
        try:
            certify(bad)
            raise AssertionError("reducible modulus not refused")
        except CertificationError:
            pass

    return ValidationReport.from_asserts([
        ("multivariate_identity_discriminates", off_by_a_thousandth),
        ("modular_remainder_audited", wrong_fibonacci),
        ("modulus_irreducibility_audited", reducible_modulus)])


def build() -> str:
    report = emit(certify(_family()), LeanProfile(namespace=("RationalIdentityExt",)),
                  [RationalIdentityEmitter()], _validation())
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: RationalIdentityExt.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
