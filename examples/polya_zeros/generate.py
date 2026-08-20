"""Pólya-with-zeros (Castle–Powers–Reznick 2011) certificates, compile-gated.

Proves `0 ≤ p` on `{xᵢ ≥ 0, Σxᵢ > 0}` from `(Σxᵢ)^N · p = Q` with every
Q-coefficient ≥ 0 — the HOMOGENEOUS Pólya lift, which (unlike lift.py's
inhomogeneous strict-only lift) tolerates zeros ON FACES.  CPR Theorem 2
characterizes exactly when such an exponent exists (zero set a union of
faces); the a = 2 tie `(x − y)²` — interior zero ray — admits none at any N.

Demonstrations:
  * `x² − xy + y²` at N = 1 (supplied):  (x+y)·p = x³ + y³;
  * `xy(x² − xy + y²)` (FINDER): zeros on BOTH faces — the tie-safe case —
    lifts at N = 1 to x⁴y + xy⁴;
  * CPR family `x² − (7/4)xy + y²` (FINDER): a = 7/4 near the a = 2 tie,
    needing a deeper lift (minimal exponent grows like 4/(2 − a)).

NEGATIVE CONTROLS (in validation): the CPR tie `(x − y)²` is refused WITH the
facial obstruction named; an insufficient exponent (N = 0 for a p needing
N = 1) is refused.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, PolyaZerosEmitter,
    ValidationReport, certify, diff_frozen, emit, freeze, polya_zeros_family,
)

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

# pt index -> (lean_name, p, N)   (N = None -> FINDER mode)
CASES = {
    0: ("polya_zeros_cauchy", x ** 2 - x * y + y ** 2, 1),
    1: ("polya_zeros_face_tie", x * y * (x ** 2 - x * y + y ** 2), None),
    2: ("polya_zeros_cpr_near_tie", x ** 2 - sp.Rational(7, 4) * x * y + y ** 2, None),
}


def _family():
    return polya_zeros_family(
        "PolyaZeros", (x, y), GridSpec([("i", [0, 1, 2])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2]),
        max_n=16)


def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "PolyaZeros")),
                [PolyaZerosEmitter()], _validation(), file_name="PolyaZeros.lean")


def _validation() -> ValidationReport:
    def tie_refused_with_reason():
        bad = polya_zeros_family(
            "Tie", (x, y), GridSpec([("i", [0])]), lambda pt: "tie",
            lambda pt: ((x - y) ** 2, None))
        try:
            certify(bad)
            raise AssertionError("the CPR tie (x-y)^2 was NOT refused")
        except CertificationError as e:
            assert "face" in str(e), f"refusal did not name the obstruction: {e}"

    def insufficient_exponent_refused():
        bad = polya_zeros_family(
            "LowN", (x, y), GridSpec([("i", [0])]), lambda pt: "low_n",
            lambda pt: (x ** 2 - x * y + y ** 2, 0))
        try:
            certify(bad)
            raise AssertionError("insufficient exponent N=0 was NOT refused")
        except CertificationError:
            pass

    return ValidationReport.from_asserts([
        ("polya_zeros_tie_refused_with_reason", tie_refused_with_reason),
        ("polya_zeros_insufficient_exponent_refused", insufficient_exponent_refused),
    ])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok:
            print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"PolyaZeros: {res.n_theorems} facial-positivity certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
