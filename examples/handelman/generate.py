"""Handelman-Positivstellensatz certificates on polytopes, compile-gated.

Proves `0 ≤ p` on a polytope `{ℓ_i ≥ 0}` from `p = Σ c_α ∏ ℓ_i^{α_i}` with every
`c_α ≥ 0` — a nonnegative combination of PRODUCTS of the linear constraints (the
LP-feasible, SDP-free polytope specialization of positivity).

Demonstrations:
  * `0 ≤ 1 − x²` on `{1 − x ≥ 0, 1 + x ≥ 0}`, via `(1−x)(1+x)`;
  * `0 ≤ x·y` on `{x ≥ 0, y ≥ 0}`, via the single product `x·y`.

NEGATIVE CONTROL (in validation): a combination that fails to reconstruct `p` is
refused at certification.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, HandelmanEmitter, LeanProfile,
    ValidationReport, certify, diff_frozen, emit, freeze, handelman_family,
)

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

# pt index -> (lean_name, p, constraints, terms)
CASES = {
    0: ("handelman_1_minus_x2", 1 - x ** 2,
        [(1 - x, "h1"), (1 + x, "h2")], [(1, (1, 1))]),
    1: ("handelman_xy", x * y,
        [(x, "hx"), (y, "hy")], [(1, (1, 1))]),
    # FINDER mode (terms = None): supply only the polytope, Telperion SEARCHES
    # for the certificate products.
    2: ("handelman_found_1mx2", 1 - x ** 2,
        [(1 - x, "h1"), (1 + x, "h2")], None),
    3: ("handelman_found_box", 2 - x ** 2 - y ** 2,
        [(1 - x, "ha"), (1 + x, "hb"), (1 - y, "hc"), (1 + y, "hd")], None),
}


def _family():
    return handelman_family(
        "Handelman", (x, y), GridSpec([("i", [0, 1, 2, 3])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))


def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "Handelman")),
                [HandelmanEmitter()], _validation(), file_name="Handelman.lean")


def _validation() -> ValidationReport:
    def discriminates():
        bad = handelman_family(
            "Bad", (x,), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (1 - x ** 2, [(1 - x, "h1")], [(1, (1,))]))  # (1-x) != 1-x^2
        try:
            certify(bad)
            raise AssertionError("bad Handelman certificate was NOT refused")
        except CertificationError:
            pass
    return ValidationReport.from_asserts([("handelman_discriminates", discriminates)])


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
    print(f"Handelman: {res.n_theorems} polytope certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
