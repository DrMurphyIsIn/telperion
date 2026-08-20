"""Constrained-SOS / Putinar-Positivstellensatz certificates, compile-gated.

Proves `0 ≤ p` on a basic closed semialgebraic set `{g_i ≥ 0}` from a Putinar
certificate `p = σ_0 + Σ σ_i·g_i` with each `σ_j` a sum of squares — the
constrained arm of real-algebraic positivity the unconstrained SOS emitter
cannot reach.

Demonstrations:
  * `0 ≤ x²·y + y` on `{y ≥ 0}`, via the SOS multiplier `σ = x² + 1`;
  * `0 ≤ x + y` on `{x ≥ 0, y ≥ 0}` (two constraints, trivial multipliers).

NEGATIVE CONTROL (in validation): a decomposition that fails to reconstruct `p`
is refused at certification — no Lean is emitted for a non-certificate.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    ConstrainedSOSEmitter,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
    putinar_family,
)

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

# pt index -> (lean_name, p, sigma0, constraints)
CASES = {
    0: ("putinar_x2y_plus_y", x ** 2 * y + y, [],
        [(y, [(1, x), (1, sp.Integer(1))], "hy")]),
    1: ("putinar_x_plus_y", x + y, [],
        [(x, [(1, sp.Integer(1))], "hx"), (y, [(1, sp.Integer(1))], "hy")]),
}


def _family():
    return putinar_family(
        "Putinar", (x, y), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))


def build():
    return emit(certify(_family()),
                LeanProfile(namespace=("G1", "Putinar")),
                [ConstrainedSOSEmitter()], _validation(),
                file_name="Putinar.lean")


def _validation() -> ValidationReport:
    def discriminates():
        # a certificate that does NOT reconstruct p is refused
        bad = putinar_family(
            "Bad", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (x ** 2 * y + y, [], [(y, [(1, x)], "hy")]))
        try:
            certify(bad)
            raise AssertionError("bad Putinar certificate was NOT refused")
        except CertificationError:
            pass
    return ValidationReport.from_asserts([("putinar_discriminates", discriminates)])


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
    print(f"Putinar: {res.n_theorems} constrained-SOS certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
