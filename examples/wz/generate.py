"""Wilf–Zeilberger creative-telescoping certificates, compile-gated.

Certifies a hypergeometric / binomial sum identity `Σ_k F(n,k) = rhs(n)` from its
WZ mate `R(n,k)`, and ships the reusable telescoping-closure lemma
`Telperion.wz_row_invariant`.

Demonstration:
  * `Σ_k C(n,k) = 2ⁿ`, with WZ mate `R(n,k) = -k / (2(n−k+1))`.  The emitted
    theorem is the denominator-cleared WZ equation — a NON-VACUOUS `ring`
    polynomial identity (kept as distinct products so a wrong mate makes it a
    false identity `ring` rejects).

NEGATIVE CONTROL (in validation): the wrong mate `R ≡ 0` fails the WZ equation
and is refused at certification.

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
    GridSpec,
    LeanProfile,
    ValidationReport,
    WZ_PRELUDE,
    WZEmitter,
    certify,
    diff_frozen,
    emit,
    freeze,
    wz_family,
)

HERE = Path(__file__).resolve().parent
n, k = sp.symbols("n k")

F = sp.binomial(n, k)
R = -k / (2 * (n - k + 1))
RHS = 2 ** n


def _family():
    return wz_family("WZ", GridSpec([("i", [0])]), lambda pt: "binom_2n",
                     lambda pt: (F, R, RHS, n, k), n=n, k=k)


def build():
    return emit(certify(_family()),
                LeanProfile(namespace=("G1", "WZ"), prelude=WZ_PRELUDE),
                [WZEmitter()], _validation(), file_name="WZ.lean")


def _validation() -> ValidationReport:
    def discriminates():
        bad = wz_family("Bad", GridSpec([("i", [0])]), lambda pt: "bad",
                        lambda pt: (F, sp.Integer(0), RHS, n, k), n=n, k=k)
        try:
            certify(bad)
            raise AssertionError("wrong WZ mate was NOT refused")
        except CertificationError:
            pass
    return ValidationReport.from_asserts([("wz_discriminates", discriminates)])


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
    print(f"WZ: {res.n_theorems} Wilf–Zeilberger certificate(s) + row-invariant "
          f"lemma, hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
