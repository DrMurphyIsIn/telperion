"""Rational-function identity certificates, compile-gated.

Crystallized from the knapsack_sos Gram-bridge arc (2026-08-20): identities of
rational functions on a ray, emitted via ne-zero haves + field_simp + ring.

Demonstrations (both from the Grigoriev knapsack rank-1 decomposition):
  * g1 * v1 : n/(2(n-1)) * (n/2 - 1) = n(n-2)/(4(n-1))  on n > 3;
  * g2 form : n(n-2)/(4(n-1)(n-3)) = (n/(2(n-1))) * ((n-2)/(2(n-3)))  on n > 3.
NEGATIVE CONTROLS: a non-identity is refused; a denominator root above the
ray bound is refused.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, GridSpec, LeanProfile, RationalIdentityEmitter,
    ValidationReport, certify, diff_frozen, emit, freeze, rational_identity_family)
HERE = Path(__file__).resolve().parent
n = sp.symbols("n")
CASES = {
    0: ("rational_identity_g1v1",
        n / (2 * (n - 1)) * (n / 2 - 1), n * (n - 2) / (4 * (n - 1)), 3),
    1: ("rational_identity_g2_product",
        n * (n - 2) / (4 * (n - 1) * (n - 3)),
        (n / (2 * (n - 1))) * ((n - 2) / (2 * (n - 3))), 3),
}
def _family():
    return rational_identity_family("RationalIdentity", (n,),
        GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "RationalIdentity")),
        [RationalIdentityEmitter()], _validation(), file_name="RationalIdentity.lean")
def _validation():
    def not_identity():
        bad = rational_identity_family("Bad", (n,), GridSpec([("i", [0])]),
            lambda pt: "bad", lambda pt: (n / (n - 1), n / (n - 2), 3))
        try: certify(bad); raise AssertionError("non-identity not refused")
        except CertificationError: pass
    def root_above_ray():
        bad = rational_identity_family("Bad2", (n,), GridSpec([("i", [0])]),
            lambda pt: "bad2", lambda pt: (n / (n - 5), n / (n - 5), 3))
        try: certify(bad); raise AssertionError("root above ray not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([
        ("rational_identity_discriminates", not_identity),
        ("ray_domain_audited", root_above_ray)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"RationalIdentity: {res.n_theorems} certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
