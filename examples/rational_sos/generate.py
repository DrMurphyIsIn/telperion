"""Rational-SOS (Artin denominator) certificates, compile-gated.

Proves `0 <= p` for polynomials that are NONNEGATIVE but NOT sums of squares --
the class the plain SOS emitter cannot reach (Hilbert). Artin: multiply by a
strictly-positive q to make q*p a sum of squares. Telperion FINDS q (a ladder of
positivity-provable strictly-positive multipliers) and the SOS via the SDP.

Needs cvxpy (`sdp` verify group; frozen Lean compile-gated in audit-compiles).

Demonstration (auto-found): the Motzkin polynomial
x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1 >= 0, via q = (1+x^2)(1+y^2).
NEGATIVE CONTROL: x^2 - 2 is negative near 0 -> refused.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, GridSpec, LeanProfile, RationalSOSEmitter,
    ValidationReport, certify, diff_frozen, emit, freeze, rational_sos_family)
HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")
MOTZKIN = x**4*y**2 + x**2*y**4 - 3*x**2*y**2 + 1
def _family():
    return rational_sos_family("RationalSOS", (x, y), GridSpec([("i", [0])]),
        lambda pt: "rational_sos_motzkin", lambda pt: (MOTZKIN, None, None))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "RationalSOS")),
        [RationalSOSEmitter()], _validation(), file_name="RationalSOS.lean")
def _validation():
    def d():
        bad = rational_sos_family("Bad", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (x**2 - 2, None, None))
        try: certify(bad); raise AssertionError("negative poly not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([("rational_sos_discriminates", d)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"RationalSOS: {res.n_theorems} Artin certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
