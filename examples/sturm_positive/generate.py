"""Sturm strict-interval positivity, compile-gated.

Proves `0 < p(x)` on a closed interval `[a,b]` -- STRICT positivity / root
exclusion. The Sturm sequence is the exact decision oracle (certifies p has no
root in [a,b]); the Lean proof combines a Bernstein certificate for p - gamma >= 0
(gamma a rational floor) with 0 < gamma.

Demonstrations: 0 < x^2 + 1 on [-2,2]; 0 < x^2 - 3x + 3 on [0,3];
0 < (x-2)(x-5) + 1 on [6,10].
NEGATIVE CONTROL: (x-3)^2 has a root at 3 in [2,4] -> refused (not strict).
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, GridSpec, LeanProfile, SturmPositiveEmitter,
    ValidationReport, certify, diff_frozen, emit, freeze, sturm_positive_family)
HERE = Path(__file__).resolve().parent
x = sp.symbols("x")
CASES = {
    0: ("sturm_x2_plus_1", x**2 + 1, -2, 2),
    1: ("sturm_x2_minus_3x_plus_3", x**2 - 3*x + 3, 0, 3),
    2: ("sturm_shifted_parabola", (x-2)*(x-5) + 1, 6, 10),
}
def _family():
    return sturm_positive_family("SturmPositive", (x,), GridSpec([("i", [0, 1, 2])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "SturmPositive")),
        [SturmPositiveEmitter()], _validation(), file_name="SturmPositive.lean")
def _validation():
    def d():
        bad = sturm_positive_family("Bad", (x,), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: ((x-3)**2, 2, 4))
        try: certify(bad); raise AssertionError("root-in-interval not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([("sturm_discriminates", d)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"SturmPositive: {res.n_theorems} strict-interval certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
