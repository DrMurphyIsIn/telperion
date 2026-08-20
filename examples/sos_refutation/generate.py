"""SOS-Positivstellensatz refutation certificates, compile-gated.

Proves a semialgebraic system is unsatisfiable OVER ℝ via -1 = σ₀ + Σσ_ig_i + Σλ_jh_j
(SOS σ), reaching systems infeasible only by positivity.

Demonstrations: `x² + 1 = 0` (σ₀ = x², λ = −1); `{x ≥ 0, x + 1 = 0}`.
NEGATIVE CONTROL: a certificate not equal to −1 -> refused.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, GridSpec, LeanProfile, SOSRefutationEmitter,
    ValidationReport, certify, diff_frozen, emit, freeze, sos_refutation_family)
HERE = Path(__file__).resolve().parent
x = sp.symbols("x")
CASES = {0: ("sos_ref_x2_plus_1", [(1, x)], [], [(x**2 + 1, -1, "he1")]),
         1: ("sos_ref_x_nonneg_and_x_plus_1", [], [(x, [(1, sp.Integer(1))], "hg1")],
             [(x + 1, -1, "he1")])}
def _family():
    return sos_refutation_family("SOSRef", (x,), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "SOSRef")),
        [SOSRefutationEmitter()], _validation(), file_name="SOSRefutation.lean")
def _validation():
    def d():
        bad = sos_refutation_family("Bad", (x,), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: ([(1, x)], [], [(x**2 + 1, 1, "he1")]))  # gives +1 not -1
        try: certify(bad); raise AssertionError("bad cert not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([("sos_ref_discriminates", d)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"SOSRefutation: {res.n_theorems} certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
