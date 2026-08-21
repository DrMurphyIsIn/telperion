"""Real-Nullstellensatz certificates, compile-gated.

Proves `p = 0` on the REAL variety of an ideal via p^(2m) + s = Σ h_k·g_k (s a sum
of squares) -- reaching real-vanishing that ordinary ideal membership misses.

Demonstrations: on the real variety of `x² + y²` (just the origin), both `x = 0`
and `y = 0`, via s = y² and s = x² respectively.
FINDER mode (sos = None): Telperion SEARCHES for (m, s) itself — Groebner normal
form of -p^(2m) + exact SOS decomposition (`find_real_nullstellensatz_certificate`,
sympy-only): re-finds s = y² for `x` on V(x²+y²), and escalates multiplicity to
m = 2 for `x` on V(x³) (x² ∉ ⟨x³⟩ but x⁴ = x·x³ is, s = 0).
NEGATIVE CONTROLS: p^(2m)+s not in the ideal -> refused; finder-mode p that does
NOT vanish on the real variety (x+1 at the origin) -> refused.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, GridSpec, LeanProfile, RealNullstellensatzEmitter,
    ValidationReport, certify, diff_frozen, emit, freeze, real_nullstellensatz_family)
HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")
CASES = {0: ("real_nss_x_zero", x, 1, [(1, y)], [x**2 + y**2]),
         1: ("real_nss_y_zero", y, 1, [(1, x)], [x**2 + y**2]),
         # FINDER mode (m = None, sos = None): Telperion searches for (m, s).
         2: ("real_nss_found_x_zero", x, None, None, [x**2 + y**2]),
         3: ("real_nss_found_mult2", x, None, None, [x**3])}
def _family():
    return real_nullstellensatz_family("RealNSS", (x, y), GridSpec([("i", [0, 1, 2, 3])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3], CASES[pt["i"]][4]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "RealNSS")),
        [RealNullstellensatzEmitter()], _validation(), file_name="RealNullstellensatz.lean")
def _validation():
    def d():
        bad = real_nullstellensatz_family("Bad", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (x, 1, [], [x**2 + y**2]))  # x^2 not in <x^2+y^2> (needs s=y^2)
        try: certify(bad); raise AssertionError("non-member not refused")
        except CertificationError: pass
    def d_finder():
        # x+1 does NOT vanish at the origin (= the real variety of x^2+y^2):
        # the finder must come back empty and certification must refuse.
        bad = real_nullstellensatz_family("BadF", (x, y), GridSpec([("i", [0])]), lambda pt: "badf",
            lambda pt: (x + 1, None, None, [x**2 + y**2]))
        try: certify(bad); raise AssertionError("finder-mode non-vanishing p not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([("real_nss_discriminates", d),
                                          ("real_nss_finder_discriminates", d_finder)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"RealNullstellensatz: {res.n_theorems} certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
