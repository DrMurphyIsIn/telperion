"""p-adic valuation certificates, exercised on the Brualdi-Goldwasser 23-structure.

The crux is the integer inequality N <= D for Phi^11 = N/D, and the whole
difficulty is the 23-cancellation count K = v_23(D) (D = 23^K * D0).  The 23's
enter as 621^(1+2c) = (3^3*23)^(1+2c) per node and cancel exactly at the tie.

This example emits, and compile-gates:
  * concrete VALUATION FACTS v_23(n) = k for the structural constants (621, 64,
    the 23^11 injection at a near-star hub, and a real tree denominator D),
    each as decidable divisibility `23^k | n and not 23^(k+1) | n`;
  * the TELESCOPING primitive (Mathlib padicValRat.mul): v_p of a product is the
    sum of valuations -- the node-by-node accounting of K;
  * the VALUATION-MAGNITUDE SPLIT: N <= 23^K * D0 from a p-free bound plus
    23^K domination -- the bridge the rational machinery cannot state.

The exact Fraction engine (padic_val) is the untrusted generator; every fact is
re-derived there (`--check`) and the Lean kernel is the arbiter.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    ValuationFact,
    certify,
    diff_frozen,
    emit,
    freeze,
    padic_val,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402
from telperion.padic import SPLIT_LEMMA, TELESCOPE_LEMMA  # noqa: E402

HERE = Path(__file__).resolve().parent
import sympy as sp  # noqa: E402


def _tree_denominator_23() -> tuple[int, int]:
    """A real (small) tree's Phi^11 = N/D; return (D, K=v23(D)).  Tree: root with
    two children, each a single 4-cherry leaf — a K>0 (non-tie) configuration."""
    def rec(cr, kids):
        ch = [rec(*k) for k in kids]
        S = sum(m for m, _ in ch)
        d = len(kids) + 1 + cr
        z = Fr(3, 3 * d + cr)
        m = z / (1 + z * S)
        a11 = (Fr(3, 2) ** (11 * cr)) * (1 + Fr(cr, 3 * d)) ** 11 * (Fr(64, 621) ** (1 + 2 * cr))
        p = a11 * (1 + z * S) ** 11
        for _, q in ch:
            p *= q
        return (m, p)
    _, phi11 = rec(0, [(4, []), (4, [])])
    D = phi11.denominator
    return D, padic_val(D, 23)


def facts() -> list[ValuationFact]:
    D, K = _tree_denominator_23()
    return [
        ValuationFact("v23_621", 621, 23, 1),          # 621 = 3^3 * 23
        ValuationFact("v23_64", 64, 23, 0),            # coprime to 23
        ValuationFact("v23_hub_injection", 23 ** 11, 23, 11),  # near-star hub 3d+cr=23
        ValuationFact("v23_tree_denominator", D, 23, K),       # a real tree's K
    ]


def build():
    fs = facts()
    # emit the facts as a single hand-assembled block (they are standalone
    # theorems); the prelude carries the telescoping + split primitives.
    body = "".join(f.lean(tactic="norm_num") for f in fs)
    emitter = CustomAssemblyEmitter(
        statement_template="«facts»«branches»",
        branch_template="",
        fills=lambda fam: {"facts": body},
        branch_fills=lambda inst: {},
        theorems=len(fs),
    )
    prof = LeanProfile(
        namespace=("G1", "Padic"),
        prelude=SPLIT_LEMMA + "\n" + TELESCOPE_LEMMA,
    )
    return emit(certify(_trivial_family()), prof, [emitter], _validation(),
               file_name="PadicValuation.lean")


def _trivial_family() -> InequalityFamily:
    return InequalityFamily(
        name="PadicValuation",
        symbols=(),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "padic_root",
        target=lambda pt: sp.Integer(0),   # 0 >= 0, trivially certified
    )


def _validation() -> ValidationReport:
    def valuations_exact():
        for f in facts():
            assert f.check(), (f.name, f.n, f.k, padic_val(f.n, f.p))
        # the split lemma's arithmetic content, dual-checked: away from the tie
        # 23^K dominates any p-free magnitude bound C once C <= 23^K.
        D, K = _tree_denominator_23()
        assert K >= 1  # this tree is off the tie
        assert 23 ** K > D // (23 ** K)   # 23^K exceeds the 23-free part D0
    return ValidationReport.from_asserts([("padic_valuations_exact", valuations_exact)])


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
    D, K = _tree_denominator_23()
    print(f"PadicValuation: {res.n_theorems} valuation facts + split/telescope "
          f"primitives, hash {res.input_hash[:16]} (sample tree K=v23(D)={K})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
