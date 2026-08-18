"""p-adic valuation certificates — first-class family on the Brualdi-Goldwasser
23-structure.

The crux is the integer inequality N <= D for Phi^11 = N/D, and the whole
difficulty is the 23-cancellation count K = v_23(D) (D = 23^K * D0).  The 23's
enter as 621^(1+2c) = (3^3*23)^(1+2c) per node and cancel exactly at the tie.

This example promotes the former hand-assembled block to a first-class
valuation family flowing through:
    certify -> validate -> emit -> freeze
with byte-stable regeneration checked by --check.

The family covers a genuine per-node grid:
  grid axis 'node': 0 = root (cr=0, d=3), 1 = cherry child (cr=4, d=5),
                    2 = tree denominator (the product of all node factors)
Each node contributes one or two ValuationFact instances (numerator + denominator
coprimality / valuation).  The product fact (node=2) ties the node-by-node K
accounting to the actual tree denominator K = v_23(D) = 19.

Emitted theorems (all decidable, `norm_num`-closable):
  v23_<node>_num: coprimality (or numerator valuation) of the node factor numerator
  v23_<node>_den: valuation of the node factor denominator
  v23_tree_denominator: v_23 of the assembled tree Phi^11 denominator

The SPLIT_LEMMA and TELESCOPE_LEMMA primitives are included in the prelude.

HONEST SCOPE: these are 23-adic PRIMITIVES (the node-by-node cancellation
accounting).  This does NOT prove the Brualdi-Goldwasser inequality; that requires
an additional arithmetic step connecting the K account to the N/D bound.
conjecture1_proved=False.

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
    LeanProfile,
    ValuationFact,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
    padic_val,
)
from telperion.emit_padic import PadicValuationEmitter, valuation_family  # noqa: E402
from telperion.padic import SPLIT_LEMMA, TELESCOPE_LEMMA  # noqa: E402

HERE = Path(__file__).resolve().parent


# ---------------------------------------------------------------------------
# Tree arithmetic
# ---------------------------------------------------------------------------

def _node_factor(cr: int, d: int) -> Fr:
    """Per-node amplitude factor a_11 = (3/2)^(11cr) * (1+cr/(3d))^11 *
    (64/621)^(1+2cr) — the rational piece of each node's contribution to
    Phi^11 in the cavity recursion."""
    return (
        Fr(3, 2) ** (11 * cr)
        * (1 + Fr(cr, 3 * d)) ** 11
        * Fr(64, 621) ** (1 + 2 * cr)
    )


def _tree_denominator_23() -> tuple[int, int]:
    """A real (small) tree's Phi^11 = N/D; return (D, K=v23(D)).

    Tree: root (cr=0) with two cherry children (cr=4, no grandchildren).
    This is a K>0 (non-tie) configuration, illustrating how 23's accumulate
    in the denominator and the SPLIT_LEMMA / TELESCOPE_LEMMA primitives apply."""
    def rec(cr, kids):
        ch = [rec(*k) for k in kids]
        S = sum(m for m, _ in ch)
        d = len(kids) + 1 + cr
        z = Fr(3, 3 * d + cr)
        m = z / (1 + z * S)
        a11 = _node_factor(cr, d)
        p = a11 * (1 + z * S) ** 11
        for _, q in ch:
            p *= q
        return (m, p)
    _, phi11 = rec(0, [(4, []), (4, [])])
    D = phi11.denominator
    return D, padic_val(D, 23)


# The two distinct node types in the small tree and the assembled denominator:
#   node=0: root, cr=0, d=3 — factor 64/621; v23(num)=0, v23(den)=1
#   node=1: cherry child, cr=4, d=5 — factor has v23(den)=9 (appears twice)
#   node=2: tree denominator D — v23(D)=19 (telescoped from 1 + 2*9 - carry)
_NODE_PARAMS = {
    0: (0, 3),   # root
    1: (4, 5),   # cherry child (cr=4, d=1+4=5)
}

PRIME = 23


def _facts_for_node(pt: dict) -> list[ValuationFact]:
    """Return the ValuationFact list for grid point pt."""
    node = pt["node"]
    if node in _NODE_PARAMS:
        cr, d = _NODE_PARAMS[node]
        f = _node_factor(cr, d)
        num, den = f.numerator, f.denominator
        label = "root" if node == 0 else "child"
        k_num = padic_val(num, PRIME) if num % PRIME == 0 else 0
        k_den = padic_val(den, PRIME) if den % PRIME == 0 else 0
        return [
            ValuationFact(f"v23_{label}_num", num, PRIME, k_num),
            ValuationFact(f"v23_{label}_den", den, PRIME, k_den),
        ]
    else:
        # node == 2: tree denominator
        D, K = _tree_denominator_23()
        return [ValuationFact("v23_tree_denominator", D, PRIME, K)]


def _lean_name_for_node(pt: dict) -> str:
    node = pt["node"]
    if node == 0:
        return "padic_root_node"
    elif node == 1:
        return "padic_child_node"
    else:
        return "padic_tree_denom"


# ---------------------------------------------------------------------------
# Family + build
# ---------------------------------------------------------------------------

def _build_family():
    grid = GridSpec([("node", [0, 1, 2])])
    return valuation_family(
        name="PadicValuation",
        grid=grid,
        lean_name=_lean_name_for_node,
        facts=_facts_for_node,
        prime=PRIME,
    )


def _validation() -> ValidationReport:
    def valuations_exact():
        for pt in _build_family().grid.points():
            for f in _facts_for_node(pt):
                assert f.check(), (
                    f"FAILED: {f.name} claims v_{f.p}({f.n})={f.k}; "
                    f"engine says {padic_val(f.n, f.p)}"
                )
        # The split-lemma arithmetic content: v23(D)=K=19 means 23^19 divides D
        # and away from the tie 23^K dominates the 23-free part D0.
        D, K = _tree_denominator_23()
        assert K >= 1, "sample tree must be off the tie (K >= 1)"
        D0 = D // (PRIME ** K)
        assert PRIME ** K > D0, (
            f"SPLIT_LEMMA content: 23^{K} = {PRIME**K} must exceed D0 = {D0}"
        )

    return ValidationReport.from_asserts(
        [("padic_valuations_exact", valuations_exact)]
    )


def build():
    fam = _build_family()
    prof = LeanProfile(
        namespace=("G1", "Padic"),
        prelude=SPLIT_LEMMA + "\n" + TELESCOPE_LEMMA,
    )
    cf = certify(fam)
    vr = _validation()
    return emit(cf, prof, [PadicValuationEmitter()], vr,
                file_name="PadicValuation.lean")


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
    total_facts = sum(len(_facts_for_node(pt)) for pt in _build_family().grid.points())
    print(
        f"PadicValuation: {res.n_theorems} valuation theorems "
        f"({total_facts} facts across {_build_family().grid.size()} nodes), "
        f"hash {res.input_hash[:16]} (sample tree K=v23(D)={K})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
