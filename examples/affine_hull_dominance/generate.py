"""Generate the affine-hull-dominance example: certify -> emit -> write.

    python examples/affine_hull_dominance/generate.py           # write lean/AffineHullDominance.lean
    python examples/affine_hull_dominance/generate.py --check   # drift check (no write)

Three instances of the exact maximum over ALL trees on n vertices of a quantity given by a
positive multilinear tree recursion, certified by convex-hull pruning of the vector states:

* `matching_sum` (n <= 14): the Randic-weighted matching sum
      pi(T) = sum over matchings M of T of prod_{uv in M} 1 / (deg u * deg v)
  with branch state (Z, W): a vertex with c children has P = prod Z_i,
  Q = sum_i W_i prod_{j != i} Z_j, Z = P + Q/d, W = P/d (d = c + 1), and pi = P + Q/k at a root
  with k children.
* `randic_sum` (n <= 12): one plus the Randic-type edge sum, 1 + sum_{uv in E} 1/(deg u deg v),
  as a three-dimensional recursion (Z, W, V) = (1, edge sum inside the branch, 1/deg(root)).
* `synthetic` (n <= 12): a clearly SYNTHETIC recursion (no claimed combinatorial meaning) with
  larger hulls: the matching bilinear map with planting [[1, 2/(c+1)^2], [1/(c+2), 0]] and root
  covector (1, 2/k^2).

For each n = 2..N the Lean file proves `IsGreatest {pi T : T.size = n} M_n` and that every tree
attaining M_n has every branch state and partial bundle state on the kept hull points; every
listed maximizer (one rooting per isomorphism class) is checked to attain M_n.

HONEST SCOPE: finite, exact statements about explicit recursions; the recursion DEFINES the
quantity (that it equals the matching sum etc. is the classical cavity identity, not
formalized).  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

# The `affine_hull_dominance` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_affine_hull_dominance import (  # noqa: E402
    MATCHING_SUM_RECURSION,
    RANDIC_SUM_RECURSION,
    SYNTHETIC_RECURSION,
    AffineHullDominanceEmitter,
    affine_hull_dominance_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    0: dict(recursion=MATCHING_SUM_RECURSION, N=14,
            label="the Randic-weighted matching sum"),
    1: dict(recursion=RANDIC_SUM_RECURSION, N=12,
            label="one plus the Randic-type edge sum"),
    2: dict(recursion=SYNTHETIC_RECURSION, N=12,
            label="a synthetic recursion"),
}
_NAMES = {0: "matching_sum", 1: "randic_sum", 2: "synthetic"}
_OUT = Path(__file__).resolve().parent / "lean" / "AffineHullDominance.lean"


def build() -> str:
    fam = affine_hull_dominance_family(
        "AffineHullDominance",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("AffineHullDominance",)),
        [AffineHullDominanceEmitter()],
        ValidationReport(checks=(("affine_hull_dominance", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: AffineHullDominance.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
