"""Generate the concave-pooled-induction example: certify -> emit -> write.

    python examples/concave_pooled_induction/generate.py           # write lean/ConcavePooledInduction.lean
    python examples/concave_pooled_induction/generate.py --check   # drift check (no write)

The classical MATCHING MESSAGE on rooted trees.  For the subtree `T_u` rooted at `u`, let
`Z` count matchings and `y_u = Z(T_u - u) / Z(T_u)`: the probability that `u` is unmatched
in a uniform random matching of `T_u`.  It obeys the tree recursion

    y_leaf = 1,     y_v = 1 / (1 + sum_{children c} y_c).

With profit `l(v) = -sum_{u in T_v} y_u` (so `g(m, R) = -1/(1+R)`, `l_leaf = -1`) and deficit
`alpha = 3/5`, the emitted theorems prove, for EVERY finite rooted tree `T`,

    sum_{u in T} y_u  >=  (3/5) |T| - U(y_root)  >=  (3/5) |T|,

by the concave witness `U` = interpolant of (0, 0), (1/2, -1/8), (1, -3/10), checked at the
pooled mean for child counts m = 1, 2 and by the one-variable tail for every m >= 3.  The
path shows the constant cannot exceed 1/phi = 0.618...; 3/5 leaves slack 0.018.

A second instance restricts the same recursion to child count <= 1 (paths): the
bounded-degree mode, no tail.  A third, clearly SYNTHETIC instance (no combinatorial meaning)
exercises an m-dependent message `h(m, R) = m / (m + 2R)` with a second denominator in
`g(m, R) = -1/(1+R)`, bounded child count <= 2, deficit 1/2.

Method: concave-witness induction, from unpublished work communicated by Professor John L.
Goldwasser.  This example is NOT the Brualdi-Goldwasser problem.

HONEST SCOPE: an inequality about the matching message on finite rooted trees, proved by a
kernel-checked certificate.  We know of no literature statement of this exact inequality; it
is a dogfood for the method, not a claimed new result.  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

# The `concave_pooled_induction` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_concave_pooled_induction import (  # noqa: E402
    MATCHING_DENSITY_SPEC,
    PATH_DENSITY_SPEC,
    ConcavePooledInductionEmitter,
    concave_pooled_induction_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

#: synthetic, for coverage of the m-dependent rendering (bounded degree, two denominators)
SYNTHETIC_MDEP_SPEC = dict(MATCHING_DENSITY_SPEC, h="m/(m+2*R)", g="-1/(1+R)",
                           alpha=sp.Rational(1, 2), M=2, tail=False)

#: synthetic REGRESSION instance for four rendering edge cases (2026-09-30): a single-piece witness
#: (`fin_cases` on one goal), R-free `h` and `g` (unused binders), an m-dependent denominator that
#: specialises to a constant other than 1 (`1 + m` at m = 1, formerly DROPPED from the closed form),
#: and identically-zero cell obligations (`rw` closes the goal itself).  The claim is true but trivial:
#: l(b) = -|b|, so l(b) + |b| = 0 <= U = 0.
SYNTHETIC_EDGE_SPEC = dict(nodes=[(0, 0), (1, 0)], h="1/(1+m)", g="-1", y_leaf=1, l_leaf=-1,
                           alpha=1, M=3, tail=False)

_SPECS = {0: MATCHING_DENSITY_SPEC, 1: PATH_DENSITY_SPEC, 2: SYNTHETIC_MDEP_SPEC,
          3: SYNTHETIC_EDGE_SPEC}
_NAMES = {0: "matching_density", 1: "path_density", 2: "synthetic_mdep", 3: "synthetic_edge"}
_OUT = Path(__file__).resolve().parent / "lean" / "ConcavePooledInduction.lean"


def build() -> str:
    fam = concave_pooled_induction_family(
        "ConcavePooledInduction",
        GridSpec([("case", [0, 1, 2, 3])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ConcavePooledInduction",)),
        [ConcavePooledInductionEmitter()],
        ValidationReport(checks=(("concave_pooled_induction", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: ConcavePooledInduction.lean does not match regeneration")
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
