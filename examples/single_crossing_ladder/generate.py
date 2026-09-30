"""Generate the single-crossing ladder example: certify -> emit -> write.

    python examples/single_crossing_ladder/generate.py           # write lean/SingleCrossingLadder.lean
    python examples/single_crossing_ladder/generate.py --check   # drift check (no write)

THE ARM LADDER.  An arm with j cherries (2j+1 vertices) has matching-sum weight
T(A_j) = c^j (1 + lambda j / ((j+1)(2+lambda))), c = 1 + lambda/2, at activity lambda, so its
per-vertex log-weight is

    F_j(lambda) = [j log((2+lambda)/2) + log((j+1 + lambda j/(2+lambda))/(j+1))] / (2j+1)
                = ((j-1)/(2j+1)) log(1 + lambda/2) + (1/(2j+1)) log(1 + (2j+1)/(2j+2) lambda).

The emitted theorems prove, for members j = 1..7 on lambda in [0, oo):
  * F_1 < F_2 < F_3 everywhere on (0, oo) (arms 1 and 2 are never best);
  * F_j and F_{j+1} cross EXACTLY ONCE, for j = 3..6, at lambda_j in the brackets
    (0.43050, 0.43051), (0.87247, 0.87248), (1.19239, 1.19240), (1.43559, 1.43560);
  * the breakpoints increase, and on (lambda_{j-1}, lambda_j) the arm A_j is the UNIQUE best
    of A_1..A_7 (A_3 on (0, lambda_3), A_7 beyond lambda_6).

A second, SYNTHETIC instance (no combinatorial meaning) exercises the bounded domain
S = [0, 2] and negative log coefficients: D = -log(1+x) + (3/2) log(1+x/10) + (1/2) log(1+2x)
crosses zero once on [0, 2] (it crosses AGAIN near 4.3, which is why the domain is bounded;
on [0, oo) the certificate is refused, and the forged unbounded claim is kernel-rejected).

HONEST SCOPE: the ladder over the finite window of members; that no arm beyond the window
wins on these intervals needs the separate unimodality of j -> F_j, which is not certified
here.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_single_crossing_ladder import (  # noqa: E402
    ARM_LADDER_SPEC,
    DOUBLE_DIP_BOUNDED_SPEC,
    SingleCrossingLadderEmitter,
    single_crossing_ladder_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {0: ARM_LADDER_SPEC, 1: DOUBLE_DIP_BOUNDED_SPEC}
_NAMES = {0: "arm_ladder", 1: "double_dip_bounded"}
_OUT = Path(__file__).resolve().parent / "lean" / "SingleCrossingLadder.lean"


def build() -> str:
    fam = single_crossing_ladder_family(
        "SingleCrossingLadder",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("SingleCrossingLadder",)),
        [SingleCrossingLadderEmitter()],
        ValidationReport(checks=(("single_crossing_ladder", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: SingleCrossingLadder.lean does not match regeneration")
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
