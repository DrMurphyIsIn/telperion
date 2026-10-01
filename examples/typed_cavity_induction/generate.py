"""Generate the typed cavity induction example: certify -> emit -> write.

    python examples/typed_cavity_induction/generate.py           # write lean/TypedCavityInduction.lean
    python examples/typed_cavity_induction/generate.py --check   # drift check (no write)

THE BBG INSTANCES.  Balister, Bollobas and Gerke (J. Graph Theory 56 (2007) 270-286) bound the
generalized Randic index R_{-alpha} through half-trees: a half-tree is a rooted tree with one
dangling edge at the root (a planted rooted tree), and c_T = R_{-alpha}(T) - beta n(T) obeys
their recursion (2), c_T = sum_i (c_{T_i} + (d(v_0) d(v_i))^{-alpha}) - beta.  At
alpha = gamma = 1 a half-tree node with k children has degree d = k + 1, so with the message
y = 1/d the recursion is the typed-cavity recursion

    h(m, R) = 1/(m + 1),    g(m, R) = R/(m + 1) - beta,    leaf (y, l) = (1, -beta).

The types are the root degrees d = 1..Delta (d = 1 the exact leaf atom), the table is their
c_d of (4)-(5), and the theorem is their Lemma 4 for maximum degree Delta: c_T <= c_{d(T)}.
The join closes a tree at a vertex of degree Delta (their Theorem 6):
R_{-1}(T) <= beta_Delta n + (beta_Delta + Delta c_Delta)/(Delta - 1).  Two instances, at the
published constants beta_3 = 7/27 (Delta = 3) and beta_4 = 139/528 (Delta = 4); the hand-written
companion TypedCavityInductionRandic.lean restates both in terms of R_{-1} itself.

A third, SYNTHETIC instance (no combinatorial meaning) exercises message-sum bins, interval
messages (Bernstein cells), the tangent band and the analytic tail.

conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_typed_cavity_induction import (  # noqa: E402
    BBG3_SPEC,
    BBG4_SPEC,
    SYNTH_SPEC,
    TypedCavityInductionEmitter,
    typed_cavity_induction_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {0: BBG3_SPEC, 1: BBG4_SPEC, 2: SYNTH_SPEC}
_NAMES = {0: "bbg3", 1: "bbg4", 2: "synth"}
_OUT = Path(__file__).resolve().parent / "lean" / "TypedCavityInduction.lean"


def build() -> str:
    fam = typed_cavity_induction_family(
        "TypedCavityInduction",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("TypedCavityInduction",)),
        [TypedCavityInductionEmitter()],
        ValidationReport(checks=(("typed_cavity_induction", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: TypedCavityInduction.lean does not match regeneration")
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
