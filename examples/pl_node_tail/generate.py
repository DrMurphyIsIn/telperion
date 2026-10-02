"""Generate the piecewise-linear node-condition tail example (monotone_tail face).

    python examples/pl_node_tail/generate.py            # write lean/PLNodeTail.lean
    python examples/pl_node_tail/generate.py --check     # drift check (no write)

Closes the two-parameter family ``m·U(y) + L(y) ≤ 0`` for all integers ``m ≥ M+1``
and all ``y ∈ (0, 1]`` in one step, from the node condition
``(M+1)·|U_i| ≥ s·(y_i − y†)`` at the piecewise-linear nodes beyond ``y†``.
Generic instances (small rational nodes, not from any application):

  * case 0: y† = 1/2, L(y) = log(1+y) − log(1+1/2) with tangent slope s = 2/3,
            nodes (1/4, 0), (1/2, −1/20), (3/4, −1/8), (1, −1/5), M = 1.
            M = 0 would be FALSE (m = 1, y = 1: −1/5 + log(4/3) > 0).
  * case 1: y† = 1/3, s = 3/4 (tangent of log(1+y) at 1/3), nodes (1/3, 0),
            (2/3, −1/40), (1, −1/30), M = 14 (the node at y = 1 binds: 15/30 ≥ 1/2).
  * case 2: the same nodes as case 0 with L abstract (the core theorem only).

For the log cases the emitter also discharges the L hypotheses and states a
hypothesis-free corollary for U = min(0, segment lines).

conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_monotone_tail import (  # noqa: E402
    MonotoneRatioTailEmitter,
    monotone_tail_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_NODES0 = [("1/4", "0"), ("1/2", "-1/20"), ("3/4", "-1/8"), ("1", "-1/5")]
_SPECS = {
    0: {"M": 1, "nodes": _NODES0, "y_dag": "1/2", "s": "2/3", "L": "log_tangent"},
    1: {"M": 14, "nodes": [("1/3", "0"), ("2/3", "-1/40"), ("1", "-1/30")],
        "y_dag": "1/3", "s": "3/4", "L": "log_tangent"},
    2: {"M": 1, "nodes": _NODES0, "y_dag": "1/2", "s": "2/3"},
}
_NAMES = {0: "pl_tail_log_half", 1: "pl_tail_log_third", 2: "pl_tail_abstract"}
_OUT = Path(__file__).resolve().parent / "lean" / "PLNodeTail.lean"


def build() -> str:
    fam = monotone_tail_family(
        "PLNodeTail",
        (),
        GridSpec([("case", list(range(len(_SPECS))))]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("PLNodeTail",)),
        [MonotoneRatioTailEmitter()],
        ValidationReport(checks=(("pl_node_tail", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: PLNodeTail.lean does not match regeneration")
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
