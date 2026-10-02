"""Generate the quadratic-sign-race example (eventual_threshold face).

    python examples/quadratic_sign_race/generate.py            # write lean/QuadraticSignRace.lean
    python examples/quadratic_sign_race/generate.py --check     # drift check (no write)

For ``P(m) = a·m² + b·m + c`` (rational coefficients) certify the exact sign
pattern on the integers ``m ≥ m0`` with no hypotheses: the vertex condition
``-b/(2a) ≤ m0`` (monotone on the range), the endpoint signs by ``norm_num``, and
the Taylor identity at the anchor by ``ring``.  Classical instances only:

  * m² − 10m − 7          : negative for 5 ≤ m ≤ 10, positive from 11 (sharp switch)
  * C(m,2) vs 3m + 20     : m(m−1)/2 − (3m + 20) = m²/2 − 7m/2 − 20 switches between
                            10 and 11 (the handshake count overtakes the linear budget)
  * m² − 3m + 1           : positive for all m ≥ 3
  * −m² − 8m − 17         : negative for all m ≥ −3

conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_eventual_threshold import (  # noqa: E402
    EventualThresholdEmitter,
    eventual_threshold_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    0: {"quadratic": ("1", "-10", "-7"), "m0": 5, "mode": "switch", "r": 10},
    1: {"quadratic": ("1/2", "-7/2", "-20"), "m0": 4, "mode": "switch", "r": 10},
    2: {"quadratic": ("1", "-3", "1"), "m0": 3, "mode": "positive"},
    3: {"quadratic": ("-1", "-8", "-17"), "m0": -3, "mode": "negative"},
}
_NAMES = {0: "sq_sub_10m_sub_7_switch", 1: "choose2_overtakes_3m_add_20",
          2: "sq_sub_3m_add_1_pos", 3: "neg_sq_sub_8m_sub_17_neg"}
_OUT = Path(__file__).resolve().parent / "lean" / "QuadraticSignRace.lean"


def build() -> str:
    fam = eventual_threshold_family(
        "QuadraticSignRace",
        GridSpec([("case", list(range(len(_SPECS))))]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("QuadraticSignRace",)),
        [EventualThresholdEmitter()],
        ValidationReport(checks=(("quadratic_sign_race", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: QuadraticSignRace.lean does not match regeneration")
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
