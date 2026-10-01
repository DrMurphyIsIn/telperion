"""Generate the mobius_tangent_cell dogfood: certify -> emit -> write.

    python examples/mobius_tangent_cell/generate.py           # write lean/MobiusTangentCell.lean
    python examples/mobius_tangent_cell/generate.py --check   # drift check (no write)

Four one-variable inequalities "linear + concave logs + one Mobius term <= 0", each
certified by tangent-line cells with a convex majorant checked at the two cell endpoints
(from unpublished work communicated by J. L. Goldwasser):

* `pade_log1p`:  log(1 + x) <= x (6 + x) / (6 + 4 x) on [1/4, 1]  (the [2/1] Pade bound;
  F = log(1 + x) - x/4 - 9/8 + 27/(24 + 16 x), Mobius coefficient > 0: convex case).
  NOT on [0, 1/4): F vanishes to order 4 at x = 0 while the tangent majorant loses a
  quadratic term, so no cell containing 0 can pass (the generator refuses there).
* `logmean_lower`: log x <= 2 (x - 1) / (x + 1) on [1/10, 1/2]  (the logarithmic-mean
  bound on (0, 1]; F = log x - 2 + 4/(x + 1), convex case; the tangent arguments are
  < 2/3, exercising the `log u = log v - n log 2` split).  Not up to x = 1, where it is
  tight to order 3.
* `concave_mobius`: log(1/4 + x) + (1/2) log(3 + x) <= x + 1/(2 (1 + x)) - 8/25 on [0, 2]
  -- a SYNTHETIC coverage instance (true with margin ~0.012), chosen to exercise two log
  terms and a NEGATIVE Mobius coefficient in F (the concave case, replaced by its tangent).
* `no_mobius`: log(1 + x) <= (9/10) x + 1/10 on [-1/2, 1/2] -- a SYNTHETIC coverage instance
  for the sigma = 0 mode (no Mobius term) and the `Real.log_one` constant (tangent at u = 1).
* `zhu_band0`: log(t/2) - 1/t <= 1243/2000 on [15/4, 23/5] -- the first band of the digamma
  envelope of Zhu, arXiv:2608.24827, Lemma 3.1 (see rvm_bridge/lean/ZhuEnvelope.lean, rhs_0),
  over the whole band.  REGRESSION instance (2026-09-30): the sides front-end used to split
  log(t/2) into log t - log 2 and refuse the constant; it now keeps each log atom whole.

HONEST SCOPE: elementary one-variable real inequalities; conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_mobius_tangent_cell import (  # noqa: E402
    MobiusTangentCellEmitter,
    mobius_tangent_cell_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

x = sp.Symbol("x")
_R = sp.Rational
_SPECS = {
    0: {"lhs": sp.log(1 + x), "rhs": x * (6 + x) / (6 + 4 * x), "var": x,
        "p": "1/4", "q": "1"},
    1: {"lhs": sp.log(x), "rhs": 2 * (x - 1) / (x + 1), "var": x,
        "p": "1/10", "q": "1/2"},
    2: {"lhs": sp.log(_R(1, 4) + x) + _R(1, 2) * sp.log(3 + x),
        "rhs": x + 1 / (2 * (1 + x)) - _R(8, 25), "var": x, "p": "0", "q": "2"},
    3: {"lhs": sp.log(1 + x), "rhs": _R(9, 10) * x + _R(1, 10), "var": x,
        "p": "-1/2", "q": "1/2"},
    4: {"lhs": sp.log(x / 2) - 1 / x, "rhs": _R(1243, 2000), "var": x,
        "p": "15/4", "q": "23/5"},
}
_NAMES = {0: "pade_log1p", 1: "logmean_lower", 2: "concave_mobius", 3: "no_mobius",
          4: "zhu_band0"}
_OUT = Path(__file__).resolve().parent / "lean" / "MobiusTangentCell.lean"


def build() -> str:
    fam = mobius_tangent_cell_family(
        "MobiusTangentCell",
        GridSpec([("case", [0, 1, 2, 3, 4])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("MobiusTangentCell",)),
        [MobiusTangentCellEmitter()],
        ValidationReport(checks=(("mobius_tangent_cell", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: MobiusTangentCell.lean does not match regeneration")
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
