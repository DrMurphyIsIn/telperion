"""Generate the scaled-interval-eval example: certify -> emit -> write.

    python examples/scaled_interval_eval/generate.py           # write lean/ScaledInterval.lean + lean/ScaledIntervalEval.lean
    python examples/scaled_interval_eval/generate.py --check   # drift check (no write)

Four instances at the default scale S = 10^40, each a kernel-checked real enclosure
``lo <= f <= hi`` whose every intermediate box is recomputed by ``decide +kernel``:

  * ``sie_exp_third``     -- exp(1/3) * (1/7) + 2/9 (a constant; exp with no reduction);
  * ``sie_cubic``         -- x^3 - 2x + 1/3 for every x in [1/3, 1/2] (a variable range);
  * ``sie_sinh_reduced``  -- exp(5/2) - exp(-5/2) (exp with argument reduction and squaring);
  * ``sie_exp_series``    -- sum_{j=0..6} exp(-j/4) x^j for every x in [0, 1/2] (a larger DAG,
    used for the per-node kernel timing in docs/SCALED_INTERVAL_EVAL_2026-10-09.md).

The prelude ``ScaledInterval.lean`` is emitted from the SAME module
(:func:`telperion.scaled_interval_prelude_lean`), so the drift check covers it too.  It is
adapted from OpenAI's openai/math ``WaveIntervals.lean`` (Apache-2.0); see its header.

conjecture1_proved = False -- enclosures of four explicit elementary expressions; nothing here
concerns zeta.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import (  # noqa: E402
    ScaledIntervalEvalEmitter, ValidationReport, certify, emit,
    scaled_interval_eval_certificate, scaled_interval_eval_family,
    scaled_interval_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
_PRELUDE_OUT = _LEAN / "ScaledInterval.lean"
_OUT = _LEAN / "ScaledIntervalEval.lean"

_R = sp.Rational
_x = sp.Symbol("x")

_SPECS = {
    0: ("sie_exp_third", dict(expr=sp.exp(_R(1, 3)) * _R(1, 7) + _R(2, 9))),
    1: ("sie_cubic", dict(expr=_x ** 3 - 2 * _x + _R(1, 3), vars={"x": ("1/3", "1/2")})),
    2: ("sie_sinh_reduced", dict(expr=sp.exp(_R(5, 2)) - sp.exp(-_R(5, 2)))),
    3: ("sie_exp_series", dict(expr=sum(sp.exp(-_R(j, 4)) * _x ** j for j in range(7)),
                               vars={"x": ("0", "1/2")})),
}


def build() -> str:
    fam = scaled_interval_eval_family(
        "ScaledIntervalEval",
        GridSpec([("case", sorted(_SPECS))]),
        lambda pt: _SPECS[pt["case"]][0],
        spec=lambda pt: dict(_SPECS[pt["case"]][1]),
    )
    checks = []
    for case in sorted(_SPECS):
        name, spec = _SPECS[case]
        spec = dict(spec)
        cert = scaled_interval_eval_certificate(spec.pop("expr"), **spec)
        lo, hi = cert.nodes[cert.root].box
        checks.append((f"root_box_ordered_{name}", lo <= hi))
        checks.append((f"claim_contains_box_{name}",
                       cert.claim_lo * cert.scale <= lo and hi <= cert.claim_hi * cert.scale))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ScaledIntervalEval",), imports=("ScaledInterval",)),
        [ScaledIntervalEvalEmitter()],
        ValidationReport(checks=tuple(checks)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    prelude = scaled_interval_prelude_lean()
    if check:
        bad = []
        if not _PRELUDE_OUT.exists() or _PRELUDE_OUT.read_text(encoding="utf-8") != prelude:
            bad.append("ScaledInterval.lean")
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            bad.append("ScaledIntervalEval.lean")
        if bad:
            print(f"DRIFT: {', '.join(bad)} do(es) not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _LEAN.mkdir(exist_ok=True)
    _PRELUDE_OUT.write_text(prelude, encoding="utf-8")
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_PRELUDE_OUT} ({len(prelude)} bytes) and {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
