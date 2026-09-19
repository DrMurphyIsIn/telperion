"""Generate the interval-Gram-inertia example: certify -> emit -> write.

    python examples/gram_inertia/generate.py           # write lean/RHInertia.lean + lean/GramInertia.lean
    python examples/gram_inertia/generate.py --check   # drift check (no write)

Four rational interval boxes, each certified to have ONE signature (p, q) shared by every real
symmetric matrix inside it.  The instances are the shapes the Mirrormere consumers actually hit:

  * ``inertia_pair_block_2``   -- the minimal defect-one rung: a 2x2 indefinite box, signature (1, 1).
    This is BraggDefect's hand-written 2x2 offline-pair block, now a generic instrument.
  * ``inertia_coupled_3``      -- a 3x3 box with a coupled positive block, signature (2, 1).
  * ``inertia_offline_pairs_4``-- a 4x4 block box with TWO independent negative directions,
    signature (2, 2) -- the ``offline_pairs_le_defect`` shape at n = 4.
  * ``inertia_fractional_3``   -- a 3x3 box with fractional midpoint and a tight width, signature
    (1, 2), exercising the narrow-margin end of the certificate.

The Lean prelude ``RHInertia.lean`` is emitted from the SAME module
(:func:`telperion.interval_gram_inertia_prelude_lean`), so the drift check covers it too: the bridge
lemmas and the instance file can never fall out of step.

conjecture1_proved = False -- a finite linear-algebra instrument; nothing here concerns zeta.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import (  # noqa: E402
    IntervalGramInertiaEmitter, ValidationReport, certify, emit,
    interval_gram_inertia_certificate, interval_gram_inertia_family,
    interval_gram_inertia_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_R = sp.Rational

# (midpoint, half-width, expected signature) -- the box is midpoint +- half-width entrywise.
_SPECS = {
    0: ([[1, 0], [0, -2]], _R(1, 10), (1, 1)),
    1: ([[2, 1, 0], [1, 2, 0], [0, 0, -3]], _R(1, 20), (2, 1)),
    2: ([[3, 1, 0, 0], [1, 3, 0, 0], [0, 0, -2, 1], [0, 0, 1, -2]], _R(1, 60), (2, 2)),
    3: ([[_R(1, 2), _R(1, 4), 0], [_R(1, 4), _R(-4, 3), 0], [0, 0, _R(-5, 6)]],
        _R(1, 100), (1, 2)),
}
_NAMES = {
    0: "inertia_pair_block_2",
    1: "inertia_coupled_3",
    2: "inertia_offline_pairs_4",
    3: "inertia_fractional_3",
}
_LEAN = Path(__file__).resolve().parent / "lean"
_OUT = _LEAN / "GramInertia.lean"
_PRELUDE_OUT = _LEAN / "RHInertia.lean"


def _box(case: int):
    mid, w, claimed = _SPECS[case]
    n = len(mid)
    lo = [[_R(mid[i][j]) - w for j in range(n)] for i in range(n)]
    hi = [[_R(mid[i][j]) + w for j in range(n)] for i in range(n)]
    return lo, hi, claimed


def build() -> str:
    fam = interval_gram_inertia_family(
        "GramInertia",
        GridSpec([("case", sorted(_SPECS))]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _box(pt["case"]),
    )
    checks = []
    for case in sorted(_SPECS):
        lo, hi, claimed = _box(case)
        cert = interval_gram_inertia_certificate(lo, hi, claimed)
        checks.append((f"signature_{_NAMES[case]}", (cert.p, cert.q) == claimed))
        checks.append((f"margin_{_NAMES[case]}", cert.margin_x > 0 and cert.margin_y > 0))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("GramInertia",), imports=("RHInertia",), prelude="open Matrix"),
        [IntervalGramInertiaEmitter()],
        ValidationReport(checks=tuple(checks)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    prelude = interval_gram_inertia_prelude_lean()
    if check:
        bad = []
        if not _PRELUDE_OUT.exists() or _PRELUDE_OUT.read_text(encoding="utf-8") != prelude:
            bad.append("RHInertia.lean")
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            bad.append("GramInertia.lean")
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
