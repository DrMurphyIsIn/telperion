"""Generate the factored endpoint enclosure example: certify -> emit -> write.

    python examples/factored_endpoint_enclosure/generate.py           # write lean/FactoredEndpointEnclosure.lean
    python examples/factored_endpoint_enclosure/generate.py --check   # drift check (no write)

Every instance is an inequality ``0 <= F`` on a CLOSED box that touches the endpoint
``l = 0``, where ``F`` vanishes to order ``k`` and the quotient ``F / l^k`` (the quantity of
interest) has no interval enclosure.  The certificate factors ``l^k`` out of a polynomial
lower bound ``Q <= D F`` (Taylor with signed remainder for the log atoms) and checks the
cofactor ``H >= 0`` on boxes with exact rational Bernstein coefficients.  All instances are
classical or synthetic:

  * log_exp:   (1 + l)^(1/l) <= e near 0, as ``0 <= l - log(1 + l)`` on [0, 1/10], k = 1
               (quotient: ``(1/l) log(1 + l) <= 1``), order-3 upper bound for the log;
  * log_sharp: ``l - log(1 + l) >= (117/250) l^2`` on [0, 1/10], k = 2, order 5 (margin
               ~1/1000 at l = 1/10; its twin with 47/100 is the negative control);
  * rational:  ``(1 + l)^-2 >= 1 - 2l + 3l^2 - 4l^3`` on [0, 1], k = 4, closed form
               (no sin enclosure exists in Telperion, so this replaces sin(l)/l);
  * synth2:    the synthetic two-variable ``l (x - l)^2 + l^2 x >= 0`` on [0, 1/2] x [1/8, 1]
               (three boxes: the cover splits in x and in l);
  * pade:      the [2/1] Pade bound ``log(1 + l) <= l (6 + l)/(6 + 4 l)`` on [0, 1/3], tight to
               order 4 at 0, k = 4 (the case ``mobius_tangent_cell`` refuses).

conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_factored_endpoint_enclosure import (  # noqa: E402
    LOG_EXP_SPEC,
    LOG_SHARP_SPEC,
    PADE_SPEC,
    RATIONAL_SPEC,
    SYNTH2_SPEC,
    FactoredEndpointEnclosureEmitter,
    factored_endpoint_enclosure_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {0: LOG_EXP_SPEC, 1: LOG_SHARP_SPEC, 2: RATIONAL_SPEC, 3: SYNTH2_SPEC, 4: PADE_SPEC}
_NAMES = {0: "log_exp", 1: "log_sharp", 2: "rational", 3: "synth2", 4: "pade"}
_OUT = Path(__file__).resolve().parent / "lean" / "FactoredEndpointEnclosure.lean"


def build() -> str:
    fam = factored_endpoint_enclosure_family(
        "FactoredEndpointEnclosure",
        GridSpec([("case", list(_SPECS))]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("FactoredEndpointEnclosure",)),
        [FactoredEndpointEnclosureEmitter()],
        ValidationReport(checks=(("factored_endpoint_enclosure", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: FactoredEndpointEnclosure.lean does not match regeneration")
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
