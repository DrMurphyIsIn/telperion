"""Generate the Bohr-Mollerup Gamma-ratio example: certify -> emit -> write.

    python examples/bohr_mollerup_gamma_ratio/generate.py           # write lean/BohrMollerupPrelude.lean + lean/BohrMollerupGammaRatio.lean
    python examples/bohr_mollerup_gamma_ratio/generate.py --check   # drift check (no write)

Three kernel-checked enclosures ``LO <= Real.Gamma x1 / Real.Gamma x2 <= HI`` at a SMALL shift
``n = 400`` (two blocks of 200; the hand-built CN-1 instance used n = 8000 for four digits):

  * ``gamma_3_8_over_7_8``  -- Gamma(3/8) / Gamma(7/8)  (the CN-1 constant, 2.17540591...);
  * ``gamma_1_3_over_2_3``  -- Gamma(1/3) / Gamma(2/3)  (1.97836...);
  * ``gamma_1_2_over_1_4``  -- Gamma(1/2) / Gamma(1/4)  (0.48887...; distinct denominators, so the
    exact product runs over the common denominator 4 while the brackets use 1/2 and 1/4).

The claims are the certified rational bounds rounded outward to the enclosure's decimal
resolution; the generator REFUSES (exit code 1, a ValueError from certify) any claim the exact
kernel comparisons do not imply, so a false enclosure is never written.

The prelude ``BohrMollerupPrelude.lean`` is emitted from the SAME module
(:func:`telperion.bohr_mollerup_prelude_lean`), so the drift check covers it too.

conjecture1_proved = False -- enclosures of three ratios of Gamma values; nothing here concerns
class numbers or zeta.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    BohrMollerupGammaRatioEmitter, ValidationReport, certify, emit,
    bohr_mollerup_gamma_ratio_certificate, bohr_mollerup_gamma_ratio_family,
    bohr_mollerup_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
_PRELUDE_OUT = _LEAN / "BohrMollerupPrelude.lean"
_OUT = _LEAN / "BohrMollerupGammaRatio.lean"

_N = 400

_SPECS = {
    0: ("gamma_3_8_over_7_8", dict(x1="3/8", x2="7/8", n=_N)),
    1: ("gamma_1_3_over_2_3", dict(x1="1/3", x2="2/3", n=_N)),
    2: ("gamma_1_2_over_1_4", dict(x1="1/2", x2="1/4", n=_N)),
}


def build() -> str:
    fam = bohr_mollerup_gamma_ratio_family(
        "BohrMollerupGammaRatio",
        GridSpec([("case", sorted(_SPECS))]),
        lambda pt: _SPECS[pt["case"]][0],
        spec=lambda pt: dict(_SPECS[pt["case"]][1]),
    )
    checks = []
    for case in sorted(_SPECS):
        name, spec = _SPECS[case]
        cert = bohr_mollerup_gamma_ratio_certificate(**spec)
        checks.append((f"enclosure_ordered_{name}", cert.lo <= cert.hi))
        checks.append((f"claim_contains_enclosure_{name}",
                       cert.claim_lo <= cert.lo and cert.hi <= cert.claim_hi))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BohrMollerupGammaRatio",), imports=("BohrMollerupPrelude",)),
        [BohrMollerupGammaRatioEmitter()],
        ValidationReport(checks=tuple(checks)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    prelude = bohr_mollerup_prelude_lean()
    if check:
        bad = []
        if not _PRELUDE_OUT.exists() or _PRELUDE_OUT.read_text(encoding="utf-8") != prelude:
            bad.append("BohrMollerupPrelude.lean")
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            bad.append("BohrMollerupGammaRatio.lean")
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
