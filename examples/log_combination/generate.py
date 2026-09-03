"""Generate the log-combination example: certify -> emit -> write.

    python examples/log_combination/generate.py            # write lean/LogCombination.lean
    python examples/log_combination/generate.py --check     # drift check (no write)

The F*-FOLDING companion to ``transcendental_enclosure``.  Certifies a rational
linear combination of logs-of-rationals bounded by a rational,

    Σ_i c_i · log(r_i)  ≤  q,

kernel-checked via Mathlib, by FOLDING the whole combination into a SINGLE log of
a rational ``Σ c_i·log(r_i) = log(∏ r_i^{c_i})`` and discharging by one of:

  * monotone route (q = 0): reduce to ``∏ r_i^{c_i} ≤ 1`` (a ``norm_num`` fact on
    integer powers after clearing denominators) + ``Real.log_le_log``.
  * tangent route (q > 0): ``log(∏) ≤ ∏ − 1`` (``Real.log_le_sub_one_of_pos``) +
    a ``norm_num`` fact ``∏ − 1 ≤ scale·q``.

Folding carries the exact cancellation, so the certificate is TIGHT AT THE TIE —
the tightness the BG ``transcendental_enclosure`` log face is missing.

DOGFOOD (cross-front port validation).  Instances 0 and 1 regenerate, in proof
structure, the two kernel-green BG theorems at
``proof/formalization/R3Cert/BGSCLSubaction.lean`` (``origin/bg/scl-on-main``):

  * log74_le_4fstar    : Real.log (7/4) ≤ 4 * FSTAR          (monotone route)
  * log54_sub_fstar_le : Real.log (5/4) − FSTAR ≤ 1/20       (tangent route)

with FSTAR := Real.log (621/64)/11 matching BGSCLInduction.  Instance 2 is a
generic non-BG reuse (2·log(3/2) ≤ log(9/4)) showing the same fold beyond BG.

conjecture1_proved=False.
"""
import argparse
import importlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


# The `log_combination` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_log_combination import (  # noqa: E402
    LogCombinationEmitter,
    log_combination_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# FSTAR prelude — matches R3Cert.BGSCLInduction so the dogfood statements match.
_FSTAR_PRELUDE = "noncomputable def FSTAR : ℝ := Real.log (621 / 64) / 11"

# spec: pt -> {"terms": [(c, r), (-k, fstar_base)], "q": ..., "route": ...}.
# Instance 0 (monotone, BG log74_le_4fstar): 1·log(7/4) − 4·FSTAR ≤ 0.
# Instance 1 (tangent,  BG log54_sub_fstar_le): 1·log(5/4) − 1·FSTAR ≤ 1/20.
# Instance 2 (generic reuse, N=1): 2·log(3/2) − 1·log(9/4) ≤ 0.
_SPECS = {
    0: {"terms": [(1, "7/4"), (-4, "621/64")], "q": "0", "route": "monotone"},
    1: {"terms": [(1, "5/4"), (-1, "621/64")], "q": "1/20", "route": "tangent"},
    2: {"terms": [(2, "3/2"), (-1, "9/4")], "q": "0", "route": "monotone",
        "fstar_base": "9/4", "fstar_den": 1},
    # Corrected-witness cells (2026-09-03): a tighter k=1 tangent and a GENERAL-k
    # tangent with a NEGATIVE threshold — the capability the corrected BG 5-case
    # witness (ρ(4)≠0) surfaced. Both build GREEN against R3Cert.BGSCLInduction
    # (proof/formalization/R3Cert/BGSCLSubactionCells.lean).
    3: {"terms": [(1, "5/4"), (-1, "621/64")], "q": "1/40", "route": "tangent"},
    4: {"terms": [(1, "7/4"), (-4, "621/64")], "q": "-1/2688", "route": "tangent"},
}
_NAMES = {0: "log74_le_4fstar", 1: "log54_sub_fstar_le", 2: "log32_sq_le_log94",
          3: "log54_sub_fstar_le_40", 4: "log74_le_4fstar_broom"}
_OUT = Path(__file__).resolve().parent / "lean" / "LogCombination.lean"


def build() -> str:
    fam = log_combination_family(
        "LogCombination",
        GridSpec([("case", [0, 1, 2, 3, 4])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("LogCombination",), prelude=_FSTAR_PRELUDE),
        [LogCombinationEmitter()],
        ValidationReport(checks=(("log_combination", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: LogCombination.lean does not match regeneration")
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
