"""Generate the anchored monotone extension example: certify -> emit -> write.

    python examples/anchored_monotone_extension/generate.py           # write lean/AnchoredMonotoneExtension.lean
    python examples/anchored_monotone_extension/generate.py --check   # drift check (no write)

(a) CLASSICAL: the hard-core (independent-set) partition function of a rooted tree.  With
q_b = Z(b, root unoccupied) / Z(b) and P = prod_c q_c over the children,

    Z_b(lam) = (prod_c Z_c(lam)) * (1 + lam P),        q_b = 1 / (1 + lam P),

(product mode).  The emitted theorems prove, for EVERY finite rooted tree b with n_b vertices:
  * Z_b is differentiable on [0, oo) and its log-derivative is the explicit recursion D_b;
  * lam D_b <= n_b lam/(1 + lam), so Z_b / (1 + lam)^{n_b} is ANTITONE on [0, oo);
  * from the anchor Z_b(0) = 1 (a node check), Z_b(lam) <= (1 + lam)^{n_b} for all lam >= 0.
This is the elementary bound "each vertex contributes at most a factor (1 + lam)"; the point
is the route (derivative recursion + two-row invariant + anchor), not the bound.

(b) SYNTHETIC matching-type SUM recursion with our own normalizer:

    R = sum_c y_c,   T_b(lam) = (prod_c T_c(lam)) * (1 + lam R),   y_b = 1 / (1 + lam R),

with the normalizer (1 + lam)^n on the threshold half-line [1, oo).  The node residual
x(1 + x)(1 + ax)(1 + a(x - 1)) is nonnegative exactly from x = 1 on (it fails for x < 1 at
large aggregate), so the threshold is exercised.  The anchor at lam = 1 is passed through as a
Lean HYPOTHESIS (the node check cannot hold: R is unbounded).

(a') The hard-core recursion again with the normalizer written ((1 + lam)^3)^(n/3) (rho = 1/3):
the same bound through a rational exponent (a real power) and the anchor node check
g(0, A)^3 <= psi(0).

Auxiliary invariant row in all three: mu = 1, kappa = -lam/(1 + lam), i.e. the root-deleted forest
obeys lam d/dlam log T(b - root) <= (n_b - 1) lam/(1 + lam).

Verified numerically first (all rooted trees with n <= 9, lam on a grid): see
tests/test_emit_anchored_monotone_extension.py.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_anchored_monotone_extension import (  # noqa: E402
    HARDCORE_CUBE_SPEC,
    HARDCORE_SPEC,
    MATCHING_SPEC,
    AnchoredMonotoneExtensionEmitter,
    anchored_monotone_extension_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {0: HARDCORE_SPEC, 1: MATCHING_SPEC, 2: HARDCORE_CUBE_SPEC}
_NAMES = {0: "hardcore", 1: "matching_sum", 2: "hardcore_cube_root"}
_OUT = Path(__file__).resolve().parent / "lean" / "AnchoredMonotoneExtension.lean"


def build() -> str:
    fam = anchored_monotone_extension_family(
        "AnchoredMonotoneExtension",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("AnchoredMonotoneExtension",)),
        [AnchoredMonotoneExtensionEmitter()],
        ValidationReport(checks=(("anchored_monotone_extension", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: AnchoredMonotoneExtension.lean does not match regeneration")
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
