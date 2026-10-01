"""Generate the concave-pooled-induction EXTENSION example (2026-10-01): certify -> emit -> write.

    python examples/concave_pooled_induction/generate_ext.py           # write lean/ConcavePooledInductionExt.lean
    python examples/concave_pooled_induction/generate_ext.py --check   # drift check (no write)

Both extensions are backward compatible; the original example (``generate.py``) is untouched
apart from its input-hash header.  Four instances, all on the classical MATCHING MESSAGE
`y_leaf = 1`, `y_v = 1/(1 + sum_children y_c)` (see ``generate.py``):

* ``leaf_exempt_matched`` (LEAF-EXEMPT): profit `l(v) = -sum_{u in T_v} (1 - y_u)`, child
  count <= 2, alpha = 27/100.  For every NON-LEAF tree,
  `sum_u (1 - y_u) >= (27/100)|T| - 83/500`.  The one-vertex tree violates this bound
  (`0 < 27/100 - 83/500`), so no certificate that pools the leaves can prove it (its witness
  would need `U(1) >= 27/100`); with the leaves entering exactly the witness lives on the
  non-leaf message range [1/3, 3/4].  The emitted `*_leaf_breaks` lemma records the violation.
* ``leaf_exempt_flat``: the same recursion at alpha = 1/4 with the flat witness 1/12, TIGHT at
  the root with two leaf children (the negative-control twin).
* ``log_profit_density`` (LOG TERM IN g): profit `g = -1/(1+R) + (1/5) log(1 + R/2)`
  (synthetic), alpha = 1/2, every finite rooted tree (tail included): each log is replaced on
  every cell by its tangent majorant, the log constants enclosed by the mobius_tangent_cell
  Taylor box.
* ``leaf_exempt_log``: both at once (alpha = 1/5, flat witness 1/10, child count <= 2).

The claims were checked numerically on random trees first (tests/test_concave_pooled_ext.py).
HONEST SCOPE: dogfoods for the two extensions, not claimed new results.  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_concave_pooled_induction import (  # noqa: E402
    LEAF_EXEMPT_FLAT_SPEC,
    LEAF_EXEMPT_LOG_SPEC,
    LEAF_EXEMPT_SPEC,
    LOG_PROFIT_SPEC,
    ConcavePooledInductionEmitter,
    concave_pooled_induction_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {0: LEAF_EXEMPT_SPEC, 1: LEAF_EXEMPT_FLAT_SPEC, 2: LOG_PROFIT_SPEC,
          3: LEAF_EXEMPT_LOG_SPEC}
_NAMES = {0: "leaf_exempt_matched", 1: "leaf_exempt_flat", 2: "log_profit_density",
          3: "leaf_exempt_log"}
_OUT = Path(__file__).resolve().parent / "lean" / "ConcavePooledInductionExt.lean"


def build() -> str:
    fam = concave_pooled_induction_family(
        "ConcavePooledInductionExt",
        GridSpec([("case", [0, 1, 2, 3])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ConcavePooledInductionExt",)),
        [ConcavePooledInductionEmitter()],
        ValidationReport(checks=(("concave_pooled_induction_ext", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: ConcavePooledInductionExt.lean does not match regeneration")
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
