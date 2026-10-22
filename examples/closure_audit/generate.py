"""Generate the closure-audit example: two audit specs and their rendered Lean scripts.

    python examples/closure_audit/generate.py           # write lean/Audit*.lean + *.spec.json
    python examples/closure_audit/generate.py --check    # drift check (no write)

This is a pipeline TOOL example, not an emitter: nothing here certifies mathematics.  The
target library `lean/ClosureAuditExample/` is hand-written (four honest theorems in
Example.lean, a negative-control module Tainted.lean with an axiom, a `sorry` and a
`native_decide`).  The generated files are:

  lean/Audit.lean / audit.spec.json
      the audit of the four honest theorems with Tainted IMPORTED into the environment, so
      the absence check (no `ClosureAuditExample.Tainted` constant in the closure, no
      `sorryAx`) is real rather than vacuous; must PASS;
  lean/AuditTainted.lean / audit_tainted.spec.json
      the audit of the three tainted theorems; must FAIL (forbidden module in the closure,
      `sorryAx` present, axioms `fake_fact` / `sorryAx` / `Lean.ofReduceBool` not allowed).

Run them (after `lake build` in lean/):

  PYTHONPATH=src python -m telperion.cli audit-closure --project examples/closure_audit/lean \\
      --spec examples/closure_audit/audit.spec.json --json /tmp/audit.json
"""
import argparse
import json
import sys
from dataclasses import asdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.closure_audit import AuditSpec, render_audit_script  # noqa: E402

_HERE = Path(__file__).resolve().parent
_LEAN = _HERE / "lean"

CLEAN = AuditSpec(
    imports=("ClosureAuditExample.Example", "ClosureAuditExample.Tainted"),
    targets=(
        "ClosureAuditExample.prime_101",
        "ClosureAuditExample.two_le_of_prime",
        "ClosureAuditExample.sum_le",
        "ClosureAuditExample.smallPrimes_prime",
    ),
    scan_patterns=("sorry", "fake", "negcontrol"),
    absent_module_prefixes=("ClosureAuditExample.Tainted",),
)

TAINTED = AuditSpec(
    imports=("ClosureAuditExample.Tainted",),
    targets=(
        "ClosureAuditExample.NegControl.via_axiom",
        "ClosureAuditExample.NegControl.via_sorry",
        "ClosureAuditExample.NegControl.via_native",
    ),
    scan_patterns=("sorry", "fake", "negcontrol"),
    absent_module_prefixes=("ClosureAuditExample.Tainted",),
)

OUTPUTS = {
    _LEAN / "Audit.lean": lambda: render_audit_script(CLEAN),
    _HERE / "audit.spec.json": lambda: json.dumps(asdict(CLEAN), indent=2) + "\n",
    _LEAN / "AuditTainted.lean": lambda: render_audit_script(TAINTED),
    _HERE / "audit_tainted.spec.json": lambda: json.dumps(asdict(TAINTED), indent=2) + "\n",
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    args = ap.parse_args()

    drift = []
    for path, build in OUTPUTS.items():
        text = build()
        if args.check:
            current = path.read_text(encoding="utf-8") if path.exists() else ""
            if current != text:
                drift.append(path.name)
        else:
            path.write_text(text, encoding="utf-8")
            print(f"wrote {path}")
    if args.check:
        if drift:
            print(f"DRIFT: {drift} do not match the generator output")
            return 1
        print(f"check: OK ({len(OUTPUTS)} files, byte-identical)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
