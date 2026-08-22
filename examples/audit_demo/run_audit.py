"""Telperion as a referee for THIRD-PARTY Lean — the proof-auditor demo.

The Lean kernel rejects a *false* theorem, but a green build still hides
meaning-level defects: a `sorry` hole, a smuggled `axiom`, a `Prop := True` stub,
or a *vacuous* reflexive theorem (`42 = 42`) dressed up as a result. As the field
ships confident LLM-generated proofs, a machine-checkable referee for anyone's
Lean is an axis no frontier prover occupies.

    python examples/audit_demo/run_audit.py

Audits a clean sample (expected: clean) and a defective sample (expected: flagged
sorry / axiom / vacuity). Exit 0 iff the clean one passes and the defective one
is caught.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.audit import audit_lean_text  # noqa: E402

HERE = Path(__file__).resolve().parent


def _audit(name: str):
    return audit_lean_text((HERE / name).read_text(encoding="utf-8"), path=name)


def main() -> int:
    clean = _audit("clean_proof.lean.txt")
    defective = _audit("defective_proof.lean.txt")
    print("=== clean_proof.lean.txt ===")
    print(clean.render())
    print("\n=== defective_proof.lean.txt ===")
    print(defective.render())
    ok = clean.ok and not defective.ok
    print(
        f"\naudit demo: {'PASS' if ok else 'FAIL'} "
        f"(clean ok={clean.ok}, defective ok={defective.ok})"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
