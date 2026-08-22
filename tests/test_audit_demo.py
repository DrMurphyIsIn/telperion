"""The proof-auditor demo — Telperion as a referee for THIRD-PARTY Lean.

Demonstrates the empty-niche differentiator (roadmap Phase 3 definition-of-done):
run `audit` on externally-authored Lean and flag the meaning-level defects the
kernel cannot — on a defective sample, clean on a well-formed one.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.audit import audit_lean_text  # noqa: E402

_DEMO = Path(__file__).resolve().parents[1] / "examples" / "audit_demo"


def _audit(name):
    return audit_lean_text((_DEMO / name).read_text(encoding="utf-8"), path=name)


def test_clean_third_party_proof_passes():
    report = _audit("clean_proof.lean.txt")
    assert report.ok, report.render()
    assert report.findings == []


def test_defective_proof_flags_sorry_axiom_and_vacuity():
    report = _audit("defective_proof.lean.txt")
    assert not report.ok
    codes = {f.code for f in report.findings}
    assert "SORRY" in codes       # incomplete proof hole
    assert "AXIOM" in codes        # smuggled axiom
    assert "VACUOUS" in codes      # reflexive tautology the kernel can't catch


def test_vacuity_finding_names_the_offending_theorem():
    report = _audit("defective_proof.lean.txt")
    vac = [f for f in report.findings if f.code == "VACUOUS"]
    assert vac and vac[0].theorem == "main_result"
