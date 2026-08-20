"""Phase 3 proof-auditor: audit EXTERNALLY-authored Lean (e.g. an LLM prover's
output) for the "green build != proved" defects — sorry/axiom/empty-tactic/stub
(soundness lint) plus per-theorem vacuity (reflexive statements a mixed file can
smuggle past the wholly-vacuous check).

Value: as the field ships confident LLM-generated / self-verified proofs, a
machine-checkable referee for anyone's Lean is an axis no frontier prover occupies.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.audit import audit_lean_text  # noqa: E402

CLEAN = """
import Mathlib
namespace Ok
theorem t (u : ℝ) (hu : 0 ≤ u) : 0 ≤ u := hu
end Ok
"""

HAS_SORRY = """
import Mathlib
theorem t : 0 ≤ (1 : ℝ) := by sorry
"""

MIXED_VACUOUS = """
import Mathlib
theorem real_one (u : ℝ) (hu : 0 ≤ u) : 0 ≤ u := hu
theorem sneaky : (0 : ℝ) = 0 := rfl
"""


def test_audit_clean_proof_has_no_findings():
    report = audit_lean_text(CLEAN)

    assert report.ok is True
    assert report.findings == []


def test_audit_flags_sorry_as_error():
    report = audit_lean_text(HAS_SORRY)

    assert report.ok is False
    assert any(f.code == "SORRY" and f.severity == "error" for f in report.findings)


def test_audit_flags_per_theorem_vacuity_in_a_mixed_file():
    # one real theorem + one reflexive tautology: the wholly-vacuous check would
    # miss it, but the auditor must name the reflexive one.
    report = audit_lean_text(MIXED_VACUOUS)

    vac = [f for f in report.findings if f.code == "VACUOUS"]
    assert len(vac) == 1
    assert vac[0].theorem == "sneaky"
    assert report.ok is False
