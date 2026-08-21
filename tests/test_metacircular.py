"""B3 — meta-circular / trusted-floor study: point the audit calculus at the
audit checks THEMSELVES.

The reflexive layer catches meaning-level defects the kernel cannot.  But is the
layer itself faithful, and where is the irreducible trusted floor?  This module
answers both, honestly:

  * `probe_structural_nonvacuity` searches for a statement the STRUCTURAL
    non-vacuity check green-lights yet is semantically vacuous (a ring identity
    `lhs = rhs`, `lhs−rhs ≡ 0`).  It finds them — a LOCATED gap, exactly the
    class the SEMANTIC `assert_certificate_sensitive` layer exists to cover.
  * `check_metachecker_noncircular` proves the structural and semantic checks are
    genuinely independent layers (a separating witness exists), not circular.
  * `trusted_base` enumerates what remains irreducibly trusted — the kernel, the
    exact-decision primitives, and the (undecidable) statement-intent match: the
    Löb/Gödel floor self-application shrinks toward but cannot reach.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.verdict import Verdict  # noqa: E402
from telperion.metacircular import (  # noqa: E402
    tautology_probes,
    substantive_probes,
    is_ring_identity,
    probe_structural_nonvacuity,
    check_metachecker_noncircular,
    trusted_base,
)


def test_tautology_probes_are_genuinely_ring_identities():
    # the adversarial battery must be honest: each "vacuous" probe really is a
    # universally-true identity (lhs − rhs expands to 0).
    for p in tautology_probes():
        assert is_ring_identity(p), f"{p.name} is not actually a ring identity"


def test_substantive_probes_are_not_identities():
    for p in substantive_probes():
        assert not is_ring_identity(p), f"{p.name} should be a genuine claim"


def test_structural_nonvacuity_has_a_located_tautology_gap():
    # the structural check is syntactic (t ⋈ t); a ring identity lhs = rhs with
    # distinct sides slips past it. This is a LOCATED scope boundary, reported
    # honestly, not a silent bug.
    v = probe_structural_nonvacuity()
    assert v.verdict == Verdict.OBSTRUCTED_AND_LOCATED
    assert v.witnesses, "the gap must be exhibited with witnesses"


def test_structural_and_semantic_checks_are_noncircular():
    # a separating witness (structural accepts, yet semantically vacuous) proves
    # the two layers are independent — the semantic layer is not redundant.
    v = check_metachecker_noncircular()
    assert v.verdict == Verdict.VALIDATED


def test_trusted_base_names_kernel_and_the_undecidable_floor():
    base = trusted_base()
    text = " ".join(item.lower() for item in base)
    assert "kernel" in text
    assert "undecidab" in text or "intent" in text  # the Löb/Gödel floor
