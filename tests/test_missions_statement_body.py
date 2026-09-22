"""`_build_body` must not append a second proof body to a declaration that has one.

The old test was `endswith(":= by sorry") or endswith(":= sorry")`, which recognises
only the two one-line spellings.  A statement whose declaration already carried a
multi-line proof got a SECOND one appended, producing the nonsense `sorry := by sorry`.
That happened live while authoring MM_leakage_composite_zero, and the malformed module
had to be re-added from the bare declaration.

The detection is scoped to the LAST declaration on purpose.  A statement module may open
with local `def`s, each carrying its own `:=`, before the theorem it exists to state.
"""
import pytest

from telperion.missions.statements import _build_body, _last_declaration_has_proof


@pytest.mark.parametrize("src", [
    "theorem t : 1 = 1 := by sorry",
    "theorem t : 1 = 1 := sorry",
    "theorem t : 1 = 1 := by\n  simp\n  sorry",
    "theorem t : 1 = 1 := by\n  constructor\n  · exact rfl",
    "def f : Nat := 3\n\ntheorem t : f = 3 := by rfl",
])
def test_an_existing_proof_body_is_left_alone(src):
    assert _last_declaration_has_proof(src)
    out = _build_body(src)
    assert out.rstrip() == src.rstrip()
    assert "sorry := by sorry" not in out


@pytest.mark.parametrize("src", [
    "theorem t : 1 = 1",
    "def f : Nat := 3\n\ntheorem t : f = 3",
    "theorem t (h : Nat := 3) : 1 = 1",
    "theorem t (p : Nat × Nat) : p = ⟨p.1, p.2⟩",
])
def test_a_bare_declaration_gets_exactly_one_suffix(src):
    assert not _last_declaration_has_proof(src)
    out = _build_body(src)
    assert out.rstrip().endswith(":= by sorry")
    assert out.count(":= by sorry") == 1


def test_a_binder_default_is_not_a_proof_body():
    """`(h : Nat := 3)` is a default argument, not a proof.  Depth must be tracked."""
    assert not _last_declaration_has_proof("theorem t (h : Nat := 3) : 1 = 1")


def test_local_defs_do_not_satisfy_the_theorem():
    """The `:=` of a leading `def` must not be mistaken for the theorem's proof."""
    src = "def f : Nat := 3\ndef g : Nat := 4\n\ntheorem t : f = 3"
    assert not _last_declaration_has_proof(src)
    assert _build_body(src).rstrip().endswith("theorem t : f = 3 := by sorry")


def test_a_commented_out_assignment_is_not_a_proof_body():
    assert not _last_declaration_has_proof("theorem t : 1 = 1\n-- was := by simp")
    assert not _last_declaration_has_proof("theorem t : 1 = 1\n/- := by simp -/")


def test_the_reported_malformation_cannot_be_produced():
    """The exact live symptom: a statement ending in `sorry` gaining ` := by sorry`."""
    out = _build_body("theorem t : 1 = 1 := by\n  sorry")
    assert "sorry := by sorry" not in out
