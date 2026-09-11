"""Workspace layout, scratch Lean projects, lift scaffolding."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.workspace import (  # noqa: E402
    PLATFORM_TOOLCHAIN,
    Workspace,
)


def test_ensure_layout_creates_dirs_and_gitignores_secrets(tmp_path):
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    for d in ("Definitions", "Theorems", "Solutions", "attempts"):
        assert (tmp_path / "wsp" / d).is_dir()
    gi = (tmp_path / "wsp" / ".gitignore").read_text()
    assert "credentials.json" in gi and "telperion_tokens.json" in gi


def test_scratch_project_pins_platform_toolchain(tmp_path):
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    proj = ws.scratch_project("M123", toolchain=PLATFORM_TOOLCHAIN,
                              mathlib_rev="v4.33.1")
    assert (proj / "lean-toolchain").read_text().strip() == PLATFORM_TOOLCHAIN
    lakefile = (proj / "lakefile.toml").read_text()
    assert 'rev = "v4.33.1"' in lakefile and "mathlib" in lakefile


def test_scaffold_lift_embeds_verbatim_statement(tmp_path):
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    stmt = "theorem solution : ∀ x : ℚ, 0 ≤ x^2 := by sorry"
    fam = ws.scaffold_lift("mile42", stmt, name="M42")
    text = fam.read_text()
    assert stmt in text                       # verbatim, for faithfulness review
    assert "InequalityFamily" in text
    assert "mile42" in text


def test_scratch_project_defaults_to_platform_mathlib_rev(tmp_path):
    """Test that default mathlib_rev is the commit SHA, not the tag."""
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    proj = ws.scratch_project("MDef")  # No explicit mathlib_rev
    lakefile = (proj / "lakefile.toml").read_text()
    # The default should be the platform commit SHA, not the tag
    assert '0df444a360eaa60ab8c11dca51a86af692955474' in lakefile
