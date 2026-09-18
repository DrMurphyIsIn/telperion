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
    assert "credentials.json" in gi and "telperion_tokens.json" in gi and ".lake/" in gi


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


def test_scaffold_lift_generated_python_is_syntactically_valid(tmp_path):
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    fam = ws.scaffold_lift("mile99", "theorem foo : True := trivial", name="Foo")
    compile(fam.read_text(), str(fam), "exec")  # raises SyntaxError on failure


# --- F8: scaffold_lift overwrite guard ---

def test_scaffold_lift_raises_file_exists_error_on_overwrite(tmp_path):
    """scaffold_lift raises FileExistsError when family.py already exists."""
    import pytest
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    ws.scaffold_lift("mile1", "theorem solution : True := trivial", name="M1")
    with pytest.raises(FileExistsError, match="already exists"):
        ws.scaffold_lift("mile1", "theorem solution : True := trivial", name="M1")


# --- F6a: scratch_project copies bundled lake-manifest.json ---

def test_scratch_project_copies_bundled_manifest_when_present(tmp_path):
    """scratch_project seeds lake-manifest.json from a supplied source path."""
    from telperion.prove2me.workspace import Workspace
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    # Provide a fake manifest source
    fake_manifest = tmp_path / "fake-lake-manifest.json"
    fake_manifest.write_text('{"version": 7, "packages": []}')
    proj = ws.scratch_project("Mtest", _manifest_source=fake_manifest)
    dest = proj / "lake-manifest.json"
    assert dest.exists(), "lake-manifest.json should be copied into scratch project"
    assert '"packages"' in dest.read_text()


def test_scratch_project_skips_manifest_when_source_absent(tmp_path):
    """scratch_project silently skips manifest copy when source doesn't exist."""
    from pathlib import Path
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    proj = ws.scratch_project("Mtest2", _manifest_source=Path("/nonexistent/manifest.json"))
    dest = proj / "lake-manifest.json"
    assert not dest.exists(), "no manifest should appear when source is absent"
