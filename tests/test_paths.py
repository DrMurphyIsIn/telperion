"""telperion.paths: one place that knows the two layouts the engine runs in.

Arda:        <arda>/telperion/{src,examples,NANODA_REV,...}  and  <arda>/.github
standalone:  <repo>/{src,examples,NANODA_REV,...}            and  <repo>/.github
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion import paths  # noqa: E402


def _layout(tmp_path, arda: bool) -> tuple[Path, Path]:
    """(repo, project) of a miniature checkout; the package dir is project/src/telperion."""
    repo = tmp_path / ("arda" if arda else "telperion")
    project = repo / "telperion" if arda else repo
    (project / "src" / "telperion").mkdir(parents=True)
    (project / "pyproject.toml").write_text('[project]\nname = "telperion"\n')
    (project / "examples").mkdir()
    (project / "NANODA_REV").write_text("0" * 40 + "\n")
    (repo / ".git").mkdir()
    (repo / ".github" / "workflows").mkdir(parents=True)
    return repo, project


def test_arda_layout(tmp_path, monkeypatch):
    repo, project = _layout(tmp_path, arda=True)
    monkeypatch.setattr(paths, "_PKG", project / "src" / "telperion")
    assert paths.project_root() == project
    assert paths.repo_root() == repo
    assert paths.examples_dir() == project / "examples"
    assert paths.examples_prefix() == "telperion/examples"
    assert paths.project_of_repo(repo) == project


def test_standalone_layout(tmp_path, monkeypatch):
    repo, project = _layout(tmp_path, arda=False)
    monkeypatch.setattr(paths, "_PKG", project / "src" / "telperion")
    assert paths.project_root() == repo
    assert paths.repo_root() == repo
    assert paths.examples_dir() == repo / "examples"
    assert paths.examples_prefix() == "examples"
    assert paths.project_of_repo(repo) == repo


def test_worktree_git_file_counts_as_git_root(tmp_path):
    # a git worktree's root holds a `.git` FILE, not a directory
    repo, project = _layout(tmp_path, arda=True)
    (repo / ".git").rmdir()
    (repo / ".git").write_text("gitdir: /elsewhere\n")
    assert paths.repo_root(project) == repo


def test_no_git_falls_back_to_the_project(tmp_path):
    # e.g. the step-2 dry-run tree or an unpacked sdist: no .git, no .github anywhere near
    project = tmp_path / "dry"
    (project / "src" / "telperion").mkdir(parents=True)
    assert paths.repo_root(project) == project
    assert paths.examples_prefix(project) == "examples"


def test_real_checkout_project_root_holds_the_pyproject():
    assert (paths.project_root() / "pyproject.toml").is_file()
    assert paths.project_root() == ROOT
    assert paths.examples_dir() == ROOT / "examples"


def test_nanoda_rev_resolves():
    # rejudge-record reads the pinned nanoda rev; it used to look for <parents[3]>/telperion/NANODA_REV,
    # which exists only in the Arda layout
    from telperion.cli import _nanoda_rev_path
    p = _nanoda_rev_path()
    assert p.is_file(), p
    assert re.fullmatch(r"[0-9a-f]{40}", p.read_text().strip())


def test_nanoda_rev_resolves_in_standalone_layout(tmp_path, monkeypatch):
    repo, project = _layout(tmp_path, arda=False)
    monkeypatch.setattr(paths, "_PKG", project / "src" / "telperion")
    from telperion.cli import _nanoda_rev_path
    assert _nanoda_rev_path() == repo / "NANODA_REV"


def test_fakes_provenance_resolves_in_both_layouts(tmp_path, monkeypatch):
    # fakes-library refs are written Arda-relative ("telperion/..."); they must land in the project either way
    from telperion.fakes_library import resolve_provenance
    for arda in (True, False):
        repo, project = _layout(tmp_path / str(arda), arda=arda)
        monkeypatch.setattr(paths, "_PKG", project / "src" / "telperion")
        assert resolve_provenance("telperion/NANODA_REV (the pin)") == project / "NANODA_REV"


def test_evolve_default_lean_project_is_a_kept_canonical_example():
    # the default used to be examples/g1_floors/lean, a BG lab island that the standalone repo does not ship
    from telperion.evolve.config import EvolveConfig
    lp = Path(EvolveConfig.default().lean_project)
    assert lp == paths.examples_dir() / "primality" / "lean"
    assert (lp / "lakefile.toml").is_file()


def test_examples_prefix_relative_to_an_explicit_repo(tmp_path):
    # a caller that already holds the repo root (the coverage gate) gets the prefix relative to THAT root
    repo = tmp_path / "repo"
    (repo / "telperion" / "examples").mkdir(parents=True)
    assert paths.examples_prefix(repo / "telperion", repo=repo) == "telperion/examples"
    assert paths.examples_prefix(repo, repo=repo) == "examples"
