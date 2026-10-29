"""Where the engine's own files are, in either layout it is checked out in.

    Arda:        <arda>/telperion/{src,examples,NANODA_REV,...}  and  <arda>/.github
    standalone:  <repo>/{src,examples,NANODA_REV,...}            and  <repo>/.github

The PROJECT root is the directory holding telperion's pyproject.toml. The REPO root is the git root, which
is where `.github/` lives: Arda's root in Arda, the project itself in the standalone repo. Code that used to
write `parents[3] / "telperion" / ...` assumed the Arda layout and breaks in the other one; ask here instead.

Every helper takes an optional project (or repo) directory so tests can point it at a miniature tree; with no
argument it answers for the installed package.
"""
from __future__ import annotations

from pathlib import Path
from typing import Optional

#: the package directory, <project>/src/telperion (a module global so tests can re-point it)
_PKG = Path(__file__).resolve().parent


def project_root(project: Optional[Path] = None) -> Path:
    """The directory holding telperion's pyproject.toml (<project>/src/telperion -> <project>)."""
    return Path(project) if project is not None else _PKG.parents[1]


def _is_git_root(d: Path) -> bool:
    # a worktree's root has a `.git` FILE; a miniature test tree may carry only `.github/`
    return (d / ".git").exists() or (d / ".github").is_dir()


def repo_root(project: Optional[Path] = None) -> Path:
    """The git root: the project itself (standalone), else its parent (Arda), else the project (no git at all,
    e.g. an unpacked sdist or the step-2 dry-run tree)."""
    p = project_root(project)
    if _is_git_root(p):
        return p
    if _is_git_root(p.parent):
        return p.parent
    return p


def project_of_repo(repo: Path) -> Path:
    """Inverse of repo_root for callers that only hold a repo root: <repo>/telperion in Arda, else <repo>."""
    repo = Path(repo)
    nested = repo / "telperion"
    if (nested / "pyproject.toml").is_file() or (nested / "examples").is_dir() or (nested / "missions").is_dir():
        return nested
    return repo


def examples_dir(project: Optional[Path] = None) -> Path:
    return project_root(project) / "examples"


def examples_prefix(project: Optional[Path] = None, repo: Optional[Path] = None) -> str:
    """The examples dir relative to the repo root, as CI workflows spell it: "telperion/examples" in Arda,
    "examples" standalone. A caller that already holds the repo root passes it as `repo`."""
    return examples_dir(project).relative_to(Path(repo) if repo is not None else repo_root(project)).as_posix()
