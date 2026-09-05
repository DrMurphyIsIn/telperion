"""Tests for the first-class ENVIRONMENT registry (:mod:`telperion.environment`).

Almost everything here is OFFLINE and runs in a fresh clone with no built mathlib:

* discovery is exercised against a SYNTHETIC ``examples/<name>/lean`` tree in a
  ``tmp_path``, where the ``Mathlib.olean`` build marker is FAKED (touched) so the
  built/unbuilt gate is tested without any real Lean;
* :func:`resolve` is exercised for all three accepted inputs (Environment / registered
  name / raw path) plus the error path;
* ``ready()`` gating is tested both ways by touching / not touching the marker.

One LIVE test discovers against the repo's real ``examples`` and asserts
``log_combination`` shows up as ready -- it is guarded by ``lean_env_ready`` and skips
cleanly when mathlib is not built (never triggers a rebuild).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))  # shared lean_env guard

import pytest  # noqa: E402

from telperion import environment as E  # noqa: E402
from telperion.environment import (  # noqa: E402
    Environment,
    UnknownEnvironmentError,
    discover_environments,
    get_environment,
    list_environments,
    mathlib_built,
    register_environment,
    resolve,
)
from lean_env import lean_env_ready  # noqa: E402


# --------------------------------------------------------------------------- #
# Synthetic-tree helpers.                                                      #
# --------------------------------------------------------------------------- #

def _make_lean_project(root: Path, name: str, *, built: bool, toolchain=None) -> Path:
    """Create ``root/<name>/lean`` as a Lake project; fake the built marker iff ``built``."""
    lean = root / name / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text("name = \"x\"\n", encoding="utf-8")
    if toolchain is not None:
        (lean / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
    if built:
        marker = lean / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
        marker.mkdir(parents=True)
        (marker / "Mathlib.olean").write_text("", encoding="utf-8")
    return lean


@pytest.fixture(autouse=True)
def _isolate_registry():
    """Each test starts and ends with a clean registry (defaults re-lazy-load)."""
    E.clear_environments()
    yield
    E.clear_environments()


# --------------------------------------------------------------------------- #
# mathlib_built marker + Environment.ready gating.                            #
# --------------------------------------------------------------------------- #

def test_mathlib_built_marker(tmp_path):
    built = _make_lean_project(tmp_path, "a", built=True)
    unbuilt = _make_lean_project(tmp_path, "b", built=False)
    assert mathlib_built(built) is True
    assert mathlib_built(unbuilt) is False


def test_mathlib_built_old_layout(tmp_path):
    # Older ``build/lib/Mathlib.olean`` (no `lean/` subdir) is also recognized.
    lean = tmp_path / "c" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text("name=\"x\"\n", encoding="utf-8")
    old = lean / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib"
    old.mkdir(parents=True)
    (old / "Mathlib.olean").write_text("", encoding="utf-8")
    assert mathlib_built(lean) is True


def test_ready_gating_requires_built(tmp_path, monkeypatch):
    # Force ``lake`` present so ready() reduces to the built marker.
    monkeypatch.setattr(E.shutil, "which", lambda _: "/usr/bin/lake")
    built = Environment.from_dir(_make_lean_project(tmp_path, "a", built=True))
    unbuilt = Environment.from_dir(_make_lean_project(tmp_path, "b", built=False))
    assert built.ready() is True
    assert unbuilt.ready() is False


def test_ready_false_without_lake(tmp_path, monkeypatch):
    monkeypatch.setattr(E.shutil, "which", lambda _: None)
    built = Environment.from_dir(_make_lean_project(tmp_path, "a", built=True))
    assert built.ready() is False  # built but no toolchain on PATH -> not ready


# --------------------------------------------------------------------------- #
# Environment.from_dir: name inference + toolchain read.                       #
# --------------------------------------------------------------------------- #

def test_from_dir_infers_name_and_toolchain(tmp_path):
    lean = _make_lean_project(
        tmp_path, "log_combination", built=True, toolchain="leanprover/lean4:v4.32.0"
    )
    env = Environment.from_dir(lean)
    assert env.name == "log_combination"          # from <name>/lean, not "lean"
    assert env.toolchain == "leanprover/lean4:v4.32.0"
    assert env.project_dir == lean
    assert env.is_lake_project() is True


def test_from_dir_missing_toolchain_is_none(tmp_path):
    lean = _make_lean_project(tmp_path, "x", built=True, toolchain=None)
    env = Environment.from_dir(lean)
    assert env.toolchain is None
    assert env.read_toolchain() is None


def test_environment_normalizes_str_project_dir(tmp_path):
    lean = _make_lean_project(tmp_path, "x", built=True)
    env = Environment(name="x", project_dir=str(lean))
    assert isinstance(env.project_dir, Path)


# --------------------------------------------------------------------------- #
# discover_environments.                                                       #
# --------------------------------------------------------------------------- #

def test_discover_finds_only_built(tmp_path):
    _make_lean_project(tmp_path, "built_one", built=True, toolchain="leanprover/lean4:v4.32.0")
    _make_lean_project(tmp_path, "unbuilt_one", built=False)
    # A non-lean example dir (no lean/ subdir) must be ignored.
    (tmp_path / "no_lean").mkdir()

    envs = discover_environments(tmp_path)
    names = [e.name for e in envs]
    assert names == ["built_one"]                 # only the built one, sorted
    assert envs[0].ready.__self__.toolchain == "leanprover/lean4:v4.32.0"


def test_discover_ready_only_false_lists_unbuilt(tmp_path):
    _make_lean_project(tmp_path, "built_one", built=True)
    _make_lean_project(tmp_path, "unbuilt_one", built=False)
    envs = discover_environments(tmp_path, ready_only=False)
    names = sorted(e.name for e in envs)
    assert names == ["built_one", "unbuilt_one"]


def test_discover_skips_non_lake_dir(tmp_path):
    # A <name>/lean dir that is NOT a Lake project (no lakefile) is skipped.
    lean = tmp_path / "bogus" / "lean"
    lean.mkdir(parents=True)
    (lean / "README").write_text("not a project", encoding="utf-8")
    assert discover_environments(tmp_path, ready_only=False) == []


def test_discover_missing_root_is_empty(tmp_path):
    assert discover_environments(tmp_path / "does_not_exist") == []


# --------------------------------------------------------------------------- #
# Registry: register / get / list, defaults, and error path.                   #
# --------------------------------------------------------------------------- #

def test_register_get_list(tmp_path):
    env = Environment.from_dir(_make_lean_project(tmp_path, "mine", built=True))
    register_environment(env)
    assert get_environment("mine") is env
    assert env in list_environments()


def test_get_unknown_raises():
    with pytest.raises(UnknownEnvironmentError):
        get_environment("nope_not_here")


def test_register_type_checked():
    with pytest.raises(TypeError):
        register_environment("not an Environment")  # type: ignore[arg-type]


def test_explicit_registration_overrides_default(tmp_path):
    # Register a custom env under a default's name; it must win.
    custom = Environment(name="log_combination", project_dir=tmp_path, description="custom")
    register_environment(custom)
    assert get_environment("log_combination") is custom


# --------------------------------------------------------------------------- #
# resolve: Environment / registered name / raw path / error.                   #
# --------------------------------------------------------------------------- #

def test_resolve_environment(tmp_path):
    env = Environment.from_dir(_make_lean_project(tmp_path, "e", built=True))
    assert resolve(env) == env.project_dir


def test_resolve_registered_name(tmp_path):
    env = Environment.from_dir(_make_lean_project(tmp_path, "named", built=True))
    register_environment(env)
    assert resolve("named") == env.project_dir


def test_resolve_raw_path(tmp_path):
    lean = _make_lean_project(tmp_path, "rawpath", built=True)
    # Not registered: falls back to the existing-directory passthrough.
    assert resolve(lean) == lean
    assert resolve(str(lean)) == lean


def test_resolve_name_wins_over_path(tmp_path, monkeypatch):
    # A registered NAME beats a same-spelled directory in cwd.
    env = Environment.from_dir(_make_lean_project(tmp_path, "collide", built=True))
    register_environment(env)
    stray = tmp_path / "stray"
    (stray / "collide").mkdir(parents=True)
    monkeypatch.chdir(stray)
    assert resolve("collide") == env.project_dir  # registry wins, not ./collide


def test_resolve_unknown_raises():
    with pytest.raises(UnknownEnvironmentError):
        resolve("neither_name_nor_dir_xyz")


# --------------------------------------------------------------------------- #
# LIVE discovery (guarded): log_combination is ready in the built worktree.    #
# --------------------------------------------------------------------------- #

_EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
_LOG_COMBO = _EXAMPLES / "log_combination" / "lean"


@pytest.mark.skipif(
    not lean_env_ready(_LOG_COMBO),
    reason="log_combination env not built (would risk a from-scratch mathlib rebuild)",
)
def test_live_discovery_finds_log_combination_ready():
    envs = discover_environments(_EXAMPLES)
    by_name = {e.name: e for e in envs}
    assert "log_combination" in by_name, "log_combination not discovered as built"
    env = by_name["log_combination"]
    assert env.ready() is True
    assert env.project_dir == _LOG_COMBO
    # And it resolves straight to the env_dir verify_lean expects.
    register_environment(env)
    assert resolve("log_combination") == _LOG_COMBO


@pytest.mark.skipif(
    not lean_env_ready(_LOG_COMBO),
    reason="log_combination env not built",
)
def test_live_default_log_combination_registered():
    # The lazy default should point at the real built project in this worktree.
    env = get_environment("log_combination")
    assert env.project_dir == _LOG_COMBO
    assert env.ready() is True
