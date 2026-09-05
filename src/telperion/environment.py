"""First-class ENVIRONMENT registry: name -> built Lake project (AXLE ``environment``).

AXLE carries an ``environment`` field on every request selecting a Lean version +
Mathlib snapshot + project deps, and one deployment serves many concurrently
(cf. ``docs/AXLE_THIRD_TOUR_2026-09-04.md`` -> "First-class Environment registry").
Telperion today threads raw ``env_dir`` paths (``examples/log_combination/lean``, BG
worktrees, ...) into :func:`telperion.verify.verify_lean` and
:func:`telperion.cert_meta.measure_heartbeats`.  This module removes that path sprawl:
it names built environments once, so callers say ``env="log_combination"`` and let
:func:`resolve` hand back a ``project_dir`` usable *directly* as ``verify_lean``'s
``env_dir``.

Design properties (mirroring the surrounding modules' discipline):

1.  EVERY primitive returns a typed result.  :class:`Environment` is a frozen typed
    record; :func:`discover_environments` returns ``list[Environment]``; :func:`resolve`
    returns a :class:`pathlib.Path`.

2.  ADDITIVE.  Nothing here mutates or imports :mod:`telperion.verify`.  The intended
    (optional) one-line thread into ``verify_lean`` is documented in the module's
    design notes, not applied -- ``environment.py`` stands alone so a central pass can
    adopt it incrementally.

3.  READY is the BUILT gate, not the EXISTS gate.  A directory (or even a ``.lake``
    subdir) existing does NOT mean the project is built; an unbuilt ``.lake`` makes
    ``lake env lean`` attempt a multi-minute from-scratch mathlib build.  The
    definitive "no rebuild will happen" marker is the compiled ``Mathlib.olean`` root
    under the mathlib dependency's build tree -- the SAME marker ``tests/lean_env.py``
    uses.  :meth:`Environment.ready` and :func:`discover_environments` both gate on it
    and err toward NOT-ready (a skip is always safe; a false "ready" causes the very
    rebuild the marker exists to prevent).  ``is_file`` is used so a ``.lake`` symlink
    into a sibling checkout (as in this worktree) is followed correctly.

The registry is a process-global dict keyed by name; :func:`register_environment`,
:func:`get_environment`, :func:`list_environments`, and :func:`clear_environments`
are its accessors.  A small set of well-known names is pre-registered lazily on first
access (see :data:`_DEFAULT_ENVIRONMENTS`).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import shutil

__all__ = [
    "Environment",
    "UnknownEnvironmentError",
    "mathlib_built",
    "register_environment",
    "get_environment",
    "list_environments",
    "clear_environments",
    "discover_environments",
    "resolve",
    "default_examples_root",
]


class UnknownEnvironmentError(KeyError):
    """Raised when a name is resolved/looked-up but is not in the registry."""


def mathlib_built(project_dir) -> bool:
    """True iff the mathlib dependency under ``project_dir/.lake`` is compiled to oleans.

    This mirrors ``tests/lean_env.py``'s ``mathlib_built`` marker byte-for-byte in
    logic: it checks for the ``Mathlib.olean`` root under the mathlib package build
    dir, covering both the current ``build/lib/lean/`` layout and the older
    ``build/lib/`` one.  ``is_file`` follows a ``.lake`` symlink into a sibling
    checkout (this worktree links ``examples/*/lean/.lake`` across trees).  Cheap (two
    ``stat`` calls, no walk) and layout-tolerant; if neither marker is found it returns
    ``False`` so callers SKIP rather than risk a from-scratch rebuild.
    """
    lib = (
        Path(project_dir) / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib"
    )
    return (lib / "lean" / "Mathlib.olean").is_file() or (lib / "Mathlib.olean").is_file()


@dataclass(frozen=True)
class Environment:
    """A named, built Lake project usable as ``verify_lean``'s ``env_dir``.

    ``name``:        registry key (e.g. ``"log_combination"``).
    ``project_dir``: the built Lake project directory -- exactly what you pass as
                     ``verify_lean(..., env_dir=env.project_dir)``.
    ``toolchain``:   the pinned Lean toolchain string (e.g.
                     ``"leanprover/lean4:v4.32.0"``), or ``None`` if unknown.  When left
                     ``None`` at construction, :meth:`from_dir` / :func:`discover_environments`
                     read it from the project's ``lean-toolchain`` file.
    ``description``: free-text note for humans / logs.

    Frozen (hashable, cheap to pass around).  ``ready()`` is the BUILT gate;
    ``read_toolchain()`` re-reads the on-disk pin.
    """

    name: str
    project_dir: Path
    toolchain: object = None          # str | None
    description: str = ""

    def __post_init__(self) -> None:
        # Normalize project_dir to a Path even if a str was passed; frozen dataclass
        # requires object.__setattr__ to mutate.
        if not isinstance(self.project_dir, Path):
            object.__setattr__(self, "project_dir", Path(self.project_dir))

    def ready(self) -> bool:
        """True iff ``lake`` is on PATH AND ``project_dir`` is really built.

        A ``True`` result means ``verify_lean`` / ``measure_heartbeats`` against this
        environment elaborate quickly (~seconds) rather than kick off a full dependency
        build.  This is the environment-scoped analog of ``tests/lean_env.py``'s
        ``lean_env_ready`` (``lake`` present + :func:`mathlib_built`).
        """
        return shutil.which("lake") is not None and mathlib_built(self.project_dir)

    def is_lake_project(self) -> bool:
        """True iff ``project_dir`` looks like a Lake project (a lakefile is present).

        Independent of whether it is BUILT -- an unbuilt-but-present project is a Lake
        project that is simply not :meth:`ready`.
        """
        d = self.project_dir
        return (d / "lakefile.toml").is_file() or (d / "lakefile.lean").is_file()

    def read_toolchain(self) -> object:
        """Read the ``lean-toolchain`` pin from disk, or ``None`` if absent/unreadable."""
        return _read_toolchain(self.project_dir)

    @classmethod
    def from_dir(
        cls,
        project_dir,
        *,
        name: object = None,
        description: str = "",
    ) -> "Environment":
        """Build an :class:`Environment` from a project directory.

        ``name`` defaults to the directory's grandparent name when the path ends in
        ``.../<name>/lean`` (the ``examples/<name>/lean`` convention), else the
        directory's own name.  ``toolchain`` is read from the project's
        ``lean-toolchain`` file.
        """
        project_dir = Path(project_dir)
        if name is None:
            name = _infer_name(project_dir)
        return cls(
            name=str(name),
            project_dir=project_dir,
            toolchain=_read_toolchain(project_dir),
            description=description,
        )


# --------------------------------------------------------------------------------------
# Small on-disk helpers.
# --------------------------------------------------------------------------------------

def _read_toolchain(project_dir) -> object:
    """Return the stripped first line of ``project_dir/lean-toolchain``, or ``None``."""
    tc = Path(project_dir) / "lean-toolchain"
    try:
        text = tc.read_text(encoding="utf-8")
    except OSError:
        return None
    line = text.strip().splitlines()[0].strip() if text.strip() else ""
    return line or None


def _infer_name(project_dir) -> str:
    """Infer a registry name from a project dir following ``examples/<name>/lean``."""
    p = Path(project_dir)
    if p.name == "lean" and p.parent.name:
        return p.parent.name
    return p.name


# --------------------------------------------------------------------------------------
# Process-global registry.
# --------------------------------------------------------------------------------------

_REGISTRY: dict = {}
_DEFAULTS_LOADED = False

# Well-known names, pre-registered lazily on first registry access.  Paths are
# RELATIVE to the examples root (see :func:`default_examples_root`) and resolved when
# the defaults are materialized, so this table is import-order- and cwd-independent.
_DEFAULT_ENVIRONMENTS = (
    ("log_combination", "log_combination/lean",
     "BG log-combination cell family (the canonical built env)."),
    ("borel_caratheodory", "borel_caratheodory/lean",
     "RH zero-free-region Borel-Caratheodory lemmas."),
)


def default_examples_root() -> Path:
    """Best-effort path to the repo's ``examples`` directory.

    ``environment.py`` lives at ``<repo>/src/telperion/environment.py``, so the repo
    root is two parents up from the package dir and ``examples`` is a sibling of
    ``src``.  Returned unconditionally (existence not asserted) so callers can decide
    how to handle a non-layout checkout.
    """
    return Path(__file__).resolve().parents[2] / "examples"


def _ensure_defaults() -> None:
    """Materialize the :data:`_DEFAULT_ENVIRONMENTS` into the registry exactly once.

    A default is only registered if its path exists AND its name is not already taken
    (an explicit :func:`register_environment` before first access WINS -- defaults
    never clobber a caller's registration).
    """
    global _DEFAULTS_LOADED
    if _DEFAULTS_LOADED:
        return
    _DEFAULTS_LOADED = True  # set first: a partial failure must not retry-loop.
    root = default_examples_root()
    for name, rel, desc in _DEFAULT_ENVIRONMENTS:
        if name in _REGISTRY:
            continue
        project_dir = root / rel
        if not project_dir.exists():
            continue
        _REGISTRY[name] = Environment(
            name=name,
            project_dir=project_dir,
            toolchain=_read_toolchain(project_dir),
            description=desc,
        )


def register_environment(env: Environment) -> Environment:
    """Register (or replace) ``env`` under ``env.name``; return it.

    An explicit registration always wins over a same-named lazy default.
    """
    if not isinstance(env, Environment):
        raise TypeError(f"register_environment expects an Environment, got {type(env)!r}")
    # Ensure defaults are considered first so an explicit call can override one, then
    # overwrite unconditionally.
    _ensure_defaults()
    _REGISTRY[env.name] = env
    return env


def get_environment(name: str) -> Environment:
    """Return the registered :class:`Environment` for ``name`` or raise.

    Raises :class:`UnknownEnvironmentError` (a ``KeyError`` subclass) when ``name`` is
    not registered, so callers can catch it narrowly.
    """
    _ensure_defaults()
    try:
        return _REGISTRY[name]
    except KeyError:
        known = ", ".join(sorted(_REGISTRY)) or "(none)"
        raise UnknownEnvironmentError(
            f"no environment named {name!r}; registered: {known}"
        ) from None


def list_environments() -> list:
    """Return all registered environments (defaults included), sorted by name."""
    _ensure_defaults()
    return [_REGISTRY[k] for k in sorted(_REGISTRY)]


def clear_environments() -> None:
    """Drop ALL registrations, including lazy defaults (test isolation helper).

    After this call the defaults are re-materialized on the next registry access.
    """
    global _DEFAULTS_LOADED
    _REGISTRY.clear()
    _DEFAULTS_LOADED = False


# --------------------------------------------------------------------------------------
# Discovery + resolution.
# --------------------------------------------------------------------------------------

def discover_environments(examples_root, *, ready_only: bool = True) -> list:
    """Scan ``examples_root/*/lean`` for BUILT Lake projects.

    For each ``<examples_root>/<name>/lean`` directory that is a Lake project (has a
    ``lakefile.toml``/``lakefile.lean``), an :class:`Environment` is constructed with
    its name inferred (``<name>``) and toolchain read from ``lean-toolchain``.  By
    default (``ready_only=True``) only environments whose mathlib is actually BUILT
    (:func:`mathlib_built`, the ``tests/lean_env.py`` marker) are returned -- a fresh
    checkout with no ``.lake`` build yields ``[]`` rather than a list that would
    trigger multi-minute rebuilds on use.  Pass ``ready_only=False`` to also list
    present-but-unbuilt projects (each still reports :meth:`Environment.ready` as
    ``False``).

    Returns a name-sorted ``list[Environment]``.  This does NOT mutate the global
    registry; feed results to :func:`register_environment` if you want them named.
    """
    root = Path(examples_root)
    found: list = []
    if not root.is_dir():
        return found
    for child in sorted(root.iterdir()):
        project_dir = child / "lean"
        if not project_dir.is_dir():
            continue
        env = Environment.from_dir(project_dir)
        if not env.is_lake_project():
            continue
        if ready_only and not mathlib_built(project_dir):
            continue
        found.append(env)
    found.sort(key=lambda e: e.name)
    return found


def resolve(env_or_name_or_path) -> Path:
    """Resolve an :class:`Environment`, a registered name, or a raw path to a project dir.

    Accepts:

    * an :class:`Environment`  -> returns ``env.project_dir``;
    * a ``str``/``Path`` that is a REGISTERED NAME -> returns that env's ``project_dir``;
    * a ``str``/``Path`` that names an existing directory -> returns it as a
      :class:`Path` (a raw ``env_dir`` passthrough, so old call sites keep working);
    * a ``str``/``Path`` that is neither -> raises :class:`UnknownEnvironmentError`.

    The returned :class:`Path` is exactly what :func:`telperion.verify.verify_lean`
    (and :func:`telperion.cert_meta.measure_heartbeats`) expect as ``env_dir``.

    Ambiguity rule: a REGISTERED NAME wins over a same-spelled relative directory, so
    ``resolve("log_combination")`` yields the registered built project even if a
    stray ``./log_combination`` directory exists in the cwd.  To force the path
    interpretation, pass an explicit path (e.g. ``Path("./log_combination")`` that is
    an existing dir but not a registered name, or an absolute path).
    """
    if isinstance(env_or_name_or_path, Environment):
        return env_or_name_or_path.project_dir

    key = env_or_name_or_path
    # A registered name wins (str or a bare Path spelled like a name).
    name_key = str(key)
    _ensure_defaults()
    if name_key in _REGISTRY:
        return _REGISTRY[name_key].project_dir

    # Otherwise treat it as a filesystem path passthrough.
    p = Path(key)
    if p.is_dir():
        return p

    known = ", ".join(sorted(_REGISTRY)) or "(none)"
    raise UnknownEnvironmentError(
        f"{name_key!r} is neither a registered environment nor an existing "
        f"directory; registered: {known}"
    )
