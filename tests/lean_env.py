"""Shared test guard: is a Lean env actually BUILT (so ``import Mathlib`` elaborates
WITHOUT triggering a from-scratch rebuild)?

The subtlety these tests kept getting wrong: the env DIRECTORY existing -- or even a
``.lake`` subdir existing -- does NOT mean the project is built.  A partial / unbuilt
``.lake`` makes ``lake env lean`` attempt a full mathlib build (minutes), so a test
that only checked ``env_dir.exists()`` / ``(.lake).is_dir()`` would HARD-FAIL (or
hang for minutes) in a fresh clone instead of skipping cleanly.  The definitive
"no rebuild will happen" marker is the presence of the built ``Mathlib.olean`` in the
mathlib dependency's build tree.

:func:`lean_env_ready` is the guard kernel-backed tests should use: it requires the
``lake`` toolchain AND a real mathlib build.  It errs toward NOT-ready (skip), never
toward a false "ready" -- a skip is always safe, whereas a false "ready" causes the
multi-minute rebuild this helper exists to prevent.
"""
from __future__ import annotations

import shutil
from pathlib import Path


def mathlib_built(env_dir) -> bool:
    """True iff the mathlib dependency under ``env_dir/.lake`` is compiled to oleans.

    Checks for the ``Mathlib.olean`` root under the mathlib package build dir, covering
    both the current ``build/lib/lean/`` layout and the older ``build/lib/`` one.  Cheap
    (two ``stat`` calls, no directory walk) and layout-tolerant; if neither marker is
    found it returns ``False`` so the caller SKIPS rather than risk a rebuild.
    """
    lib = Path(env_dir) / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib"
    return (lib / "lean" / "Mathlib.olean").is_file() or (lib / "Mathlib.olean").is_file()


def lean_env_ready(env_dir) -> bool:
    """The guard for kernel-backed tests: ``lake`` on PATH AND ``env_dir`` really built.

    A ``True`` result means ``verify_lean`` / ``measure_heartbeats`` against ``env_dir``
    will elaborate quickly (~seconds) rather than kick off a full dependency build.
    """
    return shutil.which("lake") is not None and mathlib_built(env_dir)
