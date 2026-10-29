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


def fake_trusted_env(root) -> tuple[Path, Path, Path]:
    """(env, elan_home, manifest): a fake PINNED env under `root` for pure tests of the replay checks. Its toolchain
    has a `lean` and `Init.olean`, its mathlib package `Mathlib.olean`, and its trusted manifest is built."""
    from telperion.checks.lean_replay import build_trusted_manifest
    root = Path(root)
    elan = root / "elan"
    tdir = elan / "toolchains" / "leanprover--lean4---v4.35.0"
    (tdir / "bin").mkdir(parents=True)
    (tdir / "bin" / "lean").write_text("#!/bin/sh\n")
    (tdir / "bin" / "lean").chmod(0o755)
    (tdir / "lib" / "lean").mkdir(parents=True)
    (tdir / "lib" / "lean" / "Init.olean").write_bytes(b"init")
    env = root / "env"
    ml = env / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    (ml / "Mathlib").mkdir(parents=True)
    (ml / "Mathlib.olean").write_bytes(b"ml")
    (env / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    manifest = build_trusted_manifest(env, root / "manifest.json", elan)
    return env, elan, manifest


_SESSION_MANIFEST: dict[str, Path] = {}


def session_trusted_manifest(env_dir) -> Path:
    """The REAL pinned env's trusted manifest, built once per test process in a temp dir (never in the shared
    default location), with TELPERION_TRUSTED_MANIFEST pointed at it so that every check in the process uses it."""
    import os
    import tempfile
    from telperion.checks.lean_replay import build_trusted_manifest
    key = os.path.realpath(env_dir)
    if key not in _SESSION_MANIFEST:
        import atexit
        import shutil
        d = Path(tempfile.mkdtemp(prefix="tp_manifest_"))
        atexit.register(shutil.rmtree, d, True)
        _SESSION_MANIFEST[key] = build_trusted_manifest(env_dir, d / "trusted.json")
    os.environ["TELPERION_TRUSTED_MANIFEST"] = str(_SESSION_MANIFEST[key])
    return _SESSION_MANIFEST[key]


def fake_replay_output(script: str, ok_body: str = "", needs: str | None = None, always: bool = False) -> str:
    """What a replay script would print, for pure tests: in a list run, one CLOSURE line per target (its expected
    olean, no dependencies) and LISTED; in a replay run, one READ line per target (its expected copy), then REPLAY OK,
    `ok_body` (callback output, untagged or not) and DONE; or REPLAY NEEDS `needs` unless the script imports it."""
    import re
    tag = re.search(r'def tag : String := "(TR[0-9a-f]+)"', script).group(1)
    expect = re.search(r"def expectOleans : List \(Name × String\) := \[(.*)\]", script).group(1)
    pairs = re.findall(r'\(`([^,]+), "([^"]*)"\)', expect)
    out = []
    if "def listOnly : Bool := true" in script:
        out += [f"CLOSURE {m}\t{f}" for m, f in pairs if f] + [f"REPLAY LISTED {len(pairs)}", "DONE"]
        return "".join(f"{tag}-{ln}\n" for ln in out)
    out += [f"READ {f}" for _m, f in pairs if f]
    if needs is not None and (always or f"\nimport {needs}\n" not in script):
        return "".join(f"{tag}-{ln}\n" for ln in out + [f"REPLAY NEEDS {needs}", "DONE"])
    head = "".join(f"{tag}-{ln}\n" for ln in out + ["REPLAY OK modules=[] constants=0 declared=[] axioms=[propext]"])
    return head + ok_body.replace("<TAG>", tag) + f"{tag}-DONE\n"
