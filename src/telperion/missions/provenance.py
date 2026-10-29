"""Provenance: who wrote a statement, who read it back, and what the gate actually saw.

WHY (governance 2026-09-23, docs/AUDIT_INDEPENDENCE_2026-09-23.md). The read-back is the
one link in the proof chain no machine checks: it is the testimony that the formal statement
says what its title claims. `MISSIONS_DESIGN_2026-09-11.md` section 8 required the renderer
to be independent of the author, but nothing recorded who the author was, `--auditor` was
free text, and every testimony written 2026-09-19..22 came from a subagent of the authoring
session under the same git identity. The proofs themselves are fine; the point of this
module is to make self-certification VISIBLE and refuse it where it can be recognised.

Three records, all small and all in the node file:

  [author]     identity + session + date, written by `mission add`;
  [readback]   gains auditor_identity / auditor_session / independence, written by
               `mission audit`, which REFUSES an auditor matching the author;
  [grant]      artifact + statement digests, gate version, identity, session, date --
               written by the gate only; `mission verify` recomputes the digests.

Plus a `[comparator]` sidecar recording a passing independent-judge run (deliverable 2).

None of this is unforgeable. A session can supply any identity string for itself or for a
subagent. What it buys is a record the next reader can check against git and against the
attempts ledger, and a CLI that will not write a self-audit without being lied to.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from typing import List, Optional, Tuple

from .schema import Author, ComparatorRecord, Grant, Node, Readback, SchemaError, load_node, save_node
from .statements import statement_path

#: Bumped whenever the gate's rule set changes in a way that makes an older grant weaker
#: than a fresh one. History:
#:   2026-09-23.1  first version that writes a [grant] block (digests + provenance) and
#:                 refuses a read-back whose auditor matches the author.
GATE_VERSION = "2026-09-23.1"

#: A read-back shorter than this is not a rendering of a formal statement; it is a label.
#: The shortest genuine read-back in the live registry on 2026-09-23 was 262 characters.
MIN_READBACK_CHARS = 120

#: Environment variable a session's id is taken from when `--session` is not given.
SESSION_ENV = "CLAUDE_SESSION_ID"


class SelfAuditError(SchemaError):
    """The auditor is the author (same session or same identity)."""


class ProvenanceError(SchemaError):
    """Missing or malformed provenance input (empty identity/session, unreadable file)."""


# ---------------------------------------------------------------------------
# Identity inputs
# ---------------------------------------------------------------------------

def git_identity(cwd: Optional[Path] = None) -> str:
    """`git config user.email` for *cwd*, or "" when git or the setting is absent."""
    try:
        out = subprocess.run(
            ["git", "config", "user.email"], cwd=str(cwd) if cwd else None,
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    return out.stdout.strip() if out.returncode == 0 else ""


def session_id(explicit: Optional[str] = None) -> str:
    """The session id: `explicit` when given, else `$CLAUDE_SESSION_ID`, else ""."""
    if explicit and explicit.strip():
        return explicit.strip()
    return os.environ.get(SESSION_ENV, "").strip()


def require_identity(identity: str, session: str, what: str) -> None:
    """Raise ProvenanceError unless both strings are non-empty."""
    if not (identity or "").strip():
        raise ProvenanceError(
            f"{what}: identity is empty. It is taken from `git config user.email`; set it or "
            "pass --identity.")
    if not (session or "").strip():
        raise ProvenanceError(
            f"{what}: session is empty. Pass --session or set ${SESSION_ENV}.")


# ---------------------------------------------------------------------------
# Read-back content and independence
# ---------------------------------------------------------------------------

def _words(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", text.lower()).strip()


def readback_text_problem(text: str, title: str) -> str:
    """"" if *text* is a plausible read-back of a node titled *title*; else why not.

    Two shapes are refused: a text under MIN_READBACK_CHARS, and a text that merely repeats
    the title (equal to it, or contained in it, after case/punctuation folding). Neither is a
    rendering of the formal statement, which is the only thing the read-back exists to be.
    """
    t = (text or "").strip()
    if len(t) < MIN_READBACK_CHARS:
        return (f"read-back is {len(t)} characters; a rendering of a formal statement is at "
                f"least {MIN_READBACK_CHARS}. Say what the statement quantifies over and what "
                "it concludes, in your own words.")
    tw, titlew = _words(t), _words(title or "")
    if titlew and (tw == titlew or tw in titlew):
        return "read-back repeats the node title; a read-back must render the FORMAL statement, not restate the title."
    return ""


def independence_of(author: Optional[Author], identity: str, session: str) -> str:
    """Classify an auditor {identity, session} against the node's author.

    Returns "independent" when the node has an author and both fields differ, or
    "unverified" when the node has no [author] block (it predates the field, so nothing can
    be compared). Raises SelfAuditError when either field matches the author's.
    """
    if author is None:
        return "unverified"
    if session.strip() == author.session.strip():
        raise SelfAuditError(
            f"auditor session {session!r} is the author's session; a read-back must come from "
            "a different session (MISSIONS_DESIGN_2026-09-11.md section 8).")
    if identity.strip().lower() == author.identity.strip().lower():
        raise SelfAuditError(
            f"auditor identity {identity!r} is the author's identity; a read-back must come "
            "from a different principal, not a subagent of the author under the same account.")
    return "independent"


def readback_is_self_audit(node: Node) -> bool:
    """True iff the stored read-back names the author's session or identity.

    Only decidable when both the [author] block and the structured auditor fields exist;
    legacy read-backs (no structured fields) return False here and are reported as
    `unverified` instead.
    """
    rb, au = node.readback, node.author
    if rb is None or au is None:
        return False
    if rb.independence == "self":
        return True
    if rb.auditor_session and rb.auditor_session.strip() == au.session.strip():
        return True
    if rb.auditor_identity and rb.auditor_identity.strip().lower() == au.identity.strip().lower():
        return True
    return False


# ---------------------------------------------------------------------------
# Digests and the grant block
# ---------------------------------------------------------------------------

def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Closure digest (step 0b Task 1, 2026-10-28; fail-closed + srcDir fix round 1, 10-28;
# manifest-driven externals fix round 2, Controller Ruling 0b-3, 10-28)
#
# WHY. Before this, a [rejudge] record bound itself to the sha256 of the top-level
# artifact FILE alone (RejudgeRecord.artifact_sha256). For the ladders the certificates
# live in IMPORTED modules (Arb4_h8000 imports every segment's edge certificates; the
# Hodge1 capstones import a chain of LDL^T blocks), so a re-judge that is current on the
# artifact file can still be stale on what the artifact actually proves. The owner's fix:
# bind the record to a digest over the artifact's WHOLE import closure instead.
#
# FIX ROUND 1 (Controller Ruling 0b-2): srcDir. The first cut resolved a module under a
# candidate package directory by checking `D/module_path.lean` directly -- which ignores
# `srcDir`. zzl_core's lakefile declares `srcDir = ".."`, so its modules live one
# directory ABOVE zzl_core/ itself; the first cut read each one as "external" and
# dropped it (and everything it imports). Fixed by reusing coverage.py's srcDir-aware
# package model. It also introduced FAIL CLOSED (a hand-written LIBRARY_ROOTS list).
#
# FIX ROUND 2 (Controller Ruling 0b-3): LIBRARY_ROOTS replaced by a manifest-driven
# rule, because the hand list missed `Zeta23` (rvm_bridge's `[[require]] git = ...`
# dependency) -- discovered when re-binding found its modules unresolvable under round
# 1's rule. A module is external iff its root package is a NON-PATH dependency in a
# relevant `lake-manifest.json`, or it sits under a CORE_ROOT (Init/Lean/Std/Lake). The
# package's module roots are read from its OWN lakefile under `.lake/packages/<name>
# [/subDir]` when parseable (a `.toml`, e.g. Zeta23's); when it is not (a `.lean`
# lakefile, e.g. Mathlib's) or absent, the package's own directory is treated as a bare
# source root (`Mathlib.lean` sits right there). An import matching neither still fails
# CLOSED. The digest now also pins every such external package's `name\trev`, so
# bumping Mathlib or Zeta23 makes a bound re-judge stale too.
# ---------------------------------------------------------------------------

#: Lean/Lake toolchain roots that are never a manifest-listed package (Controller
#: Ruling 0b-3): the prelude, the compiler, and their immediate core libraries.
CORE_ROOTS = frozenset({"Init", "Lean", "Std", "Lake"})


class ClosureError(ProvenanceError):
    """An import resolves to no local file, matches no manifest package, and is not a
    core root (Controller Ruling 0b-3): the closure fails CLOSED instead of silently
    shrinking."""


def _manifest_entries(pkg_dir: Path) -> Tuple[dict, ...]:
    """The `packages` entries of *pkg_dir*'s `lake-manifest.json`, or `()` when absent
    or unreadable.

    Deliberately NOT cached (unlike `coverage._package`/`_workspace`, which assume a
    stable repo during one process): a test that rewrites a manifest mid-run (e.g.
    bumping a pinned rev) must see the new content, and the file is small enough that
    re-reading it is cheap relative to the coverage.py calls already made per module.
    """
    mf = Path(pkg_dir) / "lake-manifest.json"
    if not mf.is_file():
        return ()
    try:
        doc = json.loads(mf.read_text())
    except (OSError, ValueError):
        return ()
    return tuple(e for e in (doc.get("packages") or []) if isinstance(e, dict))


def _external_package_dir(pkg_dir: Path, entry: dict) -> Path:
    """Where *entry* (a non-path manifest dependency of the package at *pkg_dir*) lives
    on disk: `<pkg_dir>/.lake/packages/<name>[/<subDir>]`."""
    base = Path(pkg_dir) / ".lake" / "packages" / str(entry.get("name") or "")
    sub = entry.get("subDir")
    return (base / str(sub)) if sub else base


def _resolve_external_entry(ws: tuple, root: str) -> Optional[dict]:
    """The non-path manifest entry (from any package's `lake-manifest.json` in *ws*)
    that provides module root *root*, or None.

    Three tiers, cheapest first, matching the brief's "declared lib" fallback:
      1. *root* matches the entry's own `name` field case-insensitively (Lake's own
         convention: `lake init Foo` gives package `foo` module root `Foo`; this is
         what resolves Mathlib/Zeta23 even when `.lake/packages` is not on disk at
         all -- e.g. a fresh checkout, or a copy that deliberately excludes `.lake`).
      2. that entry's OWN lakefile, if parseable (a `.toml` under
         `.lake/packages/<name>[/subDir]`), declares a `[[lean_lib]]` whose roots
         include *root* -- for a package whose OTHER libs don't share its name
         (Zeta23 also provides `ChallengeDeps`/`Challenge`/`Solution`).
      3. *root* exists, as a file or a directory, right under that package's own
         directory on disk (the "bare source root" convention `coverage.py` already
         uses for a local package with no declared `[[lean_lib]]`).
    """
    from . import coverage
    seen: set = set()
    for pkg in ws:
        for entry in _manifest_entries(pkg.dir):
            if entry.get("type") == "path":
                continue
            name = str(entry.get("name") or "")
            if not name or (name, str(entry.get("rev") or "")) in seen:
                continue
            seen.add((name, str(entry.get("rev") or "")))
            if root.lower() == name.lower():
                return entry
            base = _external_package_dir(pkg.dir, entry)
            toml = base / "lakefile.toml"
            if toml.is_file():
                epkg = coverage._package(base)
                if epkg is not None and any(
                        root in lib_roots for lib_roots, _g, _s in epkg.libs.values()):
                    return entry
            if (base / (root + ".lean")).is_file() or (base / root).is_dir():
                return entry
    return None


def _manifest_pins(ws: tuple) -> List[str]:
    """Sorted, deduplicated `"<name>\\t<rev>"` lines for every non-path dependency
    named in any package's `lake-manifest.json` in *ws* (Controller Ruling 0b-3): what
    the closure digest pins so bumping Mathlib or Zeta23 makes a bound record stale."""
    pins: set = set()
    for pkg in ws:
        for entry in _manifest_entries(pkg.dir):
            if entry.get("type") == "path":
                continue
            name = str(entry.get("name") or "")
            if name:
                pins.add(f"{name}\t{entry.get('rev') or ''}")
    return sorted(pins)


# ---------------------------------------------------------------------------
# lake_workspace (Controller Ruling 0b-7, 2026-10-28)
#
# WHY. `telperion/examples/zeta_zero_localization/lean`'s own lakefile.toml declares
# 27,090 `[[lean_lib]]` entries. `lake env` there emits ~2.5 MB of environment -- over
# macOS ARG_MAX (1 MB) -- so every process lake spawns from that directory fails with
# "could not execute external process", including `lake exe cache get` and even `lake
# env sh`. CI never builds the monolith directly: it builds the slim sub-workspace
# `zzl_aux/` (23 libs, `srcDir = ".."`, its own lake-manifest.json/lean-toolchain, and
# `../zzl_core` + `../../../zero_free_bridge/lean` path-required), which actually
# declares the same modules and can spawn a process. `lake_workspace` finds that
# smaller workspace generically, so the nanoda-direct route (and the closure digest's
# manifest pins) can build/export from it instead of the unusable island root.
# ---------------------------------------------------------------------------

def lake_workspace(campaign_root: Path, node: Node) -> Path:
    """The SMALLEST lakefile directory -- measured by fewest `[[lean_lib]]` entries --
    among *node*'s island lean dir and that dir's immediate subdirectories, that
    declares a `lean_lib` covering the artifact's own module (`judge.module_name_of`,
    the same module resolution `node_module`/the grant gate use; `coverage.py`'s
    lakefile model, the same one `closure_digest` already parses manifests with) AND
    whose declaration resolves that module to the artifact's own file (Fix 1,
    2026-10-28): a candidate whose `lean_lib` happens to name the same module but
    points (no `srcDir = ".."`, its own copy of the file) at a DIFFERENT file on disk is
    rejected, not accepted -- otherwise this would build and export from that copy while
    `closure_digest` goes on hashing the original artifact.

    Deterministic: ties are broken by path (lexicographic on the resolved directory
    string). When NO candidate other than the island lean dir declares the module --
    every island without a slimmer sub-workspace -- returns the island lean dir
    itself, exactly the behaviour every other route already relies on. Off-island (no
    recognised judge island at all, e.g. a synthetic test fixture with no
    `examples/<island>/lean` tree), returns the artifact's own directory, matching
    `_closure_workspace`'s fallback.
    """
    from . import coverage, judge
    from .rejudge import RejudgeSetupError, island_of_artifact

    campaign_root = Path(campaign_root).resolve()
    if node.proof is None:
        raise ProvenanceError("lake_workspace: node has no proof link")
    artifact = (campaign_root / node.proof.artifact).resolve()
    if not artifact.is_file():
        raise ProvenanceError(f"lake_workspace: artifact {artifact} does not exist")

    troot = campaign_root.parent.parent
    lean_dir = artifact.parent
    try:
        island = island_of_artifact(troot, artifact)
        lean_dir = judge.island_dir(troot, island).resolve()
    except (RejudgeSetupError, judge.JudgeError):
        return lean_dir       # off-island: no recognised workspace to search at all

    module = judge.module_name_of(lean_dir, artifact)
    # Controller Ruling 0b-9 (2026-10-28): the closure as the island model resolves it --
    # every module imported anywhere in it, mapped to its file (None = external). A
    # candidate build workspace must resolve EVERY one of these the same way (the 0b-8
    # same-file guard, extended transitively), or the build would compile a different
    # closure from the one `closure_digest` hashes.
    _files, _ws, resolution = _closure_resolution(campaign_root, node)

    candidates = [lean_dir]
    try:
        subdirs = sorted(p for p in lean_dir.iterdir() if p.is_dir())
    except OSError:
        subdirs = []
    for d in subdirs:
        if (d / "lakefile.toml").is_file():
            candidates.append(d.resolve())

    best: Optional[Tuple[Tuple[int, str], Path]] = None
    for d in candidates:
        pkg = coverage._package(d)
        if pkg is None:
            continue
        got = coverage._lib_module_file((pkg,), module)
        # Fix 1 (2026-10-28): a candidate is only a candidate if the module it declares
        # resolves to the SAME file as the artifact. Without this check, a subdir lakefile
        # with no `srcDir = ".."` that carries its own copy of the module (same name,
        # different content) would be accepted, built and exported here, while
        # `closure_digest` goes on hashing the original artifact -- the gate and the
        # export would be looking at two different files.
        if got is None or got != artifact:
            continue
        # Ruling 0b-9: transitively, not only the artifact module. The island lean dir
        # IS the island model, so it agrees with itself by construction.
        if d != lean_dir:
            cand_ws = coverage._workspace(d)
            if any(coverage._module_file(cand_ws, mod) != want
                   for mod, want in resolution.items()):
                continue
        key = (len(pkg.libs), str(d))
        if best is None or key < best[0]:
            best = (key, d)
    return best[1] if best is not None else lean_dir


def _closure_workspace(campaign_root: Path, node: Node) -> Tuple[Path, tuple]:
    """(artifact, workspace) for *node*: the artifact's resolved path, and the
    `coverage.py` package workspace (island + every `path`-required sibling,
    transitively, srcDir and all) its imports resolve against. Off-island, the
    workspace is whatever `coverage._workspace` finds at the artifact's own directory
    (typically nothing: no lakefile.toml there)."""
    if node.proof is None:
        raise ProvenanceError("closure_files: node has no proof link")
    campaign_root = Path(campaign_root).resolve()
    artifact = (Path(campaign_root) / node.proof.artifact).resolve()
    if not artifact.is_file():
        raise ProvenanceError(f"closure_files: artifact {artifact} does not exist")
    from . import coverage, judge
    from . import rejudge as _rejudge

    lean_dir = artifact.parent
    try:
        troot = campaign_root.parent.parent
        island = _rejudge.island_of_artifact(troot, artifact)
        lean_dir = judge.island_dir(troot, island)
    except (_rejudge.RejudgeSetupError, judge.JudgeError):
        pass       # no recognised island: resolve only against the artifact's own dir

    return artifact, coverage._workspace(Path(lean_dir).resolve())


def _resolve_closure(campaign_root: Path, node: Node) -> Tuple[List[Path], tuple]:
    """(closure files, workspace) for *node*'s artifact: every local Lean source file
    it imports, directly or transitively, plus the artifact itself.

    Each file's own imports (`coverage._imports`) are resolved against the workspace
    (`coverage._module_file`, which already honours `srcDir`). An import that does not
    resolve locally is external WITHOUT being an error iff it sits under a CORE_ROOT or
    matches a non-path `lake-manifest.json` dependency (`_resolve_external_entry`);
    anything else raises `ClosureError` naming the module and the importing file.
    """
    files, ws, _resolution = _closure_resolution(campaign_root, node)
    return files, ws


def _closure_resolution(campaign_root: Path, node: Node
                        ) -> Tuple[List[Path], tuple, dict]:
    """`_resolve_closure` plus the RESOLUTION it used: `{module: file-or-None}` for every
    module imported anywhere in the closure (None = external: a core root or a manifest
    package). Controller Ruling 0b-9: `lake_workspace` checks a candidate build workspace
    against exactly this map, so the closure the digest hashes is the closure the build
    actually sees."""
    artifact, ws = _closure_workspace(campaign_root, node)
    from . import coverage

    resolved: set = set()
    resolution: dict = {}
    stack = [artifact]
    while stack:
        f = stack.pop()
        if f in resolved:
            continue
        resolved.add(f)
        for mod in coverage._imports(f):
            g = coverage._module_file(ws, mod)
            resolution[mod] = g
            if g is not None:
                if g not in resolved:
                    stack.append(g)
                continue
            root = mod.split(".", 1)[0]
            if root in CORE_ROOTS or _resolve_external_entry(ws, root) is not None:
                continue
            raise ClosureError(
                f"import {mod!r} in {f} resolves to no local file, matches no "
                "manifest package, and is not a core root; the closure cannot be bound")
    return sorted(resolved), ws, resolution


def closure_files(campaign_root: Path, node: Node) -> List[Path]:
    """Every local Lean source file *node*'s artifact imports, directly or
    transitively, plus the artifact itself -- the import closure a [rejudge] record is
    bound to (Task 1; manifest-driven externals, Controller Ruling 0b-3)."""
    files, _ws = _resolve_closure(campaign_root, node)
    return files


def closure_support_files(campaign_root: Path, node: Node) -> List[Path]:
    """`lakefile.toml` + `lake-manifest.json` of the island (or the artifact's own
    directory, off-island) and every `path`-required sibling (Controller Ruling 0b-3),
    PLUS the same files for the workspace `lake_workspace` actually picks to build and
    export from and that workspace's own path-required siblings (Fix 2, 2026-10-28):
    the back-fill git rule must also cover these, since a changed `srcDir`, a changed
    `[[require]] path`, or a changed pinned `rev` could change the closure or its
    digest without any closure .lean FILE itself changing -- and since Controller
    Ruling 0b-7, the pins `closure_digest` hashes come from `lake_workspace`'s own
    workspace, not necessarily the island root's."""
    from . import coverage

    _artifact, ws = _closure_workspace(campaign_root, node)
    chosen = lake_workspace(campaign_root, node)
    chosen_ws = coverage._workspace(chosen.resolve())
    out = []
    for d in _package_dirs(tuple(ws) + chosen_ws):
        # Controller Ruling 0b-9: `lean-toolchain` (which Lean the build used) and a
        # `lakefile.lean` (a path-required package coverage.py cannot parse) are in the
        # git rule too -- they are in the digest now (`_build_config_files`).
        for name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"):
            f = Path(d) / name
            if f.is_file():
                out.append(f.resolve())
    return sorted(set(out))


def _package_dirs(ws: tuple) -> List[Path]:
    """Every package directory of *ws*, plus each `path`-required directory of those
    packages that `coverage._workspace` itself dropped (a `lakefile.lean` package it does
    not parse) -- deduplicated, in a stable order."""
    seen: List[Path] = []
    for pkg in ws:
        for d in [Path(pkg.dir)] + [Path(r) for r in pkg.requires]:
            try:
                d = d.resolve()
            except OSError:
                continue
            if d.is_dir() and d not in seen:
                seen.append(d)
    return seen


def _build_config_files(build_dir: Path) -> List[Path]:
    """Controller Ruling 0b-9 (2026-10-28): the build configuration `closure_digest`
    hashes by CONTENT -- `lean-toolchain`, `lakefile.toml` and `lakefile.lean` of the
    build workspace `lake_workspace` picks and of each of its path-required packages.
    Before this, a toolchain bump or a lakefile edit (an option, a `moreLeanArgs`, a lib
    `srcDir`) left a bound re-judge looking current."""
    from . import coverage
    out = []
    for d in _package_dirs(coverage._workspace(Path(build_dir).resolve())):
        for name in ("lean-toolchain", "lakefile.toml", "lakefile.lean"):
            f = d / name
            if f.is_file():
                out.append(f.resolve())
    return sorted(set(out))


def closure_digest(campaign_root: Path, node: Node) -> str:
    """sha256 binding a [rejudge] record to *node*'s WHOLE import closure (Task 1):
    the concatenation of every closure file's path (relative to the telperion root, so
    the digest is the same wherever the repo is checked out) and its own sha256, in
    sorted path order, followed by every external dependency's `name\\trev`
    (`_manifest_pins`, Controller Ruling 0b-3). Changes if any closure file's CONTENT
    changes, if the SET of closure files changes, or if an external dependency's
    pinned rev changes (bumping Mathlib or Zeta23).

    Controller Ruling 0b-7 (2026-10-28): the FILE set above is unchanged -- still every
    closure file resolved against the island's own (possibly monolith) workspace. The
    PINS are not: they come from `lake_workspace`'s own `lake-manifest.json` plus its
    path-required packages, i.e. the workspace actually built and exported from. For an
    island with no slimmer sub-workspace (every island this ruling does not touch),
    `lake_workspace` returns the same lean dir `_resolve_closure` already used, so the
    pins are unchanged too -- a record time/verify time MUST agree, which they do
    because both call this same function.

    Controller Ruling 0b-9 (2026-10-28): followed by `CFG` lines -- the path and sha256 of
    every `lean-toolchain`, `lakefile.toml` and `lakefile.lean` of that same build workspace
    and its path-required packages (`_build_config_files`), so a toolchain bump or a
    lakefile edit also makes a bound record stale. Since the same ruling, `lake_workspace`
    only picks a build workspace that resolves every closure module to the same file as
    the island model, so the FILE set above is also the set the build compiles."""
    campaign_root = Path(campaign_root).resolve()
    troot = campaign_root.parent.parent
    files, _ws = _resolve_closure(campaign_root, node)
    from . import coverage
    build_dir = lake_workspace(campaign_root, node).resolve()
    pin_ws = coverage._workspace(build_dir)
    h = hashlib.sha256()
    for f in files:
        try:
            rel = f.relative_to(troot)
        except ValueError:
            rel = f
        h.update(str(rel).encode("utf-8"))
        h.update(b"\0")
        h.update(sha256_file(f).encode("utf-8"))
        h.update(b"\n")
    for pin in _manifest_pins(pin_ws):
        h.update(b"PIN\0")
        h.update(pin.encode("utf-8"))
        h.update(b"\n")
    # Controller Ruling 0b-9 (2026-10-28): the build configuration's CONTENT --
    # lean-toolchain + lakefile.toml/lakefile.lean of the build workspace and its
    # path-required packages.
    for cfg in _build_config_files(build_dir):
        try:
            rel = cfg.relative_to(troot)
        except ValueError:
            rel = cfg
        h.update(b"CFG\0")
        h.update(str(rel).encode("utf-8"))
        h.update(b"\0")
        h.update(sha256_file(cfg).encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()


def build_grant(campaign_root: Path, node: Node, *, identity: str, session: str,
                today: Optional[str] = None) -> Grant:
    """The [grant] block for *node*: digests of the artifact and statement files as they are
    on disk RIGHT NOW, which is what the gate has just checked."""
    require_identity(identity, session, "grant")
    if node.proof is None:
        raise ProvenanceError("build_grant: node has no proof link")
    art = Path(campaign_root) / node.proof.artifact
    stmt = statement_path(campaign_root, node)
    return Grant(
        artifact_sha256=sha256_file(art),
        statement_sha256=sha256_file(stmt),
        gate_version=GATE_VERSION,
        date=today or date.today().isoformat(),
        identity=identity.strip(),
        session=session.strip(),
    )


def grant_digest_errors(campaign_root: Path, node: Node) -> List[str]:
    """Errors when a node's [grant] digests no longer match the files on disk. Empty when the
    node has no grant block (every node granted before 2026-09-23)."""
    g = node.grant
    if g is None:
        return []
    errs: List[str] = []
    if node.proof is None:
        return [f"has a [grant] block but no proof link"]
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        errs.append(f"[grant] names artifact {node.proof.artifact!r}, which does not exist")
    elif sha256_file(art) != g.artifact_sha256:
        errs.append(
            f"artifact {node.proof.artifact!r} has changed since the gate granted it "
            f"(grant sha256 {g.artifact_sha256[:12]}..., on disk {sha256_file(art)[:12]}...); "
            "the status rests on evidence nobody re-checked. Re-run `mission grant` after "
            "reopening, or restore the artifact.")
    stmt = statement_path(campaign_root, node)
    if not stmt.exists():
        errs.append("[grant] recorded a statement digest but the statement file is missing")
    elif sha256_file(stmt) != g.statement_sha256:
        errs.append(
            "statement file has changed since the gate granted this node "
            f"(grant sha256 {g.statement_sha256[:12]}..., on disk {sha256_file(stmt)[:12]}...)")
    return errs


def comparator_staleness(campaign_root: Path, node: Node) -> str:
    """A warning when the recorded Comparator verdict no longer describes the artifact on
    disk; "" otherwise (including when there is no record)."""
    c = node.comparator
    if c is None or node.proof is None:
        return ""
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return ""
    if sha256_file(art) != c.artifact_sha256:
        return (f"[comparator] run {c.run_id} judged a different artifact "
                f"(sha256 {c.artifact_sha256[:12]}..., on disk {sha256_file(art)[:12]}...); "
                "the independent verdict is stale until the job passes again")
    # A compositional verdict judged the PART modules (the implication and each segment), not
    # the artifact file: each one must still be the file the judge saw.
    for part in c.parts:
        f = parse_part_entry(part)
        mod, want = f.get("module", ""), f.get("sha256", "")
        if not mod or not want:
            return f"[comparator] compositional part entry without module/sha256: {part!r}"
        src = art.parent / (mod.replace(".", "/") + ".lean")
        if not src.exists():
            return f"[comparator] compositional part module {mod} no longer exists ({src.name})"
        if sha256_file(src) != want:
            return (f"[comparator] run {c.run_id} judged part {f.get('part')} with {mod} at "
                    f"sha256 {want[:12]}..., on disk {sha256_file(src)[:12]}...; the "
                    "compositional verdict is stale until the heavy judge passes again")
    return ""


def parse_part_entry(entry: str) -> dict:
    """`part=seg:h1000 slug=... theorem=... module=... sha256=... job=...` -> dict."""
    return dict(kv.split("=", 1) for kv in entry.split() if "=" in kv)


def required_ci_problem(campaign_root: Path, node: Node) -> str:
    """"" when the node declares no `requires_ci_job`, or its `[ci_record]` is a passing run
    of exactly that job on the artifact digest currently on disk; else why not."""
    req = (node.requires_ci_job or "").strip()
    if not req:
        return ""
    rec = node.ci_record
    if rec is None:
        return (f"requires a recorded passing run of CI job {req!r} (`mission ci-record`), "
                "and none is recorded")
    if rec.key != req:
        return f"requires CI job {req!r} but the record is for {rec.key!r}"
    if rec.conclusion != "success":
        return f"the recorded run {rec.run_id} of {req!r} concluded {rec.conclusion!r}, not success"
    if node.proof is None:
        return f"requires CI job {req!r} but the node has no artifact"
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return f"requires CI job {req!r} but artifact {node.proof.artifact!r} does not exist"
    cur = sha256_file(art)
    if cur != rec.artifact_sha256:
        return (f"the recorded run {rec.run_id} of {req!r} was on artifact sha256 "
                f"{rec.artifact_sha256[:12]}..., but the artifact on disk is {cur[:12]}...; "
                "record a passing run on the current artifact")
    return ""


def judged_lean_kernel_only(node: Node) -> bool:
    """True when the node's `[comparator]` record says the judge ran with nanoda OFF.

    `second_kernel` starting with "none" (e.g. "none: heavy_certificates") is the record's
    reading; `kernel_mode = "lean-kernel-only"` is the literal token the PASS line printed.
    Either one means only the Lean kernel replayed the export.
    """
    c = node.comparator
    if c is None:
        return False
    return (c.second_kernel.strip().lower().startswith("none")
            or c.kernel_mode.strip() == "lean-kernel-only")


def needs_rejudge(node: Node) -> bool:
    """A node whose proved status needs a passing local nanoda re-judge.

    Final-fix 1 (whole-branch review, 2026-10-28): driven by the flag OR by the judge record.
    Before, deleting `heavy_certificates = true` from a node toml made `rejudge_problem`
    return "" -- a node judged Lean-kernel-only in CI then stayed proved with no nanoda run at
    all. A `[comparator]` record that says nanoda was off now makes the node heavy too.

    Controller Ruling 0b-9 (2026-10-28): `judge_via = "heavy"` also counts. A node excluded
    from the per-PR bundle BY RULE (heavy workflow) is exactly the node the owner approved a
    Comparator re-judge for; before this, an h11000-shaped node with its `heavy_certificates`
    flag deleted and no `[comparator]` record read as "not needs_rejudge", so a nanoda-direct
    record could stand in for the Comparator re-judge Ruling 0b-4 demands.
    """
    return (bool(node.heavy_certificates) or judged_lean_kernel_only(node)
            or (getattr(node, "judge_via", "") or "").strip() == "heavy")


def second_kernel_claimed(node: Node) -> bool:
    """A node whose proved status is accompanied by SOME claim about a second kernel: either
    `needs_rejudge` (heavy, or judged Lean-kernel-only -- a re-judge is demanded) OR a
    `[rejudge]` record already exists (one was recorded voluntarily, as every nanoda-direct
    node's is -- none of the 7 is heavy_certificates or carries a `[comparator]` record at
    all, so `needs_rejudge` alone never sees them).

    Review fix round 1 (2026-10-28), item 2: before this, `rejudge_problem`'s `not
    needs_rejudge(node)` early return made a FAIL record or a stale-artifact-sha record on a
    non-heavy, no-`[comparator]` node completely invisible to `rejudge_problem` (and so to
    `mission verify`, the grant gate, and `render_provenance_report`) -- the record existed on
    disk, said something was wrong, and nothing downstream ever looked at it.

    Controller Ruling 0b-9 (2026-10-28): OR the node carries the durable registry marker
    `second_kernel_route`. Without it, deleting the `[rejudge]` table from one of the 7
    nanoda-direct nodes made this False, and the claim vanished with no error anywhere.
    """
    return (bool(needs_rejudge(node)) or bool(getattr(node, "second_kernel_route", ""))
            or node.rejudge is not None)


def rejudge_problem(campaign_root: Path, node: Node) -> str:
    """"" unless a node with a claimed second kernel (see `second_kernel_claimed`) lacks a
    passing, current, sufficient nanoda re-judge.

    "Claimed" covers three shapes: `heavy_certificates = true`; a `[comparator]` record whose
    second kernel was off; or simply a `[rejudge]` record being present at all (a node that is
    neither of the first two, but has one anyway -- every nanoda-direct node, step 0b Task 3).
    """
    if not second_kernel_claimed(node):
        return ""
    marker = (getattr(node, "second_kernel_route", "") or "").strip()
    if node.heavy_certificates:
        why = "heavy_certificates"
    elif judged_lean_kernel_only(node):
        why = (f"judged Lean-kernel-only (second_kernel = {node.comparator.second_kernel!r}, "
               "heavy_certificates absent)")
    elif (getattr(node, "judge_via", "") or "").strip() == "heavy":
        why = 'judge_via = "heavy"'
    elif marker:
        why = f"second_kernel_route = {marker!r}"
    else:
        why = "a [rejudge] record is present"
    r = node.rejudge
    # Controller Ruling 0b-9 (2026-10-28): the durable marker. A marked node whose
    # `[rejudge]` table was deleted, or whose record's route was edited, must fail --
    # never silently drop or change the claim. And a node that `needs_rejudge` may not be
    # MARKED nanoda-direct either (Ruling 0b-4 applies to the claim, not just the record).
    if marker and r is None:
        return f"second_kernel_route={marker} declared but no re-judge recorded"
    if marker and needs_rejudge(node) and marker != "comparator":
        return (f"second_kernel_route={marker} declared on a node that needs a Comparator "
                "re-judge (heavy, judge_via = \"heavy\", or judged Lean-kernel-only); "
                "nanoda-direct is not sufficient")
    if r is None:
        return f"{why}: no local nanoda re-judge recorded (`mission rejudge-record`)"
    if marker and r.route != marker:
        return (f"second_kernel_route={marker} declared but the [rejudge] record's route is "
                f"{r.route!r}")
    # Controller ruling 0b-5 (2026-10-28, review fix round 2): a record whose `route` is not
    # one of `rejudge.VALID_ROUTES` names nothing this codebase understands how to check --
    # reject it outright rather than let it fall through to the Comparator-only ruling below
    # (which only ever compares against the literal string "comparator").
    from .rejudge import VALID_ROUTES
    if r.route not in VALID_ROUTES:
        return f"re-judge route {r.route!r} is not a recognized route (must be one of {VALID_ROUTES})"
    # Controller ruling 0b-4 (2026-10-28, review fix round 1 item 2): a node `needs_rejudge`
    # demands a Comparator re-judge specifically -- nanoda-direct has no statement-identity
    # step, so it cannot discharge the stronger requirement a heavy/Lean-kernel-only node
    # carries, no matter how cleanly it passes. Checked before the verdict itself: a PASSING
    # nanoda-direct record on such a node is still insufficient, not merely "stale" or "FAILED".
    if needs_rejudge(node) and r.route != "comparator":
        return "heavy node requires a Comparator re-judge; nanoda-direct is not sufficient"
    if r.verdict != "pass":
        return f"local nanoda re-judge on {r.date} FAILED (nanoda {r.nanoda_rev[:8]})"
    if node.proof is None:
        return "heavy node has no artifact"
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return f"artifact {node.proof.artifact!r} does not exist"
    if sha256_file(art) != r.artifact_sha256:
        return (f"re-judge of {r.date} was on artifact sha256 {r.artifact_sha256[:12]}, "
                "which is no longer the artifact")
    # Task 1 (2026-10-28): a record must also be bound to the artifact's WHOLE import
    # closure, not only the top-level file -- a ladder capstone's certificates live in
    # imported modules. A record written before this field existed is not WRONG, just
    # unproven against the closure; back-fill (Task 2, git-verified unchanged) or re-judge.
    if not r.closure_sha256:
        return "re-judge predates closure binding; back-fill or re-judge"
    try:
        cur_closure = closure_digest(campaign_root, node)
    except ClosureError as exc:
        return f"re-judge closure cannot be resolved: {exc}"
    if cur_closure != r.closure_sha256:
        return (f"re-judge closure digest {r.closure_sha256[:12]}... no longer matches the "
                f"current import closure (now {cur_closure[:12]}...); back-fill or re-judge")
    return ""


#: Nodes created on or after this date are granted `proved` only with a passing `[checks]`
#: record (spec 5.2 grant rule, step 4 Task 4). Earlier nodes are "pre-process".
CHECKS_CUTOFF = "2026-10-28"


def checks_required(node: Node) -> bool:
    """True unless the node's `created` is an explicit, valid date before CHECKS_CUTOFF.

    Ruling 2 (step 4): an EMPTY `created` requires checks (fail-closed) -- otherwise a new node
    that omits the field skips every check. So does one that does not parse as an ISO date:
    a string compare alone would read "1999" as pre-process.
    """
    created = (node.created or "").strip()
    try:
        date.fromisoformat(created[:10])
    except ValueError:
        return True
    return created[:10] >= CHECKS_CUTOFF


def checks_problem(campaign_root: Path, node: Node) -> str:
    """"" iff the node's `[checks]` record passes on the artifact currently on disk; else why not.

    Passing: probe verdict WITNESSED, or PROBE_ONLY with a reviewer's `signoff: <who>` in the
    note (the probe is one-sided, spec 5.2); VACUOUS, REFUTED and ERROR block. The closure
    verdict must be PASS. Currency is checked by the artifact SOURCE digest only: the record's
    `olean_sha256` (the replayed closure the probe and fingerprint both ran on) cannot be
    recomputed without a build, so it is recorded for the reader and a changed source is what
    makes the record stale. Does not look at the cutoff; the gate applies `checks_required`.
    """
    k = node.checks
    if k is None:
        return "no [checks] record (`mission checks-record`)"
    if k.probe_verdict == "PROBE_ONLY":
        if not re.search(r"signoff:\s*\S", k.note or ""):
            return ("negation probe is PROBE_ONLY (one-sided: nothing witnessed the hypotheses); "
                    "it needs a reviewer's 'signoff: <who>' in the [checks] note")
    elif k.probe_verdict != "WITNESSED":
        return f"negation probe verdict is {k.probe_verdict} (recorded {k.date})"
    if k.closure_verdict != "PASS":
        return f"closure audit verdict is {k.closure_verdict} (recorded {k.date})"
    if node.proof is None:
        return "[checks] recorded but the node has no artifact"
    art = Path(campaign_root) / node.proof.artifact
    if not art.exists():
        return f"artifact {node.proof.artifact!r} does not exist"
    cur = sha256_file(art)
    if cur != k.artifact_sha256:
        return (f"[checks] of {k.date} were on artifact sha256 {k.artifact_sha256[:12]}..., but "
                f"the artifact on disk is {cur[:12]}...; re-run the checks on the current artifact")
    return ""


# ---------------------------------------------------------------------------
# Migration and report
# ---------------------------------------------------------------------------

def migrate_unverified(campaign_root: Path) -> List[str]:
    """Set `independence = "unverified"` on every read-back that has no value. Idempotent.

    Returns the slugs changed. Does not touch status, text, auditor or date, and does not
    add the field to nodes without a read-back.
    """
    changed: List[str] = []
    nodes_dir = Path(campaign_root) / "nodes"
    for p in sorted(nodes_dir.glob("*.toml")):
        node = load_node(p)
        if node.readback is None or node.readback.independence:
            continue
        rb = Readback(
            text=node.readback.text, auditor=node.readback.auditor, date=node.readback.date,
            auditor_identity=node.readback.auditor_identity,
            auditor_session=node.readback.auditor_session,
            independence="unverified",
        )
        import dataclasses
        save_node(dataclasses.replace(node, readback=rb), p)
        changed.append(p.stem)
    return changed


@dataclass(frozen=True)
class ProvenanceRow:
    campaign: str
    slug: str
    status: str
    independence: str      # "independent" | "unverified" | "self" | "none" (no read-back)
    self_audit: bool
    comparator_run: str    # "" when no passing run is recorded
    comparator_stale: bool
    lean_kernel_only: bool
    #: How the record was checked when written ("" for records predating the checks).
    log_check: str
    head_check: str
    has_grant: bool
    #: The literal `kernel=` token the log printed, or "unstated" for a pre-#632 log.
    kernel_mode: str = ""
    #: "" = judged by the per-PR bundle; "heavy" = excluded from it by rule and judged by the
    #: dispatch-only heavy workflow (see judge.HEAVY_WORKFLOW).
    judge_via: str = ""
    #: "compositional" when the recorded verdict glued separately judged parts (compose.py).
    judge_mode: str = ""
    parts: int = 0

    @property
    def flagged(self) -> bool:
        """A proved node whose read-back is not known-independent and that no passing
        Comparator run vouches for."""
        if self.status != "proved":
            return False
        if self.comparator_run and not self.comparator_stale:
            return False
        return self.independence != "independent" or self.self_audit


def provenance_rows(campaign) -> List[ProvenanceRow]:
    rows: List[ProvenanceRow] = []
    for sl in sorted(campaign.nodes):
        n = campaign.nodes[sl]
        rb = n.readback
        if rb is None:
            ind = "none"
        elif readback_is_self_audit(n):
            ind = "self"
        else:
            ind = rb.independence or "unverified"
        rows.append(ProvenanceRow(
            campaign=campaign.cname, slug=sl, status=n.status, independence=ind,
            self_audit=readback_is_self_audit(n),
            comparator_run=n.comparator.run_id if n.comparator else "",
            comparator_stale=bool(comparator_staleness(campaign.root, n)),
            # Only the heavy marker means "nanoda did not run".  Testing != "nanoda" would
            # read ANY other value -- e.g. a legacy record's "unstated" -- as the stronger
            # claim that the second kernel was skipped.
            lean_kernel_only=bool(n.comparator
                                  and n.comparator.second_kernel.startswith("none")),
            has_grant=n.grant is not None,
            log_check=(n.comparator.log_check if n.comparator else ""),
            head_check=(n.comparator.head_check if n.comparator else ""),
            kernel_mode=(n.comparator.kernel_mode if n.comparator else ""),
            judge_via=getattr(n, "judge_via", "") or "",
            judge_mode=(n.comparator.judge_mode if n.comparator else ""),
            parts=(len(n.comparator.parts) if n.comparator else 0),
        ))
    return rows


def render_provenance_report(campaign) -> str:
    """Per campaign: every PROVED node whose read-back is unverified or self-audited and
    that no passing Comparator run covers, then a one-line count."""
    rows = provenance_rows(campaign)
    proved = [r for r in rows if r.status == "proved"]
    flagged = [r for r in proved if r.flagged]
    lines = [f"{campaign.cname}: {len(proved)} proved, {len(flagged)} without an independent "
             "read-back or a passing Comparator run"]
    for r in flagged:
        comp = f"comparator={r.comparator_run}{' (stale)' if r.comparator_stale else ''}" \
            if r.comparator_run else "comparator=-"
        lines.append(f"  {r.slug:<48} readback={r.independence:<11} {comp}"
                     f"{'' if r.has_grant else '  grant=legacy'}")
        if r.judge_via == "heavy":
            # A known state, not an oversight: the per-PR bundle excludes this node BY RULE.
            lines.append(f"  {'':<48} per-PR Comparator: not run by rule (judge_via = heavy); "
                         "judged by missions-comparator-heavy.yml"
                         f"{'' if r.comparator_run else ' -- no heavy-judge run recorded yet'}")
    covered = [r for r in proved if r.comparator_run and not r.comparator_stale]
    if covered:
        lines.append(f"  ({len(covered)} proved node(s) covered by a passing Comparator run)")
    # Driven from `heavy_certificates` (not from having a `[comparator]` block at all: a
    # heavy node can be proved with NO comparator record yet, e.g. AND_ladder_h11000_kernel
    # on the real registry, and must still be reported on). `lean_kernel_only` is kept as an
    # OR so a legacy record that marks itself Lean-kernel-only without the flag still shows.
    # Review fix round 1 (2026-10-28), item 2: `second_kernel_claimed` (not `needs_rejudge`
    # alone) also picks up a node that is neither heavy nor Lean-kernel-only but carries a
    # `[rejudge]` record anyway -- every nanoda-direct node, none of which trips the first two.
    heavy_rows = [r for r in proved
                 if r.lean_kernel_only or second_kernel_claimed(campaign.nodes[r.slug])]
    for r in heavy_rows:
        node = campaign.nodes[r.slug]
        problem = rejudge_problem(campaign.root, node)
        comp = f"comparator={r.comparator_run}" if r.comparator_run else "comparator=-"
        if not problem and node.rejudge is not None:
            rj = node.rejudge
            # Controller Ruling 0b-9 (2026-10-28): name the route and whether the durable
            # `second_kernel_route` marker is set, on every passing second-kernel line.
            tag = (f" [route={rj.route}, marker="
                   f"{getattr(node, 'second_kernel_route', '') or 'unset'}]")
            if rj.route == "nanoda-direct":
                # Step 0b Task 3 (2026-10-28): this route has no Comparator statement-identity
                # step (no bundle was ever rendered for this node), so it must not read like
                # the stronger Comparator-checked line below -- see Review Focus 5.
                lines.append(f"  {r.slug:<48} {comp} Lean kernel + nanoda-direct "
                             f"(local re-judge {rj.date}, nanoda {rj.nanoda_rev[:8]}; "
                             f"no Comparator statement check){tag}")
            else:
                lines.append(f"  {r.slug:<48} {comp} Lean kernel + nanoda "
                             f"(local re-judge {rj.date}, nanoda {rj.nanoda_rev[:8]}){tag}")
        else:
            suffix = f" -- {problem}" if problem else ""
            # Review fix round 1 (2026-10-28), item 2: a non-heavy, non-Lean-kernel-only node
            # (every nanoda-direct node) reaching this branch is NOT "heavy_certificates:
            # nanoda not run" -- that wording is simply false for it, and was the reason a
            # FAIL/stale record on one of the 7 used to read like an unrelated heavy node's.
            if node.heavy_certificates:
                base = "Lean kernel only (heavy_certificates: nanoda not run)"
            elif judged_lean_kernel_only(node):
                base = "Lean kernel only (judged Lean-kernel-only; nanoda not run)"
            else:
                base = "no passing second-kernel re-judge recorded"
            lines.append(f"  {r.slug:<48} {comp} {base}{suffix}")
    for r in covered:
        weak = weak_record_reasons(r)
        if weak:
            lines.append(f"  {r.slug:<48} comparator={r.comparator_run} "
                         f"WEAKLY CHECKED: {'; '.join(weak)}")
    # Step 4 Task 4: the spec 5.2 checks, for every proved node the grant rule covers. Nodes
    # created before the cutoff were granted without them and are counted, not listed.
    pre = 0
    for r in proved:
        node = campaign.nodes[r.slug]
        if not checks_required(node):
            pre += 1
            continue
        problem = checks_problem(campaign.root, node)
        k = node.checks
        if not problem:
            signoff = " with sign-off" if k.probe_verdict == "PROBE_ONLY" else ""
            lines.append(f"  {r.slug:<48} checks: probe {k.probe_verdict}{signoff}, closure "
                         f"{k.closure_verdict} (recorded {k.date})")
        else:
            lines.append(f"  {r.slug:<48} checks: NOT PASSING -- {problem}")
    if pre:
        lines.append(f"  ({pre} proved node(s) pre-process: created before {CHECKS_CUTOFF}, "
                     "no [checks] required)")
    return "\n".join(lines) + "\n"


#: A Comparator record whose own checks were skipped or could not complete.  Not an error --
#: the record may be perfectly true -- but it must never read like a fully checked one.
def weak_record_reasons(row) -> List[str]:
    out = []
    if row.log_check == "skipped":
        out.append("written with --no-verify, so no judge log confirmed the theorem or kernel")
    elif row.log_check == "verified-offline":
        out.append("verified against a supplied log file; the job id is the recorder's word")
    if row.head_check == "unresolved":
        out.append("the artifact could not be hashed at the judged commit, so only the grant "
                   "pins the artifact")
    elif row.head_check == "skipped":
        out.append("the artifact was not checked at the judged commit")
    if row.kernel_mode == "unstated":
        out.append("the judge log predates the kernel field (#632), so it does not state "
                   "which second kernel ran")
    if row.comparator_run and not row.log_check and not row.head_check:
        out.append("predates the record checks (no log_check/head_check)")
    if getattr(row, "judge_mode", "") == "compositional":
        out.append(f"COMPOSITIONAL: the capstone's own proof was not replayed; its statement "
                   f"follows by a Comparator-checked implication from {max(row.parts - 1, 0)} "
                   "Comparator-checked segment statements, glued in telperion.missions.compose "
                   "(statement identity "
                   "by lean4export bytes, no certificate module in the implication's closure, "
                   "axioms per part)")
    return out
