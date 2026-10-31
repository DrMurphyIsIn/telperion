"""Step 5: making a mission campaign statement-first.

This module is the home for step 5's shared pieces -- the campaign-level statement freeze
(this task), and later tasks' Audit.lean generation, DEVIATIONS.md and a provenance lint.

Freeze. `FREEZE.toml` at the campaign root records the sha256 of every node's statement
BODY (`statements.statement_body`) at the moment the campaign was frozen: who froze it,
when, and the hash each statement had. `freeze_problems` re-derives those hashes from the
statement files on disk and reports drift, nodes added since the freeze, a statement file
that went missing, duplicate or self-read-back `[[unfreeze]]` entries, and an incomplete
unfreeze history. Unfreezing -- the only way to make a frozen campaign's hashes current
again -- is destructive to the freeze's truth-claim, so every version bump demands a
recorded reason AND an independent read-back of the new hashes
(`docs/AUDIT_INDEPENDENCE_2026-09-23.md`'s independence rule, applied here to the freeze
record rather than to a node's statement).

Controller Ruling 5 (fix round 1, 2026-10-30): the checks above compare the CURRENT
`FREEZE.toml` against the CURRENT statement files and against itself -- none of them notice
a statement edited and the recorded hash hand-rewritten to match, in the same commit, while
`version` is left unchanged. `freeze_history_problems` closes that hole by walking
`FREEZE.toml`'s git history and checking, between every consecutive DISTINCT state: version
never decreases; at an unchanged version, `[statements]` is identical except that new node
keys may be added; on any removed or changed hash, version is exactly +1 with a matching
`[[unfreeze]]` entry for the new version; and every earlier `[[unfreeze]]` entry is
byte-identical to what it was before (append-only). `freeze_problems` calls it.

Controller Ruling 7 (fix round 3, 2026-10-30), hardening the walk itself after a re-review
found three ways to defeat it: the walk no longer trusts `git log --follow` plus a lookup
by TODAY's path (a file renamed away and back hid every commit in between -- NEW-3); it now
walks EVERY commit on the first-parent chain from the file's first appearance to HEAD,
confirms at each one (via `ls-tree`, not a full `show`, to stay fast) that the path still
resolves to an ordinary file, and stops the moment it does not, rather than silently
skipping a commit it cannot resolve at the expected path. It also refuses a SHALLOW clone
(NEW-2 -- CI's typical default, which truncates history by construction and needs no
adversarial action to reproduce the same blind spot) and a FREEZE.toml that is, or ever
was, a symlink (its target can move independently of the history being walked). All of
this fails closed ONLY for a post-cutoff campaign, the same as Ruling 5.

Controller Ruling 8 (fix round 4, 2026-10-30), after re-review 2:
- One guarded reader. `_load_freeze_safe` is the only reader of the working-tree
  FREEZE.toml. It refuses a symlink before reading anything through it, refuses
  non-regular files and files over `FREEZE_MAX_BYTES`, and turns non-UTF-8, non-TOML and
  wrongly-shaped content into a problem string instead of an exception. `freeze_problems`
  and `freeze_grant_problem` used to read through a symlink before the walk's own check
  ran, and crashed `mission grant`/`mission verify` on non-UTF-8 content.
- A single-pass walk. Round 3's one `ls-tree` per commit (about 29 s for 2,000 commits,
  paid on every post-cutoff grant) became ONE `git log --first-parent --raw` of the path
  plus `git cat-file` for the blobs, with the same refusals. A gitlink at the path now
  says so.
- The walk runs from the repository's top level. Round 3 ran it from the campaign root,
  so every campaign in a subdirectory was reported as never committed.

What it still cannot see (NEW-1, documented rather than coded -- inherent to local git, not
fixable by walking harder): a history REWRITE that replaces the whole committed history
with one internally self-consistent fabrication (`git commit --amend` on the sole commit,
or an equivalent rebase/force-push) looks identical to an honest history, because there is
nothing else to compare it against. For a node that has already been GRANTED, this is not
actually a hole: the grant records its own `statement_sha256` (`provenance.build_grant`)
against the artifact the gate saw at grant time, independent of FREEZE.toml, so a later
rewrite cannot make a granted node's statement look unchanged to `mission verify`. For an
UNGRANTED node, an amended first freeze -- before anyone else has
fetched it -- is genuinely indistinguishable from an honest one by anything running only
against a local checkout. The intended anchor is organizational, not computational: a
protected remote branch (no force-push) with `mission verify` run in CI against the FULL
history of that branch (hence the shallow-clone refusal above), not against whatever a
local, possibly-rewritten clone happens to contain.

The same goes for everything else in the local `.git` directory (Controller Ruling 9, fix
round 5): replace refs, config, hooks, grafts and alternates are in the same trust class
as rewriting history. Anyone who can write them can rewrite history outright. The guards
here stop accidental and casual tampering:
- every git call goes through `_git`: `--no-replace-objects`, and an environment with no
  inherited `GIT_*` variables (re-review 3 bypassed the walk with a `git replace` ref, and
  separately with `GIT_DIR` aimed at a decoy repository);
- the user's config cannot change what the walk reads, because every behaviour it depends
  on is pinned by an explicit flag;
- a repository with `info/grafts` or `objects/info/(http-)alternates` is refused for a
  post-cutoff campaign.

They are not a defence against a determined owner of the clone. That anchor is still a
fresh full clone of a protected branch, verified in CI.

Step 5 Task 6 adds a second table, `[fingerprints]`: each node's statement fingerprint
(`checks.fingerprint`), recorded by `freeze`/`unfreeze` when given one (`mission freeze
--fingerprints` computes them with Lean, `compute_statement_fingerprints`). The history walk
holds it to the same rule as `[statements]`, and `statement_fingerprint_problem` is the
semantic theorem tie the gate applies to post-cutoff `[checks]` records (see the section of
that name below).

`CUTOFF` is the single source of truth for the post-process cutoff date (Controller Ruling
1, 2026-10-30): `provenance.CHECKS_CUTOFF` is an alias of it, kept for back-compat. This
module must NOT import `provenance` or `verify` at module level -- both of those already
import (or will import) this one, and a module-level import back here would cycle. Every
use of `provenance` below is therefore a lazy, in-function import.
"""
from __future__ import annotations

import datetime
import hashlib
import os
import re
import stat
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

from .schema import atomic_write_text, slug_of
from .statements import statement_body, statement_path

#: Single source of truth for the post-process cutoff date (Controller Ruling 1).
#: `telperion.missions.provenance.CHECKS_CUTOFF` is `CUTOFF` under its old name.
CUTOFF = "2026-10-28"

#: Name of the campaign-level freeze record, at the campaign root (next to `mission.toml`).
FREEZE_FILENAME = "FREEZE.toml"

#: A statement fingerprint (`checks.fingerprint`): sha256, lowercase hex.
_SHA256_HEX_RE = re.compile(r"[0-9a-f]{64}")


def freeze_path(root: Path) -> Path:
    """`<root>/FREEZE.toml`, the campaign-level freeze record."""
    return Path(root) / FREEZE_FILENAME


# ---------------------------------------------------------------------------
# TOML I/O for FREEZE.toml
#
# `schema.dumps_toml`/`loads_toml` are a closed loop over the restricted subset node/manifest
# files need (no array-of-tables). FREEZE.toml's `[[unfreeze]]` history needs exactly that,
# so this module reads with a real TOML parser (tomllib/tomli, same preference order as
# `schema.loads_toml`) and writes with a small hand-rolled emitter for the fixed shape below
# -- there is no fallback parser here, unlike schema.py's, because nothing in this repo reads
# FREEZE.toml on an interpreter old enough to lack both tomllib and tomli.
# ---------------------------------------------------------------------------

def _quote(value) -> str:
    s = str(value)
    return ('"' + s.replace("\\", "\\\\").replace('"', '\\"')
            .replace("\n", "\\n").replace("\r", "\\r") + '"')


def _dump_freeze(doc: dict) -> str:
    lines = [
        f"version = {int(doc['version'])}",
        f"frozen = {_quote(doc['frozen'])}",
        f"identity = {_quote(doc['identity'])}",
        f"session = {_quote(doc['session'])}",
    ]
    if doc.get("fingerprints_env"):
        lines.append(f"fingerprints_env = {_quote(doc['fingerprints_env'])}")
    lines += ["", "[statements]"]
    statements = doc.get("statements") or {}
    for slug in sorted(statements):
        lines.append(f"{_quote(slug)} = {_quote(statements[slug])}")
    fingerprints = doc.get("fingerprints") or {}
    if fingerprints:
        lines.append("")
        lines.append("[fingerprints]")
        for slug in sorted(fingerprints):
            lines.append(f"{_quote(slug)} = {_quote(fingerprints[slug])}")
    imports = doc.get("imports") or {}
    if imports:
        lines.append("")
        lines.append("[imports]")
        for module in sorted(imports):
            lines.append(f"{_quote(module)} = {_quote(imports[module])}")
    for entry in doc.get("unfreeze") or ():
        lines.append("")
        lines.append("[[unfreeze]]")
        lines.append(f"version = {int(entry['version'])}")
        lines.append(f"date = {_quote(entry['date'])}")
        lines.append(f"author = {_quote(entry['author'])}")
        lines.append(f"reason = {_quote(entry['reason'])}")
        lines.append(f"readback_identity = {_quote(entry['readback_identity'])}")
    return "\n".join(lines) + "\n"


#: Upper bound on a FREEZE.toml, in the working tree or in history. A real record is a few
#: hundred bytes plus one line per node; anything this large is not one, and refusing it
#: before decoding keeps a hostile file from costing more than a stat.
FREEZE_MAX_BYTES = 1 << 20

_UNFREEZE_STR_FIELDS = ("date", "author", "reason", "readback_identity")


def _is_int(value) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _freeze_shape_problem(doc: dict) -> Optional[str]:
    """Why *doc* does not have `_dump_freeze`'s shape, or None. Every reader below indexes
    these fields directly, so a hand-edit that changes a field's type must surface here as
    a problem, not later as a TypeError or ValueError (`int("two")`)."""
    if not _is_int(doc.get("version")) or doc["version"] < 1:
        return "has no positive integer `version`"
    if not isinstance(doc.get("frozen"), str):
        return "has no string `frozen` date"
    for key in ("identity", "session", "fingerprints_env"):
        if key in doc and not isinstance(doc[key], str):
            return f"has a non-string `{key}`"
    statements = doc.get("statements", {})
    if not isinstance(statements, dict) or not all(
            isinstance(v, str) for v in statements.values()):
        return "has a `statements` that is not a table of string hashes"
    fingerprints = doc.get("fingerprints", {})
    if not isinstance(fingerprints, dict) or not all(
            isinstance(v, str) for v in fingerprints.values()):
        return "has a `fingerprints` that is not a table of string fingerprints"
    imports = doc.get("imports", {})
    if not isinstance(imports, dict) or not all(isinstance(v, str) for v in imports.values()):
        return "has an `imports` that is not a table of string hashes"
    entries = doc.get("unfreeze", [])
    if not isinstance(entries, list):
        return "has an `unfreeze` that is not an array of tables"
    for entry in entries:
        if not isinstance(entry, dict) or not _is_int(entry.get("version")):
            return "has an `unfreeze` entry that is not a table with an integer `version`"
        if any(k in entry and not isinstance(entry[k], str) for k in _UNFREEZE_STR_FIELDS):
            return "has an `unfreeze` entry with a non-string field"
    return None


def _parse_freeze_bytes(data: bytes) -> Tuple[Optional[dict], Optional[str]]:
    """`(doc, None)`, or `(None, why)` where *why* completes a sentence about where the bytes
    came from ("is not valid UTF-8"). Shared by the working-tree loader and the history walk
    so both refuse the same things. Never raises."""
    if len(data) > FREEZE_MAX_BYTES:
        return None, f"is larger than {FREEZE_MAX_BYTES} bytes"
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return None, "is not valid UTF-8"
    try:
        import tomllib
    except ModuleNotFoundError:
        import tomli as tomllib  # type: ignore[no-redef]
    try:
        doc = tomllib.loads(text)
    except Exception as exc:  # TOMLDecodeError, or whatever else a hostile file provokes
        return None, f"is not valid TOML ({exc})"
    shape = _freeze_shape_problem(doc)
    if shape:
        return None, shape
    return doc, None


def _load_freeze_safe(root: Path) -> Tuple[Optional[dict], Optional[str]]:
    """THE reader of the working-tree FREEZE.toml (Controller Ruling 8, fix round 4): every
    function here that needs the record goes through this one. Returns `(doc, None)`;
    `(None, None)` when the campaign has not been frozen; or `(None, problem)` when the path
    exists but cannot be trusted. Never raises.

    Refused, in this order, before anything is read through the path: a symlink (its target
    can be any file at all -- re-review 2 found `freeze_problems` and `freeze_grant_problem`
    reading `mission.toml` through one, and crashing `mission grant`/`mission verify` with a
    UnicodeDecodeError through one aimed at binary content); anything else that is not a
    regular file (a directory, e.g. a submodule checkout); a file over `FREEZE_MAX_BYTES`.
    Then the content: not UTF-8, not TOML, or not FREEZE.toml's shape. The open uses
    O_NOFOLLOW, so a symlink swapped in after the lstat is refused too, not followed.
    """
    path = freeze_path(root)
    try:
        st = path.lstat()
    except FileNotFoundError:
        return None, None
    except OSError as exc:
        return None, f"{FREEZE_FILENAME} could not be read ({exc.strerror or exc})."
    if stat.S_ISLNK(st.st_mode):
        return None, f"{FREEZE_FILENAME} is a symlink in the working tree; refusing to trust it."
    if not stat.S_ISREG(st.st_mode):
        return None, (
            f"{FREEZE_FILENAME} in the working tree is not a regular file (a directory, e.g. "
            "a submodule checkout, or a special file); refusing to trust it."
        )
    if st.st_size > FREEZE_MAX_BYTES:
        return None, (f"{FREEZE_FILENAME} is larger than {FREEZE_MAX_BYTES} bytes; refusing "
                      "to trust it.")
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
                     | getattr(os, "O_NONBLOCK", 0))
        with os.fdopen(fd, "rb") as fh:
            if not stat.S_ISREG(os.fstat(fh.fileno()).st_mode):
                return None, (f"{FREEZE_FILENAME} changed while being read; refusing to "
                              "trust it.")
            data = fh.read(FREEZE_MAX_BYTES + 1)
    except OSError as exc:
        return None, f"{FREEZE_FILENAME} could not be read ({exc.strerror or exc})."
    doc, why = _parse_freeze_bytes(data)
    if why:
        return None, f"{FREEZE_FILENAME} {why}; refusing to trust it."
    return doc, None


def _load_freeze(root: Path) -> Optional[dict]:
    """`_load_freeze_safe` for a caller that refuses rather than reports (`unfreeze`): the
    parsed document, None if the campaign has not been frozen, or `ValueError` carrying the
    problem."""
    doc, problem = _load_freeze_safe(root)
    if problem:
        raise ValueError(problem)
    return doc


def _write_freeze(root: Path, doc: dict) -> None:
    atomic_write_text(freeze_path(root), _dump_freeze(doc))


def _hash_statement(root: Path, node) -> str:
    """sha256 hex of *node*'s on-disk statement body (`statements.statement_body`)."""
    return hashlib.sha256(statement_body(root, node).encode("utf-8")).hexdigest()


def _import_lines(text: str) -> List[str]:
    """The modules a Lean file imports (`import A.B`, comments ignored)."""
    from .judge import _guard_anchors
    code = _guard_anchors().blank_lean_code(text)
    out: List[str] = []
    for m in re.finditer(r"(?m)^[ \t]*import[ \t]+([^\n]*)$", code):
        out.extend(m.group(1).split())
    return out


def project_import_hashes(root: Path, campaign) -> Dict[str, str]:
    """Step 5 Task 6, fix round 3 (Ruling 20): module -> sha256 of its source, for every PROJECT
    module in the import closure of the campaign's statement files. A module whose first
    component is a library root (`checks.fingerprint.LIBRARY_ROOTS`: Mathlib, Init, ...) is the
    trusted env's and stops the walk; any other import must be a source file of this campaign,
    `<root>/lean/<A>/<B>.lean` (a regular file, not a symlink), whose own imports are walked in
    turn. `ValueError` for an import that is neither, or whose name is not a plain dotted
    identifier. Recorded in FREEZE.toml `[imports]`, so a change to an imported definitions
    module is visible as drift and needs an unfreeze (the semantic tie already sees it, since
    non-library constants are unfolded; this is for the read-back)."""
    from ..closure_audit import DEFAULT_LIBRARY_ROOTS, _IDENT_COMPONENT

    lean_dir = Path(root) / "lean"
    todo: List[str] = []
    for node in campaign.nodes.values():
        sp = statement_path(root, node)
        if sp.exists():
            todo.extend(_import_lines(sp.read_text(encoding="utf-8")))
    out: Dict[str, str] = {}
    while todo:
        module = todo.pop()
        if module in out or module.split(".")[0] in DEFAULT_LIBRARY_ROOTS:
            continue
        parts = module.split(".")
        if any(not p or p[0].isdigit() or not _IDENT_COMPONENT.match(p) for p in parts):
            raise ValueError(f"import {module!r} is not a plain dotted Lean module name")
        src = lean_dir.joinpath(*parts).with_suffix(".lean")
        try:
            st = src.lstat()
        except FileNotFoundError:
            raise ValueError(f"import {module!r} is neither a library module ({', '.join(DEFAULT_LIBRARY_ROOTS)}) "
                             f"nor a source file of this campaign ({src})") from None
        if not stat.S_ISREG(st.st_mode):
            raise ValueError(f"imported module {module!r} is not a regular file ({src}); refusing to hash it")
        data = src.read_bytes()
        out[module] = hashlib.sha256(data).hexdigest()
        todo.extend(_import_lines(data.decode("utf-8", errors="replace")))
    return out


def _current_statement_hashes(root: Path, campaign) -> Dict[str, str]:
    return {
        slug: _hash_statement(root, node)
        for slug, node in campaign.nodes.items()
        if statement_path(root, node).exists()
    }


# ---------------------------------------------------------------------------
# freeze / unfreeze
# ---------------------------------------------------------------------------

def _fingerprints_env(fingerprints, fingerprints_env: Optional[str]) -> Optional[str]:
    """The trusted env digest to record with *fingerprints*: *fingerprints_env*, else the one a
    `StatementFingerprints` carries; `ValueError` when there are fingerprints and no valid one."""
    env = fingerprints_env or getattr(fingerprints, "trusted_env_sha256", None)
    if not fingerprints:
        return None
    if not isinstance(env, str) or not _SHA256_HEX_RE.fullmatch(env):
        raise ValueError(f"statement fingerprints need the trusted env digest they were computed "
                         f"under (64 lowercase hex), not {env!r}.")
    return env


def _checked_fingerprints(fingerprints: Optional[Dict[str, str]],
                          statements: Dict[str, str]) -> Dict[str, str]:
    """*fingerprints* (slug -> sha256 hex) as `freeze`/`unfreeze` record them, or `ValueError`
    for one that names a node with no recorded statement or is not 64 lowercase hex."""
    out: Dict[str, str] = {}
    for slug, fp in sorted((fingerprints or {}).items()):
        if slug not in statements:
            raise ValueError(f"statement fingerprint given for {slug!r}, which has no statement "
                             "file to freeze.")
        if not isinstance(fp, str) or not _SHA256_HEX_RE.fullmatch(fp):
            raise ValueError(f"statement fingerprint for {slug!r} is not 64 lowercase hex "
                             f"characters ({fp!r}).")
        out[slug] = fp
    return out


def freeze(root: Path, *, identity: str, session: str, date: str,
           fingerprints: Optional[Dict[str, str]] = None,
           fingerprints_env: Optional[str] = None) -> dict:
    """Write `<root>/FREEZE.toml`: version 1, the freezing identity/session, and the sha256
    of every node's current statement body. Refuses (`ValueError`) if the campaign is
    already frozen -- re-running `freeze` would silently discard the unfreeze history;
    `unfreeze` is the only supported way to bring a frozen campaign's hashes current.

    Fix round 3 (Ruling 20): the imported PROJECT modules are recorded too, in `[imports]`,
    by source sha256 (`project_import_hashes`).

    Step 5 Task 6: *fingerprints* (slug -> statement fingerprint, as
    `compute_statement_fingerprints` returns them -- exactly what Lean elaborates, from a
    statement layer that is trusted read-back content) are recorded in `[fingerprints]`; with
    none, nothing is recorded there and the gate refuses every post-cutoff `[checks]` record
    with "statement fingerprint not frozen". *fingerprints_env* (default: the one a
    `StatementFingerprints` carries) is the trusted env they were computed under, recorded as
    `fingerprints_env`; fingerprints without one are refused."""
    from .provenance import require_identity

    require_identity(identity, session, "freeze")
    root = Path(root)
    # is_symlink too: exists() is False for a dangling symlink, which the write below would
    # otherwise replace silently.
    if freeze_path(root).exists() or freeze_path(root).is_symlink():
        raise ValueError(
            f"{root.name} is already frozen ({FREEZE_FILENAME} exists); use `unfreeze` to "
            "record an update, not `freeze` again."
        )
    from .registry import load_campaign

    campaign = load_campaign(root)
    statements = _current_statement_hashes(root, campaign)
    doc = {
        "version": 1,
        "frozen": date,
        "identity": identity.strip(),
        "session": session.strip(),
        "statements": statements,
        "fingerprints": _checked_fingerprints(fingerprints, statements),
        "fingerprints_env": _fingerprints_env(fingerprints, fingerprints_env),
        "imports": project_import_hashes(root, campaign),
    }
    _write_freeze(root, doc)
    return doc


def unfreeze(root: Path, *, author: str, reason: str, readback_identity: str, date: str,
             fingerprints: Optional[Dict[str, str]] = None,
             fingerprints_env: Optional[str] = None) -> dict:
    """Bump the freeze: re-hash every current statement, append a `[[unfreeze]]` entry, and
    write the new version. Refuses (`ValueError`) a self-read-back -- `readback_identity`
    equal to `author`, compared the way `provenance.independence_of` compares identities
    (case-folded) -- and refuses when the campaign was never frozen at all.

    Step 5 Task 6: the new version's `[fingerprints]` are exactly *fingerprints*; the old
    version's are never carried forward (a fingerprint also depends on the definitions a
    statement imports, which the statement hash does not cover), so an unfreeze without
    them leaves post-cutoff `[checks]` records refused until the next one with them."""
    root = Path(root)
    doc = _load_freeze(root)
    if doc is None:
        raise ValueError(f"{root.name} has no {FREEZE_FILENAME}; call `freeze` first.")
    if not (author or "").strip():
        raise ValueError("unfreeze: author must be non-empty.")
    if not (reason or "").strip():
        raise ValueError("unfreeze: reason must be non-empty.")
    if not (readback_identity or "").strip():
        raise ValueError("unfreeze: readback_identity must be non-empty.")
    if readback_identity.strip().lower() == author.strip().lower():
        raise ValueError(
            f"unfreeze: readback_identity {readback_identity!r} is the author's own identity; "
            "an unfreeze must be read back by someone else before it is trusted "
            "(docs/AUDIT_INDEPENDENCE_2026-09-23.md)."
        )

    from .registry import load_campaign

    campaign = load_campaign(root)
    new_version = int(doc.get("version", 1)) + 1
    entries = list(doc.get("unfreeze") or [])
    entries.append({
        "version": new_version,
        "date": date,
        "author": author.strip(),
        "reason": reason.strip(),
        "readback_identity": readback_identity.strip(),
    })
    statements = _current_statement_hashes(root, campaign)
    new_doc = {
        "version": new_version,
        "frozen": doc.get("frozen", ""),
        "identity": doc.get("identity", ""),
        "session": doc.get("session", ""),
        "statements": statements,
        "fingerprints": _checked_fingerprints(fingerprints, statements),
        "fingerprints_env": _fingerprints_env(fingerprints, fingerprints_env),
        "imports": project_import_hashes(root, campaign),
        "unfreeze": entries,
    }
    _write_freeze(root, new_doc)
    return new_doc


# ---------------------------------------------------------------------------
# freeze_problems / freeze_grant_problem
# ---------------------------------------------------------------------------

def freeze_problems(root: Path, *, require_history: bool = False) -> List[str]:
    """Campaign-wide freeze problems for `verify_campaign`'s read-only battery:

    - "statement drift" on any node whose current statement hash differs from the one
      recorded in FREEZE.toml;
    - any node with a statement file that was added since the freeze (not recorded at all);
    - a node recorded in FREEZE.toml whose statement file no longer exists (fix round 1,
      finding C2: deleting the file used to silently drop the node from every check here);
    - any `version > 1` missing a matching `[[unfreeze]]` entry for 2..version (a
      hand-rewritten FREEZE.toml, since `unfreeze` itself always appends exactly one per
      call);
    - more than one `[[unfreeze]]` entry for the same version (fix round 1, finding I:
      `unfreeze` never writes two, so two can only mean a hand-edit, and checking only the
      last one per version -- the previous behaviour -- let a self-read-back hide behind a
      later, clean duplicate);
    - any `[[unfreeze]]` entry that is a self-read-back, checked on EVERY entry rather than
      only the one `version` happens to point at (same reason as the previous bullet);
    - `freeze_history_problems(root)` (fix round 1, Controller Ruling 5): everything above
      compares FREEZE.toml against itself and against the statement files as they are RIGHT
      NOW, so a statement edited and the recorded hash hand-rewritten to match -- in the same
      commit, with `version` left unchanged -- passes every check above. Only the file's git
      history can catch that.

    A missing FREEZE.toml is not a problem unless a post-cutoff node is already PROVED.
    `freeze_grant_problem` already refuses to grant such a node without one, so a proved,
    post-cutoff node with no FREEZE.toml on disk means the record was removed (or never
    existed) after the fact -- the same "re-check at verify time what the gate already
    required at grant time" shape as `checks_required`'s and `rejudge_problem`'s own
    section-2 checks in `verify_campaign`. A draft or open post-cutoff node has not been
    granted yet and so has nothing to freeze; checking it here would fail every freshly
    added node before anyone could even think about granting it.

    Fix round 1 (Ruling 18, M1): the git history is REQUIRED (refused when unavailable, shallow
    and so on) whenever *require_history* is set (`freeze_grant_problem`, for a post-cutoff
    node) or a proved node is post-cutoff, whatever FREEZE.toml's own `frozen` date says.
    """
    from .provenance import checks_required

    root = Path(root)
    from .registry import load_campaign

    campaign = load_campaign(root)
    doc, unreadable = _load_freeze_safe(root)
    if unreadable:
        # Nothing in an untrusted record can be compared against, including the `frozen`
        # date that decides whether anything below applies (fix round 4, Ruling 8).
        return [unreadable]
    problems: List[str] = []

    if doc is None:
        post = sorted(slug for slug, node in campaign.nodes.items()
                      if node.status == "proved" and checks_required(node))
        if post:
            problems.append(
                f"no {FREEZE_FILENAME} at the campaign root, but post-cutoff node(s) exist "
                f"({', '.join(post)}); freeze the campaign (`mission freeze`)."
            )
        return problems

    statements = doc.get("statements") or {}
    for slug, node in sorted(campaign.nodes.items()):
        sp = statement_path(root, node)
        recorded = statements.get(slug)
        if recorded is None:
            if sp.exists():
                problems.append(
                    f"node {slug!r} has a statement file but is not recorded in "
                    f"{FREEZE_FILENAME} (added since the freeze, or removed from the record "
                    "by hand)."
                )
            continue
        if not sp.exists():
            problems.append(
                f"node {slug!r} is recorded in {FREEZE_FILENAME} but its statement file no "
                "longer exists."
            )
            continue
        current = _hash_statement(root, node)
        if current != recorded:
            problems.append(
                f"node {slug!r}: statement drift -- current hash {current[:16]}... does not "
                f"match the frozen hash {str(recorded)[:16]}... in {FREEZE_FILENAME}."
            )

    # Fix round 3 (Ruling 20): the imported project modules, by source sha256.
    recorded_imports = doc.get("imports") or {}
    try:
        current_imports = project_import_hashes(root, campaign)
    except (OSError, ValueError) as exc:
        problems.append(f"the statement files' project imports cannot be hashed: {exc}")
        current_imports = None
    if current_imports is not None:
        for module in sorted(set(recorded_imports) | set(current_imports)):
            was, now = recorded_imports.get(module), current_imports.get(module)
            if was is None:
                problems.append(
                    f"imported project module {module!r} is not recorded in {FREEZE_FILENAME} "
                    "[imports] (imported since the freeze); unfreeze to record it.")
            elif now is None:
                problems.append(
                    f"{FREEZE_FILENAME} [imports] records {module!r}, which no statement file imports "
                    "any more (or whose source is gone); unfreeze to record the change.")
            elif now != was:
                problems.append(
                    f"imported project module {module!r}: import drift -- its source hash "
                    f"{now[:16]}... does not match the frozen {was[:16]}... in {FREEZE_FILENAME}.")

    # Step 5 Task 6: `[fingerprints]` must describe recorded statements, as sha256 hex, computed
    # under one named trusted env (fix round 1, M2: `fingerprints_env`).
    env = doc.get("fingerprints_env")
    if doc.get("fingerprints") and not (env and _SHA256_HEX_RE.fullmatch(env)):
        problems.append(
            f"{FREEZE_FILENAME} records statement fingerprints but no `fingerprints_env` (the "
            "trusted env digest they were computed under, 64 lowercase hex)."
        )
    for slug, fp in sorted((doc.get("fingerprints") or {}).items()):
        if slug not in statements:
            problems.append(
                f"{FREEZE_FILENAME} records a statement fingerprint for {slug!r}, which has no "
                "[statements] entry."
            )
        if not _SHA256_HEX_RE.fullmatch(fp):
            problems.append(
                f"{FREEZE_FILENAME} records a statement fingerprint for {slug!r} that is not 64 "
                f"lowercase hex characters ({fp[:20]!r})."
            )

    version = int(doc.get("version", 1))
    entries = doc.get("unfreeze") or []

    # Self-read-back: checked on every entry, not only the last one recorded for its
    # version -- a forged self-read-back could otherwise hide behind a later, clean
    # duplicate entry for the same version (fix round 1, finding I).
    for entry in entries:
        author = str(entry.get("author", ""))
        readback_identity = str(entry.get("readback_identity", ""))
        if author.strip().lower() == readback_identity.strip().lower():
            problems.append(
                f"{FREEZE_FILENAME} [[unfreeze]] entry for version "
                f"{entry.get('version', '?')!r} is a self-read-back (readback_identity "
                f"{readback_identity!r} matches author {author!r})."
            )

    counts: Dict[int, int] = {}
    for entry in entries:
        try:
            v = int(entry.get("version", -1))
        except (TypeError, ValueError):
            continue
        counts[v] = counts.get(v, 0) + 1
    for v, n in sorted(counts.items()):
        if n > 1:
            problems.append(
                f"{FREEZE_FILENAME} has {n} [[unfreeze]] entries for version {v}; "
                "unfreeze() never writes more than one."
            )

    for v in range(2, version + 1):
        if v not in counts:
            problems.append(
                f"{FREEZE_FILENAME} version is {version} but has no [[unfreeze]] entry for "
                f"version {v}."
            )

    require = require_history or any(node.status == "proved" and checks_required(node)
                                     for node in campaign.nodes.values())
    problems.extend(freeze_history_problems(root, require=require))
    return problems


# ---------------------------------------------------------------------------
# freeze_history_problems (fix round 1, Controller Ruling 5)
# ---------------------------------------------------------------------------

def _git_env() -> Dict[str, str]:
    """The environment every git call runs in (Controller Ruling 9, fix round 5): the
    caller's, minus EVERY `GIT_*` variable -- re-review 3 pointed the whole walk at a decoy
    repository with nothing but `GIT_DIR` set, while the working-tree read still saw the
    real file -- plus no system config, no prompts, the C locale, and no replace objects.
    HOME and PATH are kept: git needs them to run at all, and the user's global config is
    defeated where it matters by the explicit flags each call pins."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_TERMINAL_PROMPT="0", LC_ALL="C",
               GIT_NO_REPLACE_OBJECTS="1")
    return env


def _git(args: Sequence[str], cwd: Path, *, stdin: Optional[bytes] = None,
         timeout: int = 10) -> Optional["subprocess.CompletedProcess[bytes]"]:
    """THE way this module runs git (Controller Ruling 9, fix round 5; a structural test
    holds every other subprocess call out of process.py): `git --no-replace-objects -C
    <cwd> <args>` in `_git_env()`, output as bytes. `--no-replace-objects` because a
    `git replace` ref made the genesis commit look like the tampered one and the walk
    returned [] (re-review 3). Returns None if git cannot be run or times out."""
    try:
        return subprocess.run(
            ["git", "--no-replace-objects", "-C", str(cwd), *args],
            input=stdin, capture_output=True, timeout=timeout, env=_git_env(),
        )
    except (OSError, subprocess.SubprocessError):
        return None


def _git_line(args: Sequence[str], cwd: Path) -> Optional[str]:
    """Stripped stdout of a successful `_git` call, or None."""
    out = _git(args, cwd)
    if out is None or out.returncode != 0:
        return None
    return os.fsdecode(out.stdout).strip()


def _is_git_repo(root: Path) -> bool:
    return _git_line(["rev-parse", "--is-inside-work-tree"], root) == "true"


def _git_toplevel(root: Path) -> Optional[Path]:
    top = _git_line(["rev-parse", "--show-toplevel"], root)
    return Path(top) if top else None


def _is_shallow_repo(root: Path) -> bool:
    return _git_line(["rev-parse", "--is-shallow-repository"], root) == "true"


#: Files in a git directory that make its object store or its parentage say something
#: other than the commits themselves: grafts rewrite parents, alternates borrow objects
#: from another repository the walk cannot vouch for (Controller Ruling 9).
_UNTRUSTED_GIT_FILES = ("info/grafts", "objects/info/alternates",
                        "objects/info/http-alternates")


def _untrusted_git_file(root: Path) -> Optional[str]:
    """A problem naming the first `_UNTRUSTED_GIT_FILES` entry present in the repository's
    git directory or common directory (a linked worktree has both), or None. Fails closed:
    if git cannot say where its directory is, that is a problem too."""
    out = _git_line(["rev-parse", "--git-dir", "--git-common-dir"], root)
    dirs = out.splitlines() if out else []
    if len(dirs) != 2:
        return (f"{FREEZE_FILENAME}: freeze history unavailable (could not locate the git "
                "directory).")
    for gitdir in dict.fromkeys(dirs):
        base = Path(gitdir) if Path(gitdir).is_absolute() else Path(root) / gitdir
        for name in _UNTRUSTED_GIT_FILES:
            if os.path.lexists(base / name):
                return (f"{FREEZE_FILENAME}: freeze history untrusted: the repository has "
                        f"{base / name}; remove it (or use a fresh full clone) so the "
                        "history walked is the repository's own.")
    return None


#: Commit header in `_freeze_path_log`'s `git log` output. Raw diff lines start with ':', and
#: the path that follows each one is consumed by position, so neither can be mistaken for it.
_LOG_MARKER = "@@commit "

#: Regular-file modes. Anything else at FREEZE.toml's path -- a symlink (120000), a
#: gitlink/submodule (160000) -- is refused.
_REGULAR_MODES = ("100644", "100755")

#: One first-parent commit at which FREEZE.toml's path changed: `(commit sha, [(path, new
#: mode, new object), ...])`, the raw diff entries against that commit's FIRST parent.
_PathChange = Tuple[str, List[Tuple[bytes, str, str]]]


def _git_head_exists(root: Path) -> bool:
    return _git_line(["rev-parse", "-q", "--verify", "HEAD^{commit}"], root) is not None


def _freeze_path_log(repo: Path, relpath: str) -> Tuple[Optional[List[_PathChange]], Optional[str]]:
    """Every commit on HEAD's first-parent chain at which *relpath* (relative to *repo*, the
    top level the command runs from) -- or anything under it,
    were it ever a directory -- differs from that commit's FIRST parent, oldest first, with
    the raw diff entries: ONE `git log` for the whole history (Controller Ruling 8, fix round
    4; round 3 ran one `git ls-tree` per commit, ~29 s for 2,000 commits on every
    post-cutoff grant). `([], None)` if HEAD has no commits; `(None, problem)` if git fails
    or prints something this does not recognise.

    Why this misses nothing round 3's per-commit walk saw: path-limited history with
    `--first-parent` compares each commit with its first parent ONLY (a merge whose side
    branch brought the whole change is still listed, because it differs from its first
    parent), and a commit it does not list is one where the path is identical to the
    previous listed state -- so checking only the listed commits checks every commit.
    `--diff-merges=first-parent` gives a merge's raw diff against that same parent, `--root`
    the root commit's. Pinned against user config: `log.follow` (which, set, turns a single
    path into `--follow` and reports a rename sandwich as one R100 entry, even with
    `--no-renames`), rename detection, submodule hiding, signatures, colour.
    `--literal-pathspecs`, so a campaign directory named with glob characters means itself.
    `-z`, so the path is never quoted."""
    args = [
        "--literal-pathspecs", "-c", "log.follow=false",
        "log", "--first-parent", "--diff-merges=first-parent", "--root", "--raw",
        "--no-abbrev", "--no-renames", "--ignore-submodules=none", "--no-color",
        "--no-show-signature", "-z", "--reverse", f"--format={_LOG_MARKER}%H",
        "HEAD", "--", relpath,
    ]
    unreadable = (f"{FREEZE_FILENAME}: freeze history could not be read (`git log` failed "
                  "or printed something unexpected).")
    out = _git(args, repo, timeout=60)
    if out is None:
        return None, unreadable
    if out.returncode != 0:
        return ([], None) if not _git_head_exists(repo) else (None, unreadable)

    marker = _LOG_MARKER.encode("ascii")
    tokens = out.stdout.split(b"\0")
    changes: List[_PathChange] = []
    i = 0
    try:
        while i < len(tokens):
            tok = tokens[i].lstrip(b"\n")
            i += 1
            if not tok:
                continue
            if tok.startswith(marker):
                changes.append((tok[len(marker):].decode("ascii"), []))
                continue
            fields = tok.decode("ascii").split() if tok.startswith(b":") else []
            # `:old_mode new_mode old_obj new_obj status`, then the path as its own token.
            # A rename or copy status (two paths) cannot occur with --no-renames and
            # log.follow off; refuse rather than guess if it ever does.
            if (len(fields) != 5 or fields[4] not in ("A", "D", "M", "T")
                    or not changes or i >= len(tokens)):
                return None, unreadable
            changes[-1][1].append((tokens[i], fields[1], fields[3]))
            i += 1
    except UnicodeDecodeError:
        return None, unreadable
    return changes, None


def _walk_freeze_log(changes: List[_PathChange], relpath: str
                     ) -> Tuple[List[Tuple[str, str]], Optional[str]]:
    """Replay `_freeze_path_log`'s changes, oldest first, and check *relpath*'s state AT each
    listed commit -- the same state round 3 read with `ls-tree` at every commit, since
    between two listed commits it cannot change. Stops, returning a problem, at the first
    commit where it is not an ordinary file; nothing after a break can be trusted, so the
    caller never looks past it:

    - anything recorded UNDER the path: FREEZE.toml was a directory;
    - the path deleted (new mode 000000) -- deleted, or moved away (a rename sandwich, fix
      round 3's NEW-3); the walk stops here, so a later re-add is never reached;
    - a symlink (120000), a gitlink/submodule (160000), or any other non-regular mode.

    Returns `([(sha, blob), ...], None)`: one entry per run of consecutive IDENTICAL blobs,
    keyed by the commit where that blob first appears (a mode-only change, 100644 to 100755,
    adds no entry)."""
    rel = os.fsencode(relpath)
    entries: List[Tuple[str, str]] = []
    last_blob: Optional[str] = None
    for sha, diff in changes:
        where = sha[:12]
        if any(path != rel and mode != "000000" for path, mode, _obj in diff):
            return entries, (f"{FREEZE_FILENAME} was a directory in history at {where}; "
                             "refusing to trust it.")
        exact = [(mode, obj) for path, mode, obj in diff if path == rel]
        if not exact:
            continue  # only entries under a directory being removed; refused when added
        mode, blob = exact[-1]
        if mode == "000000":
            return entries, f"{FREEZE_FILENAME} deleted or moved in history at {where}."
        if mode == "120000":
            return entries, (
                f"{FREEZE_FILENAME} was recorded as a symlink (mode {mode}) in history at "
                f"{where}; refusing to trust it."
            )
        if mode == "160000":
            return entries, (f"{FREEZE_FILENAME} is a gitlink/submodule at {where} (mode "
                             f"{mode} in history); refusing to trust it.")
        if mode not in _REGULAR_MODES:
            return entries, (f"{FREEZE_FILENAME} has mode {mode} in history at {where}, not "
                             "a regular file; refusing to trust it.")
        if blob != last_blob:
            entries.append((sha, blob))
            last_blob = blob
    return entries, None


def _cat_file_blobs(repo: Path, blobs: List[str]) -> Tuple[Dict[str, bytes], Optional[str]]:
    """The content of every blob in *blobs*: one `git cat-file --batch-check` for the types
    and sizes, then one `git cat-file --batch` for the contents of those that are blobs no
    larger than `FREEZE_MAX_BYTES` -- so a huge object in history is refused by its size
    and never read. A blob that is missing, not a blob, or too large maps to no content;
    `(_, problem)` if git itself fails or its output is not what was asked for."""
    unreadable = (f"{FREEZE_FILENAME}: freeze history could not be read (`git cat-file` "
                  "failed or printed something unexpected).")
    unique = list(dict.fromkeys(blobs))

    def run(mode: str, names: List[str]):
        out = _git(["cat-file", mode], repo, timeout=60,
                   stdin="".join(n + "\n" for n in names).encode("ascii"))
        return out.stdout if out is not None and out.returncode == 0 else None

    checked = run("--batch-check", unique)
    if checked is None:
        return {}, unreadable
    lines = checked.decode("ascii", "replace").splitlines()
    if len(lines) != len(unique):
        return {}, unreadable
    wanted: List[Tuple[str, int]] = []
    for name, line in zip(unique, lines):
        fields = line.split()
        if (len(fields) == 3 and fields[0] == name and fields[1] == "blob"
                and fields[2].isdigit() and int(fields[2]) <= FREEZE_MAX_BYTES):
            wanted.append((name, int(fields[2])))

    contents: Dict[str, bytes] = {}
    if not wanted:
        return contents, None
    data = run("--batch", [name for name, _size in wanted])
    if data is None:
        return {}, unreadable
    pos = 0
    for name, size in wanted:
        header_end = data.find(b"\n", pos)
        expected = f"{name} blob {size}".encode("ascii")
        if header_end < 0 or data[pos:header_end] != expected:
            return {}, unreadable
        start = header_end + 1
        if data[start + size:start + size + 1] != b"\n":
            return {}, unreadable
        contents[name] = data[start:start + size]
        pos = start + size + 1
    return contents, None


def _freeze_commit_history(repo: Path, relpath: str) -> Tuple[List[Tuple[str, dict]], Optional[str]]:
    """`([(commit sha, parsed FREEZE.toml doc), ...], None)`, oldest first, for the DISTINCT
    states *relpath* (relative to *repo*, the repository's top level) held across every commit from its first appearance to HEAD on the
    first-parent chain; or `([], None)` if it has never been committed; or `([], problem)`
    if the walk hit an absence, a directory, a symlink, a gitlink, or an unreadable blob
    partway through -- the caller must surface `problem` itself rather than silently
    falling back to "never committed", which would under-report what actually happened.

    Fix round 4 (Ruling 8): three git calls in all, however long the history -- one
    `git log --raw` (`_freeze_path_log`) and two `git cat-file` (`_cat_file_blobs`) --
    with the same refusals as round 3's per-commit walk."""
    changes, problem = _freeze_path_log(repo, relpath)
    if problem:
        return [], problem
    distinct, problem = _walk_freeze_log(changes, relpath)
    if problem:
        return [], problem
    if not distinct:
        return [], None
    contents, problem = _cat_file_blobs(repo, [blob for _sha, blob in distinct])
    if problem:
        return [], problem

    history: List[Tuple[str, dict]] = []
    for sha, blob in distinct:
        data = contents.get(blob)
        if data is None:
            return [], (f"{FREEZE_FILENAME} could not be read at commit {sha[:12]} (missing, "
                        f"not a blob, or larger than {FREEZE_MAX_BYTES} bytes).")
        doc, why = _parse_freeze_bytes(data)
        if why:
            return [], f"{FREEZE_FILENAME} could not be read at commit {sha[:12]}: it {why}."
        history.append((sha, doc))
    return history, None


def _freeze_transition_problems(prev: dict, cur: dict, label: str) -> List[str]:
    """Problems between two consecutive FREEZE.toml states (`prev` then `cur`, `label`
    naming `cur`): version going backwards; an earlier `[[unfreeze]]` entry edited or
    removed (append-only); at an unchanged version, an existing statement hash changed or
    removed, or an existing statement fingerprint changed or removed, or a fingerprint added
    for a node that was already frozen (step 5 Task 6); or, on a version change, anything
    other than exactly +1 with a matching new `[[unfreeze]]` entry."""
    problems: List[str] = []
    prev_version = int(prev.get("version", 1))
    cur_version = int(cur.get("version", 1))
    prev_entries = list(prev.get("unfreeze") or [])
    cur_entries = list(cur.get("unfreeze") or [])

    if cur_version < prev_version:
        problems.append(
            f"{FREEZE_FILENAME} at {label}: version went backwards ({prev_version} -> "
            f"{cur_version})."
        )
        return problems  # comparisons below assume a sane version; stop here

    # Fix round 1 (Ruling 18, M1): `frozen` decides whether the history checks below fail
    # closed at all, so it may never move; a back-dated `frozen` would otherwise turn "cannot
    # verify" into "pre-cutoff, nothing to verify".
    if cur.get("frozen") != prev.get("frozen"):
        problems.append(
            f"{FREEZE_FILENAME} at {label}: the `frozen` date changed ({prev.get('frozen')!r} -> "
            f"{cur.get('frozen')!r}); it is fixed at the first freeze."
        )

    if cur_entries[:len(prev_entries)] != prev_entries:
        problems.append(
            f"{FREEZE_FILENAME} at {label}: an earlier [[unfreeze]] entry was edited or "
            "removed; the unfreeze history must be append-only."
        )

    prev_statements = prev.get("statements") or {}
    cur_statements = cur.get("statements") or {}

    if cur_version == prev_version:
        removed = set(prev_statements) - set(cur_statements)
        changed = {slug for slug in prev_statements
                  if slug in cur_statements and cur_statements[slug] != prev_statements[slug]}
        if removed or changed:
            problems.append(
                f"{FREEZE_FILENAME} at {label}: statement(s) "
                f"{', '.join(sorted(removed | changed))!r} changed or were removed without a "
                "version bump."
            )
        # Step 5 Task 6: the same rule for `[fingerprints]`, the semantic half of the
        # freeze. An added fingerprint is allowed only for a node that is itself new in this
        # transition; one appearing for a node already frozen would let anyone with commit
        # access choose the fingerprint a later `[checks]` record must match.
        prev_fps = prev.get("fingerprints") or {}
        cur_fps = cur.get("fingerprints") or {}
        fp_removed = set(prev_fps) - set(cur_fps)
        fp_changed = {slug for slug in prev_fps
                      if slug in cur_fps and cur_fps[slug] != prev_fps[slug]}
        fp_added_late = {slug for slug in set(cur_fps) - set(prev_fps) if slug in prev_statements}
        if fp_removed or fp_changed:
            problems.append(
                f"{FREEZE_FILENAME} at {label}: statement fingerprint(s) "
                f"{', '.join(sorted(fp_removed | fp_changed))!r} changed or were removed "
                "without a version bump."
            )
        prev_imp, cur_imp = prev.get("imports") or {}, cur.get("imports") or {}
        imp_bad = {m for m in prev_imp if m not in cur_imp or cur_imp[m] != prev_imp[m]}
        if imp_bad:
            problems.append(
                f"{FREEZE_FILENAME} at {label}: imported project module(s) "
                f"{', '.join(sorted(imp_bad))!r} changed or were removed without a version bump."
            )
        prev_env, cur_env = prev.get("fingerprints_env"), cur.get("fingerprints_env")
        if prev_env and cur_env != prev_env:
            problems.append(
                f"{FREEZE_FILENAME} at {label}: `fingerprints_env` changed or was removed without "
                "a version bump."
            )
        if fp_added_late:
            problems.append(
                f"{FREEZE_FILENAME} at {label}: statement fingerprint(s) "
                f"{', '.join(sorted(fp_added_late))!r} added for already-frozen node(s) "
                "without a version bump; record them with `mission unfreeze --fingerprints`."
            )
    elif cur_version != prev_version + 1:
        problems.append(
            f"{FREEZE_FILENAME} at {label}: version jumped from {prev_version} to "
            f"{cur_version} (expected exactly +1)."
        )
    else:
        new_entries = cur_entries[len(prev_entries):]
        if not any(int(e.get("version", -1)) == cur_version for e in new_entries):
            problems.append(
                f"{FREEZE_FILENAME} at {label}: version is {cur_version} but no new "
                f"[[unfreeze]] entry for version {cur_version} was appended."
            )
    return problems


def freeze_history_problems(root: Path, *, require: bool = False) -> List[str]:
    """Walk FREEZE.toml's git history (its state at every commit on the first-parent chain
    from the file's first appearance to HEAD, plus the working tree as the final state) and
    check the invariants `_freeze_transition_problems` describes between every consecutive
    DISTINCT state. Since fix round 4 (Ruling 8) the walk reads only the commits where the
    path changed, all in one `git log --raw` plus `git cat-file` (`_freeze_commit_history`);
    the state at any other commit is, by construction, the previous listed one.

    One check is UNCONDITIONAL, never gated by cutoff: a working-tree FREEZE.toml that
    `_load_freeze_safe` refuses -- a symlink (refused before anything is read through it),
    not a regular file, oversized, not UTF-8, not TOML, or not FREEZE.toml's shape. None of
    its fields, the `frozen` date every other check below gates on included, can be
    trusted, so there is nothing left to gate on. A symlink recorded in HISTORY (git mode
    120000) rather than in the working tree is a different code path (the history walk
    itself, which does have a trustworthy `frozen` field to gate on) and remains
    cutoff-gated like everything below.

    Everything else fails closed only where it genuinely cannot check anything, and only
    when a post-cutoff campaign (FREEZE.toml's own `frozen` date >= `CUTOFF`) needs the
    guarantee; a pre-cutoff campaign, for which freezing at all is optional, is not
    penalised for any of these:

    - a symlink recorded at any point in history (git mode 120000) -- a symlink's target
      can change independently of the history being walked, so content comparisons through
      it prove nothing (fix round 3); likewise a gitlink/submodule (160000) or a directory
      at the path, and a blob that is not a readable FREEZE.toml (fix round 4);
    - the campaign root is not inside a git repository;
    - the repository is a SHALLOW clone (`git rev-parse --is-shallow-repository`) -- the
      history this would walk is truncated by construction, which operationally reproduces
      "no history" even though commits are present (fix round 3, NEW-2: this is also CI's
      typical default, so it needs no adversarial action to trigger);
    - the walk hits an absence or a symlink partway through history -- the file was deleted
      or moved away and back (fix round 3, NEW-3: `_freeze_commit_history` stops AT that
      commit and reports it, rather than silently continuing with whatever commits still
      happen to resolve, which is what let a rename sandwich launder an unauthorized change
      underneath one legitimate version bump);
    - the repository has `info/grafts` or `objects/info/(http-)alternates` (fix round 5,
      Ruling 9): grafts rewrite parentage and alternates borrow objects from a repository
      the walk cannot vouch for, so the history read would not be this repository's own;
    - FREEZE.toml exists but has never been committed at all (the first freeze must be
      committed before it counts -- an uncommitted first freeze is exactly the history-less
      state this check cannot see past).

    NOT covered, by design (fix round 3, NEW-1; documented, not coded): a history REWRITE
    that replaces the whole committed history with one internally self-consistent
    fabrication (`git commit --amend` on the sole commit, or an equivalent rebase/force-
    push) is invisible to a check that can only compare what it can currently see. This is
    inherent to local git, not a gap specific to this implementation. For a node that has
    already been GRANTED, a later statement change is still caught independently -- the
    grant records its own `statement_sha256` (`provenance.build_grant`) against the
    artifact the gate actually saw, so a rewritten FREEZE.toml cannot retroactively make a
    granted node's statement look unchanged. For an
    UNGRANTED node, an amended first freeze (before anyone else has fetched it) is
    genuinely indistinguishable from an honest first freeze; the anchor this check rests on
    is a protected remote branch history (no force-push) with `mission verify` run in CI
    against the FULL history of that branch, not a local, possibly-rewritten clone.
    """
    root = Path(root)

    # Reported UNCONDITIONALLY (not gated by post-cutoff like every other check below): an
    # untrusted record -- a symlink, refused before anything is read through it, or content
    # that is not FREEZE.toml at all -- leaves no `frozen` field trustworthy enough to decide
    # anything else, including whether to decide anything at all.
    doc, unreadable = _load_freeze_safe(root)
    if unreadable:
        return [unreadable]
    if doc is None:
        return []

    # Fix round 1 (Ruling 18, M1): `require` (a post-cutoff node depends on this freeze) fails
    # closed whatever the record's own, self-reported `frozen` date says.
    post_cutoff = require or str(doc.get("frozen", "")) >= CUTOFF

    if not _is_git_repo(root):
        if post_cutoff:
            return [
                f"{FREEZE_FILENAME}: freeze history unavailable (the campaign root is not "
                "inside a git repository); version bumps and the unfreeze history cannot be "
                "verified."
            ]
        return []

    if _is_shallow_repo(root):
        if post_cutoff:
            return [
                f"{FREEZE_FILENAME}: shallow clone: freeze history incomplete; fetch full "
                "history (fetch-depth: 0)."
            ]
        return []

    untrusted = _untrusted_git_file(root)
    if untrusted:
        return [untrusted] if post_cutoff else []

    toplevel = _git_toplevel(root)
    relpath = None
    if toplevel is not None:
        try:
            relpath = freeze_path(root).resolve().relative_to(toplevel.resolve()).as_posix()
        except ValueError:
            relpath = None
    if relpath is None:
        if post_cutoff:
            return [
                f"{FREEZE_FILENAME}: freeze history unavailable (could not resolve its path "
                "relative to the repository root); version bumps and the unfreeze history "
                "cannot be verified."
            ]
        return []

    # Run from the TOP LEVEL: git resolves a pathspec against its working directory, and
    # *relpath* is relative to the top level. Round 3 ran from the campaign root, so every
    # campaign in a subdirectory (`missions/<name>/`) found no history and was reported as
    # never committed (fix round 4).
    history, hist_problem = _freeze_commit_history(toplevel, relpath)
    if hist_problem:
        return [hist_problem] if post_cutoff else []
    if not history:
        if post_cutoff:
            return [
                f"{FREEZE_FILENAME} exists but has never been committed; commit the first "
                "freeze (`git add` + `git commit`) before it counts."
            ]
        return []

    states = [(f"commit {sha[:12]}", hdoc) for sha, hdoc in history]
    states.append(("the working tree", doc))

    problems: List[str] = []
    for (_prev_label, prev_doc), (cur_label, cur_doc) in zip(states, states[1:]):
        problems.extend(_freeze_transition_problems(prev_doc, cur_doc, cur_label))
    return problems


#: How many of `freeze_problems`' entries `freeze_grant_problem` quotes in a refusal.
_GRANT_PROBLEM_PREVIEW = 3


def freeze_grant_problem(root: Path, node) -> str:
    """"" unless *node* is post-cutoff (`provenance.checks_required`); else why the grant
    gate must refuse it: no FREEZE.toml exists for the campaign, its statement is not
    recorded in one, or (Controller Ruling 6, fix round 2) `freeze_problems(root)` reports
    ANY problem at all -- not only ones about this node. A post-cutoff grant rests on the
    campaign's freeze being trustworthy as a whole (the C1 tamper `freeze_history_problems`
    catches is a campaign-level fact, not a per-node one: hiding a hand-rewritten hash
    behind an unchanged version on a DIFFERENT node's statement is exactly the kind of
    forgery this must not let a clean-looking node slip past)."""
    from .provenance import checks_required

    if not checks_required(node):
        return ""
    root = Path(root)
    doc, unreadable = _load_freeze_safe(root)
    if unreadable:
        return unreadable
    if doc is None:
        return (
            f"no {FREEZE_FILENAME} at the campaign root; a post-cutoff node may not be "
            "granted until the campaign is frozen (`mission freeze`)."
        )
    statements = doc.get("statements") or {}
    slug = slug_of(node.name)
    if slug not in statements:
        return (
            f"node {slug!r} is not recorded in {FREEZE_FILENAME}; the campaign must be frozen "
            "or unfrozen to include it before this node can be granted."
        )
    problems = freeze_problems(root, require_history=True)
    if problems:
        shown = problems[:_GRANT_PROBLEM_PREVIEW]
        more = (f" (+{len(problems) - _GRANT_PROBLEM_PREVIEW} more)"
               if len(problems) > _GRANT_PROBLEM_PREVIEW else "")
        return (
            f"the campaign's freeze has unresolved problem(s){more}: " + "; ".join(shown)
        )
    return ""


# ---------------------------------------------------------------------------
# Frozen statement fingerprints: the semantic theorem tie (step 5 Task 6)
#
# The gate used to tie a `[checks]` record to the node's theorem by NAME only, through
# `guard_anchors.resolve_theorem`, a syntactic reading of the artifact that an adversarial
# artifact can fool (step 4's final re-review: `s!` interpolation, a quote inside `«»`,
# declaration text inside `«»`, `#exit`, a `(command| ...)` quotation). The sound tie is
# semantic: `mission freeze --fingerprints` records, per node, the fingerprint
# (`checks.fingerprint`) of its STATEMENT as Lean elaborates it, and for a post-cutoff node
# the checked theorem's fingerprint must equal it (`statement_fingerprint_problem`, called by
# `provenance.checks_problem` and `mission checks-record`). Whatever declaration the resolver
# picked, a `[checks]` record passes only if the theorem it checked states, after unfolding
# every non-library definition, exactly what the frozen statement states.
#
# Which constant of the statement module, and in which mode (`statement_fingerprint_target`):
# the statement file's last `theorem`/`lemma` (the form every statement file has had so far,
# `theorem foo : P := by sorry`, and the one the gate's needle is read from) in TYPE mode,
# i.e. P; with no theorem at all, its last `def`/`abbrev` (spec 7's `def S : Prop := P`) in
# VALUE mode, i.e. P again. Either way
# the frozen fingerprint is what an artifact's `theorem t : S` or `theorem t : P` gets in
# type mode. The statement file is the campaign's own frozen, read-back text, not the
# adversarial artifact; the fingerprint itself is computed from what Lean elaborated.
#
# THE TRUST MODEL (fix round 3, Ruling 20). The freeze fingerprints exactly what Lean
# elaborates from the statement file. The grammar (`_statement_text_problem`), the declaration
# range and the accounted-for check (`compute_statement_fingerprints`) stop ACCIDENTAL and
# CASUAL mismatches between the text and that elaboration; they do not make the text a
# guarantee of it. Compile-time code is still possible in the statement layer -- the statement
# file's own `by sorry` and the project modules it imports (recorded, by source sha256, in
# FREEZE.toml `[imports]`) are compiled for real -- and it is TRUSTED, as part of what the
# independent read-back approves. A campaign from an untrusted author must be frozen inside
# the sandbox. Known residual (R2): a command keyword outside the grammar's lists on an
# INDENTED line is not seen by the line-start check (a meaning-changing command that declares
# nothing, such as `unif_hint`, passes all three checks).
# ---------------------------------------------------------------------------

#: A `theorem`/`lemma` keyword token anywhere in code (after `set_option ... in`, an attribute,
#: `nonrec`, ...), then the dotted name (stopping before a `.{u}` universe list, a binder or a
#: colon). Not part of an identifier (`my.theorem`, `theorem_1`).
_KW_NAME = r"[ \t\n]+([^\s(){}\[\]:,.]+(?:\.[^\s(){}\[\]:,.]+)*)"
_THEOREM_TOKEN_RE = re.compile(r"(?<![\w.'!?])(?:theorem|lemma)(?![\w.'!?])")
_THEOREM_DECL_RE = re.compile(r"(?<![\w.'!?])(?:theorem|lemma)" + _KW_NAME)
#: A `def`/`abbrev` keyword token and its name, for the closed `def S : Prop` statement constant.
_DEF_DECL_RE = re.compile(r"(?<![\w.'!?])(?:def|abbrev)" + _KW_NAME + r"(?:\.\{[^}]*\})?")
#: Fix round 2 (Ruling 19): statement files follow a STRICT WHITELIST grammar. Every command
#: starts a line (column 0) with one of these keywords; nothing else may start a command.
_ALLOWED_COMMANDS = frozenset({
    "import", "namespace", "end", "section", "open", "universe", "variable",
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "class", "noncomputable",
})
#: What may follow `noncomputable` on its line.
_NONCOMPUTABLE_NEXT = frozenset({"def", "abbrev", "section"})
#: Refused ANYWHERE in the code: declaration generators, syntax extensions (which can swallow
#: a command, or make text mean something else), code that runs at elaboration time, and
#: modifiers outside the grammar. Matched as whole tokens (`List.prefix` does not match).
_FORBIDDEN_TOKENS = (
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "notation", "infix", "infixl",
    "infixr", "prefix", "postfix", "declare_syntax_cat", "run_cmd", "run_elab", "run_meta",
    "alias", "export", "attribute", "initialize", "builtin_initialize", "deriving",
    "set_option", "local", "scoped", "instance", "private", "protected", "opaque", "axiom",
    "irreducible_def", "omit", "include",
    # fix round 3 (Ruling 20): tactic and term forms that run arbitrary code at elaboration time
    "run_tac", "by_elab",
)
_TOKEN_RE = re.compile(r"[A-Za-z_\u0370-\u03ff\u1f00-\u1fff\u2100-\u214f]"
                       r"[\w'!?\u0370-\u03ff\u1f00-\u1fff\u2100-\u214f\u2080-\u2089\u2090-\u209c]*")
_FORBIDDEN_TOKEN_RE = re.compile(r"(?<![\w.'!?])(" + "|".join(_FORBIDDEN_TOKENS) + r")(?![\w.'!?])")
_COMMAND_TOKEN_RE = re.compile(r"(?<![\w.'!?])(" + "|".join(sorted(_ALLOWED_COMMANDS)) + r")(?![\w.'!?])")
#: Refused anywhere in the code, as text.
_FORBIDDEN_TEXT = (
    ("«", "a `«»`-quoted name (it can hide quotes and declaration text)"),
    ("`", "a backquote (a syntax quotation `` `( `` or a name literal)"),
    ("@[", "an attribute `@[...]` (no attribute is allowed in a statement file)"),
)


def _code_columns(segs) -> str:
    """The code of *segs* with every comment replaced by spaces (newlines kept), so that a
    character's line and column are its line and column in the file."""
    return "".join(t if k != "comment" else re.sub(r"[^\n]", " ", t) for k, t in segs)


def _statement_text_problem(ga, text: str) -> Optional[str]:
    """Why *text* (a statement file) is outside the statement-file grammar, or None (fix round 2,
    Ruling 19: a STRICT WHITELIST, checked with the shared lexer `guard_anchors.lean_segments`, so
    comments never trigger it). The grammar:

    - every command starts a line, at column 0, with `import`, `namespace`, `end`, `section`,
      `open`, `universe`, `variable`, `theorem`, `lemma`, `def`, `abbrev`, `structure`,
      `inductive`, `class` or `noncomputable` (then `def`, `abbrev` or `section`); any other
      token at a line start is refused, naming the line, and a command keyword anywhere else
      (mid-line, or on an indented line) is refused too;
    - no string, raw-string or char literal at all (an interpolated `s!"{"…"}"`, `m!`, `f!`,
      `throwError "{"` or `dbg_trace` hides text from any lexer but Lean's own);
    - none of `_FORBIDDEN_TOKENS` anywhere (generators such as `alias`, syntax extensions such
      as `elab`, which can swallow a command, elaboration-time code such as `run_cmd`, and
      `set_option`, `local`, `scoped`, `instance`, `private`, ...), no `#` command, no `«`, no
      backquote and no attribute. The one exception is `open scoped NS` at a line start.

    - `by` only as the statement's final `:= by sorry` (fix round 3), and no `run_tac` or
      `by_elab`: a tactic block can run code at compile time.

    Statement files come from `mission add` and declare one statement and its supporting
    definitions, so this costs nothing. It is defence in depth against ACCIDENTAL and CASUAL
    mismatches between the text and what Lean elaborates; it is not a guarantee. The statement
    layer (this file and the project modules it imports) is trusted read-back content: compiling
    it runs code, and only a sandbox makes a freeze safe against an adversarial author (Ruling
    20; see the section comment above)."""
    segs = ga.lean_segments(text)
    code = _code_columns(segs)

    def line_of(pos: int) -> int:
        return code.count("\n", 0, pos) + 1

    pos = 0
    for kind, seg in segs:
        if kind in ("string", "raw", "char"):
            return (f"the statement file has a {'char' if kind == 'char' else 'string'} literal "
                    f"(line {line_of(pos)}); statement files may not contain any")
        pos += len(seg)
    for needle, what in _FORBIDDEN_TEXT:
        i = code.find(needle)
        if i >= 0:
            return f"the statement file contains {what} (line {line_of(i)})"
    m = re.search(r"#[A-Za-z_]", code)
    if m:
        return f"the statement file contains a `#` command (line {line_of(m.start())})"
    # `open scoped NS` (the namespace's scoped notation, `π` for `Real`) is the one allowed use of
    # `scoped`; `local`/`scoped` NOTATION forms are refused through `notation`/`infix`/... below.
    m = _FORBIDDEN_TOKEN_RE.search(re.sub(r"(?m)^open[ \t]+scoped(?![\w.'!?])", "open", code))
    if m:
        return (f"the statement file uses `{m.group(1)}` (line {line_of(m.start())}), which a "
                "statement file may not")
    allowed_at: Set[int] = set()
    offset = 0
    for lineno, line in enumerate(code.split("\n"), start=1):
        start = offset
        offset += len(line) + 1
        if not line.strip() or line[0].isspace():
            continue
        tok = _TOKEN_RE.match(line)
        word = tok.group(0) if tok else line.split()[0]
        if word not in _ALLOWED_COMMANDS:
            return (f"line {lineno} starts a command with {word!r}, which is not in the "
                    "statement-file grammar")
        allowed_at.add(start)
        if word == "noncomputable":
            nxt = re.match(r"noncomputable[ \t]+(\S+)", line)
            if not nxt or nxt.group(1) not in _NONCOMPUTABLE_NEXT:
                return (f"line {lineno}: `noncomputable` must be followed by `def`, `abbrev` or "
                        "`section`")
            allowed_at.add(start + nxt.start(1))
    for m in _COMMAND_TOKEN_RE.finditer(code):
        if m.start() not in allowed_at:
            return (f"line {line_of(m.start())}: the command keyword `{m.group(1)}` does not start "
                    "a line; every command must start at column 0 of its own line")
    # Fix round 3 (Ruling 20): a tactic block runs tactics, any of which can run code at compile
    # time. The only `by` a statement file may hold is the statement's own terminal `:= by sorry`
    # (what `mission add` appends); supporting definitions use term proofs.
    bys = list(_BY_RE.finditer(code))
    if bys:
        last = bys[-1]
        # (closing `end` lines after it are fine: `namespace A … theorem t : P := by sorry` / `end A`)
        if len(bys) > 1 or not re.fullmatch(r"\s*sorry(?:\s*\nend(?:[ \t]+\S+)?)*\s*", code[last.end():]):
            bad = bys[0] if len(bys) > 1 else last
            return (f"line {line_of(bad.start())}: `by` is allowed only as the statement's final "
                    "`:= by sorry`; supporting definitions take term proofs (a tactic block runs code "
                    "at compile time)")
    return None


_BY_RE = re.compile(r"(?<![\w.'!?])by(?![\w.'!?])")


def _doc_comment_on(segs, line_start: int) -> bool:
    """Whether the last non-blank thing before offset *line_start* of the file is a doc comment
    (`/-- … -/`): Lean then records the declaration's range from the doc comment's line."""
    pos, last = 0, None
    for kind, seg in segs:
        if pos >= line_start:
            break
        piece = seg[: max(0, line_start - pos)]
        if piece.strip():
            last = (kind, piece)
        pos += len(seg)
    return last is not None and last[0] == "comment" and last[1].lstrip().startswith("/--")


_DECLARING_RE = re.compile(r"(?m)^(?:noncomputable[ \t]+)?(?:theorem|lemma|def|abbrev|structure|inductive|class)"
                           + _KW_NAME)


def statement_declared_names(ga, text: str) -> List[str]:
    """The fully qualified names a statement file's text declares (`theorem`, `lemma`, `def`,
    `abbrev`, `structure`, `inductive`, `class`, each at a line start, per the grammar),
    qualified by the `namespace`s open at each."""
    code = ga.blank_lean_code(text)
    out = []
    for m in _DECLARING_RE.finditer(code):
        parts = m.group(1).split(".")
        out.append(".".join(parts[1:]) if parts[0] == "_root_"
                   else ".".join(ga._namespace_at(code, m.start()) + parts))
    return out


def _closed_prop_defs(code: str) -> List[re.Match]:
    """The `def`/`abbrev` declarations in blanked *code* whose header is exactly `: Prop` (no
    binders): the textual counterpart of a definition whose type is literally `Prop`."""
    out = []
    for m in _DEF_DECL_RE.finditer(code):
        head = re.match(r"\s*:\s*Prop\s*:=", code[m.end():])
        if head:
            out.append(m)
    return out


def statement_fingerprint_target(root: Path, node) -> Tuple[str, str]:
    """`(fully qualified name, mode)` of the constant `mission freeze --fingerprints`
    fingerprints for *node* -- the TEXTUAL half of the choice; `compute_statement_fingerprints`
    then requires the replayed statement module to declare exactly that one statement constant
    (fix round 1, Ruling 18, finding I1).

    A statement file declares exactly ONE statement constant: one `theorem`/`lemma` (mode
    "type"), or, with none, one closed `def`/`abbrev … : Prop` (mode "value", spec 7's
    `def S : Prop`). Counted over the code, with comments and string literals blanked. In type
    mode the gate's own reader (`guard_anchors.statement_decl`) must name the same declaration;
    in value mode it must find no theorem at all. The name is qualified by the `namespace`s open
    at it (`_namespace_at`). `ValueError`, naming the node, for: a file outside the statement-file
    grammar (`_statement_text_problem`, fix round 2); more than one theorem, or more than one
    statement constant; none at all; a name that is not a plain dotted identifier; a
    disagreement with the gate's reader."""
    from .judge import _guard_anchors

    return statement_target_of_text(_guard_anchors(), statement_path(root, node).read_text(encoding="utf-8"),
                                    slug_of(node.name))


def statement_target_of_text(ga, text: str, slug: str) -> Tuple[str, str]:
    """`statement_fingerprint_target` on a statement file's *text* (`ga`: `guard_anchors`), for
    the node *slug*."""
    name, mode, _line = statement_target_details(ga, text, slug)
    return name, mode


def statement_target_details(ga, text: str, slug: str) -> Tuple[str, str, int]:
    """`statement_target_of_text` plus the (1-based) line of the file its declaration starts on,
    which the grammar puts at column 0."""
    from ..closure_audit import _IDENT_COMPONENT

    def refuse(why: str) -> ValueError:
        return ValueError(f"node {slug!r}: {why}; refusing to freeze a fingerprint for it.")

    problem = _statement_text_problem(ga, text)
    if problem:
        raise refuse(problem)
    code = ga.blank_lean_code(text)
    theorems = list(_THEOREM_DECL_RE.finditer(code))
    tokens = _THEOREM_TOKEN_RE.findall(code)
    prop_defs = _closed_prop_defs(code)
    if len(tokens) > 1 or len(theorems) != len(tokens):
        raise refuse(f"the statement file has {len(tokens)} `theorem`/`lemma` keywords; a statement "
                     "file declares exactly one statement constant")
    if theorems and prop_defs:
        raise refuse("the statement file declares both a theorem and a closed `def … : Prop`; a "
                     "statement file declares exactly one statement constant")
    if len(prop_defs) > 1:
        raise refuse(f"the statement file declares {len(prop_defs)} closed `def … : Prop`s; a "
                     "statement file declares exactly one statement constant")
    if not theorems and not prop_defs:
        raise refuse("the statement file declares no theorem, lemma or closed `def … : Prop`")
    decl = theorems[0] if theorems else prop_defs[0]
    short = decl.group(1)
    parts = short.split(".")
    if any(not p or p[0].isdigit() or not _IDENT_COMPONENT.match(p) for p in parts):
        raise refuse(f"its declaration name {short!r} is not a plain dotted Lean identifier")
    try:
        gate_short = ga.statement_decl(text)[0]
    except ga.RegistryError as exc:
        gate_short = None
        gate_error = str(exc)
    if theorems:
        if gate_short is None:
            raise refuse(f"the gate's statement reader finds no theorem in it ({gate_error})")
        if gate_short.rstrip(".") != short:      # `foo.{u}` reads as `foo.` there
            raise refuse(f"its theorem reads as {short!r} here but as {gate_short!r} to the gate")
    elif gate_short is not None:
        raise refuse(f"the gate's statement reader sees a theorem {gate_short!r} that is not in "
                     "its code")
    line = code.count("\n", 0, decl.start()) + 1
    # Fix round 3 (R4): Lean records a declaration's range from its modifiers, a doc comment
    # included, so the range check below would compare against the doc comment's line.
    line_start = sum(len(ln) + 1 for ln in text.split("\n")[: line - 1])
    if _doc_comment_on(ga.lean_segments(text), line_start):
        raise refuse("the statement declaration has a doc comment (`/-- … -/`); move the docstring "
                     "to a comment (`/- … -/` or `--`)")
    if parts[0] == "_root_":
        name = ".".join(parts[1:])
    else:
        name = ".".join(ga._namespace_at(code, decl.start()) + parts)
    return name, "type" if theorems else "value", line


class StatementFingerprints(dict):
    """slug -> statement fingerprint, plus ``trusted_env_sha256``: the trusted env
    (`checks.lean_replay.trusted_env_digest`) every one of them was computed under."""

    def __init__(self, fps=(), trusted_env_sha256: Optional[str] = None):
        super().__init__(fps)
        self.trusted_env_sha256 = trusted_env_sha256


def compute_statement_fingerprints(root: Path, *, fingerprint_text=None,
                                   **lean_kw) -> StatementFingerprints:
    """slug -> statement fingerprint for every node with a statement file, each computed by
    compiling its statement file as its own module with the pinned `lean`, kernel-replaying it
    and fingerprinting `statement_fingerprint_target` in its mode
    (`checks.fingerprint.run_statement_fingerprint`, project `<root>/lean`, so its
    `.lake/build/lib/lean` serves any campaign module a statement imports). `lean_kw` goes to
    that function (trusted_env, manifest, wrapper, timeout, memory_mb, untrusted_paths).
    `fingerprint_text` replaces it (tests). `ValueError` naming the node on the first failure:
    a freeze records every node's fingerprint or none.

    The SEMANTIC half of the choice (fix round 1, Ruling 18, finding I1): the replayed
    statement module must declare exactly one statement constant, and it must be the textual
    target -- in type mode its only theorem (and no closed `Prop` definition), in value mode its
    only closed `Prop` definition (and no theorem). Fix round 2 (Ruling
    19) adds two more: every constant the module declares must be accounted for by a textual
    declaration (its name, or a name under it), and the declaration range Lean recorded for the
    target (`fingerprint.run_statement_fingerprint`'s ``ranges``, read as data from the compiled
    olean) must start at the textual declaration's line, column 0. Every node's fingerprint must
    also come from the same trusted env.

    What this is and is not (Ruling 20): the fingerprint is exactly what Lean elaborated; the
    checks above stop accidental and casual mismatches between the statement text and that
    elaboration. Compile-time code in the statement file's tactic block or in the project
    modules it imports is trusted, as part of what the independent read-back approves, and could
    defeat them.

    NOT A SANDBOX: compiling a statement runs its code, and its imports' (see
    `checks.fingerprint`). A campaign from an untrusted author must be frozen inside the
    sandbox."""
    from .registry import load_campaign

    root = Path(root)
    if fingerprint_text is None:
        from ..checks.fingerprint import run_statement_fingerprint as fingerprint_text
    campaign = load_campaign(root)
    out = StatementFingerprints()
    for slug, node in sorted(campaign.nodes.items()):
        path = statement_path(root, node)
        if not path.exists():
            continue
        from .judge import _guard_anchors
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise ValueError(f"node {slug!r}: cannot read its statement file ({exc})") from None
        target, mode, line = statement_target_details(_guard_anchors(), text, slug)
        try:
            fps = fingerprint_text(root / "lean", text, target, mode=mode, **lean_kw)
        except (OSError, ValueError) as exc:
            raise ValueError(f"node {slug!r}: statement fingerprint of {target!r} ({mode} mode) "
                             f"failed: {exc}") from None
        declared = getattr(fps, "declared", None)
        if not isinstance(declared, dict):
            raise ValueError(f"node {slug!r}: the statement fingerprint run did not list the "
                             "module's declarations")
        # Fix round 2 (Ruling 19): every constant the module declares must be accounted for by a
        # declaration in the text: its own name, or a name under it (a structure's `mk`/`rec`/
        # `mk.injEq`, a definition's `match_1`/`proof_1`). A generator the grammar missed would
        # show up here as an unaccounted name. Those auxiliaries are then not statement constants.
        names = statement_declared_names(_guard_anchors(), text)

        def under(n: str) -> bool:
            return any(n.startswith(d + ".") for d in names)
        every = [n for k in ("theorem", "propdef", "other") for n in declared.get(k, [])]
        unaccounted = sorted(n for n in every if n not in names and not under(n))
        if unaccounted:
            raise ValueError(
                f"node {slug!r}: the statement module, as Lean elaborates it, declares "
                f"{unaccounted}, which no declaration in the statement file's text accounts for; "
                "refusing to freeze a fingerprint for it.")
        # never filter the target itself (fix round 3, R3: `structure Pt` + `theorem Pt.main`)
        theorems = [n for n in declared.get("theorem", []) if n == target or not under(n)]
        prop_defs = [n for n in declared.get("propdef", []) if n == target or not under(n)]
        want = ([target], []) if mode == "type" else ([], [target])
        if (theorems, prop_defs) != want:
            raise ValueError(
                f"node {slug!r}: the statement module, as Lean elaborates it, declares the "
                f"theorem(s) {theorems} and the closed Prop definition(s) {prop_defs}, but the "
                f"statement file reads as declaring only {target!r} ({mode} mode); refusing to "
                "freeze a fingerprint for it.")
        # Fix round 2 (Ruling 19, part 2): the declaration range Lean RECORDED for the target (read
        # as data from the compiled olean) must start where the text declares it. That stops a
        # generator (`alias`) making a same-named constant elsewhere; compile-time code in the
        # trusted statement layer could still forge the record (Ruling 20).
        ranges = getattr(fps, "ranges", None)
        if not isinstance(ranges, dict) or ranges.get(target) != (line, 0):
            got = None if not isinstance(ranges, dict) else ranges.get(target)
            raise ValueError(
                f"node {slug!r}: Lean records the declaration of {target!r} at (line, column) "
                f"{got}, but the statement file declares it at ({line}, 0); refusing to freeze a "
                "fingerprint for it.")
        env = getattr(fps, "trusted_env_sha256", None)
        if not env or not _SHA256_HEX_RE.fullmatch(env):
            raise ValueError(f"node {slug!r}: the fingerprint run names no trusted env digest")
        if out.trusted_env_sha256 not in (None, env):
            raise ValueError(f"node {slug!r}: fingerprinted under trusted env {env[:12]}..., the "
                             f"others under {out.trusted_env_sha256[:12]}...")
        out.trusted_env_sha256 = env
        out[slug] = fps[target]
    return out


def frozen_fingerprint(root: Path, node) -> Optional[str]:
    """The statement fingerprint FREEZE.toml records for *node*, or None (no FREEZE.toml, an
    untrustworthy one -- `_load_freeze_safe` -- or no `[fingerprints]` entry)."""
    doc, _unreadable = _load_freeze_safe(Path(root))
    if doc is None:
        return None
    return (doc.get("fingerprints") or {}).get(slug_of(node.name))


_ENV_UNCHECKED = object()


def statement_fingerprint_problem(root: Path, node, fingerprint: str,
                                  trusted_env_sha256=_ENV_UNCHECKED) -> str:
    """"" when *fingerprint* (the checked theorem's, type mode) equals *node*'s frozen statement
    fingerprint; else why not: an untrustworthy FREEZE.toml, no FREEZE.toml or no
    `[fingerprints]` entry ("statement fingerprint not frozen"), or a mismatch. With
    *trusted_env_sha256* (`mission checks-record`, from the fingerprint JSON) it must also be
    the frozen `fingerprints_env` ("fingerprint computed under a different trusted env"; fix
    round 1, M2); `checks_problem` has no env to compare (the record does not keep it). The
    caller decides whether the node needs it (`provenance.checks_required`)."""
    slug = slug_of(node.name)
    doc, unreadable = _load_freeze_safe(Path(root))
    if unreadable:
        return f"statement fingerprint not frozen: {unreadable}"
    frozen = None if doc is None else (doc.get("fingerprints") or {}).get(slug)
    if frozen is None:
        where = (f"no {FREEZE_FILENAME}" if doc is None
                 else f"{FREEZE_FILENAME} has no [fingerprints] entry for {slug!r}")
        return (f"statement fingerprint not frozen ({where}); a post-cutoff node's checks are "
                "tied to its frozen statement fingerprint (`mission freeze --fingerprints`, or "
                "`mission unfreeze --fingerprints`)")
    if trusted_env_sha256 is not _ENV_UNCHECKED:
        frozen_env = doc.get("fingerprints_env")
        if not frozen_env or trusted_env_sha256 != frozen_env:
            return (f"fingerprint computed under a different trusted env: the fingerprint JSON "
                    f"names {str(trusted_env_sha256)[:16]}..., the freeze recorded "
                    f"{str(frozen_env)[:16]}... (`fingerprints_env`); fingerprint the theorem "
                    "under the pinned env the campaign was frozen with, or unfreeze")
    if str(fingerprint).lower() != frozen:
        return (f"statement fingerprint mismatch: the checked theorem's fingerprint "
                f"{str(fingerprint)[:16]}... is not the frozen statement fingerprint "
                f"{frozen[:16]}... of node {slug!r}; the checked declaration does not state the "
                "node's frozen statement")
    return ""


# ---------------------------------------------------------------------------
# Audit.lean generation and its #print-axioms vs closure-audit cross-check (step 5 Task 2)
#
# `render_audit_file` writes the SOURCE of `<root>/lean/Audit.lean`: one `import` per
# distinct proved-node artifact module (de-duplicated, sorted), then one `#print axioms
# <theorem>` per proved node (sorted by slug), where `<theorem>` is the artifact
# declaration the grant gate matched (`guard_anchors.resolve_theorem`) -- never a helper
# lemma beside it, the same binding `checks-record` and `nanoda-direct record` already
# enforce. Running `lake env lean Audit.lean` then prints, for every proved node, the
# axioms the KERNEL actually accepted for its theorem.
#
# `parse_print_axioms` reads that output back; `crosscheck_axioms` compares it against a
# closure audit's per-target axiom lists (`closure_audit.AuditResult.to_json`'s
# `targets[].axioms`, the closure-walk's INDEPENDENT record of the same thing) -- the two
# are required to agree, the same way `closure_audit`'s own Lean metaprogram cross-checks
# `collectAxioms` against the closure walk internally. A difference here is one the
# metaprogram's own cross-check cannot see: it is caught only by running the two checks
# separately and comparing their OUTPUT, so a stale `.olean` that both checks happen to
# read the same way is still exposed if either one is re-run against fresher state.
# ---------------------------------------------------------------------------

def _artifact_module(campaign_root: Path, node) -> str:
    """The Lean import name of *node*'s proof artifact.

    Fix round 1 (Ruling 10, Important finding 3): this now actually calls
    `provenance.lake_workspace` -- the earlier version re-derived the island root inline
    (`rejudge.island_of_artifact` + `judge.island_dir`) and resolved the module against
    THAT, which is a parallel, un-kept-in-sync re-implementation of part of what
    `lake_workspace` already does to pick the real build/export workspace (its own
    candidate search only ever accepts a smaller sub-workspace whose declared `lean_lib`
    maps the island-root-relative module name back to the artifact's own file, so the
    import name itself does not actually change across candidates -- but going through
    the one real resolver, rather than a hand-rolled copy of its first few steps, is what
    keeps this in lock-step with it if that ever changes). Off-island (no recognised judge
    island at all -- a synthetic test fixture with no `examples/<island>/lean` tree,
    typically), `lake_workspace` itself falls back to the artifact's own directory, so the
    module is then just the artifact's file stem, same as before.

    `judge.module_name_of` has no notion of `srcDir` at all (its own docstring says so): it
    just resolves *artifact* relative to whatever directory it is given. When
    `lake_workspace` picks a smaller sub-workspace whose own `srcDir` points back ABOVE
    itself (the zzl_aux shape: the artifact then lives OUTSIDE that directory on disk),
    resolving straight against the sub-workspace directory would raise (`artifact` is not
    relative to it) even though the module name is perfectly well-defined.
    `_module_root_for` retries against the workspace's own declared source roots
    (`srcDir`-aware, via `coverage._package`) before giving up."""
    from . import judge
    from .provenance import lake_workspace

    campaign_root = Path(campaign_root).resolve()
    artifact = (campaign_root / node.proof.artifact).resolve()
    workspace = lake_workspace(campaign_root, node)
    return judge.module_name_of(_module_root_for(workspace, artifact), artifact)


def _module_root_for(workspace: Path, artifact: Path) -> Path:
    """The directory `judge.module_name_of(_, artifact)` should actually be called
    against for a *workspace* `lake_workspace` chose: *workspace* itself when *artifact*
    is under it, else the first of `coverage._package(workspace)`'s own declared source
    roots (already `srcDir`-resolved, for the package itself and each of its libs) that
    contains it. Falls back to *workspace* itself -- so the caller's own `ValueError`
    ("not relative to") names the real failure -- if none do."""
    from . import coverage

    workspace = Path(workspace).resolve()
    artifact = Path(artifact).resolve()
    if artifact.is_relative_to(workspace):
        return workspace
    pkg = coverage._package(workspace)
    for src_dir in (pkg.src_dirs if pkg is not None else ()):
        src_dir = Path(src_dir).resolve()
        if artifact.is_relative_to(src_dir):
            return src_dir
    return workspace


#: A Lean identifier component safe to emit VERBATIM into generated Lean source (no
#: guillemet-quoting, no escaping of any kind): `closure_audit._IDENT_COMPONENT`, reused
#: rather than re-written (this task's own rule for escaping helpers, extended to the
#: validation that decides whether one is even needed).
def _validate_module_name(module: str, *, slug: str) -> None:
    """Refuses (`ValueError`, naming *slug*) a module whose dotted components are not
    every one a plain Lean identifier. Fix round 1 (Ruling 10, Critical finding 1):
    `render_audit_file` writes `module` straight into an `import` line with ZERO
    sanitisation (`judge.module_name_of` just dot-joins a FILESYSTEM PATH's components,
    and POSIX permits almost anything but `/` in a path component, including a literal
    newline) -- a node whose `[proof] artifact` names a path with an evil directory
    component (e.g. `"evil\\n#eval IO.println \\"pwned\\"\\n--"`) could otherwise inject
    arbitrary Lean commands into the generated `Audit.lean`, which spec 7.2's own workflow
    runs through `lake env lean`. Unlike a theorem name, a module name is NEVER
    guillemet-quoted here -- an `import` line is not a context this function trusts itself
    to escape -- so anything that is not already a safe plain identifier is refused
    outright rather than rendered. Fix round 2 (Ruling 11): `_IDENT_COMPONENT`'s charset is
    narrower than Lean's actual identifier grammar (it has no general Unicode-letter
    support beyond the specific ranges Lean itself commonly uses), so this refuses a
    perfectly legitimate non-ASCII-but-Lean-valid module component too -- deliberately:
    this function does not attempt to special-case Lean's full identifier grammar, and
    fails closed on anything it cannot immediately recognise as safe rather than risk
    admitting a character class later proven unsafe."""
    from ..closure_audit import _IDENT_COMPONENT

    for part in module.split("."):
        if not part or part[0].isdigit() or not _IDENT_COMPONENT.match(part):
            raise ValueError(
                f"node {slug!r}: its artifact resolves to import module {module!r}, whose "
                f"component {part!r} is not a plain Lean identifier; refusing to emit it "
                "into Audit.lean (this would otherwise inject unsanitised text into "
                "generated Lean source)."
            )


def _validate_theorem_name(theorem: str, *, slug: str) -> None:
    """Refuses (`ValueError`, naming *slug*) a theorem name carrying a control character
    (a literal newline above all -- the same Lean-source-injection vector
    `_validate_module_name` exists for). Every other character is fine: unlike a module
    name, `render_audit_file` renders a theorem name through `closure_audit.
    lean_name_literal`, which already guillemet-quotes any dotted component that is not a
    plain identifier -- so a dot, a trailing prime, or even an embedded space inside a
    «»-quoted component are all legitimate Lean names -- and already refuses an embedded
    `"»"`. `guard_anchors.resolve_theorem`'s own matching (word-boundary- and
    `\\S+`-anchored regexes throughout its namespace/declaration scan) cannot actually
    produce a newline-bearing name today, but this check is cheap and keeps the theorem
    side no less defended than the module side rather than relying on that staying true."""
    if any(ord(c) < 0x20 for c in theorem):
        raise ValueError(
            f"node {slug!r}: its registered theorem {theorem!r} contains a control "
            "character; refusing to emit it into Audit.lean."
        )


#: Header `render_audit_file` writes at the top of every generated Audit.lean.
_AUDIT_HEADER = (
    "-- GENERATED by `mission audit-file`; DO NOT EDIT BY HAND.\n"
    "-- One `#print axioms` per proved node's registered theorem (the artifact declaration\n"
    "-- the grant gate matched, `guard_anchors.resolve_theorem`); `mission audit-crosscheck`\n"
    "-- compares this file's output against a closure audit's per-target axiom lists."
)


def render_audit_file(root: Path) -> str:
    """The source of `<root>/lean/Audit.lean`: `_AUDIT_HEADER`, then one `import` per
    distinct proved-node artifact module (de-duplicated, sorted), then one `#print axioms
    <theorem>` per proved node, sorted by slug (`campaign.nodes`' own key order). `<theorem>`
    is the fully-qualified name `guard_anchors.resolve_theorem` reads off the artifact --
    the same binder `checks-record` and `nanoda-direct record` already require every
    recorded check to be of. A name needing «»-escaping is rendered with
    `closure_audit.lean_name_literal`, stripped of its leading backtick: that helper
    produces a TERM-level `` `Name `` literal, but `#print axioms` takes a raw (optionally
    guillemet-escaped) identifier, never a term.

    Fix round 1 (Ruling 10, Critical finding 1): every theorem name and module name is
    validated (`_validate_theorem_name`, `_validate_module_name`) before being emitted --
    raising `ValueError`, naming the offending node, rather than writing unsanitised
    artifact-path or theorem-name text into the generated Lean source."""
    from . import judge
    from .registry import load_campaign
    from ..closure_audit import lean_name_literal

    root = Path(root)
    campaign = load_campaign(root)
    ga = judge._guard_anchors()

    printed: List[Tuple[str, str]] = []  # (slug, fully-qualified theorem), slug order
    modules: Set[str] = set()
    for slug, node in sorted(campaign.nodes.items()):
        if node.status != "proved":
            continue
        if node.proof is None:
            raise ValueError(f"node {slug!r} is proved but carries no [proof] link")
        artifact = (root / node.proof.artifact).resolve()
        stmt = statement_path(root, node)
        theorem = ga.resolve_theorem(artifact.read_text(encoding="utf-8"),
                                     stmt.read_text(encoding="utf-8"))
        _validate_theorem_name(theorem, slug=slug)
        module = _artifact_module(root, node)
        _validate_module_name(module, slug=slug)
        modules.add(module)
        printed.append((slug, theorem))

    lines = [_AUDIT_HEADER, ""]
    lines += [f"import {m}" for m in sorted(modules)]
    lines.append("")
    for _slug, theorem in printed:
        lines.append(f"#print axioms {lean_name_literal(theorem)[1:]}")
    return "\n".join(lines) + "\n"


#: A `#print axioms` header, matched against a WHOLE line (`^...$`, never a `re.search`
#: over the full text): the name is read GREEDILY up to the fixed literal suffix, so a
#: name ending in its own `'` (a trailing prime -- Mathlib's single most common naming
#: idiom, e.g. `h'`, `Foo.bar'`) is captured whole rather than truncated at that embedded
#: quote (fix round 1, Ruling 10, Critical finding 2).
_HEADER_NONE_RE = re.compile(r"^'(.+)' does not depend on any axioms$")
_HEADER_LIST_RE = re.compile(r"^'(.+)' depends on axioms: \[(.*)$")

#: A line that is NOTHING but a single quoted name (fix round 2, Ruling 11): the bare
#: `'<name>'` half of a header whose "depends on axioms"/"does not depend..." half got
#: split onto a separate line (e.g. by a terminal or log line-wrap unrelated to Lean's own
#: bracket-wrapping, which never splits the header itself -- only the axiom LIST). Lean's
#: own output never prints a line that is just one quoted identifier and nothing else, so
#: this is unambiguously a malformed/split header, not a line to ignore.
_BARE_QUOTED_NAME_RE = re.compile(r"^'.+'$")  # greedy: primed names (`'h''`) too


def _record_axioms(axioms_by_name: Dict[str, Set[str]], name: str, axioms: Set[str]) -> None:
    """Shared by both header shapes: raises `ValueError` if *name* was already recorded
    with a DIFFERENT axiom set (a parse problem -- a stale cache, two runs' output
    concatenated, ... -- reported explicitly rather than resolved by silently keeping one
    of the two); a repeat with the SAME set is not an error."""
    if name in axioms_by_name and axioms_by_name[name] != axioms:
        raise ValueError(
            f"{name!r} is printed twice in the #print axioms output with different "
            f"axiom sets: {sorted(axioms_by_name[name])} and {sorted(axioms)}."
        )
    axioms_by_name[name] = axioms


def _split_axiom_bracket(rest: str) -> Tuple[bool, str]:
    """`(True, content before the first ']')` if *rest* closes its bracket, else
    `(False, rest)` unchanged so the caller can append more lines before checking again."""
    idx = rest.find("]")
    if idx == -1:
        return False, rest
    return True, rest[:idx]


def parse_print_axioms(output: str) -> Dict[str, Set[str]]:
    """Every `#print axioms` entry in *output* (Lean's text; one line, or wrapped -- Lean
    wraps a long bracketed axiom list one axiom per line, each continuation indented),
    mapped to its axiom set -- the empty set for "does not depend on any axioms".

    Fix round 1 (Ruling 10, Critical finding 2): line-based and anchored, not a
    `[^\\]]*`-style scan across the whole text. The old scan broke on the single most
    common Lean naming idiom (a trailing prime truncated the captured name) and let an
    UNTERMINATED list silently absorb everything up to and including a LATER theorem's own
    header line -- corrupting the first theorem's axiom set with garbage text and making
    the second theorem vanish from the result entirely, with no error at all. Here, a
    continuation line must start with whitespace; a new header-looking line, or the end of
    input, before the closing `]` is an explicit `ValueError` ("unterminated axiom list"),
    never a silent absorption. A line that is neither a recognised header nor (while a
    list is open) a continuation -- a warning, an `info:` line, a blank line -- is
    ignored, UNLESS it looks like a header but does not fully match (e.g. a typo'd
    "depends on axiomss:", or a header whose closing quote and "depends on axioms" land
    on two different lines -- fix round 2, Ruling 11), which raises rather than being
    silently skipped. `str.splitlines()` already treats `\\r\\n` as a single line ending.

    Raises `ValueError` if the same theorem is printed twice with two DIFFERENT axiom
    sets (see `_record_axioms`)."""
    axioms_by_name: Dict[str, Set[str]] = {}
    lines = output.splitlines()
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        i += 1

        m_none = _HEADER_NONE_RE.match(line)
        if m_none:
            _record_axioms(axioms_by_name, m_none.group(1), set())
            continue

        m_list = _HEADER_LIST_RE.match(line)
        if m_list:
            name = m_list.group(1)
            closed, content = _split_axiom_bracket(m_list.group(2))
            while not closed:
                if i >= n or not lines[i][:1].isspace():
                    raise ValueError(
                        f"unterminated axiom list for {name!r} (no closing ']' before "
                        "end of input or the next theorem)."
                    )
                closed, more = _split_axiom_bracket(lines[i])
                content += "," + more
                i += 1
            axioms = {a.strip() for a in content.split(",") if a.strip()}
            _record_axioms(axioms_by_name, name, axioms)
            continue

        stripped = line.strip()
        if stripped.startswith("'") and (
                " depends on axioms" in stripped
                or "does not depend on any axioms" in stripped
                or _BARE_QUOTED_NAME_RE.match(stripped)):
            raise ValueError(f"unrecognised #print axioms line: {line!r}")
        # else: a warning, an `info:` line, a blank line, ... -- ignored.
    return axioms_by_name


def crosscheck_axioms(print_axioms: Dict[str, Set[str]],
                      closure_axioms: Dict[str, Sequence[str]]) -> List[str]:
    """Every theorem whose `#print axioms` set (*print_axioms*, `parse_print_axioms`'s
    output) differs from the closure audit's recorded set for it (*closure_axioms*, the
    closure audit JSON's `targets[].axioms`, keyed by target name --
    `closure_audit.AuditResult.to_json`). A theorem present on only one side is a problem
    too: a closure-audit target Audit.lean never printed, or a printed theorem the closure
    audit never audited, is exactly the drift this cross-check exists to catch (e.g. a
    stale `.olean` on one side alone -- the "stale cache" case). Sorted by name.

    Fix round 1 (Ruling 10, minor finding): *closure_axioms*' entries are type-checked as
    `list[str]` up front -- raising `ValueError` naming the offending target -- rather
    than letting a malformed JSON (a caller's bug, or a corrupted file) fail with a
    confusing `TypeError` deep inside a later `sorted()`/set operation."""
    for name, axioms in closure_axioms.items():
        if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms):
            raise ValueError(
                f"{name!r}: the closure audit's axioms entry is not a list of strings "
                f"({axioms!r})."
            )

    problems: List[str] = []
    for name in sorted(set(print_axioms) | set(closure_axioms)):
        if name not in print_axioms:
            problems.append(
                f"{name!r}: in the closure audit's targets, but Audit.lean never printed it."
            )
            continue
        if name not in closure_axioms:
            problems.append(
                f"{name!r}: printed by Audit.lean, but not among the closure audit's targets."
            )
            continue
        printed = set(print_axioms[name])
        closure = set(closure_axioms[name])
        if printed == closure:
            continue
        only_printed = sorted(printed - closure)
        only_closure = sorted(closure - printed)
        parts = []
        if only_printed:
            parts.append(f"#print axioms only has {only_printed}")
        if only_closure:
            parts.append(f"the closure audit only has {only_closure}")
        problems.append(f"{name!r}: axiom sets differ ({'; '.join(parts)}).")
    return problems


# ---------------------------------------------------------------------------
# The deviation ledger (step 5 Task 3): DEVIATIONS.md
#
# Spec 7.3: DEVIATIONS.md records every departure of a node's formal statement from its
# informal source, each with a reason and a date. A grant requires the ledger to be
# present and read back (`deviations_grant_problem`, called from `verify.grant_status`
# next to `freeze_grant_problem`, scoped by the same post-cutoff predicate,
# `provenance.checks_required`). An empty ledger must say so explicitly -- `none` -- rather
# than being silently absent or carrying a non-answer like `N/A`.
# ---------------------------------------------------------------------------

#: Name of the campaign-level deviation ledger, at the campaign root (next to `mission.toml`).
DEVIATIONS_FILENAME = "DEVIATIONS.md"

#: Upper bound on DEVIATIONS.md, the same rationale as `FREEZE_MAX_BYTES`: a real ledger is
#: a handful of one-line entries, and refusing anything this large before decoding keeps a
#: hostile file from costing more than a stat.
DEVIATIONS_MAX_BYTES = 1 << 20

#: `mission freeze` writes this when `<root>/DEVIATIONS.md` does not exist yet
#: (`write_deviations_template_if_missing`): a header comment explaining the format, and a
#: body of exactly `none` -- itself a valid ledger (`test_template_parses_as_none`), so a
#: freshly frozen campaign with no deviations recorded yet can still be granted.
DEVIATIONS_TEMPLATE = (
    "<!-- DEVIATIONS.md records every departure of a node's formal statement from its\n"
    "     informal source (spec 7.3), each with a reason and a date. Below, either:\n"
    "       - the single word `none`, if there are no deviations; or\n"
    "       - one or more lines `- YYYY-MM-DD | what departs | why`.\n"
    "     A grant requires this file to be present and read back; write `none` rather\n"
    "     than deleting it or leaving it empty. -->\n"
    "none\n"
)


def deviations_path(root: Path) -> Path:
    """`<root>/DEVIATIONS.md`, the campaign-level deviation ledger."""
    return Path(root) / DEVIATIONS_FILENAME


#: A line that is nothing but `none`, case-insensitively, with an optional trailing `.`
#: (`test_none_spellings`: `none`, `None`, `NONE.` are all the same answer).
_DEVIATIONS_NONE_RE = re.compile(r"^none\.?$", re.IGNORECASE)

#: `N/A` is explicitly NOT an accepted spelling of "no deviations" -- it reads as "this
#: question does not apply", not as "I checked and there are none" -- so it gets a
#: dedicated hint rather than falling into the generic "malformed line" message.
_DEVIATIONS_NA_RE = re.compile(r"^n/a\.?$", re.IGNORECASE)

#: One dated entry: `- YYYY-MM-DD | what | why`. `what` is matched non-greedily so the
#: first ` | ` is the one that ends it even if `why` itself contains ` | `; `why` is
#: matched greedily to end-of-line so it may contain one freely.
_DEVIATIONS_ENTRY_RE = re.compile(r"^- (\d{4}-\d{2}-\d{2}) \| (.+?) \| (.+)$")

#: The hint appended whenever a line reads as a non-answer rather than a real entry.
_DEVIATIONS_NONE_HINT = "write `none` if there are no deviations to record."


def _parsed_date(text: str) -> Optional[datetime.date]:
    """*text* as a real calendar `datetime.date`, or `None` if it is not one (`2026-02-30`
    is the right SHAPE but not a real date; `datetime.date.fromisoformat` is what actually
    catches that, a plain regex would not)."""
    try:
        return datetime.date.fromisoformat(text)
    except ValueError:
        return None


def _strip_deviations_header(lines: List[str]) -> List[Tuple[int, str]]:
    """*lines* (1-indexed against the ORIGINAL text by the caller), with the header HTML
    comment -- the first run from a `<!--` through the first `-->` after it -- and every
    blank line removed; every remaining line keeps its original 1-based line number, so a
    later error can point straight at it.

    Fix round 1 (reviewer-found Critical): content sharing a PHYSICAL line with the
    comment markers is never discarded along with them. Text before the opening `<!--`,
    and text after the closing `-->` (whether that close is on the opening line itself or
    on a later one), is kept as a body line at that same line number, stripped of the
    incidental leading/trailing whitespace the cut left behind --
    `parse_deviations("<!-- header --> - 2026-10-28 | real entry | why\\n")` used to
    silently discard the entry; it now parses it (or rejects it if malformed), same as any
    other line. Only the FIRST `<!--` is ever treated as a header open; a `<!--` appearing
    later (e.g. inside an entry's own text) is left as ordinary body text.

    Raises `ValueError` if a `<!--` is ever opened and never closed: an unterminated
    comment is malformed, not silently "the rest of the file is a comment" (the rule this
    task's brief states explicitly)."""
    body: List[Tuple[int, str]] = []
    seen_comment = False
    in_comment = False
    comment_start = 0
    for lineno, line in enumerate(lines, start=1):
        if in_comment:
            idx = line.find("-->")
            if idx == -1:
                continue
            in_comment = False
            after = line[idx + 3:].strip()
            if after:
                body.append((lineno, after))
            continue
        if not seen_comment:
            open_idx = line.find("<!--")
            if open_idx != -1:
                seen_comment = True
                comment_start = lineno
                before = line[:open_idx].strip()
                if before:
                    body.append((lineno, before))
                close_idx = line.find("-->", open_idx + 4)
                if close_idx == -1:
                    in_comment = True
                else:
                    after = line[close_idx + 3:].strip()
                    if after:
                        body.append((lineno, after))
                continue
        if not line.strip():
            continue
        body.append((lineno, line))
    if in_comment:
        raise ValueError(
            f"{DEVIATIONS_FILENAME}:{comment_start}: unterminated '<!--' comment (no "
            "closing '-->' before end of file)."
        )
    return body


def parse_deviations(text: str, *, today: Optional[datetime.date] = None) -> List[dict]:
    """*text* (`DEVIATIONS.md`'s content) parsed into a list of deviation entries, each
    `{"date": ..., "what": ..., "why": ...}`, in file order; `[]` for a ledger that says
    `none`. Raises `ValueError`, naming the offending line number, on anything else.

    After `_strip_deviations_header` removes the header comment and blank lines, what is
    left must be either exactly one line reading `none` (case-insensitively, a trailing
    `.` allowed), or one or more lines matching `_DEVIATIONS_ENTRY_RE`, each with a real
    calendar date no later than *today* (`datetime.date.today()` if not given -- a fixed
    value lets a test pin "future" without depending on the clock) and a non-empty `what`
    and `why` once stripped. Everything else raises; a bare `N/A` or a wholly empty body
    (no content lines at all) gets a dedicated hint to write `none` instead, rather than
    the generic malformed-line message. A body holding BOTH a `none` line and a real entry
    is not "exactly one line reading `none`", so it is malformed too -- the `none` line
    itself is reported, naming its line number."""
    today = today if today is not None else datetime.date.today()
    body = _strip_deviations_header(text.splitlines())

    if not body:
        raise ValueError(f"{DEVIATIONS_FILENAME}: body is empty; {_DEVIATIONS_NONE_HINT}")

    if len(body) == 1 and _DEVIATIONS_NONE_RE.match(body[0][1].strip()):
        return []

    entries: List[dict] = []
    for lineno, line in body:
        m = _DEVIATIONS_ENTRY_RE.match(line)
        if m:
            raw_date, what, why = m.groups()
            entry_date = _parsed_date(raw_date)
            if entry_date is None:
                raise ValueError(
                    f"{DEVIATIONS_FILENAME}:{lineno}: {raw_date!r} is not a real calendar "
                    "date."
                )
            if entry_date > today:
                raise ValueError(
                    f"{DEVIATIONS_FILENAME}:{lineno}: {raw_date!r} is after today "
                    f"({today.isoformat()}); a deviation cannot be dated in the future."
                )
            what, why = what.strip(), why.strip()
            if not what or not why:
                raise ValueError(
                    f"{DEVIATIONS_FILENAME}:{lineno}: empty 'what' or 'why' in {line!r}."
                )
            entries.append({"date": raw_date, "what": what, "why": why})
            continue
        if _DEVIATIONS_NA_RE.match(line.strip()):
            raise ValueError(
                f"{DEVIATIONS_FILENAME}:{lineno}: {line.strip()!r} is not an answer; "
                f"{_DEVIATIONS_NONE_HINT}"
            )
        raise ValueError(
            f"{DEVIATIONS_FILENAME}:{lineno}: malformed line (expected `none` or "
            f"`- YYYY-MM-DD | what | why`): {line!r}"
        )
    return entries


def _load_deviations_safe(root: Path) -> Tuple[Optional[str], Optional[str]]:
    """The guarded reader of the working-tree DEVIATIONS.md, the same shape and the same
    refusals as `_load_freeze_safe` (Controller Ruling 8), minus the TOML/shape parsing --
    this module only ever hands the raw text to `parse_deviations`. Returns `(text,
    None)`; `(None, None)` if the campaign has no ledger yet; or `(None, problem)` when the
    path exists but cannot be trusted: a symlink (refused before anything is read through
    it -- the same injection this guards against for FREEZE.toml), anything else that is
    not a regular file, a file over `DEVIATIONS_MAX_BYTES`, or content that is not valid
    UTF-8. Never raises."""
    path = deviations_path(root)
    try:
        st = path.lstat()
    except FileNotFoundError:
        return None, None
    except OSError as exc:
        return None, f"{DEVIATIONS_FILENAME} could not be read ({exc.strerror or exc})."
    if stat.S_ISLNK(st.st_mode):
        return None, (f"{DEVIATIONS_FILENAME} is a symlink in the working tree; refusing "
                      "to trust it.")
    if not stat.S_ISREG(st.st_mode):
        return None, (f"{DEVIATIONS_FILENAME} in the working tree is not a regular file "
                      "(a directory, e.g. a submodule checkout, or a special file); "
                      "refusing to trust it.")
    if st.st_size > DEVIATIONS_MAX_BYTES:
        return None, (f"{DEVIATIONS_FILENAME} is larger than {DEVIATIONS_MAX_BYTES} bytes; "
                      "refusing to trust it.")
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
                     | getattr(os, "O_NONBLOCK", 0))
        with os.fdopen(fd, "rb") as fh:
            if not stat.S_ISREG(os.fstat(fh.fileno()).st_mode):
                return None, (f"{DEVIATIONS_FILENAME} changed while being read; refusing "
                              "to trust it.")
            data = fh.read(DEVIATIONS_MAX_BYTES + 1)
    except OSError as exc:
        return None, f"{DEVIATIONS_FILENAME} could not be read ({exc.strerror or exc})."
    if len(data) > DEVIATIONS_MAX_BYTES:
        return None, (f"{DEVIATIONS_FILENAME} is larger than {DEVIATIONS_MAX_BYTES} bytes; "
                      "refusing to trust it.")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return None, f"{DEVIATIONS_FILENAME} is not valid UTF-8; refusing to trust it."
    return text, None


def write_deviations_template_if_missing(root: Path) -> bool:
    """Writes `DEVIATIONS_TEMPLATE` to `<root>/DEVIATIONS.md` if nothing at all is there
    yet (not even a dangling symlink), and returns whether it wrote. Called from `mission
    freeze` (Task 3): without this, a freshly frozen campaign has no ledger at all, and
    every post-cutoff grant afterwards would be refused on "no DEVIATIONS.md" until
    someone writes one by hand. A file already there, valid or not, is left alone --
    writing a template over a ledger someone actually filled in would silently discard it."""
    root = Path(root)
    path = deviations_path(root)
    if path.exists() or path.is_symlink():
        return False
    atomic_write_text(path, DEVIATIONS_TEMPLATE)
    return True


#: Name of the campaign-level read-back record for DEVIATIONS.md, at the campaign root.
DEVIATIONS_READBACK_FILENAME = "DEVIATIONS.readback.toml"


def deviations_readback_path(root: Path) -> Path:
    """`<root>/DEVIATIONS.readback.toml`: who read DEVIATIONS.md back, and the sha256 of
    the exact bytes they read (spec 7.3's "present and read back" -- distinct from merely
    PARSING the ledger, which `deviations_grant_problem` already required before this
    existed; fix round 1, reviewer-found Important)."""
    return Path(root) / DEVIATIONS_READBACK_FILENAME


def _parse_deviations_readback_bytes(data: bytes) -> Tuple[Optional[dict], Optional[str]]:
    """`(doc, None)`, or `(None, why)` completing "DEVIATIONS.readback.toml ...". Same
    small, fixed-shape TOML record as FREEZE.toml's own fields (`_parse_freeze_bytes`),
    just four required non-empty string fields, one of them a 64-hex-digit sha256."""
    if len(data) > DEVIATIONS_MAX_BYTES:
        return None, f"is larger than {DEVIATIONS_MAX_BYTES} bytes"
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return None, "is not valid UTF-8"
    try:
        import tomllib
    except ModuleNotFoundError:
        import tomli as tomllib  # type: ignore[no-redef]
    try:
        doc = tomllib.loads(text)
    except Exception as exc:  # TOMLDecodeError, or whatever else a hostile file provokes
        return None, f"is not valid TOML ({exc})"
    for key in ("ledger_sha256", "auditor_identity", "auditor_session", "date"):
        if not isinstance(doc.get(key), str) or not doc[key].strip():
            return None, f"has no non-empty string {key!r}"
    if not re.fullmatch(r"[0-9a-f]{64}", doc["ledger_sha256"]):
        return None, "has a ledger_sha256 that is not 64 lowercase hex digits"
    return doc, None


def _load_deviations_readback_safe(root: Path) -> Tuple[Optional[dict], Optional[str]]:
    """The guarded reader of DEVIATIONS.readback.toml: the same refusals as
    `_load_deviations_safe` (symlink refused via `lstat` before any read, `O_NOFOLLOW` as a
    second line of defense, non-regular files and anything over `DEVIATIONS_MAX_BYTES`
    refused, a decode error turned into a returned string), plus the TOML/shape check
    (`_parse_deviations_readback_bytes`). Returns `(doc, None)`; `(None, None)` if nothing
    is there yet; `(None, problem)` for anything this refuses. Never raises."""
    path = deviations_readback_path(root)
    try:
        st = path.lstat()
    except FileNotFoundError:
        return None, None
    except OSError as exc:
        return None, (f"{DEVIATIONS_READBACK_FILENAME} could not be read "
                      f"({exc.strerror or exc}).")
    if stat.S_ISLNK(st.st_mode):
        return None, (f"{DEVIATIONS_READBACK_FILENAME} is a symlink in the working tree; "
                      "refusing to trust it.")
    if not stat.S_ISREG(st.st_mode):
        return None, (f"{DEVIATIONS_READBACK_FILENAME} in the working tree is not a "
                      "regular file (a directory, e.g. a submodule checkout, or a special "
                      "file); refusing to trust it.")
    if st.st_size > DEVIATIONS_MAX_BYTES:
        return None, (f"{DEVIATIONS_READBACK_FILENAME} is larger than "
                      f"{DEVIATIONS_MAX_BYTES} bytes; refusing to trust it.")
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
                     | getattr(os, "O_NONBLOCK", 0))
        with os.fdopen(fd, "rb") as fh:
            if not stat.S_ISREG(os.fstat(fh.fileno()).st_mode):
                return None, (f"{DEVIATIONS_READBACK_FILENAME} changed while being read; "
                              "refusing to trust it.")
            data = fh.read(DEVIATIONS_MAX_BYTES + 1)
    except OSError as exc:
        return None, (f"{DEVIATIONS_READBACK_FILENAME} could not be read "
                      f"({exc.strerror or exc}).")
    doc, why = _parse_deviations_readback_bytes(data)
    if why:
        return None, f"{DEVIATIONS_READBACK_FILENAME} {why}; refusing to trust it."
    return doc, None


def write_deviations_readback(root: Path, *, identity: str, session: str, date: str) -> dict:
    """`mission deviations-readback`: validates `<root>/DEVIATIONS.md` -- must exist, be
    safely readable (`_load_deviations_safe`), and parse (`parse_deviations`) -- then
    writes `<root>/DEVIATIONS.readback.toml` recording its sha256 and the auditor's
    identity/session/date. Raises `ValueError` (and writes nothing) if *identity* or
    *session* is empty, or if the ledger is missing, untrusted, or malformed: a read-back
    must never be recorded against a ledger `deviations_grant_problem` would itself refuse
    to read, and this command does not know which node's author to compare the auditor
    against (DEVIATIONS.md is campaign-wide) -- that self-audit refusal happens at grant
    time instead, per node, in `deviations_grant_problem`."""
    root = Path(root)
    identity = (identity or "").strip()
    session = (session or "").strip()
    if not identity:
        raise ValueError("deviations-readback: identity must be non-empty.")
    if not session:
        raise ValueError("deviations-readback: session must be non-empty.")
    text, problem = _load_deviations_safe(root)
    if problem:
        raise ValueError(problem)
    if text is None:
        raise ValueError(f"no {DEVIATIONS_FILENAME} at the campaign root; nothing to read back.")
    parse_deviations(text)  # raises ValueError, naming the offending line, if malformed
    doc = {
        "ledger_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
        "auditor_identity": identity,
        "auditor_session": session,
        "date": date,
    }
    lines = [f"{key} = {_quote(value)}" for key, value in doc.items()]
    atomic_write_text(deviations_readback_path(root), "\n".join(lines) + "\n")
    return doc


def deviations_grant_problem(root: Path, node) -> str:
    """"" unless *node* is post-cutoff (`provenance.checks_required`, the same predicate
    `freeze_grant_problem` uses); else why the grant gate must refuse it.

    Four layers, in order: (1) DEVIATIONS.md must exist, be trustworthy
    (`_load_deviations_safe`), and parse (`parse_deviations`); (2) spec 7.3 also says
    "read back" -- which parsing alone does NOT satisfy (fix round 1, reviewer-found
    Important: the original docstring here claimed otherwise) -- so
    DEVIATIONS.readback.toml must exist, be trustworthy, and record the sha256 of the
    ledger's CURRENT content, not a stale one; (3) the node must carry an `[author]` block
    at all (fix round 2, Ruling 13: `readback_is_self_audit` treats a missing `[author]`
    as merely "undecidable" and skips its own check rather than refusing -- reasonable for
    a legacy, pre-2026-09-23 node, but a POST-CUTOFF node with none can only mean a hand
    edit removed it, since `mission add` always writes one; left as a skip here, the same
    identity could write the read-back and perform the grant with no refusal at all, which
    a reviewer reproduced live as an actual bypass of layer (4) below); (4) its auditor
    must not be the node's own author (`provenance._auditor_matches`, the exact comparison
    `readback_is_self_audit` uses for a node's own `[readback]` block, reused rather than
    re-implemented so the two self-audit checks can never drift apart)."""
    from .provenance import _auditor_matches, checks_required

    if not checks_required(node):
        return ""
    root = Path(root)
    text, problem = _load_deviations_safe(root)
    if problem:
        return problem
    if text is None:
        return (
            f"no {DEVIATIONS_FILENAME} at the campaign root; a post-cutoff node may not be "
            "granted until the deviation ledger is recorded (write `none` if there are "
            "none)."
        )
    try:
        parse_deviations(text)
    except ValueError as exc:
        return str(exc)

    readback, rb_problem = _load_deviations_readback_safe(root)
    if rb_problem:
        return rb_problem
    if readback is None:
        return (
            f"no {DEVIATIONS_READBACK_FILENAME} at the campaign root; a post-cutoff node "
            "may not be granted until DEVIATIONS.md has an independent read-back on "
            "record (`mission deviations-readback`)."
        )
    current_sha = hashlib.sha256(text.encode("utf-8")).hexdigest()
    if readback["ledger_sha256"] != current_sha:
        return (
            f"{DEVIATIONS_READBACK_FILENAME}: the ledger changed since its read-back "
            f"(recorded sha256 {readback['ledger_sha256'][:16]}..., current "
            f"{current_sha[:16]}...); read it back again (`mission deviations-readback`)."
        )
    author = node.author
    if author is None:
        return (
            "node has no [author] block; a post-cutoff grant needs one to check "
            f"{DEVIATIONS_READBACK_FILENAME}'s read-back independence (`mission add` "
            "always writes one; this node's record appears to have been edited by hand)."
        )
    if _auditor_matches(readback["auditor_identity"], readback["auditor_session"],
                        author.identity, author.session):
        return (
            f"{DEVIATIONS_READBACK_FILENAME}: its auditor (identity "
            f"{readback['auditor_identity']!r}, session {readback['auditor_session']!r}) "
            "is the node's own author; a self-read-back cannot support a grant."
        )
    return ""


# ---------------------------------------------------------------------------
# The provenance-header lint (step 5 Task 4)
#
# Spec 7.4: every ported file names its source repository, file and commit, and a lint
# check enforces this, islands included. A `.lean` file is "ported" (`ported_files`)
# either by a `ported`/`adapted`/`copied from` mention in its own first 30 lines --
# inside a `--` or `/- -/` Lean comment, never inside a string literal or in code, and
# matched via the shared Lean lexer (`judge._guard_anchors().lean_segments`, step 4's
# comment/string/raw/char split -- this does not re-lex Lean on its own) -- or by being
# named in `<root>/PORTED.toml`'s `files = [...]`, regardless of whether it carries any
# mention of its own (a hand-curated declaration of "this came from elsewhere" that a
# header-mention scan alone could miss, e.g. a file ported verbatim with its original
# header already stripped). Every ported file must then carry a line matching
# `^-- Provenance: repo=... file=... commit=<40 lowercase hex>$`, same window, same
# comment-only scan; `provenance_problems` reports every file that does not, plus every
# PORTED.toml problem of its own (unsafe or missing entries, an untrustworthy
# PORTED.toml) independent of whether any file is ported at all.
#
# Every read here is guarded the way `_load_freeze_safe` already is (Controller Ruling
# 8): a symlink refused via `lstat` before anything is read through it, `O_NOFOLLOW` as
# a second line of defense, non-regular files and oversized files refused, and a decode
# or parse failure turned into a returned problem string -- never a traceback, the CLI
# included. The tree walk never follows a directory symlink (`os.walk`'s own default)
# and never descends into `.git/`, `.lake/`, or a build directory, so a campaign cannot
# be escaped, looped back into, or made to walk an unrelated dependency tree through
# one. A PORTED.toml entry is accepted only as a path relative to *root* with no `..`
# component and no absolute form, and only once its resolved target is confirmed to
# still land inside *root* -- the same shape of escape a symlinked component could
# otherwise launder.
# ---------------------------------------------------------------------------

#: How many of a `.lean` file's lines count toward both the `ported from` mention scan
#: and the provenance-header scan (spec 7.4: "first 30 lines").
_PORTED_HEAD_LINES = 30

#: Upper bound on how much of a `.lean` file `_read_lean_head_safe` will read, so a
#: pathological single huge line (or a huge file with no early newline) costs no more
#: than one bounded read -- the same rationale as `FREEZE_MAX_BYTES`, just much smaller
#: since only a header-sized prefix is ever needed.
_LEAN_HEAD_MAX_BYTES = 1 << 16

#: Directory names the tree walk never descends into: version control and Lake's own
#: (potentially huge, and irrelevant) build/dependency output.
_SKIP_DIR_NAMES = frozenset({".git", ".lake", "build", "_build"})

#: `(?i)\b(ported|adapted|copied) from\b`, scanned only against the comment-only text
#: of a file's first `_PORTED_HEAD_LINES` lines (`_lean_head_comment_text`) -- a mention
#: inside a string literal or in ordinary code is masked out before this ever runs.
#:
#: KNOWN LIMITATION (fix round 1, review of commit 7a7df30, Minor): this is a literal
#: ASCII match, exactly spec 7.4's own wording. A Unicode homoglyph -- a Cyrillic `а`
#: (U+0430) in place of the Latin `a` in "from", e.g. -- defeats it entirely: the file
#: is never classified as ported, so no header is ever required of it. Not a bug
#: relative to the brief, which defines "ported" by this exact regex, but a real, cheap
#: way to dodge the control deliberately (or by copy-pasting from a source whose own
#: header already carries one); documented here rather than left to be rediscovered.
_PORTED_MENTION_RE = re.compile(r"(?i)\b(ported|adapted|copied) from\b")

#: The header LINE's shape, matched against the same comment-only text (`re.MULTILINE`,
#: one match per line via `finditer`, not `search` -- `provenance_problems` needs every
#: match, not just the first, to detect more than one): `repo=` and `file=` tokens are
#: anything non-whitespace, same as the brief's regex; the commit token is captured
#: lazily (`\S+?`) and un-anchored to hex here so a short or non-hex commit still
#: matches the LINE (letting `provenance_problems` report it with a specific "not 40
#: lowercase hex" message) rather than falling through to the generic "no header at
#: all" one. `[ \t\r]*` before the `$` (fix round 1, Minor: CRLF files and trailing
#: whitespace used to fail CLOSED, reported as "no header", because a trailing `\r`
#: sits between the commit token and the `\n` a plain `$` anchors on) absorbs a
#: trailing `\r` (a CRLF line ending -- Lean's own lexer, and `_lean_head_comment_text`
#: built on it, treat `\r` as part of the preceding comment's text, not a line
#: terminator) or ordinary trailing spaces/tabs before the line truly ends, without
#: ever becoming part of the captured commit token itself.
_PROVENANCE_LINE_RE = re.compile(
    r"^-- Provenance: repo=(\S+) file=(\S+) commit=(\S+?)[ \t\r]*$", re.MULTILINE)

#: The commit token's own required shape (spec 7.4's exact regex: `[0-9a-f]{40}`).
_PROVENANCE_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")

#: Name of the campaign-level declaration of explicitly-ported files, at the campaign
#: root (next to `mission.toml`).
PORTED_TOML_FILENAME = "PORTED.toml"

#: Upper bound on PORTED.toml, the same rationale as `FREEZE_MAX_BYTES`: a real one is a
#: short list of relative paths.
PORTED_TOML_MAX_BYTES = 1 << 20


def ported_toml_path(root: Path) -> Path:
    """`<root>/PORTED.toml`, the campaign-level declaration of explicitly-ported files."""
    return Path(root) / PORTED_TOML_FILENAME


def _lean_head_comment_text(text: str, *, max_lines: int = _PORTED_HEAD_LINES) -> str:
    """The first *max_lines* lines of *text*, with everything OUTSIDE a `--` or `/- -/`
    Lean comment replaced by spaces (newlines kept, so line numbers and `^`/`$` anchors
    in the result still line up with the original text). Built from the shared Lean
    lexer (`judge._guard_anchors().lean_segments`, step 4's one comment/string/raw/char
    split) rather than a new regex scan, so a `ported from` mention or a provenance
    header inside a string literal -- or split across a code/comment boundary -- can
    never be mistaken for the real thing."""
    from .judge import _guard_anchors

    snippet = "".join(text.splitlines(keepends=True)[:max_lines])
    ga = _guard_anchors()
    out: List[str] = []
    for kind, seg in ga.lean_segments(snippet):
        if kind == "comment":
            out.append(seg)
        else:
            out.append("".join(ch if ch == "\n" else " " for ch in seg))
    return "".join(out)


def _read_lean_head_safe(path: Path) -> Tuple[Optional[str], Optional[str]]:
    """The first `_PORTED_HEAD_LINES` lines of *path*, read the same guarded way as
    `_load_freeze_safe`: refuses a symlink via `lstat` before anything is read through
    it (`O_NOFOLLOW` as a second line of defense against one swapped in after the
    lstat); refuses anything that is not a regular file. Stops BEFORE a line that would
    push the total past `_LEAN_HEAD_MAX_BYTES` rather than reading a partial one, so a
    decode can never split a multi-byte UTF-8 character mid-line; a decode error (or any
    other I/O failure) becomes a returned problem string, never a traceback. Returns
    `(text, None)`, or `(None, problem)` -- *problem* names no path; the caller already
    knows which file it asked about."""
    try:
        st = path.lstat()
    except OSError as exc:
        return None, f"could not be read ({exc.strerror or exc})"
    if stat.S_ISLNK(st.st_mode):
        return None, "is a symlink; refusing to read it"
    if not stat.S_ISREG(st.st_mode):
        return None, "is not a regular file; refusing to read it"
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
                     | getattr(os, "O_NONBLOCK", 0))
        with os.fdopen(fd, "rb") as fh:
            if not stat.S_ISREG(os.fstat(fh.fileno()).st_mode):
                return None, "changed while being read; refusing to trust it"
            chunks: List[bytes] = []
            total = 0
            for _ in range(_PORTED_HEAD_LINES):
                remaining = _LEAN_HEAD_MAX_BYTES - total
                if remaining <= 0:
                    break
                line = fh.readline(remaining + 1)
                if not line:
                    break
                if total + len(line) > _LEAN_HEAD_MAX_BYTES:
                    break
                chunks.append(line)
                total += len(line)
    except OSError as exc:
        return None, f"could not be read ({exc.strerror or exc})"
    try:
        return b"".join(chunks).decode("utf-8"), None
    except UnicodeDecodeError:
        return None, "is not valid UTF-8; refusing to read it"


def _walk_lean_files(root: Path) -> List[Path]:
    """Every `.lean` file under *root*, ABSOLUTE paths, sorted. The walk never follows a
    directory symlink (`os.walk`'s own default, `followlinks=False`: a campaign cannot
    be escaped or looped back into through one) and never descends into `.git/`,
    `.lake/`, or a build directory (`_SKIP_DIR_NAMES`) -- none of them hold anything this
    lint should look at, and `.lake/` in particular can hold a huge, unrelated
    dependency tree. A `.lean` path that is ITSELF a symlink is still returned here;
    `_read_lean_head_safe` is what refuses to follow it."""
    root = Path(root)
    found: List[Path] = []
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = [d for d in dirnames if d not in _SKIP_DIR_NAMES]
        for name in filenames:
            if name.endswith(".lean"):
                found.append(Path(dirpath) / name)
    return sorted(found)


def _walk_symlinked_dirs(root: Path) -> List[Path]:
    """Every directory the walk meets that is ITSELF a symlink, ABSOLUTE paths, sorted
    -- the directory analogue of a symlinked `.lean` FILE (fix round 1). `os.walk`'s
    own `followlinks=False` already means `_walk_lean_files` never descends into one,
    but it used to do so SILENTLY: a `.lean` file reachable only through a symlinked
    directory (to a location inside the campaign, or -- Controller Ruling 15's repro --
    entirely outside it) was never walked into and so never seen at all, by either the
    auto-detection scan or this unconditional symlink check -- a `.lean`-level check
    alone could not catch it, because the ported file hiding behind it is never even
    offered to that check.

    Excludes a symlinked directory NAMED in `_SKIP_DIR_NAMES` (`.git`, `.lake`,
    `build`, `_build`) at the point it is found, and -- because the walk never
    descends into a skip-listed name at all, symlinked or not -- anything nested
    underneath one either: `.lake` in particular is routinely itself a symlink (a
    shared build cache between campaigns), and a symlinked directory living inside
    `.git/` or `.lake/` is neither interesting to this lint nor ever reached by it."""
    root = Path(root)
    found: List[Path] = []
    for dirpath, dirnames, _filenames in os.walk(root, followlinks=False):
        kept: List[str] = []
        for name in dirnames:
            if name in _SKIP_DIR_NAMES:
                continue  # never descended into, never reported (same as the file walk)
            full = Path(dirpath) / name
            if full.is_symlink():
                found.append(full)
                continue  # never descended into (os.walk's own followlinks=False);
                          # reported here instead of silently vanishing
            kept.append(name)
        dirnames[:] = kept
    return sorted(found)


def _safe_ported_relpath(root: Path, raw: str) -> Tuple[Optional[Path], Optional[str]]:
    """*raw* (one `PORTED.toml` `files` entry) as a `Path` relative to *root*, or
    `(None, reason)` if it is not safely INSIDE the campaign: not a non-empty string, an
    absolute path, a `..` component, or anything whose resolved target does not land
    inside *root* once resolved (a symlinked component walking back out, e.g.) --
    PORTED.toml entries name a file inside the campaign, never a filesystem path that
    can reach outside it."""
    if not isinstance(raw, str) or not raw.strip():
        return None, "is not a non-empty string"
    rel = Path(raw)
    if rel.is_absolute():
        return None, "is an absolute path"
    if ".." in rel.parts:
        return None, "contains '..'"
    root_resolved = Path(root).resolve()
    try:
        resolved = (root_resolved / rel).resolve()
    except OSError:
        return None, "could not be resolved"
    try:
        resolved.relative_to(root_resolved)
    except ValueError:
        return None, "resolves outside the campaign root"
    return rel, None


def _load_ported_toml_safe(root: Path) -> Tuple[Optional[List[str]], Optional[str]]:
    """The guarded reader of `<root>/PORTED.toml`'s `files = [...]` list -- the same
    refusals as `_load_freeze_safe`/`_load_deviations_safe`: a symlink refused via
    `lstat` before anything is read through it (`O_NOFOLLOW` as a second line of
    defense), anything else that is not a regular file, a file over
    `PORTED_TOML_MAX_BYTES`, content that is not UTF-8, not valid TOML, or whose `files`
    field (if present at all) is not a list of strings. Returns `(entries, None)` (`[]`
    if the file has no `files` key); `(None, None)` if PORTED.toml does not exist; or
    `(None, problem)` for anything this refuses. Never raises."""
    path = ported_toml_path(root)
    try:
        st = path.lstat()
    except FileNotFoundError:
        return None, None
    except OSError as exc:
        return None, f"{PORTED_TOML_FILENAME} could not be read ({exc.strerror or exc})."
    if stat.S_ISLNK(st.st_mode):
        return None, (f"{PORTED_TOML_FILENAME} is a symlink in the working tree; "
                      "refusing to trust it.")
    if not stat.S_ISREG(st.st_mode):
        return None, (f"{PORTED_TOML_FILENAME} in the working tree is not a regular "
                      "file (a directory, e.g. a submodule checkout, or a special "
                      "file); refusing to trust it.")
    if st.st_size > PORTED_TOML_MAX_BYTES:
        return None, (f"{PORTED_TOML_FILENAME} is larger than {PORTED_TOML_MAX_BYTES} "
                      "bytes; refusing to trust it.")
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
                     | getattr(os, "O_NONBLOCK", 0))
        with os.fdopen(fd, "rb") as fh:
            if not stat.S_ISREG(os.fstat(fh.fileno()).st_mode):
                return None, (f"{PORTED_TOML_FILENAME} changed while being read; "
                              "refusing to trust it.")
            data = fh.read(PORTED_TOML_MAX_BYTES + 1)
    except OSError as exc:
        return None, f"{PORTED_TOML_FILENAME} could not be read ({exc.strerror or exc})."
    if len(data) > PORTED_TOML_MAX_BYTES:
        return None, (f"{PORTED_TOML_FILENAME} is larger than {PORTED_TOML_MAX_BYTES} "
                      "bytes; refusing to trust it.")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return None, f"{PORTED_TOML_FILENAME} is not valid UTF-8; refusing to trust it."
    from .schema import loads_toml

    try:
        doc = loads_toml(text)
    except Exception as exc:  # malformed TOML, or whatever else a hostile file provokes
        return None, f"{PORTED_TOML_FILENAME} is not valid TOML ({exc})."
    files = doc.get("files", [])
    if not isinstance(files, list) or not all(isinstance(f, str) for f in files):
        return None, f"{PORTED_TOML_FILENAME} has a `files` that is not a list of strings."
    return files, None


def ported_files(root: Path) -> List[Path]:
    """Every file counted as "ported" (spec 7.4) under *root*, as paths RELATIVE to it,
    sorted and de-duplicated: every `.lean` file under *root* (`_walk_lean_files`) whose
    first 30 lines carry a `ported`/`adapted`/`copied from` mention inside a Lean
    comment (never inside a string literal or in code -- `_lean_head_comment_text` masks
    both out before `_PORTED_MENTION_RE` ever runs), plus every safe, existing entry
    named in `<root>/PORTED.toml`'s `files = [...]`.

    A `.lean` file this cannot safely read (a symlink, a decode failure, ...) is simply
    not auto-detected by its own mention -- there is nothing to scan -- but is still
    included here if PORTED.toml names it explicitly; `provenance_problems` is what
    then reports the read failure as a problem, rather than this function silently
    deciding the file is not ported after all. A PORTED.toml entry that is unsafe (does
    not resolve inside *root*) or names a file that does not exist is never added here
    either; `provenance_problems` reports both directly so a bad entry is still visible
    even though nothing on disk can be checked for a header.
    """
    root = Path(root)
    found: Set[Path] = set()

    for lean_path in _walk_lean_files(root):
        text, problem = _read_lean_head_safe(lean_path)
        if problem:
            continue
        if _PORTED_MENTION_RE.search(_lean_head_comment_text(text)):
            found.add(lean_path.relative_to(root))

    entries, _problem = _load_ported_toml_safe(root)
    for raw in entries or ():
        rel, _reason = _safe_ported_relpath(root, raw)
        if rel is not None and (root / rel).exists():
            found.add(rel)

    return sorted(found)


def provenance_problems(root: Path) -> List[str]:
    """Spec 7.4: every ported file names its source repository, file and commit.
    Reports, in this order:

    - every `.lean` file the walk (`_walk_lean_files`) finds that is ITSELF a symlink
      -- UNCONDITIONALLY, whether or not it turns out to be "ported" at all (fix round
      1, Controller Ruling 14, Critical). `_read_lean_head_safe` refuses to follow one,
      so `ported_files`'s auto-detection scan cannot tell whether a symlinked file
      mentions "ported from" -- before this, such a file that was not ALSO declared in
      PORTED.toml was simply never added to `found`, and so never visited by anything
      below either: a ported file hidden behind a symlink (to another file inside the
      campaign, or -- the reviewer's exploit -- to one entirely outside it) evaded the
      lint completely, with zero diagnostic anywhere. A symlink that stays inside
      *root* and IS declared in PORTED.toml still also gets its own "is a symlink;
      refusing to read it" message from the per-file loop further down; that overlap is
      harmless (the file genuinely cannot be read either way) and is left alone rather
      than suppressed, so the two passes never need to coordinate about which one
      "owns" reporting a given file;
    - every directory the walk meets that is ITSELF a symlink, excluding one named in
      `_SKIP_DIR_NAMES` (and anything nested under one) -- also UNCONDITIONAL (fix
      round 2, Controller Ruling 15): the walk already never follows one
      (`_walk_lean_files`'s `followlinks=False`), but it used to do so SILENTLY, which
      reopened the exact bypass fix round 1 closed for files one level up -- a `.lean`
      file reachable only through a symlinked directory is never walked into at all,
      so it can never even reach the symlinked-FILE check above;
    - `<root>/PORTED.toml` itself unreadable, untrustworthy or malformed
      (`_load_ported_toml_safe`);
    - each PORTED.toml entry that is not a safe path inside *root* (absolute, `..`, or
      resolving outside it, including through a symlinked directory COMPONENT of the
      path -- `_safe_ported_relpath`);
    - each otherwise-safe PORTED.toml entry whose file does not exist on disk;
    - for every file `ported_files(root)` returns that DOES exist: unreadable (a
      symlink, not valid UTF-8, ...) via `_read_lean_head_safe`; more than one line
      matching the provenance header's shape in its first 30 lines (fix round 1,
      Minor: a second, different header -- even one that is itself malformed -- must
      not be silently ignored just because `finditer` would otherwise report only
      drift on the first); no such line at all; or (when there is exactly one) a header
      whose commit is not exactly 40 lowercase hex digits.

    Sorted; islands included, same as everything else `_walk_lean_files` reaches, since
    nothing here is scoped to a particular subdirectory of the campaign."""
    root = Path(root)
    problems: List[str] = []

    for lean_path in _walk_lean_files(root):
        if lean_path.is_symlink():
            problems.append(
                f"{lean_path.relative_to(root).as_posix()}: symlinked .lean file; "
                "replace it with a regular file."
            )

    for dir_path in _walk_symlinked_dirs(root):
        problems.append(
            f"{dir_path.relative_to(root).as_posix()}/: symlinked directory; the lint "
            "does not follow it, replace it with a real directory."
        )

    entries, toml_problem = _load_ported_toml_safe(root)
    if toml_problem:
        problems.append(toml_problem)
    for raw in entries or ():
        rel, reason = _safe_ported_relpath(root, raw)
        if rel is None:
            problems.append(f"{PORTED_TOML_FILENAME}: entry {raw!r} {reason}.")
            continue
        if not (root / rel).exists():
            problems.append(
                f"{PORTED_TOML_FILENAME}: entry {rel.as_posix()!r} does not exist."
            )

    for rel in ported_files(root):
        path = root / rel
        if not path.exists():
            continue  # already reported above, from the PORTED.toml pass
        text, problem = _read_lean_head_safe(path)
        if problem:
            problems.append(f"{rel.as_posix()}: {problem}.")
            continue
        masked = _lean_head_comment_text(text)
        matches = list(_PROVENANCE_LINE_RE.finditer(masked))
        if not matches:
            problems.append(
                f"{rel.as_posix()}: ported file has no provenance header "
                "(`-- Provenance: repo=<repo> file=<file> commit=<40 lowercase hex>`) "
                f"in its first {_PORTED_HEAD_LINES} lines."
            )
            continue
        if len(matches) > 1:
            problems.append(
                f"{rel.as_posix()}: multiple provenance headers in its first "
                f"{_PORTED_HEAD_LINES} lines; exactly one is required."
            )
            continue
        commit = matches[0].group(3)
        if not _PROVENANCE_COMMIT_RE.match(commit):
            problems.append(
                f"{rel.as_posix()}: Provenance header's commit {commit!r} is not "
                "exactly 40 lowercase hex characters."
            )
    return sorted(problems)


def campaign_is_post_cutoff(root: Path) -> bool:
    """Whether *root*'s FREEZE.toml records a `frozen` date on or after `CUTOFF` -- the
    same predicate `freeze_history_problems` computes internally, exposed here so a
    caller (`verify.verify_campaign`, step 5 Task 4) can gate `provenance_problems` by
    it without ever reading FREEZE.toml directly: the date is read through
    `_load_freeze_safe`, the ONE guarded reader of it (Controller Ruling 8). False
    whenever no FREEZE.toml exists, or it exists but cannot be trusted at all --
    `freeze_problems`/`freeze_history_problems` already surface an untrustworthy record
    as its own error; this is not where that problem gets reported a second time."""
    doc, problem = _load_freeze_safe(root)
    if problem or doc is None:
        return False
    return str(doc.get("frozen", "")) >= CUTOFF

