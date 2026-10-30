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

`CUTOFF` is the single source of truth for the post-process cutoff date (Controller Ruling
1, 2026-10-30): `provenance.CHECKS_CUTOFF` is an alias of it, kept for back-compat. This
module must NOT import `provenance` or `verify` at module level -- both of those already
import (or will import) this one, and a module-level import back here would cycle. Every
use of `provenance` below is therefore a lazy, in-function import.
"""
from __future__ import annotations

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
        "",
        "[statements]",
    ]
    statements = doc.get("statements") or {}
    for slug in sorted(statements):
        lines.append(f"{_quote(slug)} = {_quote(statements[slug])}")
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
    for key in ("identity", "session"):
        if key in doc and not isinstance(doc[key], str):
            return f"has a non-string `{key}`"
    statements = doc.get("statements", {})
    if not isinstance(statements, dict) or not all(
            isinstance(v, str) for v in statements.values()):
        return "has a `statements` that is not a table of string hashes"
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


def _current_statement_hashes(root: Path, campaign) -> Dict[str, str]:
    return {
        slug: _hash_statement(root, node)
        for slug, node in campaign.nodes.items()
        if statement_path(root, node).exists()
    }


# ---------------------------------------------------------------------------
# freeze / unfreeze
# ---------------------------------------------------------------------------

def freeze(root: Path, *, identity: str, session: str, date: str) -> dict:
    """Write `<root>/FREEZE.toml`: version 1, the freezing identity/session, and the sha256
    of every node's current statement body. Refuses (`ValueError`) if the campaign is
    already frozen -- re-running `freeze` would silently discard the unfreeze history;
    `unfreeze` is the only supported way to bring a frozen campaign's hashes current."""
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
    doc = {
        "version": 1,
        "frozen": date,
        "identity": identity.strip(),
        "session": session.strip(),
        "statements": _current_statement_hashes(root, campaign),
    }
    _write_freeze(root, doc)
    return doc


def unfreeze(root: Path, *, author: str, reason: str, readback_identity: str, date: str) -> dict:
    """Bump the freeze: re-hash every current statement, append a `[[unfreeze]]` entry, and
    write the new version. Refuses (`ValueError`) a self-read-back -- `readback_identity`
    equal to `author`, compared the way `provenance.independence_of` compares identities
    (case-folded) -- and refuses when the campaign was never frozen at all."""
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
    new_doc = {
        "version": new_version,
        "frozen": doc.get("frozen", ""),
        "identity": doc.get("identity", ""),
        "session": doc.get("session", ""),
        "statements": _current_statement_hashes(root, campaign),
        "unfreeze": entries,
    }
    _write_freeze(root, new_doc)
    return new_doc


# ---------------------------------------------------------------------------
# freeze_problems / freeze_grant_problem
# ---------------------------------------------------------------------------

def freeze_problems(root: Path) -> List[str]:
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

    problems.extend(freeze_history_problems(root))
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
    removed; or, on a version change, anything other than exactly +1 with a matching new
    `[[unfreeze]]` entry."""
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


def freeze_history_problems(root: Path) -> List[str]:
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

    post_cutoff = str(doc.get("frozen", "")) >= CUTOFF

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
    problems = freeze_problems(root)
    if problems:
        shown = problems[:_GRANT_PROBLEM_PREVIEW]
        more = (f" (+{len(problems) - _GRANT_PROBLEM_PREVIEW} more)"
               if len(problems) > _GRANT_PROBLEM_PREVIEW else "")
        return (
            f"the campaign's freeze has unresolved problem(s){more}: " + "; ".join(shown)
        )
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
    outright rather than rendered."""
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
    "depends on axiomss:"), which raises rather than being silently skipped.
    `str.splitlines()` already treats `\\r\\n` as a single line ending.

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
                or "does not depend on any axioms" in stripped):
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
