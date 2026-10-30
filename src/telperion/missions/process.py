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

`CUTOFF` is the single source of truth for the post-process cutoff date (Controller Ruling
1, 2026-10-30): `provenance.CHECKS_CUTOFF` is an alias of it, kept for back-compat. This
module must NOT import `provenance` or `verify` at module level -- both of those already
import (or will import) this one, and a module-level import back here would cycle. Every
use of `provenance` below is therefore a lazy, in-function import.
"""
from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple

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


def _load_freeze(root: Path) -> Optional[dict]:
    """The parsed FREEZE.toml document, or None if the campaign has not been frozen."""
    path = freeze_path(root)
    if not path.exists():
        return None
    try:
        import tomllib
    except ModuleNotFoundError:
        import tomli as tomllib  # type: ignore[no-redef]
    return tomllib.loads(path.read_text())


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
    if freeze_path(root).exists():
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
    doc = _load_freeze(root)
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

def _is_git_repo(root: Path) -> bool:
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--is-inside-work-tree"],
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return out.returncode == 0 and out.stdout.strip() == "true"


def _git_toplevel(root: Path) -> Optional[Path]:
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    return Path(out.stdout.strip())


def _is_shallow_repo(root: Path) -> bool:
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--is-shallow-repository"],
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return out.returncode == 0 and out.stdout.strip() == "true"


def _first_parent_chain(root: Path) -> List[str]:
    """Every commit on HEAD's first-parent chain, oldest first (`git log --first-parent
    --reverse`). First-parent, not every ancestor of every merge, so a merge commit does
    not pull a side branch's unrelated history into the walk below."""
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "log", "--first-parent", "--reverse", "--format=%H"],
            capture_output=True, text=True, timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if out.returncode != 0:
        return []
    return [s for s in out.stdout.split() if s]


def _first_commit_with_path(root: Path, relpath: str) -> Optional[str]:
    """The oldest first-parent commit at which *relpath* exists at all -- found via a
    path-filtered log (cheap: this is only to locate where the exhaustive walk below
    should START, never to decide which commits that walk visits; every commit from here
    to HEAD is visited whether or not it touches *relpath*, specifically so a window where
    the file sat at a different path is not silently skipped -- fix round 3, NEW-3)."""
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "log", "--first-parent", "--reverse",
             "--format=%H", "--", relpath],
            capture_output=True, text=True, timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    shas = [s for s in out.stdout.split() if s]
    return shas[0] if shas else None


def _ls_tree_entry(root: Path, sha: str, relpath: str) -> Optional[Tuple[str, str]]:
    """`(mode, blob)` for *relpath* as recorded AT *sha* -- not at today's path, at this
    commit's own tree -- or `None` if it is absent there or the lookup itself fails.
    `ls-tree` is a cheap, content-free lookup (no blob is fetched), so this can run for
    every commit in a long walk without `git show`'s cost."""
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "ls-tree", sha, "--", relpath],
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    line = out.stdout.strip()
    if not line:
        return None
    meta, sep, _path = line.partition("\t")
    if not sep:
        return None
    fields = meta.split()
    if len(fields) != 3:
        return None
    mode, _obj_type, blob = fields
    return mode, blob


def _load_blob_toml(root: Path, blob: str) -> Optional[dict]:
    try:
        show = subprocess.run(
            ["git", "-C", str(root), "show", blob],
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if show.returncode != 0:
        return None
    try:
        import tomllib
    except ModuleNotFoundError:
        import tomli as tomllib  # type: ignore[no-redef]
    try:
        return tomllib.loads(show.stdout)
    except Exception:
        return None


def _walk_freeze_blobs(root: Path, chain: List[str], relpath: str
                       ) -> Tuple[List[Tuple[str, str]], Optional[str]]:
    """Confirm *relpath* exists as an ordinary (non-symlink) blob at EVERY commit in
    *chain*, oldest first -- not only the ones a path-filtered log would show, so a window
    where the file was absent (renamed away, deleted) cannot hide between two commits where
    it happens to exist again (fix round 3, NEW-3). Stops, and returns a problem string, at
    the first commit that fails this -- the caller must never look past it (the point of
    the check is exactly that nothing downstream of a break in the chain can be trusted).

    Returns `([(sha, blob), ...], None)` on success: one entry per run of consecutive
    IDENTICAL blobs (keyed by the sha where that blob first appears in the walk), since
    re-reading and re-parsing an unchanged blob at every commit that merely didn't touch it
    buys nothing (fix round 3's own "stay fast" note) -- the existence/mode check above
    still ran for every commit regardless, which is the part that must not be skipped.
    """
    entries: List[Tuple[str, str]] = []
    last_blob: Optional[str] = None
    for sha in chain:
        got = _ls_tree_entry(root, sha, relpath)
        if got is None:
            return entries, f"{FREEZE_FILENAME} deleted or moved in history at {sha[:12]}."
        mode, blob = got
        if mode == "120000":
            return entries, (
                f"{FREEZE_FILENAME} was recorded as a symlink (mode {mode}) in history at "
                f"{sha[:12]}; refusing to trust it."
            )
        if blob != last_blob:
            entries.append((sha, blob))
            last_blob = blob
    return entries, None


def _freeze_commit_history(root: Path, relpath: str) -> Tuple[List[Tuple[str, dict]], Optional[str]]:
    """`([(commit sha, parsed FREEZE.toml doc), ...], None)`, oldest first, for the DISTINCT
    states *relpath* held across every commit from its first appearance to HEAD on the
    first-parent chain; or `([], None)` if it has never been committed; or `([], problem)`
    if the walk hit an absence, a symlink, or an unreadable blob partway through (fix round
    3) -- the caller must surface `problem` itself rather than silently falling back to
    "never committed", which would under-report what actually happened."""
    chain = _first_parent_chain(root)
    if not chain:
        return [], None

    first = _first_commit_with_path(root, relpath)
    if first is None or first not in chain:
        return [], None

    walk = chain[chain.index(first):]
    distinct, problem = _walk_freeze_blobs(root, walk, relpath)
    if problem:
        return [], problem

    history: List[Tuple[str, dict]] = []
    for sha, blob in distinct:
        doc = _load_blob_toml(root, blob)
        if doc is None:
            return [], f"{FREEZE_FILENAME} could not be read at commit {sha[:12]}."
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
    """Walk FREEZE.toml's git history (every commit on the first-parent chain from the
    file's first appearance to HEAD, not only the ones that touch its path, plus the
    working tree as the final state) and check the invariants `_freeze_transition_problems`
    describes between every consecutive DISTINCT state.

    One check is UNCONDITIONAL, never gated by cutoff: FREEZE.toml being a symlink in the
    working tree. Reading it (`_load_freeze`) follows the symlink, so even the `frozen`
    date every other check below relies on to decide whether it applies cannot be trusted
    once the path itself is a symlink -- there is nothing left to gate on. A symlink
    recorded in HISTORY (git mode 120000) rather than in the working tree is a different
    code path (the history walk itself, which does have a trustworthy `frozen` field to
    gate on) and remains cutoff-gated like everything below.

    Everything else fails closed only where it genuinely cannot check anything, and only
    when a post-cutoff campaign (FREEZE.toml's own `frozen` date >= `CUTOFF`) needs the
    guarantee; a pre-cutoff campaign, for which freezing at all is optional, is not
    penalised for any of these:

    - a symlink recorded at any point in history (git mode 120000) -- a symlink's target
      can change independently of the history being walked, so content comparisons through
      it prove nothing (fix round 3);
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

    # Checked BEFORE loading anything, and reported UNCONDITIONALLY (not gated by
    # post-cutoff like every other check below): `_load_freeze` reads straight through a
    # symlink, so a symlinked FREEZE.toml poisons even the `frozen` field this function
    # would otherwise use to decide whether it cares -- there is no field left that can be
    # trusted enough to decide anything else, including whether to decide anything at all.
    if freeze_path(root).is_symlink():
        return [f"{FREEZE_FILENAME} is a symlink in the working tree; refusing to trust it."]

    doc = _load_freeze(root)
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

    history, hist_problem = _freeze_commit_history(root, relpath)
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
    doc = _load_freeze(root)
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
