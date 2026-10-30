"""Step 5: making a mission campaign statement-first.

This module is the home for step 5's shared pieces -- the campaign-level statement freeze
(this task), and later tasks' Audit.lean generation, DEVIATIONS.md and a provenance lint.

Freeze. `FREEZE.toml` at the campaign root records the sha256 of every node's statement
BODY (`statements.statement_body`) at the moment the campaign was frozen: who froze it,
when, and the hash each statement had. `freeze_problems` re-derives those hashes from the
statement files on disk and reports drift, nodes added since the freeze, and an incomplete
or self-read-back unfreeze history. Unfreezing -- the only way to make a frozen campaign's
hashes current again -- is destructive to the freeze's truth-claim, so every version bump
demands a recorded reason AND an independent read-back of the new hashes
(`docs/AUDIT_INDEPENDENCE_2026-09-23.md`'s independence rule, applied here to the freeze
record rather than to a node's statement).

`CUTOFF` is the single source of truth for the post-process cutoff date (Controller Ruling
1, 2026-10-30): `provenance.CHECKS_CUTOFF` is an alias of it, kept for back-compat. This
module must NOT import `provenance` or `verify` at module level -- both of those already
import (or will import) this one, and a module-level import back here would cycle. Every
use of `provenance` below is therefore a lazy, in-function import.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Dict, List, Optional

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
    - any `version > 1` missing a matching `[[unfreeze]]` entry for 2..version (a
      hand-rewritten FREEZE.toml, since `unfreeze` itself always appends one);
    - any `[[unfreeze]]` entry that is a self-read-back (same check `unfreeze` itself
      refuses at write time, re-applied here against whatever is actually on disk).

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
        if not statement_path(root, node).exists():
            continue
        recorded = statements.get(slug)
        if recorded is None:
            problems.append(
                f"node {slug!r} was added since the freeze and is not recorded in "
                f"{FREEZE_FILENAME}."
            )
            continue
        current = _hash_statement(root, node)
        if current != recorded:
            problems.append(
                f"node {slug!r}: statement drift -- current hash {current[:16]}... does not "
                f"match the frozen hash {str(recorded)[:16]}... in {FREEZE_FILENAME}."
            )

    version = int(doc.get("version", 1))
    by_version = {}
    for entry in (doc.get("unfreeze") or []):
        try:
            by_version[int(entry.get("version", -1))] = entry
        except (TypeError, ValueError):
            continue
    for v in range(2, version + 1):
        entry = by_version.get(v)
        if entry is None:
            problems.append(
                f"{FREEZE_FILENAME} version is {version} but has no [[unfreeze]] entry for "
                f"version {v}."
            )
            continue
        author = str(entry.get("author", ""))
        readback_identity = str(entry.get("readback_identity", ""))
        if author.strip().lower() == readback_identity.strip().lower():
            problems.append(
                f"{FREEZE_FILENAME} [[unfreeze]] entry for version {v} is a self-read-back "
                f"(readback_identity {readback_identity!r} matches author {author!r})."
            )
    return problems


def freeze_grant_problem(root: Path, node) -> str:
    """"" unless *node* is post-cutoff (`provenance.checks_required`) and either no
    FREEZE.toml exists for its campaign or its statement is not recorded in one; else why
    the grant gate must refuse it."""
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
    return ""
