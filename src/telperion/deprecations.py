"""Extract authoritative lemma-rename data from Mathlib SOURCE (offline tool).

``repair.py`` needs a table of ``old_name -> new_name`` renames to mechanically
fix proofs that break on Mathlib version drift.  Rather than hand-maintaining that
table, this module derives it from the ONE unambiguous place Mathlib records a
rename: the deprecated *alias* attribute.

Mathlib marks a renamed declaration with an ``alias`` whose body is the new name::

    @[deprecated (since := \"2026-05-27\")] alias try_rfl := tryRfl
    @[deprecated (since := \"2026-01-06\")] protected alias isAntisymm := antisymm
    @[deprecated (since := \"2026-02-24\")]
    alias inducedMap := ConditionallyCompleteLinearOrderedField.inducedMap

The attribute also appears in two OTHER shapes that this extractor deliberately
IGNORES, because they do not give an unambiguous old->new pair on the same line:

    @[deprecated NewName (since := \"...\")]   -- new name, but attached to a `theorem`,
                                             -- so the OLD name is on a later line
    @[deprecated \"use Foo instead\" (since := \"...\")]  -- free-text message, no name

Only the ``alias OLD := NEW`` form pins both names together, so that is the only
form harvested here.  (A ``@[deprecated NewName]`` sitting *in front of* an alias
is fine — the ``alias`` body still wins; see the regex, which keys off ``alias``.)

This is a one-off / offline tool: run it centrally against a checked-out mathlib
to emit ``src/telperion/deprecations.json``, which ``repair.py`` then loads.  It is
NOT imported on the hot path.

conjecture1_proved = False.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

# A deprecated ALIAS, in any of the shapes seen in real Mathlib v4.3x source:
#   * attribute inline with the alias, or split onto the preceding line (\s* spans
#     the newline);
#   * the attribute list may carry a free-text message, a replacement-name token,
#     `since := "..."`, and/or sibling attributes (`@[simp, deprecated ...]`,
#     `@[deprecated ..., norm_cast]`) — `[^\]]*\bdeprecated\b[^\]]*` tolerates all;
#   * `alias` may be preceded by up to two declaration modifiers
#     (`protected`, `private`, `meta`, `noncomputable`, `scoped`, `unsafe`,
#     `partial`).
# `old` is the token up to the first whitespace/`:`/`=`; `new` is the token after
# `:=` up to the next whitespace — this drops any trailing type ascription and
# stops before end-of-line comments.
_MODIFIER = r"(?:protected|private|meta|noncomputable|scoped|unsafe|partial)"
_ALIAS_RE = re.compile(
    r"@\[[^\]]*\bdeprecated\b[^\]]*\]"
    r"\s*"
    + _MODIFIER + r"?\s*"
    + _MODIFIER + r"?\s*"
    r"alias\s+"
    r"(?P<old>[^\s:=]+)\s+"
    r":=\s*"
    r"(?P<new>[^\s\n]+)"
)


@dataclass
class RenameTable:
    """Result of scanning a Mathlib source tree for deprecated aliases.

    ``renames`` is the ``old -> new`` map (last write wins when the same old name
    is aliased in more than one file).  ``files_scanned`` / ``alias_hits`` give
    provenance for the extraction; ``collisions`` records old names that were seen
    with more than one distinct new name (informational — the map keeps the last).
    """

    renames: Dict[str, str] = field(default_factory=dict)
    files_scanned: int = 0
    alias_hits: int = 0
    collisions: Dict[str, List[str]] = field(default_factory=dict)

    def to_json(self) -> str:
        """Serialize just the rename map (sorted) as pretty JSON for committing."""
        payload = {
            "_comment": (
                "Auto-extracted mathlib deprecated-alias renames (old -> new). "
                "Regenerate via telperion.deprecations; do not hand-edit."
            ),
            "renames": {k: self.renames[k] for k in sorted(self.renames)},
        }
        return json.dumps(payload, indent=2, ensure_ascii=False) + "\n"


def extract_from_text(text: str) -> Dict[str, str]:
    """Return the ``old -> new`` renames found in a single Lean source string."""
    out: Dict[str, str] = {}
    for m in _ALIAS_RE.finditer(text):
        out[m.group("old")] = m.group("new")
    return out


def extract_renames(mathlib_root) -> RenameTable:
    """Walk ``mathlib_root`` for ``*.lean`` files and collect deprecated aliases.

    ``mathlib_root`` should be the directory that contains the top-level
    ``Mathlib/`` package (e.g. ``.../.lake/packages/mathlib``); the walk recurses,
    so pointing at either that dir or its ``Mathlib`` subdir both work.
    """
    root = Path(mathlib_root)
    table = RenameTable()
    for path in sorted(root.rglob("*.lean")):
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        table.files_scanned += 1
        for old, new in extract_from_text(text).items():
            table.alias_hits += 1
            prev = table.renames.get(old)
            if prev is not None and prev != new:
                seen = table.collisions.setdefault(old, [prev])
                if new not in seen:
                    seen.append(new)
            table.renames[old] = new
    return table


def write_json(mathlib_root, out_path) -> RenameTable:
    """Extract renames from ``mathlib_root`` and write the JSON to ``out_path``."""
    table = extract_renames(mathlib_root)
    Path(out_path).write_text(table.to_json(), encoding="utf-8")
    return table


def _main(argv: Optional[List[str]] = None) -> int:
    import argparse

    ap = argparse.ArgumentParser(
        description="Extract mathlib deprecated-alias renames into deprecations.json",
    )
    ap.add_argument(
        "mathlib_root",
        help="path to a mathlib source root (dir containing Mathlib/)",
    )
    ap.add_argument(
        "-o", "--out",
        default=str(Path(__file__).with_name("deprecations.json")),
        help="output JSON path (default: src/telperion/deprecations.json)",
    )
    a = ap.parse_args(argv)
    table = write_json(a.mathlib_root, a.out)
    print(
        "scanned {files} files, {hits} alias hits -> {n} renames "
        "({c} collisions) written to {out}".format(
            files=table.files_scanned,
            hits=table.alias_hits,
            n=len(table.renames),
            c=len(table.collisions),
            out=a.out,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
