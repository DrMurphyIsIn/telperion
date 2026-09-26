"""Verbatim-mirror drift between a campaign's registry definitions and the island copies.

A registry node's statement is written against the campaign's `Statements/*Defs.lean`
vocabulary.  The Lean that actually proves it lives in an island, and the island does not
import the registry: it **re-declares** the same definitions, annotated in-file as a mirror.
The grant gate then matches the node's statement against the artifact by normalized text
containment.

That match is only meaningful while the two copies agree.  If an island's copy of a
definition drifts from the registry's, the gate still passes and the node still reads
`proved`, but the theorem proved is about different constants than the statement names.
Nothing in the pipeline notices.  One island, `rvm_bridge`, is safe because its mirror is
GENERATED and `generate.py --check` compares it byte-for-byte.  Every other mirror is a
hand copy kept in step by a comment.

This module supplies the missing check for the hand copies.

SCOPE, stated honestly.  The comparison is textual after stripping comments and collapsing
whitespace.  That is exact for `mirrormere`, whose 31 mirrored declarations agree character
for character, and it is the right gate there.  It is NOT yet exact for `rh`, `anduril` and
`bg`, whose copies differ from the registry in two cosmetic ways that carry no mathematical
content:

  * namespace qualification -- the registry package must write `DIntvProd.DIntv.sign?`
    where the island, sitting inside `namespace DIntvProd`, writes `DIntv.sign?`;
  * binder naming -- `Bcap (mu : Q)` against `Bcap (μ : Q)`.

Both were checked by hand and neither changes a definition.  Normalizing them reliably needs
Lean-level comparison rather than text, so those campaigns are reported and not gated.  A
strict gate there today would be a noise machine, and a noisy gate gets switched off.

The durable fix is to generate the mirrors the way `rvm_bridge` does, which makes drift
impossible by construction rather than detectable after the fact.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

#: Keywords that end a declaration.  `omit` / `include` / `local` matter: they appear as
#: standalone modifier lines BETWEEN declarations, and swallowing one makes an otherwise
#: identical pair compare unequal.  That false positive is why they are listed.
_TERMINATORS = (
    "def|abbrev|theorem|lemma|instance|structure|inductive|class|example|end|namespace|"
    "section|open|variable|import|universe|attribute|macro|notation|syntax|elab|"
    "set_option|deriving|omit|include|local|opaque|axiom"
)
_MODIFIERS = r"(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*"
_DECL_START = re.compile(r"(?m)^" + _MODIFIERS + r"(?:" + _TERMINATORS + r")\b")
_DEF_HEAD = re.compile(_MODIFIERS + r"(def|abbrev)\s+([^\s({\[:]+)")


def _strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)   # block comments and docstrings
    return re.sub(r"(?m)--.*$", "", src)


def declarations(path: Path) -> dict[str, str]:
    """Every top-level `def`/`abbrev` in `path`, as name -> whitespace-normalized text."""
    src = _strip_comments(Path(path).read_text())
    starts = [m.start() for m in _DECL_START.finditer(src)] + [len(src)]
    out: dict[str, str] = {}
    for i in range(len(starts) - 1):
        chunk = src[starts[i]:starts[i + 1]]
        head = _DEF_HEAD.match(chunk)
        if head:
            out[head.group(2)] = re.sub(r"\s+", " ", chunk).strip()
    return out


#: Same bare name, different object: island declarations that are NOT copies of the
#: registry definition and must not be compared against it.  Keyed by (bare name, island
#: file path suffix); the value is the reason, kept here so the exemption is auditable.
#: `test_missions_mirror_drift` pins that every exemption is still needed (the two texts still
#: differ), so a stale entry fails loudly instead of masking a real drift.
NOT_MIRRORS: dict[tuple[str, str], str] = {
    ("archSide", "rvm_bridge/lean/E6Bridge15.lean"):
        "BombieriLagarias.archSide (the rh campaign's Li-face archimedean closed form, mirrored "
        "verbatim from missions/rh RHDefs into E6Bridge15 for the B7 node) is not a copy of "
        "WeilExplicit.archSide (MMDefs): same bare name, different namespace and object (2026-09-21).",
    ("autocorr", "weil_form_enclosure/lean/WeilFormDefs.lean"):
        "WeilForm.autocorr is `abbrev autocorr g := crossCorr g g` (the emitter island's own "
        "vocabulary, namespace WeilForm), not a copy of WeilExplicit.autocorr (MMDefs, "
        "2026-09-20): the same integral written through crossCorr, in another namespace.",
    ("autocorr", "rvm_bridge/lean/ZhuSymbol.lean"):
        "ZhuSymbol re-declares the WeilForm block (weilForm, crossCorr, abbrev autocorr) verbatim "
        "from missions/rh RHDefs / WeilFormDefs for the Zhu window node (2026-09-23); against "
        "MMDefs's WeilExplicit.autocorr it is the same bare name in another namespace, exactly "
        "as the WeilFormDefs entry above.",
}


def _exempt(name: str, island_file: Path) -> bool:
    posix = island_file.as_posix()
    return any(name == n and posix.endswith(suffix) for (n, suffix) in NOT_MIRRORS)


@dataclass(frozen=True)
class Mirror:
    name: str
    island_file: str
    in_sync: bool


def check_mirrors(defs_file: Path, examples_root: Path) -> list[Mirror]:
    """Compare every island re-declaration against the campaign's registry definitions."""
    base = declarations(defs_file)
    rows: list[Mirror] = []
    for lean in sorted(Path(examples_root).glob("*/lean/**/*.lean")):
        if ".lake" in lean.parts:
            continue   # dependency sources (Mathlib, Zeta23) are not island copies of anything
        island = declarations(lean)
        for name in sorted(set(island) & set(base)):
            if _exempt(name, lean):
                continue
            rows.append(Mirror(name, str(lean), island[name] == base[name]))
    return rows


def drifted(rows: list[Mirror]) -> list[Mirror]:
    return [r for r in rows if not r.in_sync]
