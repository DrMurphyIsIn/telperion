"""Port-match gate — the CROSS-TOOLCHAIN half of the trust boundary.

`verify_lean` certifies a proof COMPILES and is axiom-clean; `negative_control`
certifies a FALSE instance is kernel-rejected; `statement_match` certifies a
declaration states its INTENDED proposition, by elaborating
`theorem __sigmatch_foo : T := @foo` — a defeq check, which needs `foo` and `T` to
live in ONE Lean environment.

None of those applies to the shape this module gates.  Telperion's islands are pinned
to DIFFERENT toolchains (v4.32.0, v4.33.0-rc2, v4.34.0-rc1), by necessity: an island
that consumes an external development inherits that development's Mathlib pin.  When a
result proved on island A is needed on island B, the two cannot meet in one
environment, and the composition is done by RE-PROVING the island-A lemma verbatim on
island B.  That re-proof is only as trustworthy as the claim that it says *the same
thing*: nothing in the Lean toolchain can check it, because the source declaration is
not importable there.

`port_match_check` is that check, at the level the two files share — TEXT.  For each
ported declaration it extracts the statement from the source island's file and from the
target island's file, normalizes away comments and whitespace, and compares:

  * `theorem` / `lemma`: the head `theorem NAME <binders> : <type>` up to the first
    top-level `:=` (the PROOF may legitimately differ — different tactic spellings for
    different Mathlib versions — but the statement may not);
  * `def` / `abbrev`: the whole block INCLUDING the body (for a definition the body *is*
    the content; a drifted body silently redefines the vocabulary).

Typical use in an island's `generate.py --check`, so CI fails on drift:

    from telperion.port_match import port_match_check
    res = port_match_check(source_text, target_text,
                           ["IsUniformlyDiscrete", "exists_close_of_card_gt"],
                           source_label="quasicrystal v4.32 BoundaryLemmas.lean",
                           target_label="rvm_bridge v4.33 W2cAssembly.lean")
    if not res.all_match:
        for line in res.failure_lines():
            print("  - " + line)

`source_text` may be the live file when both islands are in the checkout, or a PINNED
copy of the source statements (with the source branch + blob recorded) when they are
not — cross-branch islands are the normal case.  `port_match_pinned` checks both at
once: target against pin, and pin against the live source when it is available, so the
pin cannot rot either.

SCOPE / HONESTY.  This is a TEXT gate, not a semantic one.  It certifies that the
ported statement is character-for-character (modulo comments and whitespace) the source
statement; it does NOT certify that the two toolchains give that text the same meaning
(a Mathlib notation change across versions would be invisible here).  It is exactly the
guarantee that the re-proof cannot silently drift from the artifact it re-proves, and
any report using it must say that the dependency was discharged by a verbatim re-proof
rather than by consuming the source artifact.

conjecture1_proved = False.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

_STATEMENT_KINDS = ("theorem", "lemma", "example")
_DEF_KINDS = ("def", "abbrev", "noncomputable def")
# a top-level declaration keyword, used to find the end of a `def` block
_DECL_START = (r"def|theorem|lemma|end|namespace|noncomputable|abbrev|structure|open|section|"
               r"instance|class|variable|example|@\[")


@dataclass
class PortMatchResult:
    """Outcome of comparing ported declarations against their source island."""

    all_match: bool
    matched: list = field(default_factory=list)      # decl names whose statement matches
    drifted: dict = field(default_factory=dict)      # name -> (source_text, target_text)
    missing: dict = field(default_factory=dict)      # name -> which side it was absent from
    source_label: str = "source"
    target_label: str = "target"

    def summary(self) -> str:
        tag = "OK" if self.all_match else "DRIFT"
        total = len(self.matched) + len(self.drifted) + len(self.missing)
        extra = ""
        if self.drifted:
            extra += f"; {len(self.drifted)} drifted: {sorted(self.drifted)}"
        if self.missing:
            extra += f"; {len(self.missing)} missing: {sorted(self.missing)}"
        return (f"[{tag}] {len(self.matched)}/{total} ported declarations match "
                f"{self.source_label} -> {self.target_label}{extra}")

    def failure_lines(self) -> list:
        """One human-readable line per failure, ready to print in a drift check."""
        lines = []
        for name, where in sorted(self.missing.items()):
            lines.append(f"ported `{name}` not found in {where}")
        for name, (want, have) in sorted(self.drifted.items()):
            lines.append(f"ported `{name}` drifted from {self.source_label}:\n"
                         f"  {self.source_label}: {want}\n"
                         f"  {self.target_label}: {have}")
        return lines


def strip_comments(text: str) -> str:
    """Drop Lean block comments `/- ... -/` and line comments `-- ...`."""
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def normalize(text: str) -> str:
    """Comment-free, whitespace-collapsed form: the comparison normal form."""
    return re.sub(r"\s+", " ", strip_comments(text)).strip()


def decl_kind(text: str, name: str):
    """`'theorem'`, `'def'`, or `None` if `name` is not declared in `text`."""
    body = strip_comments(text)
    if re.search(rf"\b(?:theorem|lemma|example)\s+{re.escape(name)}\b", body):
        return "theorem"
    if re.search(rf"\b(?:def|abbrev)\s+{re.escape(name)}\b", body):
        return "def"
    return None


def statement_text(text: str, name: str, kind=None):
    """The normalized ported statement of `name` in `text`, or `None` if absent.

    For a theorem this is `theorem NAME <binders> : <type>` up to the first top-level
    `:=` (proof excluded).  For a def it is the whole `def NAME ... := <body>` block up
    to the next top-level declaration (body INCLUDED).
    """
    kind = kind or decl_kind(text, name)
    if kind is None:
        return None
    body = strip_comments(text)
    if kind == "theorem":
        m = re.search(rf"\b(?:theorem|lemma|example)\s+{re.escape(name)}\b(.*?)\s*:=",
                      body, flags=re.S)
        if not m:
            return None
        return re.sub(r"\s+", " ", f"theorem {name}{m.group(1)}").strip()
    m = re.search(rf"\b(?:def|abbrev)\s+{re.escape(name)}\b.*?(?=\n(?:{_DECL_START})\b)",
                  body, flags=re.S)
    if not m:
        # last declaration in the file: run to the end
        m = re.search(rf"\b(?:def|abbrev)\s+{re.escape(name)}\b.*", body, flags=re.S)
        if not m:
            return None
    # normalize the leading keyword so `noncomputable def f` and `def f` compare equal
    return re.sub(r"\s+", " ", m.group(0)).strip()


def _lookup(texts, name, label):
    """First (text, label) in `texts` declaring `name`, else (None, None)."""
    for text, lab in texts:
        if decl_kind(text, name) is not None:
            return text, lab
    return None, label


def _as_pairs(texts, default_label):
    if isinstance(texts, str):
        return [(texts, default_label)]
    out = []
    for item in texts:
        if isinstance(item, str):
            out.append((item, default_label))
        else:
            out.append((item[0], item[1]))
    return out


def port_match_check(source, target, decls, *, source_label="source island",
                     target_label="target island") -> PortMatchResult:
    """Check every declaration in `decls` was ported verbatim from `source` to `target`.

    `source` / `target` are Lean source TEXT, or a sequence of texts (optionally
    `(text, label)` pairs) searched in order — a ported block may be split across
    several modules on either side.  Returns a :class:`PortMatchResult`; the `kind`
    (theorem vs def) is taken from the SOURCE side, so a def that became a theorem (or
    vice versa) is reported as drift rather than silently compared in the wrong mode.
    """
    src = _as_pairs(source, source_label)
    tgt = _as_pairs(target, target_label)
    res = PortMatchResult(all_match=True, source_label=source_label, target_label=target_label)
    for name in decls:
        stext, slab = _lookup(src, name, source_label)
        if stext is None:
            res.all_match = False
            res.missing[name] = source_label
            continue
        kind = decl_kind(stext, name)
        want = statement_text(stext, name, kind)
        ttext, tlab = _lookup(tgt, name, target_label)
        if ttext is None:
            res.all_match = False
            res.missing[name] = target_label
            continue
        if decl_kind(ttext, name) != kind:
            res.all_match = False
            res.drifted[name] = (f"[{kind}] {want}", f"[{decl_kind(ttext, name)}] "
                                 f"{statement_text(ttext, name)}")
            continue
        have = statement_text(ttext, name, kind)
        if want != have:
            res.all_match = False
            res.drifted[name] = (want, have)
        else:
            res.matched.append(name)
    return res


def port_match_pinned(pin, target, decls, *, live=None, pin_label="pinned source text",
                      target_label="target island",
                      live_label="live source island") -> tuple:
    """Two-sided check for a source island that is NOT in this checkout.

    Returns `(target_vs_pin, pin_vs_live_or_None)`.  The first certifies the port
    matches the pinned copy of the source statements; the second, present only when
    `live` is given (the source island IS in the checkout, e.g. after a branch merge),
    certifies the pin itself still matches the live file — so the pin cannot rot into a
    fiction of the artifact it claims to quote.
    """
    first = port_match_check(pin, target, decls, source_label=pin_label,
                             target_label=target_label)
    if live is None:
        return first, None
    second = port_match_check(live, pin, decls, source_label=live_label,
                              target_label=pin_label)
    return first, second
