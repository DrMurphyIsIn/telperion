#!/usr/bin/env python3
"""Registry-anchored axiom-guard check: every PROVED node on an island must be printed clean.

WHY (closure run 2026-09-22, audit ledger C1 + the rvm_bridge floor finding). The island
guard jobs asserted a FLOOR on the number of `#print axioms` lines (rvm_bridge: 45), not the
presence of each registry theorem. A floor says "the guard ran"; it does not say "the guard
covers the theorems the registry calls proved". A node whose theorem is never printed can
depend on `sorryAx` or on a self-declared `axiom` and every floor-based job stays green. C1
was exactly that shape: `RH_zero_free_polylog` and `RH_zero_free_gamma5` were proved in the
registry while no workflow ran the guard that prints them.

This script derives the anchor list FROM THE REGISTRY instead of hand-maintaining it:

  1. every `telperion/missions/*/nodes/*.toml` with `status = "proved"` whose
     `[proof].artifact` resolves into `telperion/examples/<island>/`;
  2. the theorem the grant gate matched: the last `theorem`/`lemma` declaration of the
     node's statement file (`missions/<campaign>/lean/Statements/<slug>.lean`), located in
     the artifact at the declaration whose text is that statement followed by a proof body
     (the gate's own `statement_matches` criterion), and fully qualified by the artifact's
     `namespace` blocks at that point;
  3. the guard output (one or more files, `lake env lean AxiomGuard*.lean` stdout) must
     contain, for each fully qualified name, a `'<name>' depends on axioms: [...]` (or
     `does not depend on any axioms`) line whose list is a subset of Lean's three standard
     axioms `[propext, Classical.choice, Quot.sound]`, and no `sorryAx` anywhere.

Usage (from the repository root, or with --telperion):

    python telperion/scripts/guard_anchors.py --island rvm_bridge axioms.out
    python telperion/scripts/guard_anchors.py --island li_positivity lp.out zf.out
    python telperion/scripts/guard_anchors.py --island dbn --list      # show the anchors
    python telperion/scripts/guard_anchors.py --island rvm_bridge --exclude-heavy axioms.out
    python telperion/scripts/guard_anchors.py --island rvm_bridge --only-heavy hodge1_axioms.out

`judge_via = "heavy"` nodes (2026-10-13): their artifacts import certificates that no AxiomGuard*
lib may pull in, so their anchors are printed by a separate heavy guard (Hodge1_Guard on
rvm_bridge). The AxiomGuard* job passes --exclude-heavy and the heavy guard job --only-heavy;
together they cover every proved node. With a filter, an island that has proved nodes but none
on that side of the split passes with an OK line (exit 0); an island with no proved node at all
is still refused (exit 2).

Exit 0 iff every anchor is printed clean; 1 otherwise (each miss is an `::error::` line);
2 on a registry/usage problem (unreadable node, statement not found in its artifact, an
island with no proved nodes -- a typo'd island must not pass vacuously).

Standalone on purpose: stdlib only (Python >= 3.11 for tomllib), so it runs in CI jobs that
never install the telperion package. The Lean lexer below (`lean_segments`, with `strip_lean_comments`,
`strip_string_literals`, `normalize_lean` and `blank_lean_code` on top) is the ONE shared implementation:
`telperion.missions.verify` and `telperion.checks.negation_probe` load this file and call it, and
`tests/test_guard_anchors.py` pins the parity.

conjecture1_proved = False.
"""
from __future__ import annotations

import argparse
import re
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
_SENTINEL = "DO NOT EDIT BY HAND"


# ---------------------------------------------------------------------------
# Lean text lexing and normalisation: the ONE shared implementation. telperion.missions.verify and
# telperion.checks.negation_probe load and call these (they used to carry copies, which drifted).
# ---------------------------------------------------------------------------

#: A char literal: `'x'`, `'\\n'`, `'\\x41'`, `'\\u{3b1}'` (Lean's escapes). Only where a char literal can start,
#: i.e. not after an identifier character (`h'` is a name, not the start of a literal).
_CHAR_LIT_RE = re.compile(r"'(?:\\x[0-9a-fA-F]{2}|\\u\{[0-9a-fA-F]+\}|\\.|[^\\'\n])'")
_RAW_OPEN_RE = re.compile(r'r(#*)"')


def _ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?.\u00bb"


def lean_segments(text: str) -> List[Tuple[str, str]]:
    """Split Lean source into (kind, text) segments in Lean's own lexing order, one left-to-right pass:
    `comment` (`--` to the end of the line, or a NESTED `/- -/` block, doc comments included; an unterminated block
    swallows the rest, as in Lean), `string` (`"..."` with backslash escapes; an unterminated one runs to the end),
    `raw` (`r"..."`, `r#"..."#`, closed only by the same number of `#`), `char` (`'"'`, `'\\''`, ...), and `code`
    (everything else). Comment markers inside strings, raw strings and char literals are inert, and a `"` inside a
    char literal or a raw string does not open a string (the desync the final re-review demonstrated with
    `r"\\" ++ "`). Concatenating every segment gives back `text`."""
    segs: List[Tuple[str, str]] = []
    code: List[str] = []
    i, n = 0, len(text)

    def push(kind: str, j: int) -> int:
        if code:
            segs.append(("code", "".join(code)))
            code.clear()
        segs.append((kind, text[i:j]))
        return j
    while i < n:
        ch = text[i]
        prev = text[i - 1] if i else " "
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = push("comment", n if j < 0 else j)
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            i = push("comment", j)
        elif ch == "r" and not _ident_char(prev) and _RAW_OPEN_RE.match(text, i):
            hashes = _RAW_OPEN_RE.match(text, i).group(1)
            close = text.find('"' + hashes, i + 2 + len(hashes))
            i = push("raw", n if close < 0 else close + 1 + len(hashes))
        elif ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = push("string", min(n, j + 1))
        elif ch == "'" and not _ident_char(prev) and _CHAR_LIT_RE.match(text, i):
            i = push("char", _CHAR_LIT_RE.match(text, i).end())
        else:
            code.append(ch)
            i += 1
    if code:
        segs.append(("code", "".join(code)))
    return segs


def strip_lean_comments(text: str) -> str:
    """Remove `--` and nested `/- -/` comments; keep string, raw-string and char literals intact (Lean lex order)."""
    return "".join(t for k, t in lean_segments(text) if k != "comment")


def normalize_lean(text: str) -> str:
    text = strip_lean_comments(text)
    text = re.sub(r"\s+", " ", text).strip()
    text = re.sub(r":=\s*by\s+sorry$", "", text).strip()
    text = re.sub(r":=\s*sorry$", "", text).strip()
    return text


def strip_string_literals(text: str) -> str:
    """Blank string and raw-string literals to `""` (char literals and comments are kept as they are). For
    containment the contents are attacker-controlled text: a statement inside a string is not a declaration."""
    return "".join('""' if k in ("string", "raw") else t for k, t in lean_segments(text))


def blank_lean_code(text: str) -> str:
    """Code only: comments dropped, string and raw-string literals replaced by `""` and char literals by `' '`, each
    followed by the newlines it contained, so a line start in the result is a line start in the source (for
    `^namespace` / `^theorem` scans)."""
    out = []
    for k, t in lean_segments(text):
        nl = "\n" * t.count("\n")
        out.append(t if k == "code" else ('""' if k in ("string", "raw") else "' '" if k == "char" else "") + nl)
    return "".join(out)


_PROOF_BODY_RE = re.compile(r"^\s*(:=|by\b)")
_IDENT = r"[^\s(){}\[\]:,]+"
_DECL_RE = re.compile(
    r"(?m)(?:^|(?<=\s))(theorem|lemma)\s+(" + _IDENT + r")")


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

class RegistryError(Exception):
    pass


@dataclass(frozen=True)
class Anchor:
    node: str           # registry slug, e.g. MM_effective_threshold_unbounded
    campaign: str
    artifact: Path
    theorem: str        # fully qualified Lean name the guard must print


def island_of(path: Path) -> Optional[str]:
    parts = path.resolve().parts
    for i in range(len(parts) - 2):
        if parts[i] == "telperion" and parts[i + 1] == "examples":
            return parts[i + 2]
    return None


def statement_decl(statement_text: str) -> Tuple[str, str]:
    """(short name, normalized text from the last theorem/lemma keyword) of a statement file."""
    lines = statement_text.split("\n")
    k = 0
    while k < len(lines) and not lines[k].strip():
        k += 1
    if k < len(lines) and _SENTINEL in lines[k]:
        k += 1
    body = "\n".join(
        ln for ln in lines[k:]
        if not ln.strip().startswith("import ") and not ln.strip().startswith("open "))
    norm = normalize_lean(body)
    decls = list(_DECL_RE.finditer(norm))
    if not decls:
        raise RegistryError("statement file declares no theorem/lemma")
    last = decls[-1]
    return last.group(2), norm[last.start():]


def _namespace_at(code: str, pos: int) -> List[str]:
    """Namespace components in force at offset `pos` of comment-stripped Lean `code`."""
    stack: List[Tuple[str, List[str]]] = []
    tok = re.compile(
        r"(?m)^[ \t]*(?:(namespace)[ \t]+(\S+)|(?:noncomputable[ \t]+)?(section)\b[ \t]*(\S*)"
        r"|(mutual)\b|(end)\b[ \t]*([^\s]*))")
    for m in tok.finditer(code, 0, pos):
        if m.group(1):
            stack.append(("ns", m.group(2).split(".")))
        elif m.group(3):
            stack.append(("sec", []))
        elif m.group(5):
            stack.append(("mutual", []))
        elif m.group(6):
            name = m.group(7)
            if name and stack and stack[-1][0] == "ns":
                # `end A.B` closes `namespace A.B` (possibly opened as nested namespaces)
                want = name.split(".")
                while want and stack and stack[-1][0] == "ns":
                    top = stack.pop()[1]
                    want = want[: len(want) - len(top)]
            elif stack:
                stack.pop()
    return [c for kind, parts in stack if kind == "ns" for c in parts]


def resolve_theorem(artifact_text: str, statement_text: str) -> str:
    """Fully qualified name of the artifact declaration the grant gate matched."""
    short, needle = statement_decl(statement_text)
    code = strip_string_literals(strip_lean_comments(artifact_text))
    hits: List[str] = []
    pat = re.compile(r"(?<![\w.'])(theorem|lemma)\s+" + re.escape(short) + r"(?![\w.'])")
    for m in pat.finditer(code):
        rest = normalize_lean(code[m.start():])
        if not rest.startswith(needle) or not _PROOF_BODY_RE.match(rest[len(needle):]):
            continue
        prefix = code[max(0, m.start() - 80):m.start()]
        if re.search(r"\bprivate\s+(?:\S+\s+)*$", prefix.split("\n")[-1] + " "):
            raise RegistryError(f"`{short}` is private in the artifact; the guard cannot print it")
        if short.startswith("_root_."):
            hits.append(short[len("_root_."):])
        else:
            hits.append(".".join(_namespace_at(code, m.start()) + [short]))
    hits = sorted(set(hits))
    if not hits:
        raise RegistryError(
            f"no `theorem {short}` in the artifact states the node statement followed by a proof "
            "body (the grant gate's criterion) -- statement/artifact drift")
    if len(hits) > 1:
        raise RegistryError(f"ambiguous: the statement matches {hits}")
    return hits[0]


def is_heavy(doc: dict) -> bool:
    """`judge_via = "heavy"`: the node's artifact imports certificates no AxiomGuard* lib may pull
    in, so its anchor is printed by a separate heavy guard (e.g. Hodge1_Guard), not AxiomGuard*."""
    return str(doc.get("judge_via", "") or "").strip() == "heavy"


def _island_nodes(telperion_root: Path, island: str, errors: List[str]):
    """(node toml, campaign root, node doc, resolved artifact) of every proved island node."""
    for toml_path in sorted((telperion_root / "missions").glob("*/nodes/*.toml")):
        campaign_root = toml_path.parent.parent
        try:
            doc = tomllib.loads(toml_path.read_text())
        except (OSError, tomllib.TOMLDecodeError) as e:
            errors.append(f"{toml_path}: unreadable ({e})")
            continue
        if doc.get("status") != "proved":
            continue
        proof = doc.get("proof") or {}
        art = proof.get("artifact")
        if not art or not str(art).endswith(".lean"):
            continue
        artifact = (campaign_root / art).resolve()
        if island_of(artifact) != island:
            continue
        yield toml_path, campaign_root, doc, artifact


def count_island_nodes(telperion_root: Path, island: str) -> int:
    """Proved nodes on the island, heavy or not (the vacuity check: a typo'd island has none)."""
    return sum(1 for _ in _island_nodes(telperion_root, island, []))


def load_anchors(telperion_root: Path, island: str,
                 heavy: Optional[bool] = None) -> List[Anchor]:
    """Anchors of the island's proved nodes. heavy=None: all of them (the default); False: only
    nodes that are NOT judge_via = "heavy"; True: only those that are. Filtered nodes are not
    resolved at all, so a heavy node's artifact never has to be read by the ordinary job."""
    anchors: List[Anchor] = []
    errors: List[str] = []
    for toml_path, campaign_root, doc, artifact in _island_nodes(telperion_root, island, errors):
        if heavy is not None and is_heavy(doc) != heavy:
            continue
        slug = str(doc.get("name", toml_path.stem)).replace(".", "_")
        stmt = campaign_root / "lean" / "Statements" / f"{slug}.lean"
        try:
            thm = resolve_theorem(artifact.read_text(), stmt.read_text())
        except (OSError, RegistryError) as e:
            errors.append(f"{campaign_root.name}/{slug}: {e}")
            continue
        anchors.append(Anchor(slug, campaign_root.name, artifact, thm))
    if errors:
        raise RegistryError("\n".join(errors))
    return anchors


# ---------------------------------------------------------------------------
# Guard output
# ---------------------------------------------------------------------------

_AXIOM_LINE = re.compile(
    r"'(\S+?)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))")


def _canon(name: str) -> str:
    return name.replace("«", "").replace("»", "")


def parse_guard_output(text: str) -> Dict[str, List[Set[str]]]:
    """name -> every axiom set printed for it. Lines are joined first: Lean wraps long lists."""
    flat = re.sub(r"\s+", " ", text)
    out: Dict[str, List[Set[str]]] = {}
    for m in _AXIOM_LINE.finditer(flat):
        axioms = set() if m.group(3) else {a.strip() for a in m.group(2).split(",") if a.strip()}
        out.setdefault(_canon(m.group(1)), []).append(axioms)
    return out


def check(anchors: Sequence[Anchor], guard_text: str) -> List[str]:
    """Error messages; empty means every anchor is printed and clean."""
    errs: List[str] = []
    if "sorryAx" in guard_text:
        errs.append("guard output mentions sorryAx")
    printed = parse_guard_output(guard_text)
    for a in anchors:
        sets = printed.get(_canon(a.theorem))
        if not sets:
            errs.append(f"{a.campaign}/{a.node}: `{a.theorem}` is never printed by the guard")
            continue
        for s in sets:
            extra = s - STANDARD_AXIOMS
            if extra:
                errs.append(f"{a.campaign}/{a.node}: `{a.theorem}` depends on "
                            f"non-standard axioms {sorted(extra)}")
    return errs


def main(argv: Optional[Iterable[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--island", required=True, help="example island, e.g. rvm_bridge")
    ap.add_argument("--telperion", type=Path,
                    default=Path(__file__).resolve().parents[1],
                    help="telperion/ directory (default: this script's parent)")
    ap.add_argument("--list", action="store_true", help="print the derived anchors and exit")
    sel = ap.add_mutually_exclusive_group()
    sel.add_argument("--exclude-heavy", action="store_true",
                     help="skip judge_via = \"heavy\" nodes (their anchors are printed by a "
                          "separate heavy guard, never by AxiomGuard*)")
    sel.add_argument("--only-heavy", action="store_true",
                     help="check ONLY judge_via = \"heavy\" nodes (run against the heavy guard's "
                          "output)")
    ap.add_argument("guard_output", nargs="*", type=Path,
                    help="files holding `lake env lean AxiomGuard*.lean` output")
    args = ap.parse_args(list(argv) if argv is not None else None)

    heavy = True if args.only_heavy else False if args.exclude_heavy else None
    what = {None: "proved", True: "proved heavy", False: "proved non-heavy"}[heavy]
    try:
        anchors = load_anchors(args.telperion, args.island, heavy=heavy)
    except RegistryError as e:
        for line in str(e).splitlines():
            print(f"::error::{line}")
        return 2
    if not anchors:
        if heavy is None or count_island_nodes(args.telperion, args.island) == 0:
            print(f"::error::no proved registry node has its artifact on island `{args.island}`"
                  " -- refusing to pass vacuously")
            return 2
        # The island is real (it has proved nodes), just none on this side of the split -- e.g.
        # the heavy guard job before the first heavy node is granted.
        print(f"OK: no {what} registry node on `{args.island}` yet; nothing to check here.")
        return 0
    if args.list:
        for a in anchors:
            print(f"{a.campaign}/{a.node}\t{a.theorem}")
        return 0
    if not args.guard_output:
        ap.error("give at least one guard output file (or --list)")
    text = "\n".join(p.read_text(errors="replace") for p in args.guard_output)
    errs = check(anchors, text)
    for e in errs:
        print(f"::error::{e}")
    if errs:
        print(f"FAIL: {len(errs)} problem(s) across {len(anchors)} registry anchors on "
              f"`{args.island}`")
        return 1
    print(f"OK: all {len(anchors)} {what} registry anchors on `{args.island}` are printed by "
          "the guard with axioms within [propext, Classical.choice, Quot.sound].")
    return 0


if __name__ == "__main__":
    sys.exit(main())
