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

Exit 0 iff every anchor is printed clean; 1 otherwise (each miss is an `::error::` line);
2 on a registry/usage problem (unreadable node, statement not found in its artifact, an
island with no proved nodes -- a typo'd island must not pass vacuously).

Standalone on purpose: stdlib only (Python >= 3.11 for tomllib), so it runs in CI jobs that
never install the telperion package. The Lean comment stripper and normalizer below mirror
`telperion.missions.verify`; `tests/test_guard_anchors.py` pins them against the originals.

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
# Lean text normalisation (mirrors telperion.missions.verify; parity-tested)
# ---------------------------------------------------------------------------

def strip_lean_comments(text: str) -> str:
    """Remove `--` and nested `/- -/` comments; keep string literals intact (Lean lex order)."""
    out = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == "-" and text[i:i + 2] == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif ch == "/" and text[i:i + 2] == "/-":
            depth = 1
            i += 2
            while i < n and depth:
                if text[i:i + 2] == "/-":
                    depth += 1
                    i += 2
                elif text[i:i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif ch == '"':
            out.append(ch)
            i += 1
            while i < n:
                out.append(text[i])
                if text[i] == "\\" and i + 1 < n:
                    out.append(text[i + 1])
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def normalize_lean(text: str) -> str:
    text = strip_lean_comments(text)
    text = re.sub(r"\s+", " ", text).strip()
    text = re.sub(r":=\s*by\s+sorry$", "", text).strip()
    text = re.sub(r":=\s*sorry$", "", text).strip()
    return text


def strip_string_literals(text: str) -> str:
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', text)


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


def load_anchors(telperion_root: Path, island: str) -> List[Anchor]:
    anchors: List[Anchor] = []
    errors: List[str] = []
    missions = telperion_root / "missions"
    for toml_path in sorted(missions.glob("*/nodes/*.toml")):
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
    ap.add_argument("guard_output", nargs="*", type=Path,
                    help="files holding `lake env lean AxiomGuard*.lean` output")
    args = ap.parse_args(list(argv) if argv is not None else None)

    try:
        anchors = load_anchors(args.telperion, args.island)
    except RegistryError as e:
        for line in str(e).splitlines():
            print(f"::error::{line}")
        return 2
    if not anchors:
        print(f"::error::no proved registry node has its artifact on island `{args.island}`"
              " -- refusing to pass vacuously")
        return 2
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
    print(f"OK: all {len(anchors)} proved registry anchors on `{args.island}` are printed by "
          "the guard with axioms within [propext, Classical.choice, Quot.sound].")
    return 0


if __name__ == "__main__":
    sys.exit(main())
