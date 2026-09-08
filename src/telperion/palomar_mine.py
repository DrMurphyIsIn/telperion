"""Palomar certificate mining — distill the Palomar registry into Telperion.

The Palomar registry (https://palomar-registry.org, data at
`https://data.palomar-registry.org/recent.json`) publishes Lean-verified,
comparator-checked formalizations.  Many of them carry the same *certificate
shapes* Telperion emits (SOS/PSD positivity, real-rootedness/hyperbolicity,
Hermitian eigenvalue/inertia, finite-decide/enclosure, argument-principle, …),
and several directly touch this project's two research fronts — the Riemann
zeta zero-free / positive-proportion work (RH) and the Brualdi–Goldwasser tree
permanent-ratio conjecture (BG).

This module is the systematic distiller.  It is deliberately split into a PURE,
offline-testable core (`classify_entry`, `mine`, `mining_report`) and a thin
network layer (`fetch_registry`, `poll`), so the classification logic is unit
tested without hitting the network — the same untrusted-input / testable-core
discipline the emitters use.

`poll(state_path)` is the recurring subroutine: it fetches the registry, diffs
against the entry ids seen on previous runs, classifies only the NEW entries,
records them, and returns the new mining candidates.  A scheduler (cron / the
`/loop` skill) calling `poll` on an interval turns "new Palomar entry" into
"surfaced candidate Telperion emitter" automatically.

Nothing here trusts Palomar: a mining candidate is a *lead* for a human/agent to
build and CI-verify an emitter, never an emitter itself.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Callable, Iterable

DATA_URL = "https://data.palomar-registry.org/recent.json"
FEED_URL = "https://data.palomar-registry.org/feed.xml"

# --------------------------------------------------------------------------- #
# Topic lexicons — the two research fronts this project mines Palomar for.     #
# --------------------------------------------------------------------------- #

TOPIC_KEYWORDS: dict[str, str] = {
    # Riemann zeta / analytic number theory front.
    "rh": r"""riemann|zeta\b|\bxi\b|xi function|L-function|L-series|dirichlet series|
              von ?mangoldt|explicit formula|pair correlation|critical line|nontrivial zero|
              li-?keiper|li'?s criterion|li coefficient|de ?bruijn|newman|jensen|laguerre|
              tur[aá]n|selberg|montgomery|hardy|prime.?count|zero-?free""",
    # Brualdi–Goldwasser tree / permanent-ratio front (graph + linear algebra).
    "bg": r"""\bgraph|\btree\b|\bforest\b|spanning|laplacian|permanent|\bmatching|immanant|
              adjacenc|incidence|chip.?fir|riemann.?roch|interlac|log.?concav|unimodal|
              newton inequalit|extremal|circulant|hadamard|block design|degree sequence|
              totally nonneg|k[őo]nig|k[őo]nig-?egerv[aá]ry""",
    # Shared proof-complexity / certificate-ladder front.
    "pvsnp": r"""sum.?of.?squares|\bSOS\b|sos degree|proof complexity|nullstellensatz|
                 grigoriev|tseitin|knapsack|pseudo-?expectation|lasserre|positivstellensatz""",
}
_TOPIC_RE = {k: re.compile(v, re.I | re.X) for k, v in TOPIC_KEYWORDS.items()}

# --------------------------------------------------------------------------- #
# Shape rules — math vocabulary -> Telperion emitter family.                   #
# `kind` is an EXISTING Telperion emitter kind (the candidate maps onto proven #
# tooling) or None (a candidate NEW shape to design). Ordered; all matches are #
# collected, so one entry can surface several shapes.                          #
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class ShapeRule:
    pattern: str
    family: str
    kind: str | None            # existing Telperion `kind`, or None for a NEW candidate
    note: str = ""

SHAPE_RULES: tuple[ShapeRule, ...] = (
    ShapeRule(r"li-?keiper|li'?s criterion|li coefficient",
              "Li positivity ladder", None,
              "certify λ_n ≥ 0 for finite n onto the formalized RH⇔Li reduction"),
    ShapeRule(r"explicit formula|pair correlation|von ?mangoldt|weil (positivity|form|explicit)",
              "explicit-formula / Weil positivity", None,
              "finite test-function-family PSD form; feeds HermitianMomentInertia"),
    ShapeRule(r"jensen|laguerre|tur[aá]n|hyperbolic(ity)?|real.?root|log.?concav|newton inequalit",
              "real-rootedness / hyperbolicity", "interlacing",
              "discriminant/Hankel/Newton real-rootedness; Jensen–Pólya (Track 1)"),
    ShapeRule(r"sum.?of.?squares|\bSOS\b|semidefinit|positive semidefinite|\bPSD\b|gram matrix|low.?rank",
              "SOS / PSD positivity", "psd_form", "LDLᵀ / rational-SOS Gram bridge"),
    ShapeRule(r"eigenvalue|spectral|hermitian|inertia|signature|numerical range|adjacency spectrum",
              "Hermitian eigenvalue / inertia", "rank_trace_scalar",
              "HermitianMomentInertia family (rank–trace / Sylvester / von Neumann)"),
    ShapeRule(r"argument principle|winding|residue|zero.?count|contour|turing",
              "argument-principle / winding", "argument_principle", ""),
    ShapeRule(r"permanent|\bmatching\b|immanant|spanning tree|cavity recursion",
              "permanent / matching (BG cavity)", None,
              "cavity recursion + rational_identity; Brualdi–Goldwasser core"),
    ShapeRule(r"interlac",
              "interlacing / Newton inequalities", "interlacing", ""),
    ShapeRule(r"nullstellensatz|handelman|putinar|positivstellensatz|ch[vw][aá]tal|gomory|integer round",
              "Positivstellensatz / integer rounding", "handelman", ""),
    ShapeRule(r"interval arithmetic|enclosure|exact.?arithmetic|finite.?dimensional|\bdecide\b|"
              r"exact rational|finite (table|check|core)",
              "finite-decide / enclosure", "finite_decide", ""),
    ShapeRule(r"spectral theorem|self-?adjoint|projection-?valued|stone'?s theorem|cayley transform",
              "spectral-theory infrastructure (Hilbert–Pólya)", None,
              "unbounded self-adjoint substrate; enables Track 4 statements"),
)
_SHAPE_RE = [(re.compile(r.pattern, re.I), r) for r in SHAPE_RULES]

# external-numeric trust boundary (a mined shape whose kernel proof consumes an
# out-of-Lean numeric oracle — the documented seam, not a defect).
_TRUST_RE = re.compile(
    r"\barb\b|interval.?arithmetic|enclosure|floating.?point|numeric(al)? (certif|input|enclosure|bound)|"
    r"\d{2,}.?bit", re.I)


@dataclass
class MiningCandidate:
    entry_id: str
    title: str
    source_repo: str
    topics: list[str]
    shapes: list[dict]                 # {family, kind, novelty, note}
    trust_boundary: bool
    msc: str
    score: int
    abstract_snippet: str = ""
    source_name: str = "palomar"
    # lead_type: how close this entry is to a buildable kernel certificate.
    #   "formalized_certificate" = already Lean-verified (Palomar/Mathlib) -> direct port lead;
    #   "raw_math" = unformalized (arXiv / Zulip discussion) -> formalize-first candidate.
    lead_type: str = "formalized_certificate"

    @property
    def has_new_shape(self) -> bool:
        return any(s["novelty"] == "candidate_new" for s in self.shapes)


def _entry_text(entry: dict) -> tuple[str, str]:
    """(searchable text, msc string) for one registry entry."""
    cls = entry.get("classification") or {}
    if isinstance(cls, dict):
        msc = " ".join(cls.get("msc") or cls.get("msc2020") or [])
    else:
        msc = str(cls)
    text = " ".join(str(entry.get(k, "")) for k in ("title", "abstract")) + " " + msc
    return text, msc


def _source_repo(entry: dict) -> str:
    src = entry.get("source") or {}
    if isinstance(src, dict):
        return str(src.get("repo") or src.get("url") or src.get("repository") or "")
    return str(src)


def classify_entry(entry: dict, topics: Iterable[str] | None = None) -> MiningCandidate | None:
    """Classify one Palomar entry into a mining candidate, or None if it carries
    no recognizable certificate shape / no requested topic.

    Pure and deterministic — the unit-tested core.  `topics` restricts to a
    subset of `TOPIC_KEYWORDS` (default: all)."""
    text, msc = _entry_text(entry)
    want = list(topics) if topics is not None else list(TOPIC_KEYWORDS)
    matched_topics = [t for t in want if t in _TOPIC_RE and _TOPIC_RE[t].search(text)]
    if not matched_topics:
        return None
    shapes: list[dict] = []
    seen_family: set[str] = set()
    for rx, rule in _SHAPE_RE:
        if rx.search(text) and rule.family not in seen_family:
            seen_family.add(rule.family)
            shapes.append({
                "family": rule.family,
                "kind": rule.kind,
                "novelty": "existing" if rule.kind else "candidate_new",
                "note": rule.note,
            })
    if not shapes:
        return None
    trust = bool(_TRUST_RE.search(text))
    # score: shapes + topics, with a bonus for a genuinely new candidate shape.
    score = len(shapes) + len(matched_topics) + sum(1 for s in shapes if s["novelty"] == "candidate_new")
    ab = re.sub(r"\s+", " ", str(entry.get("abstract", ""))).strip()
    return MiningCandidate(
        entry_id=str(entry.get("id", "")),
        title=str(entry.get("title", "")),
        source_repo=_source_repo(entry),
        topics=matched_topics,
        shapes=shapes,
        trust_boundary=trust,
        msc=msc,
        score=score,
        abstract_snippet=ab[:240],
    )


def mine(entries: Iterable[dict], topics: Iterable[str] | None = None,
         min_score: int = 1) -> list[MiningCandidate]:
    """Classify every entry and return the candidates (score ≥ min_score),
    ranked by score (desc) then entry id (for determinism)."""
    out = []
    for e in entries:
        c = classify_entry(e, topics=topics)
        if c is not None and c.score >= min_score:
            out.append(c)
    out.sort(key=lambda c: (-c.score, c.entry_id))
    return out


def mining_report(candidates: list[MiningCandidate]) -> str:
    """A markdown mining report: candidates grouped by whether they surface a
    NEW candidate shape vs. map onto an existing emitter."""
    lines = [f"# Palomar mining report — {len(candidates)} candidate(s)", ""]
    new = [c for c in candidates if c.has_new_shape]
    exist = [c for c in candidates if not c.has_new_shape]
    for title, group in (("New candidate emitter shapes", new),
                         ("Map onto existing emitters", exist)):
        if not group:
            continue
        lines.append(f"## {title}")
        for c in group:
            fams = ", ".join(
                f"{s['family']}"
                + (f" → `{s['kind']}`" if s["kind"] else " → **NEW**")
                for s in c.shapes)
            tb = "  [external numeric trust boundary]" if c.trust_boundary else ""
            lines.append(f"- **[{c.entry_id}]** {c.title}  (score {c.score}, topics {','.join(c.topics)}){tb}")
            lines.append(f"    - shapes: {fams}")
            if c.source_repo:
                lines.append(f"    - source: `{c.source_repo}`")
        lines.append("")
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Network + recurring poll (thin; not exercised by the offline unit tests).    #
# --------------------------------------------------------------------------- #

def fetch_registry(url: str = DATA_URL, timeout: float = 30.0) -> list[dict]:
    """Fetch the Palomar registry and return its entry list.  Thin urllib call;
    raises on network / parse failure (a poll failure, never a wrong classification)."""
    import urllib.request
    # The data CDN 403s the default python-urllib User-Agent; send an explicit one.
    req = urllib.request.Request(url, headers={"User-Agent": "telperion-palomar-mine/0.1"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310 (fixed https host)
        data = json.loads(resp.read().decode("utf-8"))
    return data.get("entries", data) if isinstance(data, dict) else data


def parse_feed(xml_text: str) -> list[dict]:
    """Parse the Palomar RSS feed (`feed.xml`) into classify_entry-compatible
    entry dicts.  Pure (offline-testable).  RSS items carry title, description
    (→ abstract) and a link `…?id=PALOMAR-…&version=N`; the id is parsed from the
    link so the seen-state is shared with the `recent.json` source.  RSS items
    lack the structured MSC of `recent.json`, so title+abstract drive matching."""
    import html
    import re as _re
    import xml.etree.ElementTree as ET

    root = ET.fromstring(xml_text)
    out: list[dict] = []
    for item in root.iter("item"):
        def _text(tag: str) -> str:
            el = item.find(tag)
            return html.unescape(el.text or "") if el is not None and el.text else ""
        link = _text("link")
        m = _re.search(r"[?&]id=([^&]+)", link)
        out.append({
            "id": m.group(1) if m else link,
            "title": _text("title"),
            "abstract": _text("description"),
            "source": {"url": link},
        })
    return out


def fetch_feed(url: str = FEED_URL, timeout: float = 30.0) -> list[dict]:
    """Fetch + parse the Palomar RSS feed — a lighter-weight alternate source to
    `fetch_registry` (same entry shape, shared id space)."""
    import urllib.request
    req = urllib.request.Request(url, headers={"User-Agent": "telperion-palomar-mine/0.1"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310 (fixed https host)
        return parse_feed(resp.read().decode("utf-8"))


def load_seen(state_path: str | Path) -> set[str]:
    p = Path(state_path)
    if not p.exists():
        return set()
    return set(json.loads(p.read_text()).get("seen", []))


def save_seen(state_path: str | Path, seen: set[str]) -> None:
    Path(state_path).write_text(json.dumps({"seen": sorted(seen)}, indent=0))


def poll(state_path: str | Path, topics: Iterable[str] | None = None,
         url: str = DATA_URL, fetch: Callable[[str], list[dict]] | None = None,
         min_score: int = 1) -> list[MiningCandidate]:
    """The recurring subroutine: fetch the registry, keep only entries whose id
    was NOT seen on a previous run, classify those, persist the enlarged seen-set,
    and return the new candidates (ranked).

    `fetch` is injectable (defaults to `fetch_registry`) so the poll loop is
    tested offline.  First run classifies everything (seen-set empty)."""
    fetch = fetch or fetch_registry
    entries = fetch(url)
    seen = load_seen(state_path)
    fresh = [e for e in entries if str(e.get("id", "")) not in seen]
    candidates = mine(fresh, topics=topics, min_score=min_score)
    save_seen(state_path, seen | {str(e.get("id", "")) for e in entries})
    return candidates
