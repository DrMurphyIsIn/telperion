"""Source-monitoring subsystem — grow Telperion in tandem with the math frontier.

Generalizes the Palomar miner (`palomar_mine`) into a pluggable framework: a
shared classifier core (topic lexicons × shape rules → `MiningCandidate`, reused
from `palomar_mine`) driven by interchangeable **source adapters**, each
normalizing its feed into the common entry shape `{id, title, abstract, source,
[classification]}` and declaring a **lead_type**:

  - ``LEAD_FORMALIZED`` — the entry is already Lean-verified (Palomar, Mathlib,
    Compfiles) → a matched shape is a *direct port lead* (build the emitter).
  - ``LEAD_RAW`` — the entry is unformalized (arXiv paper, Zulip discussion) → a
    matched shape is a *formalize-first candidate* (much bigger lift, weaker
    signal). Tagged so we NEVER mistake "a paper exists" for "a certificate exists".

`poll_source(source, state_path)` is the recurring subroutine per source (fetch →
diff vs seen-state → classify NEW → tag with source + lead_type → persist). A
scheduler runs one poll per source on an interval; adapters that need credentials
(Zulip) or the network are injected/gated so the core stays offline-testable.

Adapters live in sibling modules and register here:
  - `palomar`  (formalized) — palomar_mine.fetch_registry / fetch_feed
  - `arxiv`    (raw)        — this module (arXiv Atom API)
  - `github`   (formalized) — source_mining_github.fetch_github_repos
  - `zulip`    (raw)        — source_mining_zulip.fetch_zulip
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Iterable

from .palomar_mine import (
    classify_entry,
    load_seen,
    mine as _mine_entries,
    save_seen,
    MiningCandidate,
)

LEAD_FORMALIZED = "formalized_certificate"
LEAD_RAW = "raw_math"


@dataclass
class Source:
    """A monitored math source: a name, its lead_type, and a `fetch()` returning
    classify_entry-compatible entry dicts.  `fetch` is a thunk so the network /
    credentials stay out of the pure core (inject a fake in tests)."""

    name: str
    lead_type: str
    fetch: Callable[[], list[dict]]
    default_topics: tuple[str, ...] = ("rh", "bg", "pvsnp")


def mine_source(source: Source, entries: Iterable[dict], topics: Iterable[str] | None = None,
                min_score: int = 1) -> list[MiningCandidate]:
    """Classify + rank a source's entries, tagging each candidate with the
    source name and lead_type (so a raw-math lead can never be read as a ready
    certificate)."""
    cands = _mine_entries(entries, topics=topics, min_score=min_score)
    for c in cands:
        c.source_name = source.name
        c.lead_type = source.lead_type
    return cands


def poll_source(source: Source, state_path: str | Path, topics: Iterable[str] | None = None,
                min_score: int = 1) -> list[MiningCandidate]:
    """Incremental per-source poll: fetch, keep entries whose id was not seen on a
    previous run, classify + tag, persist the enlarged seen-set, return new
    candidates (ranked)."""
    topics = list(topics) if topics is not None else list(source.default_topics)
    entries = source.fetch()
    seen = load_seen(state_path)
    fresh = [e for e in entries if str(e.get("id", "")) not in seen]
    cands = mine_source(source, fresh, topics=topics, min_score=min_score)
    save_seen(state_path, seen | {str(e.get("id", "")) for e in entries})
    return cands


# --------------------------------------------------------------------------- #
# arXiv adapter (raw math) — the frontier firehose.                           #
# --------------------------------------------------------------------------- #

ARXIV_API = "http://export.arxiv.org/api/query"
# Certificate-relevant arXiv categories: number theory, combinatorics, algebraic
# geometry, representation theory, and computational complexity.
ARXIV_CATEGORIES = ("math.NT", "math.CO", "math.AG", "math.RT", "cs.CC")


def parse_arxiv_atom(xml_text: str) -> list[dict]:
    """Parse an arXiv Atom API response into classify_entry-compatible entries.
    Pure (offline-testable).  id = the arXiv id (e.g. 2601.01234); title/abstract
    from <title>/<summary>; arXiv `term`s carried in `classification.arxiv`."""
    import re as _re
    import xml.etree.ElementTree as ET

    ns = {"a": "http://www.w3.org/2005/Atom"}
    root = ET.fromstring(xml_text)
    out: list[dict] = []
    for e in root.findall("a:entry", ns):
        def _t(tag: str) -> str:
            el = e.find(f"a:{tag}", ns)
            return " ".join((el.text or "").split()) if el is not None and el.text else ""
        raw_id = _t("id")                       # http://arxiv.org/abs/2601.01234v1
        m = _re.search(r"abs/([^v]+)", raw_id)
        cats = [c.get("term", "") for c in e.findall("a:category", ns)]
        out.append({
            "id": (m.group(1) if m else raw_id).strip(),
            "title": _t("title"),
            "abstract": _t("summary"),
            "classification": {"arxiv": cats},
            "source": {"url": raw_id},
        })
    return out


def fetch_arxiv(categories: Iterable[str] = ARXIV_CATEGORIES, max_results: int = 100,
                url: str = ARXIV_API, timeout: float = 30.0) -> list[dict]:
    """Fetch the most recent arXiv submissions in the certificate-relevant
    categories, newest first."""
    import urllib.parse
    import urllib.request

    q = " OR ".join(f"cat:{c}" for c in categories)
    params = urllib.parse.urlencode({
        "search_query": q, "sortBy": "submittedDate",
        "sortOrder": "descending", "max_results": str(max_results),
    })
    req = urllib.request.Request(f"{url}?{params}",
                                 headers={"User-Agent": "telperion-source-mining/0.1"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310
        return parse_arxiv_atom(resp.read().decode("utf-8"))


def arxiv_source(categories: Iterable[str] = ARXIV_CATEGORIES, max_results: int = 100) -> Source:
    return Source(name="arxiv", lead_type=LEAD_RAW,
                  fetch=lambda: fetch_arxiv(categories, max_results),
                  default_topics=("rh", "bg", "pvsnp"))


# --------------------------------------------------------------------------- #
# Source registry — adapters register here; external ones imported lazily.     #
# --------------------------------------------------------------------------- #

def palomar_source(use_feed: bool = False) -> Source:
    from . import palomar_mine as pm
    return Source(name="palomar", lead_type=LEAD_FORMALIZED,
                  fetch=(pm.fetch_feed if use_feed else pm.fetch_registry))


def build_source(name: str) -> Source:
    """Resolve a source by name (lazy imports keep optional adapters/credentials
    out of the import path)."""
    name = name.lower()
    if name == "palomar":
        return palomar_source()
    if name == "palomar-feed":
        return palomar_source(use_feed=True)
    if name == "arxiv":
        return arxiv_source()
    if name in ("github", "mathlib"):
        from .source_mining_github import github_source
        return github_source()
    if name == "challenges":
        # Local-clone adapter: needs a path + repo name, supplied via env
        # (TELPERION_CHALLENGE_REPO_PATH / _NAME) since build_source is zero-arg.
        import os
        path = os.environ.get("TELPERION_CHALLENGE_REPO_PATH")
        rname = os.environ.get("TELPERION_CHALLENGE_REPO_NAME", "local/checkout")
        if not path:
            raise ValueError(
                "challenges source needs TELPERION_CHALLENGE_REPO_PATH "
                "(a local formalization-repo clone with ComparatorChallenges/)")
        from .source_mining_challenges import challenge_source
        return challenge_source(path, rname)
    if name == "zulip":
        from .source_mining_zulip import zulip_source
        return zulip_source()
    raise ValueError(f"unknown source: {name!r} "
                     f"(known: palomar, palomar-feed, arxiv, github, zulip)")


ALL_SOURCES = ("palomar", "arxiv", "github", "zulip")


def source_report(candidates: list[MiningCandidate]) -> str:
    """Mining report that surfaces the lead_type split (formalized = ready to
    port; raw = formalize-first)."""
    lines = [f"# Source-mining report — {len(candidates)} candidate lead(s)", ""]
    formal = [c for c in candidates if c.lead_type == LEAD_FORMALIZED]
    raw = [c for c in candidates if c.lead_type == LEAD_RAW]
    for title, group, hint in (
        ("Formalized-certificate leads (build the emitter)", formal, "port"),
        ("Raw-math leads (formalize first — bigger lift)", raw, "formalize"),
    ):
        if not group:
            continue
        lines.append(f"## {title}")
        for c in group:
            fams = ", ".join(
                (f"{s['family']} → `{s['kind']}`" if s["kind"] else f"{s['family']} → **NEW**")
                for s in c.shapes)
            lines.append(f"- **[{c.source_name}:{c.entry_id}]** {c.title}  "
                         f"(score {c.score}, topics {','.join(c.topics)})")
            lines.append(f"    - shapes: {fams}")
            if c.source_repo:
                lines.append(f"    - source: `{c.source_repo}`")
        lines.append("")
    return "\n".join(lines)
