"""Zero-free-strip watcher: notice the next OpenAI-7/8-type release the day it appears.

The RH programme's strategy note (RH_PROGRAM_2026-10-10.md, SEXTIC_BOTTLENECK_2026-10-11.md) concluded
that the project's demonstrated edge is response time: three days from OpenAI's zero-free half-plane
Re s > 7/8 to a judged, registered, published Lambda <= 9/32, through the verified dbn converter
Lambda <= 2 (theta - 1/2)^2. The only thing that converter needs is a new fixed zero-free strip for zeta,
or for any element of the extended Selberg class (selberg_newman covers the lower half). This module
watches the two places such a result would appear:

* the openai/math preprint directory (GitHub contents API), where the 7/8 result was released;
* the arXiv API, math.NT, for titles/abstracts mentioning zero-free regions, the de Bruijn-Newman
  constant, the quasi-Riemann hypothesis, higher-order theta/large-sieve inputs (the sextic bottleneck).

Design copied from palomar_mine.py: the classifier is pure (unit-testable), the network layer is thin,
and `poll(state_path)` diffs against the ids seen before and reports only what is new. The daily
workflow runs `poll` against the COMMITTED seen-list and FAILS when there are new hits (a red mark
someone sees, as ci-schedule-health does); whoever triages then commits the updated seen-list. Nothing
here proves anything; conjecture1_proved = False.
"""
from __future__ import annotations

import json
import re
import urllib.request
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable
from xml.etree import ElementTree as ET

OPENAI_PREPRINTS_URL = "https://api.github.com/repos/openai/math/contents/preprints"
ARXIV_QUERY = (
    "http://export.arxiv.org/api/query?search_query="
    "cat:math.NT+AND+%28"
    "all:%22zero-free%22+OR+all:%22zero+free%22+OR+all:%22de+Bruijn-Newman%22+OR+all:%22de+Bruijn+Newman%22"
    "+OR+all:%22quasi-Riemann%22+OR+all:%22Riemann+hypothesis%22+OR+all:%22Selberg+class%22"
    "+OR+all:%22metaplectic+theta%22+OR+all:%22large+sieve%22+OR+all:%22Gauss+sums%22%29"
    "&sortBy=submittedDate&sortOrder=descending&max_results=60"
)

#: What the dbn converter can consume directly, or what moves the sextic bottleneck. The tiers are
#: ordered: "strip" is the jackpot (a fixed zero-free vertical strip inside the critical strip),
#: "dbn" is anything about the constant itself, "input" is an estimate the 7/8 method is bottlenecked on.
TIERS: dict[str, str] = {
    "strip": r"""zero[- ]?free\s+(half[- ]?plane|strip)|quasi[- ]?riemann|no\s+zeros?\s+(with|for)\s+re|
                 \bre\s*\(?s\)?\s*>\s*\d|half[- ]?plane\s+re\b|
                 zeros?\s+of\s+(the\s+)?(riemann\s+)?zeta[^.]*\b(real\s+part|re\s*\(?s\)?\s*(>|\\?ge|at\s+least))""",
    "dbn": r"""de\s+bruijn[- ]?newman|heat\s+flow.*(zeta|xi)|newman'?s?\s+conjecture|polymath\s?15""",
    "input": r"""(cubic|quartic|sextic|biquadratic|higher[- ]order|metaplectic)\s+(theta|gauss\s+sum|large\s+sieve)|
                 large\s+sieve.*(cubic|quartic|sextic|order)|kubota|patterson|selberg\s+class""",
}
_TIER_RE = {k: re.compile(v, re.I | re.X) for k, v in TIERS.items()}


@dataclass(frozen=True)
class WatchHit:
    source: str          # "openai" | "arxiv"
    entry_id: str        # stable id (openai directory name, arXiv id)
    title: str
    url: str
    tier: str            # "strip" | "dbn" | "input"
    matched: str         # the text fragment that matched
    date: str = ""


def classify(title: str, abstract: str = "") -> tuple[str, str] | None:
    """Return (tier, matched fragment) for the best tier, or None. Pure."""
    text = f"{title}\n{abstract}"
    for tier in ("strip", "dbn", "input"):
        m = _TIER_RE[tier].search(text)
        if m:
            return tier, m.group(0).strip()
    return None


def classify_openai_entries(entries: Iterable[dict]) -> list[WatchHit]:
    """openai/math preprint directories are named Title-Words-Month-Day-Year; the title is the name."""
    hits = []
    for e in entries:
        name = e.get("name", "")
        if e.get("type") != "dir" or not name:
            continue
        title = name.replace("-", " ")
        c = classify(title)
        if c:
            hits.append(WatchHit("openai", name, title, e.get("html_url") or f"https://github.com/openai/math/tree/main/preprints/{name}", c[0], c[1]))
    return hits


def parse_arxiv_feed(xml_text: str) -> list[dict]:
    """Atom feed -> dicts with id, title, summary, published, link. Pure."""
    ns = {"a": "http://www.w3.org/2005/Atom"}
    root = ET.fromstring(xml_text)
    out = []
    for entry in root.findall("a:entry", ns):
        def _t(tag: str) -> str:
            el = entry.find(f"a:{tag}", ns)
            return (el.text or "").strip() if el is not None else ""
        arxiv_id = _t("id").rsplit("/", 1)[-1]
        out.append({"id": arxiv_id, "title": re.sub(r"\s+", " ", _t("title")), "summary": re.sub(r"\s+", " ", _t("summary")),
                    "published": _t("published")[:10], "link": _t("id")})
    return out


def classify_arxiv_entries(entries: Iterable[dict]) -> list[WatchHit]:
    hits = []
    for e in entries:
        c = classify(e.get("title", ""), e.get("summary", ""))
        if c:
            hits.append(WatchHit("arxiv", e["id"], e.get("title", ""), e.get("link", ""), c[0], c[1], e.get("published", "")))
    return hits


def report(hits: list[WatchHit]) -> str:
    if not hits:
        return "zero-free watch: nothing new."
    order = {"strip": 0, "dbn": 1, "input": 2}
    lines = [f"zero-free watch: {len(hits)} new item(s)"]
    for h in sorted(hits, key=lambda h: (order[h.tier], h.source, h.entry_id)):
        lines.append(f"  [{h.tier:5}] {h.source:6} {h.date:10} {h.title}  <{h.url}>  (matched: {h.matched})")
    if any(h.tier == "strip" for h in hits):
        lines.append("  ACTION: a candidate zero-free strip. Read it, replay it through Comparator if it is Lean, and run the")
        lines.append("          dbn converter (RH_dbn_real_zeros_of_zeta_halfplane / selberg_newman) for a certified Lambda bound.")
    return "\n".join(lines)


# ---- network layer (thin) -------------------------------------------------------------------------

def _get(url: str, timeout: float = 30.0) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "telperion-zero-free-watch/1.0", "Accept": "application/json, application/atom+xml"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def fetch_openai(url: str = OPENAI_PREPRINTS_URL) -> list[dict]:
    return json.loads(_get(url).decode("utf-8"))


def fetch_arxiv(url: str = ARXIV_QUERY) -> list[dict]:
    return parse_arxiv_feed(_get(url).decode("utf-8"))


def load_seen(state_path: str | Path) -> set[str]:
    p = Path(state_path)
    return set(json.loads(p.read_text())["seen"]) if p.exists() else set()


def save_seen(state_path: str | Path, seen: set[str]) -> None:
    Path(state_path).write_text(json.dumps({"seen": sorted(seen)}, indent=1) + "\n")


def poll(state_path: str | Path, *, update_state: bool = False,
         openai_entries: list[dict] | None = None, arxiv_entries: list[dict] | None = None) -> list[WatchHit]:
    """Fetch both sources (or take injected entries), return hits not seen before; optionally record them."""
    seen = load_seen(state_path)
    oa = openai_entries if openai_entries is not None else fetch_openai()
    ax = arxiv_entries if arxiv_entries is not None else fetch_arxiv()
    hits = [h for h in classify_openai_entries(oa) + classify_arxiv_entries(ax) if f"{h.source}:{h.entry_id}" not in seen]
    if update_state:
        save_seen(state_path, seen | {f"{h.source}:{h.entry_id}" for h in hits})
    return hits


def main(argv: list[str] | None = None) -> int:
    import argparse, sys
    ap = argparse.ArgumentParser(description="poll openai/math + arXiv math.NT for zero-free-strip releases")
    ap.add_argument("--state", default="telperion/research/watch/zero_free_seen.json")
    ap.add_argument("--update", action="store_true", help="record the new hits in the seen-list (triage done)")
    ap.add_argument("--fail-on-new", action="store_true", help="exit 1 when there are new hits (CI red mark)")
    a = ap.parse_args(argv)
    hits = poll(a.state, update_state=a.update)
    print(report(hits))
    return 1 if (a.fail_on_new and hits) else 0


if __name__ == "__main__":
    raise SystemExit(main())
