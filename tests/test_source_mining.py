"""Source-monitoring framework — offline unit tests (core + arXiv adapter).

Exercises the arXiv Atom parser, lead_type tagging (raw vs formalized), the
generalized incremental `poll_source` (injected fetch), the lead_type-split
report, and source resolution.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.source_mining import (  # noqa: E402
    LEAD_FORMALIZED,
    LEAD_RAW,
    Source,
    arxiv_source,
    build_source,
    mine_source,
    parse_arxiv_atom,
    poll_source,
    source_report,
)
from telperion.palomar_mine import load_seen  # noqa: E402

ARXIV_ATOM = """<?xml version="1.0" encoding="UTF-8"?>
<feed xmlns="http://www.w3.org/2005/Atom">
  <entry>
    <id>http://arxiv.org/abs/2601.01234v1</id>
    <title>A new zero-free region for the Riemann zeta function via sum-of-squares</title>
    <summary>We prove an explicit-formula positivity bound and a semidefinite
      certificate for the pair correlation of nontrivial zeros.</summary>
    <category term="math.NT"/>
    <category term="math.CO"/>
  </entry>
  <entry>
    <id>http://arxiv.org/abs/2601.05678v2</id>
    <title>Cohomology of moduli stacks</title>
    <summary>A study of derived categories with no relevance here.</summary>
    <category term="math.AG"/>
  </entry>
</feed>"""


def test_parse_arxiv_atom_extracts_id_title_summary_categories():
    entries = parse_arxiv_atom(ARXIV_ATOM)
    assert len(entries) == 2
    e0 = entries[0]
    assert e0["id"] == "2601.01234"                       # version stripped, abs/ parsed
    assert "zero-free region" in e0["title"]
    assert "pair correlation" in e0["abstract"]
    assert e0["classification"]["arxiv"] == ["math.NT", "math.CO"]


def test_arxiv_candidates_are_tagged_raw_math():
    src = arxiv_source()
    cands = mine_source(src, parse_arxiv_atom(ARXIV_ATOM))
    assert cands, "the RH/SOS arXiv entry should classify"
    c = cands[0]
    assert c.source_name == "arxiv"
    assert c.lead_type == LEAD_RAW                        # unformalized -> formalize-first
    assert "rh" in c.topics
    fams = {s["family"] for s in c.shapes}
    assert "SOS / PSD positivity" in fams or "explicit-formula / Weil positivity" in fams


def test_poll_source_is_incremental(tmp_path):
    state = tmp_path / "arxiv-seen.json"
    src = Source(name="arxiv", lead_type=LEAD_RAW,
                 fetch=lambda: parse_arxiv_atom(ARXIV_ATOM))
    first = poll_source(src, state)
    assert {c.entry_id for c in first} == {"2601.01234"}   # only the relevant one
    # both ids recorded as seen (off-topic too), so nothing re-surfaces
    assert load_seen(state) == {"2601.01234", "2601.05678"}
    assert poll_source(src, state) == []


def test_source_report_splits_by_lead_type():
    raw = Source("arxiv", LEAD_RAW, lambda: parse_arxiv_atom(ARXIV_ATOM))
    formal = Source("palomar", LEAD_FORMALIZED, lambda: [])
    cands = mine_source(raw, parse_arxiv_atom(ARXIV_ATOM))
    # fabricate a formalized candidate by re-tagging
    fc = mine_source(formal, parse_arxiv_atom(ARXIV_ATOM))
    for c in fc:
        c.lead_type = LEAD_FORMALIZED
        c.source_name = "palomar"
    rep = source_report(cands + fc)
    assert "Formalized-certificate leads (build the emitter)" in rep
    assert "Raw-math leads (formalize first" in rep


def test_build_source_resolves_known_and_rejects_unknown():
    assert build_source("arxiv").name == "arxiv"
    assert build_source("palomar").lead_type == LEAD_FORMALIZED
    try:
        build_source("nonsense")
        raised = False
    except ValueError:
        raised = True
    assert raised
