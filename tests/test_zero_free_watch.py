"""The zero-free watcher classifies without the network and diffs against the seen-list."""
import json
from telperion import zero_free_watch as w


def test_classify_tiers():
    assert w.classify("The Quasi Riemann Hypothesis") == ("strip", "Quasi Riemann")
    assert w.classify("A zero-free half-plane for Hecke L-functions")[0] == "strip"
    assert w.classify("On the de Bruijn-Newman constant")[0] == "dbn"
    assert w.classify("Newman's conjecture for the extended Selberg class")[0] == "dbn"
    assert w.classify("A sextic large sieve")[0] == "input"
    assert w.classify("An unconditional first moment for cubic Gauss sums")[0] == "input"
    assert w.classify("Log-abundance in characteristic zero") is None
    assert w.classify("Critical bond and site percolation on the cubic lattice") is None


def test_openai_directory_names_and_seen_list(tmp_path):
    entries = [
        {"name": "The-Quasi-Riemann-Hypothesis-October-5-2026", "type": "dir"},
        {"name": "An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026", "type": "dir"},
        {"name": "Log-abundance-in-characteristic-zero-September-24-2026", "type": "dir"},
        {"name": "README.md", "type": "file"},
    ]
    state = tmp_path / "seen.json"
    hits = w.poll(state, openai_entries=entries, arxiv_entries=[], update_state=True)
    assert {h.entry_id for h in hits} == {"The-Quasi-Riemann-Hypothesis-October-5-2026",
                                          "An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026"}
    assert [h.tier for h in sorted(hits, key=lambda h: h.tier)] == ["input", "strip"]
    # second poll: nothing new
    assert w.poll(state, openai_entries=entries, arxiv_entries=[]) == []
    assert len(json.loads(state.read_text())["seen"]) == 2


def test_arxiv_feed_parse_and_report():
    xml = """<?xml version="1.0" encoding="UTF-8"?>
<feed xmlns="http://www.w3.org/2005/Atom">
  <entry><id>http://arxiv.org/abs/2610.99999v1</id><title>A zero-free strip for the Riemann
   zeta function</title><summary>We show zeta has no zeros with Re s &gt; 0.8.</summary>
   <published>2026-10-11T00:00:00Z</published></entry>
  <entry><id>http://arxiv.org/abs/2610.11111v1</id><title>Counting points on curves</title>
   <summary>Unrelated.</summary><published>2026-10-11T00:00:00Z</published></entry>
</feed>"""
    entries = w.parse_arxiv_feed(xml)
    assert [e["id"] for e in entries] == ["2610.99999v1", "2610.11111v1"]
    hits = w.classify_arxiv_entries(entries)
    assert len(hits) == 1 and hits[0].tier == "strip" and hits[0].date == "2026-10-11"
    rep = w.report(hits)
    assert "ACTION" in rep and "2610.99999v1" in rep
    assert w.report([]) == "zero-free watch: nothing new."
