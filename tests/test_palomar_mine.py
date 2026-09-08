"""Palomar certificate mining — offline unit tests (no network).

Exercises the pure classification core (topic + shape detection, ranking, trust
boundary), the mining report, and the incremental `poll` subroutine with an
injected fetch (so "regularly poll Palomar for new candidate emitters" is tested
deterministically without hitting the registry).
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.palomar_mine import (  # noqa: E402
    classify_entry,
    mine,
    mining_report,
    parse_feed,
    poll,
    load_seen,
)

FEED_XML = """<?xml version='1.0' encoding='utf-8'?>
<rss version="2.0"><channel><title>Palomar</title>
  <item>
    <title>Li's criterion for the Riemann Hypothesis</title>
    <link>https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-05-000005&amp;version=1</link>
    <description>RiemannHypothesis iff every Li-Keiper coefficient of the completed xi function
      has nonnegative real part &amp;quot;λ_n&amp;quot;.</description>
  </item>
  <item>
    <title>Adjunctions in category theory</title>
    <link>https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-01-000099&amp;version=2</link>
    <description>Adjoint functors and natural transformations.</description>
  </item>
</channel></rss>"""


# --- synthetic fixtures modelling real registry entries -------------------- #

LI = {
    "id": "P-LI", "title": "Li's criterion for the Riemann Hypothesis",
    "abstract": "RiemannHypothesis holds iff every Li-Keiper coefficient of the completed xi "
                "function has nonnegative real part.",
    "classification": {"msc": ["11M26", "11M06", "30D15"]},
    "source": {"repo": "nicholasbulka/li-criterion-rh-equivalence-lean"},
}
BOLLOBAS = {
    "id": "P-BN", "title": "A proof of the Bollobas-Nikiforov conjecture in Lean",
    "abstract": "For a finite simple graph G with adjacency eigenvalues, a positive semidefinite "
                "matrix theorem bounds the spectral quantity; Laplacian.",
    "classification": {"msc": ["05C50", "15B48", "15A18"]},
    "source": {"repo": "example/bollobas-nikiforov"},
}
PERM_TREE = {
    "id": "P-PERM", "title": "Cotangent permanent evaluation",
    "abstract": "Exact evaluation of a permanent via a cavity recursion over the spanning tree "
                "Laplacian of a graph.",
    "classification": {"msc": ["11C20", "15A15", "05C05"]},
    "source": {"repo": "example/permanent"},
}
ARB = {
    "id": "P-ARB", "title": "Zeta zero localization by interval arithmetic",
    "abstract": "Locates nontrivial zeros of the Riemann zeta function on the critical line from "
                "Arb interval-arithmetic enclosures; argument principle winding count.",
    "classification": {"msc": ["11M26"]},
    "source": {"repo": "example/zeta-loc"},
}
IRRELEVANT = {
    "id": "P-CAT", "title": "Adjunctions in category theory",
    "abstract": "A formalization of adjoint functors and natural transformations.",
    "classification": {"msc": ["18A40"]},
    "source": {"repo": "example/cat"},
}


def test_li_criterion_is_a_new_shape_candidate_under_rh():
    c = classify_entry(LI)
    assert c is not None
    assert "rh" in c.topics
    fams = {s["family"]: s for s in c.shapes}
    assert "Li positivity ladder" in fams
    assert fams["Li positivity ladder"]["kind"] is None          # a NEW candidate shape
    assert c.has_new_shape
    assert c.source_repo == "nicholasbulka/li-criterion-rh-equivalence-lean"


def test_bollobas_maps_onto_existing_psd_and_inertia_emitters():
    c = classify_entry(BOLLOBAS)
    assert c is not None and "bg" in c.topics
    kinds = {s["kind"] for s in c.shapes}
    assert "psd_form" in kinds                                    # SOS/PSD -> existing
    assert "rank_trace_scalar" in kinds                           # eigenvalue/inertia -> existing
    assert not c.has_new_shape                                    # both map onto existing tooling


def test_permanent_tree_is_bg_cavity_new_shape():
    c = classify_entry(PERM_TREE)
    assert c is not None and "bg" in c.topics
    fams = {s["family"] for s in c.shapes}
    assert "permanent / matching (BG cavity)" in fams
    assert c.has_new_shape


def test_topic_filter_excludes_off_topic():
    # LI is a pure-RH entry: it must vanish when only BG is requested.
    assert classify_entry(LI, topics=["bg"]) is None
    assert classify_entry(LI, topics=["rh"]) is not None


def test_trust_boundary_flagged_for_arb_enclosures():
    c = classify_entry(ARB)
    assert c is not None and c.trust_boundary is True
    # and a purely kernel-internal entry is not flagged
    assert classify_entry(BOLLOBAS).trust_boundary is False


def test_irrelevant_entry_is_ignored():
    assert classify_entry(IRRELEVANT) is None


def test_mine_ranks_by_score_and_filters():
    cands = mine([IRRELEVANT, LI, BOLLOBAS, PERM_TREE, ARB])
    ids = [c.entry_id for c in cands]
    assert "P-CAT" not in ids                                     # filtered (no topic/shape)
    # scores are non-increasing
    assert all(cands[i].score >= cands[i + 1].score for i in range(len(cands) - 1))
    # a high min_score prunes the thin candidates
    assert all(c.score >= 4 for c in mine([LI, BOLLOBAS, PERM_TREE, ARB], min_score=4))


def test_mining_report_sections():
    rep = mining_report(mine([LI, BOLLOBAS, PERM_TREE]))
    assert "New candidate emitter shapes" in rep
    assert "Map onto existing emitters" in rep
    assert "**NEW**" in rep and "`psd_form`" in rep


def test_poll_is_incremental(tmp_path):
    state = tmp_path / "seen.json"
    batch1 = [LI, BOLLOBAS]
    # first poll: empty seen -> both classified
    first = poll(state, fetch=lambda url: batch1)
    assert {c.entry_id for c in first} == {"P-LI", "P-BN"}
    assert load_seen(state) == {"P-LI", "P-BN"}
    # second poll, same registry -> nothing new
    assert poll(state, fetch=lambda url: batch1) == []
    # a new entry appears -> only it is surfaced
    third = poll(state, fetch=lambda url: batch1 + [PERM_TREE])
    assert {c.entry_id for c in third} == {"P-PERM"}
    assert load_seen(state) == {"P-LI", "P-BN", "P-PERM"}


def test_parse_feed_extracts_id_title_abstract():
    entries = parse_feed(FEED_XML)
    assert len(entries) == 2
    e0 = entries[0]
    assert e0["id"] == "PALOMAR-2026-09-05-000005"          # parsed from the link ?id=
    assert e0["title"].startswith("Li's criterion")
    assert '"λ_n"' in e0["abstract"]                        # &quot; unescaped to "


def test_feed_entries_classify_without_msc():
    # RSS entries carry no structured MSC; title+abstract must still classify.
    e = parse_feed(FEED_XML)[0]
    c = classify_entry(e)
    assert c is not None and "rh" in c.topics
    assert any(s["family"] == "Li positivity ladder" for s in c.shapes)


def test_poll_over_feed_is_incremental(tmp_path):
    state = tmp_path / "seen_feed.json"
    # only the Li entry is a candidate; both ids are recorded as seen.
    got = poll(state, fetch=lambda url: parse_feed(FEED_XML))
    assert {c.entry_id for c in got} == {"PALOMAR-2026-09-05-000005"}
    assert load_seen(state) == {"PALOMAR-2026-09-05-000005", "PALOMAR-2026-09-01-000099"}
    assert poll(state, fetch=lambda url: parse_feed(FEED_XML)) == []


def test_poll_topic_scoping(tmp_path):
    state = tmp_path / "seen_rh.json"
    got = poll(state, topics=["rh"], fetch=lambda url: [LI, PERM_TREE])
    # PERM_TREE is BG-only; under an rh-scoped poll only LI is a candidate,
    # but BOTH are still recorded as seen (so they never re-surface).
    assert {c.entry_id for c in got} == {"P-LI"}
    assert load_seen(state) == {"P-LI", "P-PERM"}
