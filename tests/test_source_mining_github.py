"""GitHub-repos source adapter — offline unit tests (no network).

Exercises the pure commit-JSON normalizer (`parse_github_commits`): id/title/
abstract extraction, merge-commit skipping, and that a real-sounding theorem
commit flows through the shared classifier into a formalized-certificate lead.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.palomar_mine import classify_entry  # noqa: E402
from telperion.source_mining import LEAD_FORMALIZED  # noqa: E402
from telperion.source_mining_github import (  # noqa: E402
    GITHUB_REPOS,
    github_source,
    parse_github_commits,
)

REPO = "leanprover-community/mathlib4"

# Real-shaped GitHub commit JSON (trimmed to the fields the parser reads).
COMMITS = [
    {
        "sha": "9a1338a6a1a8eb784150b180bee61950c418eca9",
        "commit": {
            "author": {"date": "2026-09-08T14:44:26Z"},
            "message": "feat: add Jensen polynomial hyperbolicity for degree 3\n\n"
                        "Proves the degree-3 Jensen polynomials associated to the "
                        "Riemann xi function are hyperbolic (real-rooted).",
        },
        "html_url": "https://github.com/leanprover-community/mathlib4/commit/9a1338a6a1",
    },
    {
        "sha": "5432597b56357d43e4184241d03940b11aaad5f4",
        "commit": {
            "author": {"date": "2026-09-08T14:44:23Z"},
            "message": "Merge pull request #41557 from lakesare/convolution",
        },
        "html_url": "https://github.com/leanprover-community/mathlib4/commit/5432597b56",
    },
    {
        "sha": "0000000000000000000000000000000000000000",
        "commit": {
            "author": {"date": "2026-09-07T00:00:00Z"},
            "message": "chore: bump toolchain to nightly",
        },
        "html_url": "https://github.com/leanprover-community/mathlib4/commit/0000000000",
    },
]


def test_parse_extracts_id_title_abstract():
    entries = parse_github_commits(COMMITS, REPO)
    # merge commit skipped -> 2 of 3 remain.
    assert len(entries) == 2
    jensen = entries[0]
    assert jensen["id"] == f"{REPO}@9a1338a6a1a8"          # repo@sha[:12]
    assert jensen["title"] == "feat: add Jensen polynomial hyperbolicity for degree 3"
    assert jensen["abstract"].startswith("feat: add Jensen polynomial")
    assert "hyperbolic (real-rooted)" in jensen["abstract"]  # full message, not just first line
    assert jensen["source"] == {"repo": REPO, "url": COMMITS[0]["html_url"]}


def test_merge_commits_skipped():
    entries = parse_github_commits(COMMITS, REPO)
    assert all(not e["title"].startswith("Merge ") for e in entries)
    assert all("41557" not in e["id"] for e in entries)


def test_jensen_commit_classifies_as_formalized_lead():
    entries = parse_github_commits(COMMITS, REPO)
    cand = classify_entry(entries[0])
    assert cand is not None, "Jensen hyperbolicity commit should classify"
    # 'jensen' is an rh-topic keyword.
    assert "rh" in cand.topics
    # real-rootedness / hyperbolicity shape maps onto the `interlacing` emitter.
    families = {s["family"] for s in cand.shapes}
    kinds = {s["kind"] for s in cand.shapes}
    assert "real-rootedness / hyperbolicity" in families
    assert "interlacing" in kinds


def test_toolchain_bump_does_not_classify():
    entries = parse_github_commits(COMMITS, REPO)
    # the chore commit has no topic/shape signal.
    assert classify_entry(entries[1]) is None


def test_github_source_is_formalized():
    src = github_source()
    assert src.name == "github"
    assert src.lead_type == LEAD_FORMALIZED
    assert callable(src.fetch)
    assert "dwrensha/compfiles" in GITHUB_REPOS
