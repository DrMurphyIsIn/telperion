"""Comparator-challenge ingest adapter: offline parse/find/ingest + honest
skip-gating for the optional comparator run + GitHub-repo-list extension."""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.source_mining import LEAD_FORMALIZED, build_source, mine_source  # noqa: E402
from telperion.source_mining_challenges import (  # noqa: E402
    challenge_source, find_challenge_configs, ingest_challenges,
    parse_challenge_config, run_comparator_check,
)
from telperion.source_mining_github import GITHUB_REPOS  # noqa: E402

_NS_CFG = {
    "challenge_module": "ComparatorChallenges.NavierStokes",
    "solution_module": "NavierStokes.ComparatorSolution",
    "enable_nanoda": True,
    "theorem_names": [
        "NavierStokes.Comparator.navier_stokes_breakdown_R3",
        "NavierStokes.Comparator.navier_stokes_breakdown_periodic",
    ],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
}


def _mk_repo(tmp_path: Path) -> Path:
    d = tmp_path / "repo" / "ComparatorChallenges"
    d.mkdir(parents=True)
    (d / "NavierStokes.json").write_text(json.dumps(_NS_CFG))
    (d / "broken.json").write_text("{not json")
    (d / "unrelated.json").write_text(json.dumps({"foo": 1}))
    return tmp_path / "repo"


def test_parse_challenge_config():
    e = parse_challenge_config(_NS_CFG, "openai/NavierStokesAndEuler",
                               "ComparatorChallenges/NavierStokes.json")
    assert e["id"] == "openai/NavierStokesAndEuler#challenge:NavierStokes"
    assert "navier_stokes_breakdown_R3" in e["title"]
    assert e["source"]["kind"] == "comparator-challenge"
    assert parse_challenge_config({"foo": 1}, "r", "f.json") is None


def test_find_and_ingest(tmp_path):
    repo = _mk_repo(tmp_path)
    cfgs = find_challenge_configs(repo)
    assert any(p.name == "NavierStokes.json" for p in cfgs)
    entries = ingest_challenges(repo, "openai/NavierStokesAndEuler")
    assert len(entries) == 1  # broken + unrelated skipped
    assert entries[0]["source"]["theorem_names"]


def test_challenge_source_mines(tmp_path):
    repo = _mk_repo(tmp_path)
    src = challenge_source(repo, "openai/NavierStokesAndEuler")
    assert src.lead_type == LEAD_FORMALIZED
    cands = mine_source(src, src.fetch())
    assert isinstance(cands, list)  # classification ran (content-dependent hits)


def test_build_source_env_gating(tmp_path, monkeypatch):
    monkeypatch.delenv("TELPERION_CHALLENGE_REPO_PATH", raising=False)
    with pytest.raises(ValueError, match="TELPERION_CHALLENGE_REPO_PATH"):
        build_source("challenges")
    repo = _mk_repo(tmp_path)
    monkeypatch.setenv("TELPERION_CHALLENGE_REPO_PATH", str(repo))
    monkeypatch.setenv("TELPERION_CHALLENGE_REPO_NAME", "openai/NavierStokesAndEuler")
    src = build_source("challenges")
    assert len(src.fetch()) == 1


def test_run_comparator_skips_without_lakefile(tmp_path, monkeypatch):
    # even with lake on PATH, a repo without a lakefile is an honest skip
    repo = _mk_repo(tmp_path)
    res = run_comparator_check(repo, repo / "ComparatorChallenges" / "NavierStokes.json")
    assert res["status"] == "skipped"


def test_github_repo_list_extended():
    for r in ("openai/NavierStokesAndEuler", "anthropics/zeta-23-lean",
              "AxiomMath/ZetaZeros"):
        assert r in GITHUB_REPOS
