"""Mission coverage + the empty-band driver in the standalone layout (step 2b).

The coverage gate used to assume <repo>/telperion/examples and a campaign at <repo>/telperion/missions/<c>.
In the standalone repo (<repo>/examples, <repo>/missions/<c>) every proved island node was refused for a
"missing" workflow, because the gate looked for .github one directory ABOVE the repo.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.missions.coverage import artifact_coverage_error, ci_built_islands, islands_with_lean  # noqa: E402
from telperion.missions.verify import _repo_root  # noqa: E402


def _tree(tmp_path, *, arda: bool, wire_ci: bool = True):
    """A miniature checkout with campaign `demo` and one example island `isl`."""
    repo = tmp_path / "repo"
    project = repo / "telperion" if arda else repo
    camp = project / "missions" / "demo"
    camp.mkdir(parents=True)
    lean = project / "examples" / "isl" / "lean"
    lean.mkdir(parents=True)
    (lean / "Art.lean").write_text("theorem art_thm : 1 + 1 = 2 := by norm_num\n")
    (lean / "lakefile.toml").write_text('name = "Isl"\ndefaultTargets = ["Art"]\n\n[[lean_lib]]\nname = "Art"\n')
    wf = repo / ".github" / "workflows"
    wf.mkdir(parents=True)
    prefix = "telperion/examples" if arda else "examples"
    run = "lake build" if wire_ci else "python generate.py --check"
    (wf / "ci.yml").write_text("on: push\njobs:\n  build:\n    steps:\n"
                               f"      - working-directory: {prefix}/isl/lean\n        run: {run}\n")
    return repo, camp, lean / "Art.lean"


@pytest.mark.parametrize("arda", [True, False], ids=["arda", "standalone"])
def test_repo_root_from_campaign_root(tmp_path, arda):
    repo, camp, _ = _tree(tmp_path, arda=arda)
    assert _repo_root(camp) == repo


@pytest.mark.parametrize("arda", [True, False], ids=["arda", "standalone"])
def test_wired_island_node_is_not_refused(tmp_path, arda):
    repo, camp, art = _tree(tmp_path, arda=arda)
    assert ci_built_islands(_repo_root(camp)) == {"isl"}
    assert artifact_coverage_error(art, _repo_root(camp)) is None


@pytest.mark.parametrize("arda", [True, False], ids=["arda", "standalone"])
def test_islands_with_lean_finds_the_examples_dir(tmp_path, arda):
    repo, _camp, _ = _tree(tmp_path, arda=arda)
    assert islands_with_lean(repo) == {"isl"}


def test_unwired_island_message_names_the_standalone_path(tmp_path):
    repo, camp, art = _tree(tmp_path, arda=False, wire_ci=False)
    err = artifact_coverage_error(art, _repo_root(camp))
    assert err is not None and "`lake build` in examples/isl/lean" in err
    assert "telperion/examples" not in err


def test_empty_band_driver_has_no_lab_default_output(tmp_path):
    # run_empty_band used to default its output to examples/zeta_zero_localization/lean, a legacy lab island
    from telperion.driver_empty_band import run_empty_band
    with pytest.raises(ValueError, match="out_dir"):
        run_empty_band("1/100", "99/100", "0", "55/16", winding_prec=160, write=True, check=True)


def test_unwired_island_message_names_the_arda_path(tmp_path):
    repo, camp, art = _tree(tmp_path, arda=True, wire_ci=False)
    err = artifact_coverage_error(art, _repo_root(camp))
    assert err is not None and "`lake build` in telperion/examples/isl/lean" in err


def test_coverage_message_uses_the_shared_examples_prefix(tmp_path, monkeypatch):
    # one definition of "the examples dir as a workflow spells it": telperion.paths.examples_prefix
    import telperion.missions.coverage as cov
    monkeypatch.setattr(cov, "examples_prefix", lambda project=None, repo=None: "SHARED")
    repo, camp, art = _tree(tmp_path, arda=False, wire_ci=False)
    assert "`lake build` in SHARED/isl/lean" in artifact_coverage_error(art, _repo_root(camp))
