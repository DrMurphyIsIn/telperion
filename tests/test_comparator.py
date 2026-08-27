"""Tests for the Comparator bridge (telperion.comparator).

Pure-Python: no Lean toolchain, no Comparator binaries.  Verifies the config
matches the ten-proofs schema, names are extracted/qualified correctly, and the
challenge scaffold restates the emitted signatures with an independent proof.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from telperion import (
    CLEAN_AXIOMS,
    LeanProfile,
    challenge_config,
    challenge_for_result,
    emitted_theorem_names,
    emitted_theorem_names_by_file,
    render_challenge_scaffold,
    render_sharded_challenge_scaffolds,
    sharded_challenge_configs,
    solution_module_of,
    write_challenge_config,
)
from telperion.provenance import EmitResult

HERE = Path(__file__).resolve().parent
FROZEN = HERE.parent / "examples" / "bernoulli" / "frozen" / "Bernoulli.lean"
R7_FROZEN = HERE.parent / "examples" / "r7_starofhubs" / "frozen"

_TWO = """\
import Mathlib

namespace Bernoulli

theorem bernoulli_k1 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 0 := by
  positivity

theorem bernoulli_k2 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x ^ 2 := by
  positivity

end Bernoulli
"""


def _result(files):
    return EmitResult(
        family_name="Bernoulli", input_hash="deadbeef" * 8,
        files=files, n_theorems=sum(f.count("theorem ") for f in files.values()),
        n_checks=2,
    )


def test_names_qualified_and_ordered():
    res = _result({"Bernoulli.lean": _TWO})
    prof = LeanProfile(namespace=("Bernoulli",))
    assert emitted_theorem_names(res, prof) == [
        "Bernoulli.bernoulli_k1", "Bernoulli.bernoulli_k2"
    ]


def test_names_no_namespace():
    res = _result({"Foo.lean": "theorem a : True := trivial\ntheorem b : True := trivial\n"})
    assert emitted_theorem_names(res, LeanProfile()) == ["a", "b"]


def test_solution_module_from_filename():
    assert solution_module_of(_result({"Bernoulli.lean": _TWO})) == "Bernoulli"
    assert solution_module_of(_result({"Sub/Mod.lean": "theorem a:True:=trivial"})) == "Sub.Mod"
    with pytest.raises(ValueError):
        solution_module_of(_result({"A.lean": "theorem a:True:=trivial",
                                    "B.lean": "theorem b:True:=trivial"}))


def test_config_schema_matches_ten_proofs():
    cfg = challenge_config(
        challenge_module="BernoulliChallenge", solution_module="Bernoulli",
        theorem_names=["Bernoulli.bernoulli_k1"],
    )
    # Exact field set + order of ComparatorChallenges/C_PermanentFormulaLowerBound.json
    assert list(cfg.keys()) == [
        "challenge_module", "solution_module", "theorem_names",
        "permitted_axioms", "enable_nanoda",
    ]
    assert cfg["permitted_axioms"] == list(CLEAN_AXIOMS)
    assert cfg["enable_nanoda"] is True
    # JSON round-trips
    assert json.loads(json.dumps(cfg)) == dict(cfg)


def test_config_rejects_degenerate_inputs():
    with pytest.raises(ValueError):
        challenge_config(challenge_module="C", solution_module="S", theorem_names=[])
    with pytest.raises(ValueError):
        challenge_config(challenge_module="C", solution_module="S",
                         theorem_names=["x"], permitted_axioms=[])
    with pytest.raises(ValueError):
        challenge_config(challenge_module="", solution_module="S", theorem_names=["x"])


def test_challenge_for_result_end_to_end(tmp_path):
    res = _result({"Bernoulli.lean": _TWO})
    prof = LeanProfile(namespace=("Bernoulli",))
    cfg = challenge_for_result(res, prof, challenge_module="BernoulliChallenge")
    assert cfg["solution_module"] == "Bernoulli"
    assert cfg["theorem_names"] == ["Bernoulli.bernoulli_k1", "Bernoulli.bernoulli_k2"]
    p = write_challenge_config(tmp_path / "c.json", cfg)
    assert json.loads(p.read_text())["challenge_module"] == "BernoulliChallenge"


def test_scaffold_restates_signatures_with_independent_proof():
    res = _result({"Bernoulli.lean": _TWO})
    prof = LeanProfile(namespace=("Bernoulli",))
    lean = render_challenge_scaffold(res, prof, module_name="BernoulliChallenge")
    assert "import Mathlib" in lean
    assert "namespace Bernoulli" in lean and "end Bernoulli" in lean
    # same signatures ...
    assert "theorem bernoulli_k1 (x : ℝ) (hx : 0 ≤ x) :" in lean
    assert "0 ≤ x ^ 2" in lean
    # ... proved independently of Telperion's `have hkey ... rw` certificate
    assert lean.count(":= by\n  positivity") == 2
    assert "hkey" not in lean


@pytest.mark.skipif(not FROZEN.exists(), reason="frozen Bernoulli.lean not present")
def test_against_real_frozen_output():
    res = _result({"Bernoulli.lean": FROZEN.read_text()})
    prof = LeanProfile(namespace=("Bernoulli",))
    names = emitted_theorem_names(res, prof)
    assert names == [f"Bernoulli.bernoulli_k{k}" for k in range(2, 7)]
    cfg = challenge_for_result(res, prof, challenge_module="BernoulliChallenge")
    assert len(cfg["theorem_names"]) == 5


# --- sharded (multi-file) emits ----------------------------------------------

_BASE = "Ns.Sub.Cells"


def _sharded_result():
    def shard(names):
        body = "\n\n".join(
            f"theorem {n} (x : ℝ) (hx : 0 ≤ x) :\n    0 ≤ x ^ 2 := by\n  positivity"
            for n in names
        )
        return f"import Mathlib\n\nnamespace Ns\nnamespace Sub\n\n{body}\n\nend Sub\nend Ns\n"
    # emit() names shard files from module_base's LAST component: Cells.lean, Cells2.lean, ...
    return _result({
        "Cells.lean": shard(["a1", "a2"]),
        "Cells2.lean": shard(["b1"]),
        "Cells3.lean": shard(["c1", "c2"]),
    })


def test_sharded_configs_one_per_shard():
    res = _sharded_result()
    prof = LeanProfile(namespace=("Ns", "Sub"))
    configs = sharded_challenge_configs(res, prof, module_base=_BASE)
    assert [c["solution_module"] for c in configs] == [
        "Ns.Sub.Cells", "Ns.Sub.Cells2", "Ns.Sub.Cells3"
    ]
    assert [c["challenge_module"] for c in configs] == [
        "Ns.Sub.CellsChallenge", "Ns.Sub.Cells2Challenge", "Ns.Sub.Cells3Challenge"
    ]
    # each shard's own theorems, qualified, partitioned across configs
    assert configs[0]["theorem_names"] == ["Ns.Sub.a1", "Ns.Sub.a2"]
    assert configs[1]["theorem_names"] == ["Ns.Sub.b1"]
    assert configs[2]["theorem_names"] == ["Ns.Sub.c1", "Ns.Sub.c2"]
    all_names = [n for c in configs for n in c["theorem_names"]]
    assert len(all_names) == len(set(all_names)) == 5  # disjoint, complete


def test_sharded_scaffolds_standalone_and_independent():
    res = _sharded_result()
    prof = LeanProfile(namespace=("Ns", "Sub"))
    scaffolds = render_sharded_challenge_scaffolds(res, prof, module_base=_BASE)
    assert list(scaffolds) == [
        "CellsChallenge.lean", "Cells2Challenge.lean", "Cells3Challenge.lean"
    ]
    for text in scaffolds.values():
        assert "import Mathlib" in text
        # standalone: challenge does NOT import the solution shards
        assert "import Ns.Sub.Cells" not in text
        assert "namespace Ns\nnamespace Sub" in text
    assert scaffolds["Cells2Challenge.lean"].count(":= by\n  positivity") == 1


def test_by_file_names_and_shard_module_edge_cases():
    res = _sharded_result()
    prof = LeanProfile(namespace=("Ns", "Sub"))
    by_file = emitted_theorem_names_by_file(res, prof)
    assert list(by_file) == ["Cells.lean", "Cells2.lean", "Cells3.lean"]
    assert by_file["Cells.lean"] == ["Ns.Sub.a1", "Ns.Sub.a2"]
    # a file that isn't a shard of the base is rejected loudly
    from telperion.comparator import _shard_module_for
    with pytest.raises(ValueError):
        _shard_module_for("Unrelated.lean", _BASE)


@pytest.mark.skipif(not (R7_FROZEN / "Cells.lean").exists(),
                    reason="frozen r7 shards not present")
def test_against_real_sharded_frozen_r7():
    files = {p.name: p.read_text() for p in R7_FROZEN.glob("Cells*.lean")}
    res = _result(files)
    # mirrors examples/r7_starofhubs/family.py profile() (namespace + heartbeats option)
    prof = LeanProfile(namespace=("R7Hyps", "StarOfHubs"),
                       options=("set_option maxHeartbeats 1600000",))
    base = "R7Hyps.StarOfHubs.Cells"
    configs = sharded_challenge_configs(res, prof, module_base=base)
    # 9 shards -> modules Cells, Cells2 .. Cells9
    assert [c["solution_module"] for c in configs] == (
        ["R7Hyps.StarOfHubs.Cells"]
        + [f"R7Hyps.StarOfHubs.Cells{i}" for i in range(2, 10)]
    )
    total = sum(len(c["theorem_names"]) for c in configs)
    assert total == 972  # the whole star-of-hubs discharge
    for c in configs:
        assert c["permitted_axioms"] == list(CLEAN_AXIOMS)
        assert all(n.startswith("R7Hyps.StarOfHubs.") for n in c["theorem_names"])
    # every listed theorem is DECLARED in its own solution shard (no cross-shard names)
    scaffolds = render_sharded_challenge_scaffolds(res, prof, module_base=base)
    assert len(scaffolds) == 9
    assert "set_option maxHeartbeats 1600000" in scaffolds["Cells2Challenge.lean"]
