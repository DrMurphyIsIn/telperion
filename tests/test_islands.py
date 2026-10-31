"""Step 6 Task 1: the island registry (`islands/<name>/`), its validation, `telperion island list|check`, and
the kernel policy reading each island's toolchain.

`_island(tmp, **overrides)` builds a well-formed registration that is verified unless an override says
otherwise: `replay=None` drops the [replay] section, `replay={...}` / `checks={...}` patch it, any other
keyword patches island.toml's top level, and `drop=[...]` removes top-level keys.
"""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion import islands  # noqa: E402
from telperion.checks import kernel_policy as kp  # noqa: E402

NANODA = (ROOT / "NANODA_REV").read_text().strip()
CHALLENGE = b"import Mathlib\n\nnamespace Demo.Challenge\n\ntheorem main : 1 + 1 = 2 := sorry\n\nend Demo.Challenge\n"
THEOREMS = ["Demo.Challenge.main", "Demo.Challenge.aux"]
COMMIT = "c1e023fa3ae7161219dde3dcb73f0c28ff972be2"
LOG_SHA = "ab" * 32
FP = "cd" * 32


def _toml_value(v) -> str:
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return repr(v)
    if isinstance(v, str):
        return json.dumps(v)
    if isinstance(v, list):
        return "[" + ", ".join(_toml_value(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{ " + ", ".join(f"{json.dumps(k)} = {_toml_value(x)}" for k, x in v.items()) + " }"
    raise TypeError(v)


def _island(tmp: Path, name: str = "demo", *, replay="default", checks=None, drop=(), challenge=CHALLENGE,
            comparator=None, replay_md="default", **overrides) -> Path:
    d = tmp / "islands" / name
    d.mkdir(parents=True, exist_ok=True)
    sha = hashlib.sha256(challenge).hexdigest()
    top = {
        "name": name,
        "source": "https://github.com/AxiomMath/Demo",
        "commit": COMMIT,
        "toolchain": "leanprover/lean4:v4.35.0",
        "licence": "Apache-2.0",
        "challenge_module": "Challenge.Basic",
        "solution_module": "Solution.Basic",
        "challenge_sha256": sha,
        "theorems": list(THEOREMS),
        "intended_use": "a test island",
    }
    top.update(overrides)
    for k in drop:
        top.pop(k)
    lines = [f"{k} = {_toml_value(v)}" for k, v in top.items()]
    rep = None
    if replay is not None:
        rep = {
            "date": "2026-10-31",
            "commit": top.get("commit", COMMIT),
            "challenge_sha256": top.get("challenge_sha256", sha),
            "nanoda_rev": NANODA,
            "comparator_tag": "v4.35.0",
            "log_sha256": LOG_SHA,
            "verdict": "pass",
        }
        if isinstance(replay, dict):
            rep.update(replay)
        lines.append("[replay]")
        lines += [f"{k} = {_toml_value(v)}" for k, v in rep.items()]
        lines.append("[replay.checks]")
        chk = {t: {"probe": "PROBE_ONLY", "fingerprint": FP} for t in top.get("theorems", THEOREMS)}
        if checks is not None:
            chk = checks
        lines += [f"{json.dumps(k)} = {_toml_value(v)}" for k, v in chk.items()]
    (d / "island.toml").write_text("\n".join(lines) + "\n")
    (d / "challenge.lean").write_bytes(challenge)
    if comparator is None:
        comparator = {"challenge_module": "Challenge.Basic", "solution_module": "Solution.Basic",
                      "theorem_names": list(top.get("theorems", THEOREMS)),
                      "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True}
    (d / "comparator.json").write_text(json.dumps(comparator, indent=2) + "\n")
    if replay_md == "default" and rep is not None:
        replay_md = f"# Replay of {name}\n\ncommit {rep['commit']}\nComparator log sha256 {rep['log_sha256']}\nPASS\n"
    if isinstance(replay_md, str) and replay_md != "default":
        (d / "REPLAY.md").write_text(replay_md)
    return tmp


def _git(root: Path) -> Path:
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    subprocess.run(["git", "-C", str(root), "add", "-A"], check=True)
    return root


def _cli(*argv):
    env = {**os.environ, "PYTHONPATH": str(ROOT / "src")}
    return subprocess.run([sys.executable, "-m", "telperion.cli", *argv], env=env, capture_output=True, text=True)


# --- the brief's cases -------------------------------------------------------------------------------------------

def test_valid_unreplayed_is_self_reported(tmp_path):
    root = _island(tmp_path, replay=None)
    probs = islands.island_problems(root, "demo")
    assert len(probs) == 1 and "not replayed" in probs[0]
    assert islands.status(root, "demo") == "self-reported"
    isl = islands.load_island(root, "demo")
    assert isl.name == "demo" and isl.replay is None and isl.theorems == tuple(THEOREMS)
    with pytest.raises(islands.IslandError, match=r"^island 'demo': .*not replayed"):
        islands.require_verified(root, "demo")


def test_valid_replayed_is_verified(tmp_path):
    root = _island(tmp_path)
    assert islands.island_problems(root, "demo") == []
    assert islands.status(root, "demo") == "verified"
    isl = islands.require_verified(root, "demo")
    assert isl.commit == COMMIT and isl.replay.verdict == "pass"
    assert dict(isl.replay.checks)["Demo.Challenge.main"].probe == "PROBE_ONLY"


def test_commit_change_invalidates(tmp_path):
    # the pin moved (Review Focus 1); the replay recorded for the old pin no longer counts
    root = _island(tmp_path, commit="1d7edeb4e67096f9da1b37cd4b763e8b73886655", replay={"commit": COMMIT})
    probs = islands.island_problems(root, "demo")
    assert any("replay ran at commit" in p for p in probs)
    assert islands.status(root, "demo") == "self-reported"
    with pytest.raises(islands.IslandError):
        islands.require_verified(root, "demo")


def test_challenge_copy_tamper(tmp_path):
    # a local edit to the registered copy (Review Focus 2), with the record left as it was
    root = _island(tmp_path)
    (root / "islands" / "demo" / "challenge.lean").write_bytes(CHALLENGE.replace(b"1 + 1 = 2", b"True"))
    probs = islands.island_problems(root, "demo")
    assert any("challenge.lean" in p and "sha256" in p for p in probs)
    assert islands.status(root, "demo") == "self-reported"


def test_missing_theorem_check(tmp_path):
    root = _island(tmp_path, checks={"Demo.Challenge.main": {"probe": "WITNESSED", "fingerprint": FP}})
    probs = islands.island_problems(root, "demo")
    assert any("Demo.Challenge.aux" in p and "no [replay.checks] entry" in p for p in probs)
    assert islands.status(root, "demo") == "self-reported"


@pytest.mark.parametrize("name", ["nope", "../demo", "demo/..", "Demo", "", ".", "demo\x00"])
def test_require_verified_unknown_name(tmp_path, name):
    root = _island(tmp_path)
    with pytest.raises(islands.IslandError) as ei:
        islands.require_verified(root, name)
    assert str(ei.value).startswith(f"island {name!r}: ")
    assert islands.status(root, name) == "self-reported"


def test_policy_sees_island_toolchain(tmp_path):
    _island(tmp_path, "demo")
    _island(tmp_path, "old", toolchain="leanprover/lean4:v4.34.0-rc2")
    root = _git(tmp_path)
    found = kp.find_projects(root)
    assert ("islands/demo", "leanprover/lean4:v4.35.0") in found
    assert ("islands/old", "leanprover/lean4:v4.34.0-rc2") in found
    probs = kp.policy_problems(root, {})
    assert any(p.startswith("islands/old:") and "below the floor" in p for p in probs)
    assert not any(p.startswith("islands/demo") for p in probs)
    ex = {"islands/old": {"toolchain": "leanprover/lean4:v4.34.0-rc2", "reason": "external island; nanoda"}}
    assert kp.policy_problems(root, ex) == []


def test_cli_list_and_check_exit_codes(tmp_path):
    root = _island(tmp_path, "demo")
    _island(tmp_path, "raw", replay=None)
    r = _cli("island", "list", "--root", str(root))
    assert r.returncode == 0, r.stderr
    assert "demo" in r.stdout and "verified" in r.stdout and "raw" in r.stdout and "self-reported" in r.stdout
    r = _cli("island", "check", "demo", "--root", str(root))
    assert r.returncode == 0, r.stdout + r.stderr
    r = _cli("island", "check", "raw", "--root", str(root))
    assert r.returncode == 1 and "not replayed" in r.stdout
    r = _cli("island", "check", "--root", str(root))
    assert r.returncode == 1 and "raw" in r.stdout
    r = _cli("island", "check", "nope", "--root", str(root))
    assert r.returncode == 1 and "no such island" in r.stdout
    (root / "islands" / "raw" / "island.toml").write_bytes(b"\xff\xfe not toml")
    for argv in (("island", "list"), ("island", "check"), ("island", "check", "raw")):
        r = _cli(*argv, "--root", str(root))
        assert "Traceback" not in r.stderr, r.stderr
    assert _cli("island", "list", "--root", str(root)).returncode == 0
    assert _cli("island", "check", "raw", "--root", str(root)).returncode == 1


# --- verified is all or nothing ----------------------------------------------------------------------------------

def test_extra_check_entry_invalidates(tmp_path):
    chk = {t: {"probe": "PROBE_ONLY", "fingerprint": FP} for t in THEOREMS}
    chk["Demo.Challenge.extra"] = {"probe": "PROBE_ONLY", "fingerprint": FP}
    root = _island(tmp_path, checks=chk)
    assert any("Demo.Challenge.extra" in p and "not in theorems" in p for p in islands.island_problems(root, "demo"))
    assert islands.status(root, "demo") == "self-reported"


@pytest.mark.parametrize("probe", ["VACUOUS", "REFUTED", "ERROR"])
def test_probe_must_be_probe_only_or_witnessed(tmp_path, probe):
    chk = {t: {"probe": "PROBE_ONLY", "fingerprint": FP} for t in THEOREMS}
    chk[THEOREMS[1]] = {"probe": probe, "fingerprint": FP}
    root = _island(tmp_path, checks=chk)
    assert any(probe in p for p in islands.island_problems(root, "demo"))
    assert islands.status(root, "demo") == "self-reported"


@pytest.mark.parametrize("entry", [
    {"probe": "WITNESSED", "fingerprint": "cd" * 31},
    {"probe": "WITNESSED", "fingerprint": "CD" * 32},
    {"probe": "witnessed", "fingerprint": FP},
    {"probe": "WITNESSED"},
    {"probe": "WITNESSED", "fingerprint": FP, "note": "x"},
])
def test_bad_check_entry_is_a_problem(tmp_path, entry):
    chk = {t: {"probe": "PROBE_ONLY", "fingerprint": FP} for t in THEOREMS}
    chk[THEOREMS[0]] = entry
    root = _island(tmp_path, checks=chk)
    assert islands.island_problems(root, "demo")
    assert islands.status(root, "demo") == "self-reported"


@pytest.mark.parametrize("patch,needle", [
    ({"verdict": "fail"}, "verdict"),
    ({"challenge_sha256": "ee" * 32}, "replay challenge_sha256"),
    ({"nanoda_rev": "0" * 40}, "NANODA_REV"),
    ({"comparator_tag": "v4.34.0"}, "comparator_tag"),
])
def test_replay_mismatch_invalidates(tmp_path, patch, needle):
    root = _island(tmp_path, replay=patch)
    probs = islands.island_problems(root, "demo")
    assert any(needle in p for p in probs), probs
    assert islands.status(root, "demo") == "self-reported"


@pytest.mark.parametrize("md", [None, "# Replay\nPASS\n"])
def test_replay_md_must_record_the_replay(tmp_path, md):
    root = _island(tmp_path, replay_md=md)
    assert any("REPLAY.md" in p for p in islands.island_problems(root, "demo"))
    assert islands.status(root, "demo") == "self-reported"


@pytest.mark.parametrize("cfg_patch,needle", [
    ({"enable_nanoda": False}, "enable_nanoda"),
    ({"enable_nanoda": "true"}, "enable_nanoda"),
    ({"permitted_axioms": ["propext", "Quot.sound", "Classical.choice", "sorryAx"]}, "permitted_axioms"),
    ({"theorem_names": ["Demo.Challenge.main"]}, "theorem_names"),
    ({"challenge_module": "Other.Basic"}, "challenge_module"),
    ({"extra": 1}, "unknown key"),
])
def test_comparator_json_rules(tmp_path, cfg_patch, needle):
    cfg = {"challenge_module": "Challenge.Basic", "solution_module": "Solution.Basic",
           "theorem_names": list(THEOREMS), "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
           "enable_nanoda": True}
    cfg.update(cfg_patch)
    root = _island(tmp_path, comparator=cfg)
    probs = islands.island_problems(root, "demo")
    assert any("comparator.json" in p and needle in p for p in probs), probs
    assert islands.status(root, "demo") == "self-reported"


# --- strict schema -------------------------------------------------------------------------------------------------

@pytest.mark.parametrize("over", [
    {"commit": COMMIT.upper()},
    {"commit": COMMIT[:39]},
    {"challenge_sha256": "AB" * 32},
    {"challenge_sha256": "ab" * 31},
    {"toolchain": "leanprover/lean4:4.35.0"},
    {"toolchain": "leanprover/lean4:v4.35.0\n"},
    {"toolchain": "leanprover/lean4:nightly-2026-10-01"},
    {"name": "other"},
    {"theorems": []},
    {"theorems": ["Demo.Challenge.main", "Demo.Challenge.main"]},
    {"theorems": ["Demo.Challenge.mαin"]},
    {"theorems": ["Demo..main"]},
    {"theorems": ["Demo.Challenge.main x"]},
    {"theorems": "Demo.Challenge.main"},
    {"challenge_module": "Challenge/Basic"},
    {"source": "http://example.com/x"},
    {"licence": ""},
    {"unknown_key": "x"},
    {"commit": 7},
])
def test_strict_schema(tmp_path, over):
    root = _island(tmp_path, **over)
    assert islands.island_problems(root, "demo")
    assert islands.status(root, "demo") == "self-reported"
    with pytest.raises(islands.IslandError):
        islands.load_island(root, "demo")


@pytest.mark.parametrize("key", ["source", "commit", "toolchain", "theorems", "challenge_sha256", "intended_use"])
def test_missing_key_is_a_problem(tmp_path, key):
    root = _island(tmp_path, drop=[key], replay=None)
    assert any(key in p for p in islands.island_problems(root, "demo"))


@pytest.mark.parametrize("patch", [{"extra": "x"}, {"date": "31 Oct 2026"}, {"verdict": "PASS"},
                                   {"comparator_tag": "4.35.0"}, {"log_sha256": "ab" * 31}])
def test_strict_replay_schema(tmp_path, patch):
    root = _island(tmp_path, replay=patch)
    assert islands.island_problems(root, "demo")
    assert islands.status(root, "demo") == "self-reported"


def test_bad_directory_name_is_a_problem(tmp_path):
    root = _island(tmp_path, "Bad_Name")
    assert islands.island_problems(root, "Bad_Name")
    assert "Bad_Name" in islands.island_names(root)[0]


# --- fail closed on every read --------------------------------------------------------------------------------------

@pytest.mark.parametrize("fname", ["island.toml", "challenge.lean", "comparator.json", "REPLAY.md"])
def test_symlinked_file_is_refused(tmp_path, fname):
    root = _island(tmp_path)
    p = root / "islands" / "demo" / fname
    real = tmp_path / f"real-{fname}"
    real.write_bytes(p.read_bytes())
    p.unlink()
    p.symlink_to(real)
    probs = islands.island_problems(root, "demo")
    assert any(fname in p and "symlink" in p for p in probs), probs
    assert islands.status(root, "demo") == "self-reported"


def test_symlinked_island_dir_is_refused(tmp_path):
    real = _island(tmp_path / "elsewhere")
    (tmp_path / "islands").mkdir()
    (tmp_path / "islands" / "demo").symlink_to(real / "islands" / "demo")
    probs = islands.island_problems(tmp_path, "demo")
    assert any("symlink" in p for p in probs)
    with pytest.raises(islands.IslandError, match="symlink"):
        islands.require_verified(tmp_path, "demo")


def test_symlinked_islands_root_is_refused(tmp_path):
    real = _island(tmp_path / "elsewhere")
    (tmp_path / "islands").symlink_to(real / "islands")
    assert any("symlink" in p for p in islands.island_problems(tmp_path, "demo"))
    names, probs = islands.island_names(tmp_path)
    assert names == [] and any("symlink" in p for p in probs)
    assert _cli("island", "list", "--root", str(tmp_path)).returncode == 1


@pytest.mark.parametrize("content,needle", [
    (b"\xff\xfe", "UTF-8"),
    (b"name = ", "TOML"),
    (b"x = 1\n" + b"#" * (1 << 20), "larger than"),
])
def test_unreadable_island_toml_is_a_problem(tmp_path, content, needle):
    root = _island(tmp_path)
    (root / "islands" / "demo" / "island.toml").write_bytes(content)
    probs = islands.island_problems(root, "demo")
    assert any(needle in p for p in probs), probs
    with pytest.raises(islands.IslandError):
        islands.load_island(root, "demo")


def test_island_dir_that_is_a_file_is_refused(tmp_path):
    (tmp_path / "islands").mkdir()
    (tmp_path / "islands" / "demo").write_text("x")
    assert islands.island_problems(tmp_path, "demo")
    with pytest.raises(islands.IslandError):
        islands.require_verified(tmp_path, "demo")


# --- kernel policy wiring -------------------------------------------------------------------------------------------

@pytest.mark.parametrize("content", [b"\xff", b"name = ", b'name = "demo"\n', b'toolchain = 4\n'])
def test_policy_garbled_island_toml_is_a_problem(tmp_path, content):
    root = _island(tmp_path)
    (root / "islands" / "demo" / "island.toml").write_bytes(content)
    _git(root)
    probs = kp.policy_problems(root, {})
    assert any(p.startswith("islands/demo:") for p in probs), probs
    assert not any(proj == "islands/demo" for proj, _ in kp.find_projects(root))


def test_policy_missing_island_toml_is_a_problem(tmp_path):
    root = _git(_island(tmp_path))
    (root / "islands" / "demo" / "island.toml").unlink()
    assert any(p.startswith("islands/demo:") for p in kp.policy_problems(root, {}))
    # an island directory that was never committed is still seen
    (root / "islands" / "fresh").mkdir()
    assert any(p.startswith("islands/fresh:") for p in kp.policy_problems(root, {}))


def test_policy_symlinked_island_is_a_problem(tmp_path):
    real = _island(tmp_path / "elsewhere", toolchain="leanprover/lean4:v4.32.0")
    (tmp_path / "islands").mkdir()
    (tmp_path / "islands" / "demo").symlink_to(real / "islands" / "demo")
    _git(tmp_path)
    assert any(p.startswith("islands/demo:") and "symlink" in p for p in kp.policy_problems(tmp_path, {}))


def test_policy_island_exception_is_not_stale_and_mismatch_is_seen(tmp_path):
    root = _git(_island(tmp_path, toolchain="leanprover/lean4:v4.34.0-rc2"))
    ex = {"islands/demo": {"toolchain": "leanprover/lean4:v4.34.0", "reason": "x"}}
    probs = kp.policy_problems(root, ex)
    assert any("islands/demo" in p and "toolchain mismatch" in p for p in probs)
    assert not any("no such project" in p for p in probs)


def test_policy_island_lean_toolchain_collision_is_a_problem(tmp_path):
    root = _island(tmp_path, toolchain="leanprover/lean4:v4.35.0")
    (root / "islands" / "demo" / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
    _git(root)
    assert any(p.startswith("islands/demo:") and "lean-toolchain" in p for p in kp.policy_problems(root, {}))
