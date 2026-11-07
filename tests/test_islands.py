"""Step 6 Tasks 1-2: the island registry (`islands/<name>/`), its validation, `telperion island list|check`, the
kernel policy reading each island's toolchain, and `island add|replay|record-replay`.

`_island(tmp, **overrides)` builds a well-formed registration that is verified unless an override says
otherwise: `replay=None` drops the [replay] section, `replay={...}` / `checks={...}` patch it, any other
keyword patches island.toml's top level, and `drop=[...]` removes top-level keys. A replayed registration carries
its archived evidence (Ruling 6) under `islands/<name>/replay/`: a Comparator log (`_log`), one probe JSON per
theorem (`_probe_doc`) and a fingerprint JSON (`_fp_doc`), all passing; the [replay] record names their sha256s.
Nothing here runs git (beyond `git init` for the policy tests), lake or lean: `fetch` and `run` are fakes.
"""
import hashlib
import json
import lzma
import os
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion import islands  # noqa: E402
from telperion.checks import kernel_policy as kp  # noqa: E402

NANODA = (ROOT / "NANODA_REV").read_text().strip()
CHALLENGE = b"import Mathlib\n\nnamespace Demo.Challenge\n\ntheorem main : 1 + 1 = 2 := sorry\n\nend Demo.Challenge\n"
CHALLENGE_SHA = hashlib.sha256(CHALLENGE).hexdigest()
THEOREMS = ["Demo.Challenge.main", "Demo.Challenge.aux"]
COMMIT = "c1e023fa3ae7161219dde3dcb73f0c28ff972be2"
FP = "cd" * 32
OLEAN = "0e" * 32
FIXTURES = ROOT / "tests" / "fixtures" / "islands"


#: What Comparator v4.35.0 exports besides the theorems, in its order (fixtures/islands/rj_spec.out): builtins, then
#: the theorems, then the permitted axioms and the kernel primitives.
EXPORT_HEAD = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
EXPORT_TAIL = ["propext", "Quot.sound", "Classical.choice", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd",
               "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
               "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk",
               "Char", "optParam", "autoParam", "semiOutParam", "outParam"]


def _log(*, name="demo", commit=COMMIT, sha=CHALLENGE_SHA, theorems=THEOREMS, nanoda=NANODA, rc=0,
         nanoda_line="nanoda kernel accepts the solution", drop=(), extra=(), before_exit=(), exports_extra=(),
         exports_drop=(), config_sha=None) -> str:
    """A passing Comparator log in the shape of the real riemann-jensen spec run (fixtures/islands/rj_spec.out):
    `drop` removes lines containing any of its strings, `extra` appends lines at the end, `before_exit` inserts
    lines just before the exit line; `exports_extra` / `exports_drop` change both export lists (as a run under
    another config would); `config_sha` adds a runner `COMPARATOR_CONFIG sha256 <hex>` line."""
    names = ", ".join(n for n in [*EXPORT_HEAD, *theorems, *EXPORT_TAIL, *exports_extra] if n not in exports_drop)
    lines = [f"ISLAND-HEADER island={name} commit={commit} challenge_sha256={sha}",
             "== demo start",
             f"COMPARATOR_NANODA {'a8' * 16} (nanoda_lib {nanoda})",
             *([f"COMPARATOR_CONFIG sha256 {config_sha}"] if config_sha else []),
             "== comparator",
             "Building Challenge.Basic",
             "warning: Challenge/Basic.lean:5:8: declaration uses `sorry`",
             f"Exporting #[{names}] from Challenge.Basic",
             "Building Solution.Basic",
             f"Exporting #[{names}] from Solution.Basic",
             "Running nanoda kernel on solution",
             nanoda_line,
             "Running Lean default kernel on solution.",
             "Lean default kernel accepts the solution",
             "Your solution is okay!",
             *before_exit,
             f"ISLAND-demo-EXIT {rc}",
             *extra]
    lines = [l for l in lines if not any(d in l for d in drop)]
    return "\n".join(lines) + "\n"


def _probe_doc(theorem, verdict="PROBE_ONLY", **patch) -> dict:
    """`telperion probe-negation --json --file <challenge>` stdout for one theorem of the challenge module."""
    doc = {"verdict": verdict, "detail": "no counterexample found", "olean_sha256": OLEAN, "olean_closure": [],
           "axioms": ["propext", "sorryAx"], "module": "Challenge.Basic", "theorem": theorem,
           "source_sha256": CHALLENGE_SHA}
    doc.update(patch)
    return doc


def _fp_doc(theorems=THEOREMS, fp=FP, **patch) -> dict:
    """`telperion fingerprint --json --import Challenge.Basic --target ... --file <challenge>` stdout."""
    doc = {"fingerprints": {t: fp for t in theorems}, "olean_sha256": OLEAN, "olean_closure": [],
           "module": "Challenge.Basic", "theorem": None, "source_sha256": CHALLENGE_SHA,
           "axioms": ["propext", "sorryAx"], "mode": "type", "trusted_env_sha256": None}
    doc.update(patch)
    return doc


def _dump(doc) -> bytes:
    return (json.dumps(doc) + "\n").encode()


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _archive(d: Path, log_text: str, probe_docs, fp_doc) -> dict:
    """Write the evidence files into `d/replay/` as record-replay archives them; the [replay] sha256 keys."""
    rd = d / "replay"
    rd.mkdir(parents=True, exist_ok=True)
    (rd / "comparator.log.xz").write_bytes(lzma.compress(log_text.encode()))
    probe_sha = {}
    for doc in probe_docs:
        raw = _dump(doc)
        probe_sha[doc["theorem"]] = _sha(raw)
        (rd / f"probe-{_sha(raw)}.json").write_bytes(raw)
    raw = _dump(fp_doc)
    (rd / "fingerprint.json").write_bytes(raw)
    return {"log_sha256": _sha(log_text.encode()), "probe_sha256": probe_sha, "fingerprint_sha256": _sha(raw)}


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
            comparator=None, replay_md="default", evidence=None, **overrides) -> Path:
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
        thms = top.get("theorems", THEOREMS)
        thms = thms if isinstance(thms, list) and all(isinstance(t, str) for t in thms) else THEOREMS
        ev = dict(evidence or {})
        log_text = ev.get("log") or _log(name=name, sha=sha, theorems=thms,
                                         commit=top["commit"] if isinstance(top.get("commit"), str) else COMMIT)
        probe_docs = ev.get("probes") or [_probe_doc(t, source_sha256=sha) for t in thms]
        shas = _archive(d, log_text, probe_docs, ev.get("fp") or _fp_doc(thms, source_sha256=sha))
        rep = {
            "date": "2026-10-31",
            "commit": top.get("commit", COMMIT),
            "challenge_sha256": top.get("challenge_sha256", sha),
            "nanoda_rev": NANODA,
            "comparator_tag": "v4.35.0",
            "verdict": "pass",
            **shas,
        }
        if isinstance(replay, dict):
            rep.update(replay)
        lines.append("[replay]")
        lines += [f"{k} = {_toml_value(v)}" for k, v in rep.items()]
        lines.append("[replay.checks]")
        chk = {t: {"probe": "PROBE_ONLY", "fingerprint": FP} for t in thms}
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
        replay_md = f"# Replay of {name}\n\nA human summary; not evidence.\n"
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


# --- the brief's cases ------------------------------------------------------------------------------------------------

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


# --- verified is all or nothing ---------------------------------------------------------------------------------------

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


@pytest.mark.parametrize("md", [None, "# Replay\nPASS\n", "\xff not even text"])
def test_replay_md_is_not_evidence(tmp_path, md):
    # Ruling 6: REPLAY.md is a generated human summary; whatever it says (or its absence) never moves the status
    root = _island(tmp_path, replay_md=None)
    if md is not None:
        (root / "islands" / "demo" / "REPLAY.md").write_text(md, encoding="utf-8", errors="surrogateescape")
    assert islands.island_problems(root, "demo") == []
    assert islands.status(root, "demo") == "verified"


def test_fabricated_replay_md_without_evidence_is_self_reported(tmp_path):
    # the Task 1 review's attack: REPLAY.md naming the pin and a log sha256, a [replay] to match, and no real log
    root = _island(tmp_path)
    rep_dir = root / "islands" / "demo" / "replay"
    for f in rep_dir.iterdir():
        f.unlink()
    rep_dir.rmdir()
    (root / "islands" / "demo" / "REPLAY.md").write_text(f"<!-- commit {COMMIT} log_sha256 {'ab' * 32} -->\n")
    probs = islands.island_problems(root, "demo")
    assert any("replay/" in p for p in probs), probs
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


# --- strict schema ----------------------------------------------------------------------------------------------------

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


# --- fail closed on every read ----------------------------------------------------------------------------------------

@pytest.mark.parametrize("fname", ["island.toml", "challenge.lean", "comparator.json", "replay/comparator.log.xz",
                                   "replay/fingerprint.json"])
def test_symlinked_file_is_refused(tmp_path, fname):
    root = _island(tmp_path)
    p = root / "islands" / "demo" / fname
    real = tmp_path / f"real-{fname.replace('/', '-')}"
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


# --- kernel policy wiring ---------------------------------------------------------------------------------------------

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


def test_policy_toolchain_goes_through_the_strict_parser(tmp_path):
    # Ruling 6 (Task 1 review, Minor 1): a trailing space made `island check` refuse the toolchain while the policy
    # stripped it and said OK; both now read island.toml through one strict parser
    root = _git(_island(tmp_path, toolchain="leanprover/lean4:v4.35.0 "))
    assert islands.status(root, "demo") == "self-reported"
    probs = kp.policy_problems(root, {})
    assert any(p.startswith("islands/demo:") and "toolchain" in p for p in probs), probs
    assert not any(proj == "islands/demo" for proj, _ in kp.find_projects(root))


# --- Task 2: the Comparator log ---------------------------------------------------------------------------------------

RJ_THEOREMS = ("RiemannJensen.Challenge.exists_isDedekindZetaContinuation",
               "RiemannJensen.Challenge.isDedekindZetaContinuation_unique",
               "RiemannJensen.Challenge.dedekind_thm_main",
               "RiemannJensen.Challenge.riemannJensen_main")
RJ_CHALLENGE_SHA = "eeae0da96ab3d5784522a5745dc46353b1a804c3ea32972be4040cd4cd73354c"


def _isl(**patch) -> "islands.Island":
    kw = dict(name="demo", source="https://github.com/AxiomMath/Demo", commit=COMMIT,
              toolchain="leanprover/lean4:v4.35.0", licence="Apache-2.0", challenge_module="Challenge.Basic",
              solution_module="Solution.Basic", challenge_sha256=CHALLENGE_SHA, theorems=tuple(THEOREMS),
              intended_use="a test island", replay=None)
    kw.update(patch)
    return islands.Island(**kw)


RJ = dict(name="riemann-jensen", source="https://github.com/AxiomMath/RiemannJensen",
          challenge_sha256=RJ_CHALLENGE_SHA, theorems=RJ_THEOREMS)


def test_real_rj_spec_log_passes():
    # the auditor-held standalone Comparator e3dcf308 log of riemann-jensen @c1e023fa (md5 76bc5e06), scrubbed of
    # sandbox paths, its 150 `Built` lines trimmed to 3 and two status glyphs replaced by ASCII
    text = (FIXTURES / "rj_spec.out").read_text()
    log = islands.parse_comparator_log(text)
    assert log.header == ("riemann-jensen", COMMIT, RJ_CHALLENGE_SHA)
    assert log.nanoda_rev == NANODA and log.exit_code == 0
    assert islands.comparator_log_problems(text, _isl(**RJ), NANODA) == []


def test_real_rj_tamper_log_fails():
    # the same run's negative control: challenge edited (2 <= d -> 3 <= d); Comparator refused it, exit 1
    text = (FIXTURES / "rj_spec_tamper.out").read_text()
    probs = islands.comparator_log_problems(text, _isl(**RJ), NANODA)
    assert any("challenge_sha256" in p for p in probs), probs
    assert any("uncaught exception" in p for p in probs), probs
    assert any("exit" in p for p in probs), probs


@pytest.mark.parametrize("line", ["nanoda kernel accepts the solution", "Nanoda kernel accepts the solution"])
def test_nanoda_accept_line_either_capitalisation(line):
    # Comparator v4.32.0 / v4.33.0-rc2 print "Nanoda ...", v4.35.0 (the real spec run) prints "nanoda ..."
    assert islands.comparator_log_problems(_log(nanoda_line=line), _isl(), NANODA) == []


def test_log_with_status_glyphs_parses():
    # lake's status glyphs (U+26A0, U+2714) are in a real log; the parser takes them as ordinary text
    text = _log(before_exit=()).replace("Building Solution.Basic",
                                        "\u26a0 [1/2] Built Demo.Thing (1s)\n\u2714 [2/2] Built Solution.Basic")
    assert islands.comparator_log_problems(text, _isl(), NANODA) == []


@pytest.mark.parametrize("text,needle", [
    (_log().split("\n", 1)[1], "ISLAND-HEADER"),                                           # no header
    ("== start\n" + _log(), "first line"),                                                 # header not first
    (_log(commit="1d7edeb4e67096f9da1b37cd4b763e8b73886655"), "commit"),
    (_log(sha="ee" * 32), "challenge_sha256"),
    (_log(name="other"), "island"),
    (_log(commit=COMMIT.upper()), "ISLAND-HEADER"),
    (_log(extra=[f"ISLAND-HEADER island=demo commit={COMMIT} challenge_sha256={CHALLENGE_SHA}"]), "ISLAND-HEADER"),
    (_log(drop=["Lean default kernel accepts"]), "Lean default kernel accepts the solution"),
    (_log(drop=["nanoda kernel accepts"]), "nanoda kernel accepts the solution"),
    (_log(drop=["Your solution is okay!"]), "Your solution is okay!"),
    (_log(extra=["Your solution is okay!"]), "more than once"),
    (_log(drop=["kernel accepts", "okay"],
          before_exit=["nanoda kernel accepts the solution Lean default kernel accepts the solution "
                       "Your solution is okay!"]), "accepts"),
    (_log().replace("nanoda kernel accepts the solution\n", "").replace(
        "Your solution is okay!\n", "Your solution is okay!\nnanoda kernel accepts the solution\n"), "order"),
    (_log(nanoda="0" * 40), "NANODA_REV"),
    (_log(drop=["COMPARATOR_NANODA"]), "COMPARATOR_NANODA"),
    (_log(extra=[f"COMPARATOR_NANODA {'a8' * 16} (nanoda_lib {NANODA})"]), "COMPARATOR_NANODA"),
    (_log(rc=1), "exit"),
    (_log(drop=["-EXIT"]), "exit"),
    (_log(extra=["ISLAND-demo-EXIT 0"]), "exit"),
    (_log(before_exit=["error: Challenge/Basic.lean:3:0: unknown identifier"]), "error"),
    (_log(before_exit=["uncaught exception: Challenge and solution theorem statement do not match"]), "uncaught"),
    (_log(before_exit=['unpermitted axiom "sorryAx" used by Demo.Challenge.main']), "axiom"),
    (_log(before_exit=["Illegal axiom detected: 'sorryAx'"]), "axiom"),
    (_log(theorems=THEOREMS[:1]), "Demo.Challenge.aux"),
    (_log(drop=["from Solution.Basic"]), "Solution.Basic"),
    (_log(extra=[f"Exporting #[{', '.join(THEOREMS)}] from Challenge.Basic"]), "Challenge.Basic"),
    (_log(extra=["ISLAND-SOMETHING else"]), "ISLAND-"),
])
def test_log_rules(text, needle):
    probs = islands.comparator_log_problems(text, _isl(), NANODA)
    assert any(needle in p for p in probs), probs


# --- Task 2: island add -----------------------------------------------------------------------------------------------

AXIOM_CONFIG = {"challenge_module": "Challenge.Basic", "solution_module": "Solution.Basic",
                "theorem_names": list(THEOREMS), "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                "enable_nanoda": True}
APACHE = "\n                                 Apache License\n                           Version 2.0, January 2004\n"


def _fake_fetch(config=None, *, head=COMMIT, challenge=CHALLENGE, toolchain="leanprover/lean4:v4.35.0\n",
                licence=APACHE, calls=None):
    def fetch(source, commit, dest):
        if calls is not None:
            calls.append((source, commit, Path(dest)))
        dest = Path(dest)
        (dest / ".git" / "info").mkdir(parents=True, exist_ok=True)      # a clone's git dir (no exclude patterns)
        (dest / "Comparator").mkdir(parents=True, exist_ok=True)
        (dest / "Challenge").mkdir(exist_ok=True)
        (dest / "Comparator" / "comparator.json").write_text(json.dumps(config or AXIOM_CONFIG, indent=4) + "\n")
        (dest / "Challenge" / "Basic.lean").write_bytes(challenge)
        (dest / "lean-toolchain").write_text(toolchain)
        if licence is not None:
            (dest / "LICENSE").write_text(licence)
        return head
    return fetch


def _add(tmp_path, name="demo", **kw):
    fetch = kw.pop("fetch", None) or _fake_fetch()
    run = kw.pop("run", None) or FakeRun()
    return islands.add_island(tmp_path / "repo", name, "https://github.com/AxiomMath/Demo", COMMIT, "a test island",
                              fetch=fetch, run=run, tools=tmp_path / "tools", **kw)


def test_add_writes_registration(tmp_path):
    calls = []
    isl = _add(tmp_path, fetch=_fake_fetch(calls=calls))
    assert calls == [("https://github.com/AxiomMath/Demo", COMMIT, tmp_path / "tools" / "islands" / "demo" / "src")]
    d = tmp_path / "repo" / "islands" / "demo"
    assert sorted(p.name for p in d.iterdir()) == ["REPLAY.md", "challenge.lean", "comparator.json", "island.toml"]
    assert (d / "challenge.lean").read_bytes() == CHALLENGE
    doc = tomllib.loads((d / "island.toml").read_text())
    assert "replay" not in doc
    assert doc["commit"] == COMMIT and doc["challenge_sha256"] == CHALLENGE_SHA
    assert doc["toolchain"] == "leanprover/lean4:v4.35.0" and doc["licence"] == "Apache-2.0"
    assert doc["theorems"] == THEOREMS and doc["intended_use"] == "a test island"
    cfg = json.loads((d / "comparator.json").read_text())
    assert cfg == {**AXIOM_CONFIG, "theorem_names": THEOREMS}
    assert "not yet replayed" in (d / "REPLAY.md").read_text()
    assert isl.name == "demo" and isl.replay is None
    # a valid registration whose only problem is that it has not been replayed
    probs = islands.island_problems(tmp_path / "repo", "demo")
    assert len(probs) == 1 and "not replayed" in probs[0], probs


def test_add_rejects_config_with_extra_axiom(tmp_path):
    # Axiom's config permits sorryAx (and turns nanoda off): ours is written with the three axioms and nanoda on,
    # and REPLAY.md records each difference
    cfg = {**AXIOM_CONFIG, "permitted_axioms": ["propext", "Quot.sound", "Classical.choice", "sorryAx"],
           "enable_nanoda": False}
    _add(tmp_path, fetch=_fake_fetch(cfg))
    d = tmp_path / "repo" / "islands" / "demo"
    ours = json.loads((d / "comparator.json").read_text())
    assert ours["permitted_axioms"] == ["propext", "Quot.sound", "Classical.choice"]
    assert ours["enable_nanoda"] is True
    md = (d / "REPLAY.md").read_text()
    assert "sorryAx" in md and "permitted_axioms" in md and "enable_nanoda" in md
    assert len(islands.island_problems(tmp_path / "repo", "demo")) == 1


def test_comparator_json_matches_the_spec_run_config():
    # our writer reproduces, byte for byte, the config the riemann-jensen spec run used (its log: md5 1c619f6c)
    text = islands.comparator_json_text("Challenge.Basic", "Solution.Basic", RJ_THEOREMS)
    assert hashlib.md5(text.encode()).hexdigest() == "1c619f6c101866f65cc95b1bc53baa74"


@pytest.mark.parametrize("kw,needle", [
    ({"name": "Bad_Name"}, "island name"),
    ({"name": "../x"}, "island name"),
])
def test_add_refuses_bad_name_before_fetching(tmp_path, kw, needle):
    calls = []
    with pytest.raises(islands.IslandError, match=needle):
        _add(tmp_path, fetch=_fake_fetch(calls=calls), **kw)
    assert calls == [] and not (tmp_path / "repo" / "islands").exists()


@pytest.mark.parametrize("source,commit", [("http://github.com/x", COMMIT), ("https://github.com/x y", COMMIT),
                                           ("https://github.com/x", COMMIT[:39]), ("https://github.com/x", "HEAD")])
def test_add_refuses_bad_source_or_commit_before_fetching(tmp_path, source, commit):
    calls = []
    with pytest.raises(islands.IslandError):
        islands.add_island(tmp_path / "repo", "demo", source, commit, "use", fetch=_fake_fetch(calls=calls),
                           tools=tmp_path / "tools")
    assert calls == []


def test_add_refuses_an_existing_island(tmp_path):
    _add(tmp_path)
    with pytest.raises(islands.IslandError, match="already"):
        _add(tmp_path)


@pytest.mark.parametrize("fetch_kw,needle", [
    ({"head": "1d7edeb4e67096f9da1b37cd4b763e8b73886655"}, "HEAD"),
    ({"toolchain": "leanprover/lean4:nightly\n"}, "toolchain"),
    ({"config": {**AXIOM_CONFIG, "theorem_names": ["Demo.Challenge.main x"]}}, "theorem"),
    ({"licence": "All rights reserved."}, "licence"),
])
def test_add_refuses_a_bad_clone_and_writes_nothing(tmp_path, fetch_kw, needle):
    with pytest.raises(islands.IslandError, match=needle):
        _add(tmp_path, fetch=_fake_fetch(**fetch_kw))
    assert not (tmp_path / "repo" / "islands" / "demo").exists()


def test_add_licence_flag_overrides_detection(tmp_path):
    _add(tmp_path, fetch=_fake_fetch(licence="All rights reserved."), licence="LicenseRef-Custom")
    doc = tomllib.loads((tmp_path / "repo" / "islands" / "demo" / "island.toml").read_text())
    assert doc["licence"] == "LicenseRef-Custom"


def test_add_refuses_symlinked_clone_file(tmp_path):
    def fetch(source, commit, dest):
        _fake_fetch()(source, commit, dest)
        p = Path(dest) / "Challenge" / "Basic.lean"
        p.unlink()
        p.symlink_to(tmp_path / "elsewhere.lean")
        (tmp_path / "elsewhere.lean").write_bytes(CHALLENGE)
        return COMMIT
    with pytest.raises(islands.IslandError, match="symlink"):
        _add(tmp_path, fetch=fetch)


# --- Task 2: island replay (injected runner) --------------------------------------------------------------------------

def _cmp_output(**kw) -> str:
    """What `lake env comparator <cfg>` prints: the log between the runner's own lines and its exit line."""
    lines = _log(**kw).splitlines()
    start = lines.index("Building Challenge.Basic")
    end = next(i for i, l in enumerate(lines) if l.endswith(f"-EXIT {kw.get('rc', 0)}"))
    return "\n".join(lines[start:end]) + "\n"


class FakeRun:
    """The injected `run`: canned outputs by command, every argv recorded."""

    def __init__(self, *, head=COMMIT, nanoda_head=NANODA, comparator=None, comparator_rc=0, probes=None, fp=None,
                 build_rc=0, status="", status_rc=0, ls_files="H Challenge/Basic.lean\nH lean-toolchain\n"):
        self.calls = []
        self.status, self.status_rc, self.ls_files = status, status_rc, ls_files
        self.head, self.nanoda_head = head, nanoda_head
        self.comparator = _cmp_output() if comparator is None else comparator
        self.comparator_rc, self.build_rc = comparator_rc, build_rc
        self.probes = probes or {}
        self.fp = fp

    def __call__(self, argv, *, cwd, env=None, timeout):
        assert isinstance(argv, list) and all(isinstance(a, str) for a in argv)
        self.calls.append(list(argv))
        if "rev-parse" in argv:
            nanoda = any(a.endswith(f"nanoda-{NANODA[:8]}") for a in argv)
            return islands.RunResult(0, (self.nanoda_head if nanoda else self.head) + "\n")
        if "status" in argv:
            return islands.RunResult(self.status_rc, self.status)
        if "ls-files" in argv:
            return islands.RunResult(0, self.ls_files)
        if "cache" in argv or "build" in argv:
            return islands.RunResult(self.build_rc, "Build completed successfully.\n", 1.5, 1000)
        if "comparator" in argv:
            return islands.RunResult(self.comparator_rc, self.comparator, 60.0, 2000)
        if "probe-negation" in argv:
            thm = argv[argv.index("--theorem") + 1]
            doc = self.probes.get(thm) or _probe_doc(thm)
            return islands.RunResult(0, json.dumps(doc) + "\n", 2.0, 500)
        if "fingerprint" in argv:
            return islands.RunResult(0, json.dumps(self.fp or _fp_doc()) + "\n", 3.0, 600)
        raise AssertionError(f"unexpected command {argv}")


def _tools(tmp_path) -> Path:
    t = tmp_path / "tools"
    src = t / "islands" / "demo" / "src"
    (src / ".git" / "info").mkdir(parents=True)                         # a clone's git dir (no exclude patterns)
    (src / "Challenge").mkdir(parents=True)
    (src / "Challenge" / "Basic.lean").write_bytes(CHALLENGE)
    (src / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    for rel in ("comparator-v4.35.0/.lake/build/bin/comparator",
                "comparator-v4.35.0/.lake/packages/lean4export/.lake/build/bin/lean4export",
                f"nanoda-{NANODA[:8]}/target/release/nanoda_bin", "bin/landrun"):
        (t / rel).parent.mkdir(parents=True, exist_ok=True)
        (t / rel).write_text("#!/bin/sh\n")
    return t


def _replay(tmp_path, run, **kw):
    root = tmp_path / "repo"
    if not (root / "islands" / "demo").exists():
        _island(root, replay=None)
    tools = tmp_path / "tools" if (tmp_path / "tools").exists() else _tools(tmp_path)
    return root, islands.replay_island(root, "demo", run=run, tools=tools, date="2026-10-31", leanlock=None, **kw)


def test_replay_pass_writes_replay_table(tmp_path):
    run = FakeRun(probes={THEOREMS[1]: _probe_doc(THEOREMS[1], "WITNESSED")})
    root, res = _replay(tmp_path, run)
    assert res.verdict == "pass", res.problems
    isl = islands.load_island(root, "demo")
    rep = isl.replay
    assert rep.verdict == "pass" and rep.commit == COMMIT and rep.challenge_sha256 == CHALLENGE_SHA
    assert rep.nanoda_rev == NANODA and rep.comparator_tag == "v4.35.0" and rep.date == "2026-10-31"
    assert dict(rep.checks) == {THEOREMS[0]: islands.TheoremCheck("PROBE_ONLY", FP),
                                THEOREMS[1]: islands.TheoremCheck("WITNESSED", FP)}
    log = (tmp_path / "tools" / "islands" / "demo" / "comparator.log").read_text()
    assert log.splitlines()[0] == f"ISLAND-HEADER island=demo commit={COMMIT} challenge_sha256={CHALLENGE_SHA}"
    assert rep.log_sha256 == _sha(log.encode()) == res.log_sha256
    rd = root / "islands" / "demo" / "replay"
    assert lzma.decompress((rd / "comparator.log.xz").read_bytes()).decode() == log
    assert islands.island_problems(root, "demo") == []
    md = (root / "islands" / "demo" / "REPLAY.md").read_text()
    assert "2026-10-31" in md and "PASS" in md and rep.log_sha256 in md and "lake build" in md
    assert "wall" in md and "peak" in md
    # the commands, in order; names reach them as list elements, never through a shell
    kinds = [c[c.index("lake") + 1] if "lake" in c else
             ("status" if "status" in c else "ls-files" if "ls-files" in c else c[-1]) for c in run.calls]
    assert kinds[:7] == ["HEAD", "status", "ls-files", "HEAD", "exe", "build", "env"]
    assert run.calls[1][3:] == ["-c", "core.excludesFile=/dev/null", "status", "--porcelain",
                                "--untracked-files=all", "--ignore-submodules=none"]
    assert run.calls[2][3:] == ["ls-files", "-v"]
    # the runner binds the log to our comparator.json
    cfg_sha = _sha((root / "islands" / "demo" / "comparator.json").read_bytes())
    assert f"COMPARATOR_CONFIG sha256 {cfg_sha}" in log.splitlines()
    probes = [c for c in run.calls if "probe-negation" in c]
    assert [c[c.index("--theorem") + 1] for c in probes] == THEOREMS
    cmp = next(c for c in run.calls if "comparator" in c)
    assert cmp[-1] == str((root / "islands" / "demo" / "comparator.json").resolve())


def test_sorry_axiom_fails(tmp_path):
    # Review Focus 3: the PNT fork's sorry reaching a theorem. Comparator's own text (Comparator/Axioms.lean) is an
    # uncaught exception, before any kernel runs, with exit 1
    out = "\n".join(l for l in _cmp_output().splitlines() if "accepts" not in l and "okay" not in l)
    out += "\nuncaught exception: Illegal axiom detected: 'sorryAx'\n"
    root, res = _replay(tmp_path, FakeRun(comparator=out, comparator_rc=1))
    assert res.verdict == "fail" and any("axiom" in p for p in res.problems), res.problems
    assert islands.load_island(root, "demo").replay is None
    assert not (root / "islands" / "demo" / "replay").exists()
    md = (root / "islands" / "demo" / "REPLAY.md").read_text()
    assert "FAIL" in md and "sorryAx" in md
    assert islands.status(root, "demo") == "self-reported"


def test_probe_vacuous_fails(tmp_path):
    run = FakeRun(probes={THEOREMS[1]: _probe_doc(THEOREMS[1], "VACUOUS")})
    root, res = _replay(tmp_path, run)
    assert res.verdict == "fail" and any("VACUOUS" in p and THEOREMS[1] in p for p in res.problems), res.problems
    assert islands.load_island(root, "demo").replay is None
    assert "FAIL" in (root / "islands" / "demo" / "REPLAY.md").read_text()


def test_head_mismatch_refuses(tmp_path):
    run = FakeRun(head="1d7edeb4e67096f9da1b37cd4b763e8b73886655")
    with pytest.raises(islands.IslandError, match="HEAD"):
        _replay(tmp_path, run)
    assert len(run.calls) == 1 and "rev-parse" in run.calls[0]
    root = tmp_path / "repo"
    assert islands.load_island(root, "demo").replay is None
    assert not (tmp_path / "tools" / "islands" / "demo" / "comparator.log").exists()


@pytest.mark.parametrize("setup,needle", [
    (lambda t: (t / "islands/demo/src/Challenge/Basic.lean").write_bytes(CHALLENGE + b"-- edited\n"), "sha256"),
    (lambda t: (t / "islands/demo/src/lean-toolchain").write_text("leanprover/lean4:v4.34.0\n"), "toolchain"),
    (lambda t: (t / "bin/landrun").unlink(), "landrun"),
    (lambda t: (t / f"nanoda-{NANODA[:8]}/target/release/nanoda_bin").unlink(), "nanoda"),
])
def test_replay_refuses_a_bad_clone_or_missing_tool(tmp_path, setup, needle):
    tools = _tools(tmp_path)
    setup(tools)
    run = FakeRun()
    with pytest.raises(islands.IslandError, match=needle):
        _replay(tmp_path, run)
    assert not any("lake" in c for c in run.calls)


def test_replay_refuses_nanoda_checkout_at_another_rev(tmp_path):
    run = FakeRun(nanoda_head="0" * 40)
    with pytest.raises(islands.IslandError, match="NANODA_REV"):
        _replay(tmp_path, run)
    assert not any("lake" in c for c in run.calls)


def test_replay_build_failure_fails_without_comparator(tmp_path):
    run = FakeRun(build_rc=1)
    root, res = _replay(tmp_path, run)
    assert res.verdict == "fail" and any("lake" in p for p in res.problems), res.problems
    assert not any("comparator" in c for c in run.calls)
    assert "FAIL" in (root / "islands" / "demo" / "REPLAY.md").read_text()


def test_comparator_tag_known_for_island_toolchains():
    from telperion.missions import judge
    assert judge.comparator_tag("leanprover/lean4:v4.35.0") == "v4.35.0"
    assert judge.comparator_tag("leanprover/lean4:v4.34.0-rc2") == "v4.34.0-rc2"


def test_subprocess_run_passes_argv_as_data(tmp_path):
    # the real runner: list argv, no shell, so a hostile-looking argument is just a string
    res = islands.subprocess_run(["printf", "%s", "x; touch pwned"], cwd=tmp_path, timeout=30)
    assert res.rc == 0 and res.output == "x; touch pwned" and not (tmp_path / "pwned").exists()
    res = islands.subprocess_run(["sleep", "5"], cwd=tmp_path, timeout=0.2)
    assert res.rc != 0 and "timed out" in res.output
    res = islands.subprocess_run([str(tmp_path / "no-such-binary")], cwd=tmp_path, timeout=30)
    assert res.rc != 0 and "cannot run" in res.output


# --- Task 2: island record-replay (Ruling 1) --------------------------------------------------------------------------

def _inputs(tmp_path, *, log=None, probes=None, fp="default") -> dict:
    """Externally produced evidence, as the sandbox operator hands it over: files outside the registry."""
    ext = tmp_path / "ext"
    ext.mkdir(exist_ok=True)
    (ext / "comparator.out").write_text(_log() if log is None else log)
    paths = []
    for i, doc in enumerate([_probe_doc(t) for t in THEOREMS] if probes is None else probes):
        (ext / f"probe{i}.json").write_bytes(_dump(doc))
        paths.append(ext / f"probe{i}.json")
    kw = {"log": ext / "comparator.out", "probe_jsons": paths, "fingerprint_json": None}
    if fp is not None:
        (ext / "fp.json").write_bytes(_dump(_fp_doc() if fp == "default" else fp))
        kw["fingerprint_json"] = ext / "fp.json"
    return kw


def _record(tmp_path, *, tag="v4.35.0", date="2026-10-31", **inputs):
    root = tmp_path / "repo"
    if not (root / "islands" / "demo").exists():
        _island(root, replay=None)
    return root, islands.record_replay(root, "demo", date=date, comparator_tag=tag, **_inputs(tmp_path, **inputs))


def test_record_replay_pass_archives_evidence_and_verifies(tmp_path):
    root, res = _record(tmp_path)
    assert res.verdict == "pass", res.problems
    assert islands.island_problems(root, "demo") == []
    rep = islands.load_island(root, "demo").replay
    rd = root / "islands" / "demo" / "replay"
    log = (tmp_path / "ext" / "comparator.out").read_bytes()
    assert lzma.decompress((rd / "comparator.log.xz").read_bytes()) == log and rep.log_sha256 == _sha(log)
    doc = tomllib.loads((root / "islands" / "demo" / "island.toml").read_text())
    probe_sha = doc["replay"]["probe_sha256"]
    assert set(probe_sha) == set(THEOREMS)
    for i, t in enumerate(THEOREMS):
        raw = (tmp_path / "ext" / f"probe{i}.json").read_bytes()
        assert probe_sha[t] == _sha(raw) and (rd / f"probe-{_sha(raw)}.json").read_bytes() == raw
    raw = (tmp_path / "ext" / "fp.json").read_bytes()
    assert doc["replay"]["fingerprint_sha256"] == _sha(raw) and (rd / "fingerprint.json").read_bytes() == raw
    assert sorted(p.name for p in rd.iterdir()) == sorted(
        ["comparator.log.xz", "fingerprint.json"] + [f"probe-{s}.json" for s in probe_sha.values()])
    md = (root / "islands" / "demo" / "REPLAY.md").read_text()
    assert "record-replay" in md and "PASS" in md and rep.log_sha256 in md


@pytest.mark.parametrize("inputs,needle", [
    ({"probes": []}, "no negation-probe JSON"),
    ({"probes": [_probe_doc(THEOREMS[0])]}, THEOREMS[1]),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[0])]}, "more than one"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[1], "REFUTED")]}, "REFUTED"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[1], "ERROR")]}, "ERROR"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc("Demo.Challenge.other")]}, "not one of the island's"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[1], module="Solution.Basic")]}, "module"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[1], source_sha256="ee" * 32)]}, "source_sha256"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[1], source_sha256=None)]}, "source_sha256"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[1], stale=True)]}, "stale"),
    ({"probes": [_probe_doc(THEOREMS[0]), _probe_doc(THEOREMS[1], olean_sha256="ff" * 32)]}, "olean_sha256"),
    ({"probes": [_probe_doc(THEOREMS[0]), ["not", "an", "object"]]}, "object"),
    ({"fp": None}, "no fingerprint JSON"),
    ({"fp": _fp_doc(THEOREMS[:1])}, THEOREMS[1]),
    ({"fp": _fp_doc(THEOREMS + ["Demo.Challenge.other"])}, "Demo.Challenge.other"),
    ({"fp": _fp_doc(fp="CD" * 32)}, "fingerprint"),
    ({"fp": _fp_doc(mode="value")}, "mode"),
    ({"fp": _fp_doc(module=None)}, "module"),
    ({"fp": _fp_doc(source_sha256="ee" * 32)}, "source_sha256"),
    ({"fp": {"error": "refused: axiom"}}, "error"),
    ({"log": _log(sha="ee" * 32)}, "challenge_sha256"),
    ({"log": _log(commit="1d7edeb4e67096f9da1b37cd4b763e8b73886655")}, "commit"),
    ({"log": _log(before_exit=['unpermitted axiom "sorryAx"'])}, "axiom"),
    ({"log": _log(nanoda="0" * 40)}, "NANODA_REV"),
    ({"log": _log(rc=137)}, "exit"),
    ({"tag": "v4.34.0"}, "comparator_tag"),
])
def test_record_replay_fail_writes_no_replay(tmp_path, inputs, needle):
    root, res = _record(tmp_path, **inputs)
    assert res.verdict == "fail" and any(needle in p for p in res.problems), res.problems
    assert islands.load_island(root, "demo").replay is None
    assert not (root / "islands" / "demo" / "replay").exists()
    assert "FAIL" in (root / "islands" / "demo" / "REPLAY.md").read_text()
    assert islands.status(root, "demo") == "self-reported"


def test_record_replay_fail_drops_an_earlier_replay(tmp_path):
    root, res = _record(tmp_path)
    assert res.verdict == "pass" and islands.status(root, "demo") == "verified"
    _, res = _record(tmp_path, log=_log(rc=1))
    assert res.verdict == "fail"
    assert islands.load_island(root, "demo").replay is None
    assert not (root / "islands" / "demo" / "replay").exists()
    md = (root / "islands" / "demo" / "REPLAY.md").read_text()
    assert md.count("PASS") >= 1 and "FAIL" in md and "dropped" in md


def _symlink_log(p: Path):
    (p.parent / "real.out").write_text(_log())
    p.unlink()
    p.symlink_to(p.parent / "real.out")


@pytest.mark.parametrize("break_it,needle", [
    (_symlink_log, "symlink"),
    (lambda p: p.write_bytes(b"\xff\xfe" + _log().encode()), "UTF-8"),
    (lambda p: p.unlink(), "missing"),
])
def test_record_replay_refuses_unreadable_log(tmp_path, break_it, needle):
    root = _island(tmp_path / "repo", replay=None)
    kw = _inputs(tmp_path)
    break_it(kw["log"])
    with pytest.raises(islands.IslandError, match=needle):
        islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", **kw)
    assert not (root / "islands" / "demo" / "replay").exists()


def test_record_replay_refuses_oversized_log(tmp_path, monkeypatch):
    monkeypatch.setattr(islands, "LOG_MAX_BYTES", 100)
    root = _island(tmp_path / "repo", replay=None)
    with pytest.raises(islands.IslandError, match="larger than"):
        islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", **_inputs(tmp_path))


@pytest.mark.parametrize("kw", [{"date": "31 Oct 2026"}, {"comparator_tag": "4.35.0"}])
def test_record_replay_refuses_bad_date_or_tag(tmp_path, kw):
    root = _island(tmp_path / "repo", replay=None)
    args = {"date": "2026-10-31", "comparator_tag": "v4.35.0", **kw}
    with pytest.raises(islands.IslandError):
        islands.record_replay(root, "demo", **args, **_inputs(tmp_path))


def test_record_replay_refuses_a_broken_registration(tmp_path):
    root = _island(tmp_path / "repo", replay=None)
    (root / "islands" / "demo" / "challenge.lean").write_bytes(CHALLENGE + b"-- edited\n")
    with pytest.raises(islands.IslandError, match="challenge.lean"):
        islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", **_inputs(tmp_path))


def test_replay_and_record_replay_share_one_verdict(tmp_path, monkeypatch):
    # Ruling 1: one verdict function behind both commands ...
    seen = []
    real = islands.evaluate_replay
    monkeypatch.setattr(islands, "evaluate_replay", lambda *a, **k: seen.append(k.get("log_text")) or real(*a, **k))
    _replay(tmp_path / "a", FakeRun())
    _record(tmp_path / "b")
    assert len(seen) >= 2


@pytest.mark.parametrize("defect", ["vacuous", "sorry", "fp-missing", "refuted"])
def test_replay_and_record_replay_agree_on_each_defect(tmp_path, defect):
    # ... and it reads the same evidence the same way, whichever command fed it
    probes = {THEOREMS[1]: _probe_doc(THEOREMS[1], {"vacuous": "VACUOUS", "refuted": "REFUTED"}.get(defect,
                                                                                                    "PROBE_ONLY"))}
    before = ['unpermitted axiom "sorryAx" used by Demo.Challenge.aux'] if defect == "sorry" else []
    fp = _fp_doc(THEOREMS[:1]) if defect == "fp-missing" else _fp_doc()
    (tmp_path / "a").mkdir()
    _, a = _replay(tmp_path / "a", FakeRun(probes=probes, fp=fp, comparator=_cmp_output(before_exit=before)))
    _, b = _record(tmp_path / "b", log=_log(before_exit=before), fp=fp,
                   probes=[_probe_doc(THEOREMS[0]), probes[THEOREMS[1]]])
    assert a.verdict == b.verdict == "fail"
    assert sorted(a.problems) == sorted(b.problems)


def test_cli_record_replay(tmp_path):
    root = _island(tmp_path / "repo", replay=None)
    kw = _inputs(tmp_path)
    argv = ["island", "record-replay", "demo", "--root", str(root), "--log", str(kw["log"]),
            "--fingerprint-json", str(kw["fingerprint_json"]), "--date", "2026-10-31", "--comparator-tag", "v4.35.0"]
    for p in kw["probe_jsons"]:
        argv += ["--probe-json", str(p)]
    r = _cli(*argv)
    assert r.returncode == 0, r.stdout + r.stderr
    assert "PASS" in r.stdout and "verified" in r.stdout
    assert _cli("island", "check", "demo", "--root", str(root)).returncode == 0
    # no probes: FAIL, exit 1, nothing recorded, no traceback
    root2 = _island(tmp_path / "repo2", replay=None)
    r = _cli("island", "record-replay", "demo", "--root", str(root2), "--log", str(kw["log"]),
             "--date", "2026-10-31", "--comparator-tag", "v4.35.0")
    assert r.returncode == 1 and "FAIL" in r.stdout and "Traceback" not in r.stderr
    # an unreadable log: refused, exit 1, no traceback
    r = _cli("island", "record-replay", "demo", "--root", str(root2), "--log", str(tmp_path / "nope"),
             "--date", "2026-10-31", "--comparator-tag", "v4.35.0")
    assert r.returncode == 1 and "Traceback" not in r.stderr and "record-replay" in r.stderr
    r = _cli("island", "record-replay", "../x", "--root", str(root2), "--log", str(kw["log"]),
             "--date", "2026-10-31", "--comparator-tag", "v4.35.0")
    assert r.returncode == 1 and "Traceback" not in r.stderr


def test_cli_add_and_replay_parse(tmp_path):
    # the parsers exist; a bad name is refused cleanly before anything is fetched or run
    for argv in (("island", "add", "Bad_Name", "--source", "https://github.com/x", "--commit", COMMIT, "--use", "x",
                  "--root", str(tmp_path), "--tools", str(tmp_path / "tools")),
                 ("island", "replay", "Bad_Name", "--root", str(tmp_path), "--tools", str(tmp_path / "tools"))):
        r = _cli(*argv)
        assert r.returncode == 1 and "Traceback" not in r.stderr and "island name" in r.stderr, r.stderr
    assert not (tmp_path / "tools").exists()


# --- Task 2 / Ruling 6: island check re-verifies the archived evidence on every call ----------------------------------

def _rewrap(root: Path, text: str):
    """Replace the archived log by *text* (a consistent re-archive: island.toml's log_sha256 updated to match)."""
    d = root / "islands" / "demo"
    old = _sha(lzma.decompress((d / "replay" / "comparator.log.xz").read_bytes()))
    (d / "replay" / "comparator.log.xz").write_bytes(lzma.compress(text.encode()))
    toml = d / "island.toml"
    toml.write_text(toml.read_text().replace(old, _sha(text.encode())))


@pytest.mark.parametrize("text,needle", [
    (_log(before_exit=["error: something broke"]), "error"),
    (_log(rc=1), "exit"),
    (_log(sha="ee" * 32), "challenge_sha256"),
    (_log(commit="1d7edeb4e67096f9da1b37cd4b763e8b73886655"), "commit"),
    (_log(drop=["Lean default kernel accepts"]), "Lean default kernel"),
    (_log(nanoda="0" * 40), "NANODA_REV"),
])
def test_archived_log_is_reparsed(tmp_path, text, needle):
    root = _island(tmp_path)
    _rewrap(root, text)
    probs = islands.island_problems(root, "demo")
    assert any("archived" in p and needle in p for p in probs), probs
    assert islands.status(root, "demo") == "self-reported"


def _evidence_file(root, pattern):
    return next((root / "islands" / "demo" / "replay").glob(pattern))


@pytest.mark.parametrize("tamper,needle", [
    (lambda r: (r / "islands/demo/replay/comparator.log.xz").unlink(), "comparator.log.xz"),
    (lambda r: (r / "islands/demo/replay/comparator.log.xz").write_bytes(lzma.compress(_log(rc=1).encode())),
     "log_sha256"),
    (lambda r: (r / "islands/demo/replay/comparator.log.xz").write_bytes(_log().encode()), "xz"),
    (lambda r: (r / "islands/demo/replay/comparator.log.xz").write_bytes(
        lzma.compress(_log().encode()) + lzma.compress(b"more")), "xz"),
    (lambda r: (r / "islands/demo/replay/fingerprint.json").unlink(), "fingerprint.json"),
    (lambda r: (r / "islands/demo/replay/fingerprint.json").write_bytes(_dump(_fp_doc(fp="ef" * 32))),
     "fingerprint_sha256"),
    (lambda r: _evidence_file(r, "probe-*.json").write_bytes(_dump(_probe_doc(THEOREMS[0], "VACUOUS"))),
     "probe_sha256"),
    (lambda r: _evidence_file(r, "probe-*.json").unlink(), "probe-"),
    (lambda r: (r / "islands/demo/replay/notes.txt").write_text("x"), "unexpected"),
])
def test_archived_evidence_tamper_is_seen(tmp_path, tamper, needle):
    root = _island(tmp_path)
    assert islands.status(root, "demo") == "verified"
    tamper(root)
    probs = islands.island_problems(root, "demo")
    assert any(needle in p for p in probs), probs
    assert islands.status(root, "demo") == "self-reported"


def test_archived_log_decompression_is_bounded(tmp_path, monkeypatch):
    root = _island(tmp_path)
    monkeypatch.setattr(islands, "LOG_MAX_BYTES", 200)
    probs = islands.island_problems(root, "demo")
    assert any("larger than" in p and "comparator.log.xz" in p for p in probs), probs


def test_symlinked_replay_dir_is_refused(tmp_path):
    root = _island(tmp_path)
    rd = root / "islands" / "demo" / "replay"
    rd.rename(tmp_path / "real-replay")
    rd.symlink_to(tmp_path / "real-replay")
    probs = islands.island_problems(root, "demo")
    assert any("replay/" in p and "symlink" in p for p in probs), probs


def test_checks_must_agree_with_the_archived_jsons(tmp_path):
    # the probe JSONs say WITNESSED for aux and the fingerprint JSON says FP; [replay.checks] says otherwise
    chk = {THEOREMS[0]: {"probe": "PROBE_ONLY", "fingerprint": FP},
           THEOREMS[1]: {"probe": "PROBE_ONLY", "fingerprint": FP}}
    root = _island(tmp_path, checks=chk, evidence={"probes": [_probe_doc(THEOREMS[0]),
                                                               _probe_doc(THEOREMS[1], "WITNESSED")]})
    probs = islands.island_problems(root, "demo")
    assert any(THEOREMS[1] in p and "WITNESSED" in p and "[replay.checks]" in p for p in probs), probs
    chk[THEOREMS[1]] = {"probe": "WITNESSED", "fingerprint": "ef" * 32}
    root = _island(tmp_path / "b", checks=chk, evidence={"probes": [_probe_doc(THEOREMS[0]),
                                                                     _probe_doc(THEOREMS[1], "WITNESSED")]})
    probs = islands.island_problems(root, "demo")
    assert any(THEOREMS[1] in p and "fingerprint" in p and "[replay.checks]" in p for p in probs), probs


def test_probe_sha256_keys_must_name_the_probed_theorem(tmp_path):
    # two theorems' probe files swapped under their keys: each file is intact, but it is the other theorem's
    root = _island(tmp_path)
    toml = root / "islands" / "demo" / "island.toml"
    doc = tomllib.loads(toml.read_text())
    a, b = (doc["replay"]["probe_sha256"][t] for t in THEOREMS)
    toml.write_text(toml.read_text().replace(a, "TMP").replace(b, a).replace("TMP", b))
    probs = islands.island_problems(root, "demo")
    assert any("probe_sha256" in p and THEOREMS[0] in p for p in probs), probs


@pytest.mark.parametrize("patch", [{"probe_sha256": {THEOREMS[0]: "ab" * 31}}, {"fingerprint_sha256": "AB" * 32},
                                   {"probe_sha256": "x"}])
def test_strict_replay_evidence_schema(tmp_path, patch):
    root = _island(tmp_path, replay=patch)
    assert islands.island_problems(root, "demo")
    assert islands.status(root, "demo") == "self-reported"


def test_record_replay_writes_toml_island_check_reads(tmp_path):
    # the writer's island.toml round-trips through the strict schema: every key, nothing else
    root, res = _record(tmp_path)
    doc = tomllib.loads((root / "islands" / "demo" / "island.toml").read_text())
    assert set(doc["replay"]) == {"date", "commit", "challenge_sha256", "nanoda_rev", "comparator_tag", "log_sha256",
                                  "probe_sha256", "fingerprint_sha256", "verdict", "checks"}
    assert doc["name"] == "demo" and doc["theorems"] == THEOREMS


@pytest.mark.parametrize("patch", [{"olean_sha256": [1]}, {"verdict": ["PROBE_ONLY"]}, {"module": {"a": 1}},
                                   {"source_sha256": "x" * 10000}])
def test_hostile_archived_json_never_raises(tmp_path, patch):
    # odd JSON values (unhashable, huge) in archived or ingested evidence are problems, never exceptions or floods
    probes = [_probe_doc(THEOREMS[0], **patch), _probe_doc(THEOREMS[1])]
    root = _island(tmp_path, evidence={"probes": probes})
    probs = islands.island_problems(root, "demo")
    assert probs and all(len(p) < 600 for p in probs), probs
    root2 = _island(tmp_path / "b", replay=None)
    _, res = _record(tmp_path / "b", probes=probes)
    assert res.verdict == "fail" and islands.status(root2, "demo") == "self-reported"


@pytest.mark.parametrize("which", ["fingerprint", "probe"])
@pytest.mark.parametrize("content", [b"null\n", b"[]\n", b"7\n"])
def test_archived_json_that_is_not_an_object_is_seen(tmp_path, which, content):
    # a consistent re-archive (sha256 updated to match) of a JSON file that is not an object at all
    root = _island(tmp_path)
    d = root / "islands" / "demo"
    toml = d / "island.toml"
    f = d / "replay" / "fingerprint.json" if which == "fingerprint" else next((d / "replay").glob("probe-*.json"))
    old = _sha(f.read_bytes())
    target = f if which == "fingerprint" else f.with_name(f"probe-{_sha(content)}.json")
    f.unlink()
    target.write_bytes(content)
    toml.write_text(toml.read_text().replace(old, _sha(content)))
    probs = islands.island_problems(root, "demo")
    assert probs, "a non-object archived JSON must not read as verified"
    assert islands.status(root, "demo") == "self-reported"


# --- Task 2 fix round 1 (Ruling 8) ------------------------------------------------------------------------------------

ZZ2_THEOREMS = tuple(f"ZetaZeros.Challenge.{t}" for t in (
    "prop_simple_real_lower", "prop_distinct_lower", "prop_simple_plus_real_lower", "prop_simple_or_real_lower",
    "thm_simple", "thm_distinct", "thm_average", "thm_simple_or_critical", "thm_simple_numeric",
    "thm_distinct_numeric", "thm_average_numeric", "thm_simple_or_critical_numeric"))
ZZ2 = dict(name="zeta-zeros-v2", source="https://github.com/AxiomMath/ZetaZerosV2",
           commit="1d7edeb4e67096f9da1b37cd4b763e8b73886655", toolchain="leanprover/lean4:v4.34.0-rc2",
           challenge_sha256="dc3cc10e3fb36af0c966a5de73e1ac37ff379825a627807f973920b396fda0b7", theorems=ZZ2_THEOREMS)


def test_real_zz2_log_passes():
    # the auditor-held standalone Comparator v4.34.0-rc2 log of zeta-zeros-v2 @1d7edeb4 (md5 573d6ead), normalized
    # (scratch prefix -> $SCRATCH), its Built lines trimmed to 3, glyphs made ASCII. rc2 exports no optParam & co.
    text = (FIXTURES / "zz2_main.out").read_text()
    assert islands.comparator_log_problems(text, _isl(**ZZ2), NANODA, comparator_tag="v4.34.0-rc2") == []
    # and it is bound to its tag: judged as a v4.35.0 run, the export set is wrong
    probs = islands.comparator_log_problems(text, _isl(**ZZ2), NANODA, comparator_tag="v4.35.0")
    assert any("optParam" in p for p in probs), probs


def test_fixtures_are_normalized():
    for f in ("rj_spec.out", "rj_spec_tamper.out", "zz2_main.out"):
        text = (FIXTURES / f).read_text()
        assert "$SCRATCH/" in text and "/tmp/claude-0" not in text, f


@pytest.mark.parametrize("kw,needle", [
    ({"exports_extra": ["sorryAx"]}, "sorryAx"),                        # the library's own config permits sorryAx
    ({"exports_extra": ["Demo.myAxiom"]}, "Demo.myAxiom"),              # any extra permitted axiom
    ({"exports_extra": ["Demo.Challenge.helperDef"]}, "Demo.Challenge.helperDef"),   # a definition_names hole
    ({"exports_drop": ["Classical.choice"]}, "Classical.choice"),        # a config that is not ours either way
    ({"exports_extra": ["propext"]}, "more than once"),
])
def test_export_lists_are_bound_to_our_config(kw, needle):
    # C1: a run under another config passes Comparator quietly; the export lists are how it shows
    probs = islands.comparator_log_problems(_log(**kw), _isl(), NANODA)
    assert any(needle in p and "export" in p for p in probs), probs


def test_unknown_comparator_tag_fails():
    probs = islands.comparator_log_problems(_log(), _isl(), NANODA, comparator_tag="v4.36.0")
    assert any("v4.36.0" in p and "export" in p for p in probs), probs
    probs = islands.comparator_log_problems(_log(), _isl(toolchain="leanprover/lean4:v4.36.0"), NANODA)
    assert any("v4.36.0" in p for p in probs), probs


def test_real_rj_log_with_sorryax_exported_fails():
    # the reviewer's reproduction: the real log, as if run under Axiom's sorryAx-permitting config
    text = (FIXTURES / "rj_spec.out").read_text().replace("Classical.choice, Nat.add", "Classical.choice, sorryAx, "
                                                                                        "Nat.add")
    probs = islands.comparator_log_problems(text, _isl(**RJ), NANODA)
    assert any("sorryAx" in p for p in probs), probs


def test_upstream_config_permitting_sorryax_fails_replay(tmp_path):
    # Review Focus 3, the quiet way: Comparator accepted (nanoda on, exit 0) because the config permitted sorryAx
    root, res = _replay(tmp_path, FakeRun(comparator=_cmp_output(exports_extra=["sorryAx"])))
    assert res.verdict == "fail" and any("sorryAx" in p for p in res.problems), res.problems
    assert islands.load_island(root, "demo").replay is None


def test_archived_log_with_sorryax_exported_is_self_reported(tmp_path):
    root = _island(tmp_path)
    _rewrap(root, _log(exports_extra=["sorryAx"]))
    probs = islands.island_problems(root, "demo")
    assert any("archived" in p and "sorryAx" in p for p in probs), probs


@pytest.mark.parametrize("line,ok", [
    (None, True),                                                   # external logs carry no such line
    ("right", True),
    ("COMPARATOR_CONFIG sha256 " + "ab" * 32, False),               # another config's bytes
    ("COMPARATOR_CONFIG md5 1c619f6c101866f65cc95b1bc53baa74", False),
    ("two", False),
])
def test_comparator_config_line(tmp_path, line, ok):
    _island(tmp_path / "repo", replay=None)
    cfg_sha = _sha((tmp_path / "repo" / "islands" / "demo" / "comparator.json").read_bytes())
    right = f"COMPARATOR_CONFIG sha256 {cfg_sha}"
    extra = {None: [], "right": [right], "two": [right, right]}.get(line, [line])
    _, res = _record(tmp_path, log=_log(before_exit=extra))
    assert (res.verdict == "pass") is ok, res.problems
    if not ok:
        assert any("COMPARATOR_CONFIG" in p for p in res.problems), res.problems


def test_comparator_json_rewritten_after_replay_is_seen(tmp_path):
    # a replay that bound itself to our comparator.json's bytes stops counting when those bytes change
    root, res = _replay(tmp_path, FakeRun())
    assert res.verdict == "pass" and islands.status(root, "demo") == "verified"
    cfg = root / "islands" / "demo" / "comparator.json"
    cfg.write_text(json.dumps(json.loads(cfg.read_text()), indent=4) + "\n")    # same content, other bytes
    probs = islands.island_problems(root, "demo")
    assert any("COMPARATOR_CONFIG" in p for p in probs), probs


SCRATCH = "/tmp/claude-0/-home-user-Arda/00000000-1111-4222-8333-444444444444/scratchpad"


def test_record_replay_normalizes_the_scratch_prefix(tmp_path):
    # Ruling 7: what is judged is what is archived, and it names no session scratch path
    raw = _log(before_exit=[f"project {SCRATCH}/island/rjfresh", f"COMPARATOR_LANDRUN {SCRATCH}/pub/shim.sh"])
    root = _island(tmp_path / "repo", replay=None)
    res = islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", scratch_prefix=SCRATCH,
                                **_inputs(tmp_path, log=raw))
    assert res.verdict == "pass", res.problems
    archived = lzma.decompress((root / "islands" / "demo" / "replay" / "comparator.log.xz").read_bytes()).decode()
    assert archived == raw.replace(SCRATCH, "$SCRATCH") and SCRATCH not in archived
    assert islands.load_island(root, "demo").replay.log_sha256 == _sha(archived.encode()) == res.log_sha256
    md = (root / "islands" / "demo" / "REPLAY.md").read_text()
    assert hashlib.md5(raw.encode()).hexdigest() in md and _sha(raw.encode()) in md and SCRATCH not in md
    assert islands.status(root, "demo") == "verified"


@pytest.mark.parametrize("prefix", ["relative/scratch", "/", "/tmp", "/tmp/a b", "/tmp/x/", "/tmp/../etc",
                                    "/tmp/./x", "", "/tmp/$X", "/tmp/not-in-the-log"])
def test_scratch_prefix_is_refused_unless_a_plain_absolute_path_in_the_log(tmp_path, prefix):
    raw = _log(before_exit=[f"project {SCRATCH}/island"])
    root = _island(tmp_path / "repo", replay=None)
    with pytest.raises(islands.IslandError, match="scratch"):
        islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", scratch_prefix=prefix,
                              **_inputs(tmp_path, log=raw))
    assert not (root / "islands" / "demo" / "replay").exists()


def test_cli_record_replay_scratch_prefix(tmp_path):
    root = _island(tmp_path / "repo", replay=None)
    kw = _inputs(tmp_path, log=_log(before_exit=[f"project {SCRATCH}/island"]))
    argv = ["island", "record-replay", "demo", "--root", str(root), "--log", str(kw["log"]), "--scratch-prefix",
            SCRATCH, "--fingerprint-json", str(kw["fingerprint_json"]), "--date", "2026-10-31",
            "--comparator-tag", "v4.35.0"]
    for p in kw["probe_jsons"]:
        argv += ["--probe-json", str(p)]
    r = _cli(*argv)
    assert r.returncode == 0, r.stdout + r.stderr
    archived = lzma.decompress((root / "islands" / "demo" / "replay" / "comparator.log.xz").read_bytes()).decode()
    assert "$SCRATCH/island" in archived


@pytest.mark.parametrize("status,rc", [(" M Challenge/Basic.lean\n", 0), ("?? stray.lean\n", 0), ("", 128)])
def test_add_refuses_a_dirty_clone(tmp_path, status, rc):
    # I2: an existing clone with an edit (the tamper control's 2 <= d -> 3 <= d) must not register as the pin
    run = FakeRun(status=status, status_rc=rc)
    with pytest.raises(islands.IslandError, match="clean|status"):
        _add(tmp_path, run=run)
    assert not (tmp_path / "repo" / "islands" / "demo").exists()
    assert any("status" in c for c in run.calls)


@pytest.mark.parametrize("status,rc", [(" M Solution/Basic.lean\n", 0), ("?? Extra.lean\n", 0), ("", 1)])
def test_replay_refuses_a_dirty_clone(tmp_path, status, rc):
    run = FakeRun(status=status, status_rc=rc)
    with pytest.raises(islands.IslandError, match="clean|status"):
        _replay(tmp_path, run)
    assert not any("lake" in c for c in run.calls)
    assert islands.load_island(tmp_path / "repo", "demo").replay is None


def test_deeply_nested_json_never_raises(tmp_path):
    # M1: json.loads raises RecursionError, not ValueError, on deep nesting
    deep = b"[" * 200000 + b"]" * 200000
    root = _island(tmp_path)
    d = root / "islands" / "demo"
    old = _sha((d / "replay" / "fingerprint.json").read_bytes())
    (d / "replay" / "fingerprint.json").write_bytes(deep)
    (d / "island.toml").write_text((d / "island.toml").read_text().replace(old, _sha(deep)))
    assert islands.island_problems(root, "demo")
    root2 = _island(tmp_path / "b", replay=None)
    kw = _inputs(tmp_path / "b")
    kw["fingerprint_json"].write_bytes(deep)
    with pytest.raises(islands.IslandError, match="JSON"):
        islands.record_replay(root2, "demo", date="2026-10-31", comparator_tag="v4.35.0", **kw)


def test_xz_memlimit(tmp_path, monkeypatch):
    # M2: the decoder's memory is capped, whatever dictionary the stream's header declares
    root = _island(tmp_path)
    assert islands.status(root, "demo") == "verified"
    monkeypatch.setattr(islands, "XZ_MEMLIMIT", 1 << 20)          # below the 8 MiB dictionary of the default preset
    probs = islands.island_problems(root, "demo")
    assert any("comparator.log.xz" in p and "xz" in p for p in probs), probs


def test_a_large_passing_log_stays_verified(tmp_path):
    # M3: a log record-replay accepts must not read self-reported because its archive exceeds a smaller cap
    noise = [os.urandom(48).hex() for _ in range(25000)]                     # ~2.4 MB, incompressible
    _, res = _record(tmp_path, log=_log(before_exit=noise))
    assert res.verdict == "pass", res.problems
    archive = tmp_path / "repo" / "islands" / "demo" / "replay" / "comparator.log.xz"
    assert archive.stat().st_size > islands.MAX_BYTES
    assert islands.island_problems(tmp_path / "repo", "demo") == []


def test_archive_over_the_cap_is_seen(tmp_path, monkeypatch):
    root = _island(tmp_path)
    monkeypatch.setattr(islands, "LOG_MAX_BYTES", 50)
    probs = islands.island_problems(root, "demo")
    assert any("comparator.log.xz" in p and "larger than" in p for p in probs), probs


def test_stale_staging_directories_are_reported(tmp_path):
    # M5: a hard-killed add or replay leaves a dot-prefixed stage; it is named for what it is
    root = _island(tmp_path)
    (root / "islands" / ".demo.add-x1y2").mkdir()
    names, probs = islands.island_names(root)
    assert names == ["demo"] and any("stale staging directory" in p and ".demo.add-x1y2" in p for p in probs), probs
    assert islands.island_problems(root, "demo") == []
    (root / "islands" / "demo" / ".replay-new-abc").mkdir()
    probs = islands.island_problems(root, "demo")
    assert any("stale staging directory" in p and ".replay-new-abc" in p for p in probs), probs


def test_subprocess_run_timeout_with_a_grandchild_holding_the_pipe(tmp_path):
    # M8: a grandchild in its own session keeps stdout open after the group kill; the runner must still return
    import time
    script = ("import subprocess, time; subprocess.Popen(['sleep', '20'], start_new_session=True); "
              "time.sleep(20)")
    t0 = time.monotonic()
    res = islands.subprocess_run([sys.executable, "-c", script], cwd=tmp_path, timeout=0.5)
    assert res.rc == 124 and "timed out" in res.output
    assert time.monotonic() - t0 < 15


# --- Task 2 closing commit (Ruling 9) ---------------------------------------------------------------------------------

def _git_repo(d: Path) -> Path:
    """A throwaway local repo (no network, no clone) with two committed files, as a clone looks after `island add`."""
    g = ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-c", "commit.gpgsign=false", "-C", str(d)]
    d.mkdir(parents=True)
    subprocess.run(["git", "init", "-q", str(d)], check=True)
    (d / "Challenge").mkdir()
    (d / "Challenge" / "Basic.lean").write_bytes(CHALLENGE)
    (d / "Solution").mkdir()
    (d / "Solution" / "Basic.lean").write_text("-- the solution\n")
    subprocess.run([*g, "add", "-A"], check=True)
    subprocess.run([*g, "commit", "-q", "-m", "x"], check=True)
    return d


def _plumb(d: Path, case: str, home: Path):
    git = ["git", "-C", str(d)]
    if case == "assume-unchanged":
        subprocess.run([*git, "update-index", "--assume-unchanged", "Solution/Basic.lean"], check=True)
        (d / "Solution" / "Basic.lean").write_text("-- edited\n")
    elif case == "skip-worktree":
        subprocess.run([*git, "update-index", "--skip-worktree", "Solution/Basic.lean"], check=True)
        (d / "Solution" / "Basic.lean").write_text("-- edited\n")
    elif case == "info-exclude":
        (d / ".git" / "info" / "exclude").write_text("Extra/\n")
        (d / "Extra").mkdir()
        (d / "Extra" / "Hidden.lean").write_text("x\n")
    elif case == "global-excludes":
        (home / "ignore").write_text("Extra/\n")
        (home / "gitconfig").write_text(f"[core]\n\texcludesFile = {home / 'ignore'}\n")
        (d / "Extra").mkdir()
        (d / "Extra" / "Hidden.lean").write_text("x\n")
    elif case == "deep-untracked":
        (d / "Solution" / "Deep" / "Er").mkdir(parents=True)
        (d / "Solution" / "Deep" / "Er" / "New.lean").write_text("x\n")


@pytest.mark.parametrize("case", ["clean", "assume-unchanged", "skip-worktree", "info-exclude", "global-excludes",
                                  "deep-untracked"])
def test_dirty_clone_check_with_real_git(tmp_path, monkeypatch, case):
    # N1: states plain `git status --porcelain` reads as clean (real git, a local throwaway repo)
    home = tmp_path / "home"
    home.mkdir()
    monkeypatch.setenv("GIT_CONFIG_GLOBAL", str(home / "gitconfig"))
    (home / "gitconfig").write_text("")
    d = _git_repo(tmp_path / "clone")
    _plumb(d, case, home)
    problem = islands._dirty_clone_problem(islands.subprocess_run, d)
    if case == "clean":
        assert problem is None
    else:
        assert problem and "clean" in problem, (case, problem)


@pytest.mark.parametrize("flag", ["h", "S", "s"])
def test_add_and_replay_refuse_assume_unchanged_or_skip_worktree_entries(tmp_path, flag):
    ls = f"H Challenge/Basic.lean\n{flag} Solution/Basic.lean\n"
    with pytest.raises(islands.IslandError, match="assume-unchanged|skip-worktree"):
        _add(tmp_path / "a", run=FakeRun(ls_files=ls))
    run = FakeRun(ls_files=ls)
    with pytest.raises(islands.IslandError, match="assume-unchanged|skip-worktree"):
        _replay(tmp_path / "b", run)
    assert not any("lake" in c for c in run.calls)


def test_replay_refuses_a_hidden_info_exclude(tmp_path):
    tools = _tools(tmp_path)
    exclude = tools / "islands" / "demo" / "src" / ".git" / "info" / "exclude"
    exclude.parent.mkdir(parents=True, exist_ok=True)
    exclude.write_text("# git ls-files --others --exclude-from=.git/info/exclude\nSolution/\n")
    run = FakeRun()
    with pytest.raises(islands.IslandError, match="info/exclude"):
        _replay(tmp_path, run)
    assert not any("lake" in c for c in run.calls)
    exclude.write_text("# only comments, as `git init` writes it\n\n")
    root, res = _replay(tmp_path, FakeRun())
    assert res.verdict == "pass", res.problems


def test_replay_refuses_a_reused_lake_packages(tmp_path):
    # N1: an edited dependency under the ignored .lake/packages/ would be compiled and judged as the pin's
    tools = _tools(tmp_path)
    (tools / "islands" / "demo" / "src" / ".lake" / "packages" / "mathlib").mkdir(parents=True)
    run = FakeRun()
    with pytest.raises(islands.IslandError, match=r"\.lake/packages"):
        _replay(tmp_path, run)
    assert not any("lake" in c for c in run.calls)


def test_record_replay_refuses_a_session_scratch_path_without_prefix(tmp_path):
    # N2: a forgotten --scratch-prefix must not archive the session path
    root = _island(tmp_path / "repo", replay=None)
    kw = _inputs(tmp_path, log=_log(before_exit=[f"project {SCRATCH}/island/rjfresh"]))
    with pytest.raises(islands.IslandError, match="--scratch-prefix"):
        islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", **kw)
    assert not (root / "islands" / "demo" / "replay").exists()


def test_record_replay_refuses_a_second_session_path_after_normalizing(tmp_path):
    other = "/tmp/claude-0/-home-user-Arda/9d2b7a61-0000-4c4c-8b8b-0123456789ab/scratchpad"
    root = _island(tmp_path / "repo", replay=None)
    kw = _inputs(tmp_path, log=_log(before_exit=[f"project {SCRATCH}/island", f"tools {other}/tools35"]))
    with pytest.raises(islands.IslandError, match="session scratch path"):
        islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", scratch_prefix=SCRATCH, **kw)


def test_plain_tmp_paths_are_not_session_paths(tmp_path):
    root = _island(tmp_path / "repo", replay=None)
    kw = _inputs(tmp_path, log=_log(before_exit=["landrun-bwrap: ro=[/ /tmp/tmp.XXWhqYh9] cmd=/elan/bin/lean",
                                                 "/tmp/claude-0/no-uuid-here/x"]))
    res = islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", **kw)
    assert res.verdict == "pass", res.problems


def test_record_replay_normalizes_the_jsons_too(tmp_path):
    # out of scope item (Ruling 9): the probe and fingerprint JSONs get the same normalization, judged as archived
    probes = [_probe_doc(THEOREMS[0], detail=f"no counterexample ({SCRATCH}/env)"), _probe_doc(THEOREMS[1])]
    fp = _fp_doc(trusted_env=f"{SCRATCH}/lean-env")
    root = _island(tmp_path / "repo", replay=None)
    kw = _inputs(tmp_path, log=_log(before_exit=[f"project {SCRATCH}/island"]), probes=probes, fp=fp)
    res = islands.record_replay(root, "demo", date="2026-10-31", comparator_tag="v4.35.0", scratch_prefix=SCRATCH, **kw)
    assert res.verdict == "pass", res.problems
    rd = root / "islands" / "demo" / "replay"
    for f in rd.iterdir():
        text = (lzma.decompress(f.read_bytes()) if f.suffix == ".xz" else f.read_bytes()).decode()
        assert SCRATCH not in text and "/tmp/claude-0" not in text, f.name
    assert "$SCRATCH/lean-env" in (rd / "fingerprint.json").read_text()
    assert islands.status(root, "demo") == "verified"
    # and without the prefix, a JSON carrying the session path is refused like the log
    root_b = _island(tmp_path / "b" / "repo", replay=None)
    kw = _inputs(tmp_path / "b", probes=probes)
    with pytest.raises(islands.IslandError, match="--scratch-prefix"):
        islands.record_replay(root_b, "demo", date="2026-10-31", comparator_tag="v4.35.0", **kw)


def test_replay_refuses_a_tag_without_export_set_before_building(tmp_path):
    # N3: v4.34.0 has a Comparator tag but no COMPARATOR_EXPORTS entry: refuse before hours of building
    root = tmp_path / "repo"
    _island(root, replay=None, toolchain="leanprover/lean4:v4.34.0")
    tools = _tools(tmp_path)
    (tools / "islands" / "demo" / "src" / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
    run = FakeRun()
    with pytest.raises(islands.IslandError, match="export set"):
        islands.replay_island(root, "demo", run=run, tools=tools, date="2026-10-31", leanlock=None)
    assert not any("lake" in c for c in run.calls)


@pytest.mark.parametrize("tc", ["leanprover/lean4:v4.32.0\n", "leanprover/lean4:v4.36.0\n"])
def test_add_refuses_a_toolchain_without_export_set(tmp_path, tc):
    with pytest.raises(islands.IslandError, match="export set|Comparator tag"):
        _add(tmp_path, fetch=_fake_fetch(toolchain=tc))
    assert not (tmp_path / "repo" / "islands" / "demo").exists()


# --- option A: lead-authored challenge overlays ---------------------------------------------------------------------
#
# A fake upstream library with no challenge module: Demo/Defs.lean holds the definition, Demo/Main.lean the two
# theorems (with proofs), Demo/All.lean (the solution) imports Main. The overlay restates both theorems by sorry.

OV_COMMIT = "27cdb2049be62ee2911429b47f54774078450e32"
OV_PATH = "Demo/TelperionChallenge.lean"
OV_MODULE = "Demo.TelperionChallenge"
OV_SOLUTION = "Demo.All"
OV_THEOREMS = ["Demo.two_eq", "Demo.two_pos"]
OV_UPSTREAM = {
    "Demo/Defs.lean": "module\n\npublic import Mathlib\n\nnamespace Demo\n\ndef two : ℕ := 2\n\nend Demo\n",
    "Demo/Main.lean": ("module\n\npublic import Demo.Defs\n\n@[expose] public section\n\nnamespace Demo\n\n"
                       "/-- Two is one plus one. -/\n@[simp]\ntheorem two_eq : two = 1 + 1 := by\n  rfl\n\n"
                       "theorem two_pos :\n    0 < two := by\n  decide\n\nend Demo\n"),
    "Demo/All.lean": "module\n\npublic import Demo.Main\n",
    "lean-toolchain": "leanprover/lean4:v4.35.0\n",
    "LICENSE": APACHE,
}
OVERLAY = ("module\n\npublic import Demo.Defs\n\n/-! A statement-only overlay. -/\n\n@[expose] public section\n\n"
           "namespace Demo\n\n-- upstream: Demo/Main.lean:11\n/-- Two is one plus one. -/\n"
           "theorem two_eq : two = 1 + 1 := by sorry\n\n-- upstream: Demo/Main.lean:14\n"
           "theorem two_pos :\n    0 < two := by sorry\n\nend Demo\n")
OVERLAY_SHA = hashlib.sha256(OVERLAY.encode()).hexdigest()


def _ov_tree(d: Path, files=None, *, git=False) -> Path:
    """The upstream tree at *d*; with *git*, a real committed repo (whose HEAD is then the pin to register)."""
    for rel, text in (OV_UPSTREAM if files is None else files).items():
        (d / rel).parent.mkdir(parents=True, exist_ok=True)
        (d / rel).write_text(text)
    (d / ".git" / "info").mkdir(parents=True, exist_ok=True)
    if git:
        g = ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-c", "commit.gpgsign=false", "-C",
             str(d)]
        subprocess.run(["git", "init", "-q", str(d)], check=True)
        subprocess.run([*g, "add", "-A"], check=True)
        subprocess.run([*g, "commit", "-q", "-m", "pin"], check=True)
    return d


def _ov_fetch(files=None, *, calls=None):
    def fetch(source, commit, dest):
        if calls is not None:
            calls.append(dest)
        _ov_tree(Path(dest), files)
        return OV_COMMIT
    return fetch


def _ov_write(tmp_path: Path, overlay: str = OVERLAY) -> Path:
    p = tmp_path / "authored" / "challenge.lean"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(overlay)
    return p


def _ov_add(tmp_path, *, overlay=OVERLAY, files=None, imports=("Demo.Defs",), solution=OV_SOLUTION, path=OV_PATH,
            run=None):
    return islands.add_overlay_island(tmp_path / "repo", "demo", "https://github.com/AxiomMath/Demo", OV_COMMIT,
                                      "a test overlay island", overlay=_ov_write(tmp_path, overlay),
                                      overlay_path=path, overlay_imports=list(imports), solution_module=solution,
                                      fetch=_ov_fetch(files), run=run or FakeRun(), tools=tmp_path / "tools",
                                      date="2026-11-06")


def _ov_island(root: Path, *, commit=OV_COMMIT, overlay=OVERLAY) -> Path:
    """An unreplayed overlay registration written directly (no clone), as `island add --overlay` writes it."""
    isl = islands.Island(name="demo", source="https://github.com/AxiomMath/Demo", commit=commit,
                         toolchain="leanprover/lean4:v4.35.0", licence="Apache-2.0", challenge_module=OV_MODULE,
                         solution_module=OV_SOLUTION, challenge_sha256=hashlib.sha256(overlay.encode()).hexdigest(),
                         theorems=tuple(OV_THEOREMS), intended_use="a test overlay island", replay=None,
                         challenge_source="overlay", overlay_path=OV_PATH, overlay_imports=("Demo.Defs",))
    d = root / "islands" / "demo"
    d.mkdir(parents=True)
    (d / "island.toml").write_text(islands._dumps_island(isl, None))
    (d / "challenge.lean").write_text(overlay)
    (d / "comparator.json").write_text(islands.comparator_json_text(OV_MODULE, OV_SOLUTION, OV_THEOREMS))
    return root


def _ov_log(*, header="overlay_sha256", sha=OVERLAY_SHA, commit=OV_COMMIT, **kw) -> str:
    """A passing Comparator log for the overlay island: the challenge is the overlay module, the solution upstream's."""
    text = _log(sha=sha, commit=commit, theorems=OV_THEOREMS, **kw)
    return (text.replace(f"challenge_sha256={sha}", f"{header}={sha}")
            .replace("Challenge.Basic", OV_MODULE).replace("Solution.Basic", OV_SOLUTION))


def _ov_evidence(tmp_path: Path, *, log=None, sha=OVERLAY_SHA) -> dict:
    ext = tmp_path / "ext"
    ext.mkdir(exist_ok=True)
    (ext / "comparator.out").write_text(_ov_log() if log is None else log)
    paths = []
    for i, t in enumerate(OV_THEOREMS):
        (ext / f"probe{i}.json").write_bytes(_dump(_probe_doc(t, module=OV_MODULE, source_sha256=sha)))
        paths.append(ext / f"probe{i}.json")
    (ext / "fp.json").write_bytes(_dump(_fp_doc(OV_THEOREMS, module=OV_MODULE, source_sha256=sha)))
    return {"log": ext / "comparator.out", "probe_jsons": paths, "fingerprint_json": ext / "fp.json"}


def test_overlay_add_writes_registration(tmp_path):
    isl = _ov_add(tmp_path)
    d = tmp_path / "repo" / "islands" / "demo"
    assert sorted(p.name for p in d.iterdir()) == ["REPLAY.md", "challenge.lean", "comparator.json", "island.toml"]
    assert (d / "challenge.lean").read_text() == OVERLAY
    doc = tomllib.loads((d / "island.toml").read_text())
    assert doc["challenge_source"] == "overlay" and "challenge_sha256" not in doc and "replay" not in doc
    assert doc["overlay_path"] == OV_PATH and doc["overlay_sha256"] == OVERLAY_SHA
    assert doc["overlay_imports"] == ["Demo.Defs"] and doc["challenge_module"] == OV_MODULE
    assert doc["solution_module"] == OV_SOLUTION and doc["theorems"] == OV_THEOREMS
    assert json.loads((d / "comparator.json").read_text())["challenge_module"] == OV_MODULE
    md = (d / "REPLAY.md").read_text()
    assert "OVERLAY" in md and "`Demo/Main.lean:11`" in md and "`Demo/Main.lean:14`" in md
    assert isl.is_overlay and isl.sha_key == "overlay_sha256" and isl.challenge_sha256 == OVERLAY_SHA
    probs = islands.island_problems(tmp_path / "repo", "demo")
    assert len(probs) == 1 and "not replayed" in probs[0], probs


def _swap(old, new):
    return OVERLAY.replace(old, new)


@pytest.mark.parametrize("kw,needle", [
    ({"overlay": _swap("two = 1 + 1", "two = 2 + 0")}, "differs from upstream"),                   # a changed statement
    ({"overlay": _swap("two = 1 + 1 :=", "two = 1 + 1 ∨ True :=")}, "differs from upstream"),        # a weaker one
    ({"overlay": _swap("Main.lean:11", "Main.lean:10")}, "does not begin a `theorem`"),
    ({"overlay": _swap("Main.lean:14", "Main.lean:11")}, "the theorem there is Demo.two_eq"),
    ({"overlay": _swap("namespace Demo", "namespace Demo.Sub").replace("end Demo", "end Demo.Sub")},
     "the theorem there is Demo.two_eq, not Demo.Sub.two_eq"),
    ({"overlay": _swap("public import Demo.Defs", "public import Demo.Defs\npublic import Demo.Main")},
     "neither Mathlib nor one of overlay_imports"),
    ({"overlay": _swap("public import Demo.Defs", "public import Demo.Main"), "imports": ("Demo.Main",)},
     "would clash"),
    ({"overlay": _swap("namespace Demo\n", "namespace Demo\n\ndef three : ℕ := 3\n")}, "`def` is not allowed"),
    ({"overlay": _swap("namespace Demo\n", "namespace Demo\n\ninstance : Inhabited ℕ := ⟨3⟩\n")}, "not allowed"),
    ({"overlay": _swap("theorem two_pos", "@[simp]\ntheorem two_pos")}, "not allowed"),
    ({"overlay": _swap("theorem two_pos", "private theorem two_pos")}, "not allowed"),
    ({"overlay": _swap("namespace Demo\n", "namespace Demo\n\nset_option autoImplicit true\n")}, "not allowed"),
    ({"overlay": _swap("two = 1 + 1 := by sorry", "two = 1 + 1 := by rfl")}, "not proved `:= by sorry`"),
    ({"overlay": _swap("two = 1 + 1 := by sorry", "two = 1 + 1 := id (by sorry)")}, "not proved `:= by sorry`"),
    ({"overlay": _swap("-- upstream: Demo/Main.lean:14\n", "")}, "no `-- upstream:"),
    ({"overlay": _swap("/-- Two is one plus one. -/", "/-- Two is \"one plus one\". -/") + "#eval \"x\"\n"},
     "string literal"),
    ({"overlay": _swap("end Demo", "end Other")}, "does not close"),
    ({"overlay": OVERLAY + "\nimport Mathlib\n"}, "import after the first command"),
    ({"overlay": _swap("theorem two_pos", "omit [x] in\nnamespace X\ntheorem two_pos")}, "followed by a theorem"),
    ({"solution": "Demo.Lone", "files": {**OV_UPSTREAM, "Demo/Lone.lean": "module\n\npublic import Demo.Defs\n"}},
     "does not import Demo.Main"),
    ({"files": {**OV_UPSTREAM, OV_PATH: "-- an upstream file of that name\n"}}, "ADDED file"),
    ({"files": {**OV_UPSTREAM, "Comparator/comparator.json": json.dumps(AXIOM_CONFIG)}}, "ships Comparator"),
    ({"imports": ("Demo.Defs", "Mathlib.Data.Nat.Basic")}, "Mathlib modules are always allowed"),
    ({"path": "Other/TelperionChallenge.lean"}, "is not a directory of the tree"),
    ({"path": "Other/TelperionChallenge.lean"}, "not under the solution module's root"),
])
def test_overlay_add_refuses_and_writes_nothing(tmp_path, kw, needle):
    with pytest.raises(islands.IslandError, match=needle):
        _ov_add(tmp_path, **kw)
    assert not (tmp_path / "repo" / "islands" / "demo").exists()


def test_overlay_parse_reads_names_pointers_and_headers():
    p = islands.parse_overlay(OVERLAY)
    assert p.problems == () and p.imports == ("Demo.Defs",)
    assert [(t.name, t.upstream) for t in p.theorems] == [("Demo.two_eq", ("Demo/Main.lean", 11)),
                                                         ("Demo.two_pos", ("Demo/Main.lean", 14))]
    assert p.theorems[1].header == "theorem two_pos : 0 < two"
    # nested block comments and `omit ... in` before a theorem; `_root_` names
    text = ("import Mathlib\n/- a /- nested -/ comment theorem bogus : False := by sorry -/\nnamespace A\n"
            "variable {n : ℕ} [NeZero n]\n-- upstream: X.lean:3\nomit [NeZero n] in\n"
            "theorem _root_.B.c : n = n := by sorry\nend A\n")
    p = islands.parse_overlay(text)
    assert p.problems == () and [t.name for t in p.theorems] == ["B.c"] and p.theorems[0].upstream == ("X.lean", 3)
    assert islands.parse_overlay("import Mathlib\n/- open\n").problems


def test_overlay_sha_mismatch_is_refused(tmp_path):
    _ov_add(tmp_path)
    root = tmp_path / "repo"
    p = root / "islands" / "demo" / "challenge.lean"
    p.write_text(OVERLAY + "-- an edit\n")
    probs = islands.island_problems(root, "demo")
    assert any("overlay_sha256" in x and "overlay was edited" in x for x in probs), probs
    with pytest.raises(islands.IslandError, match="overlay_sha256"):
        islands.record_replay(root, "demo", date="2026-11-06", comparator_tag="v4.35.0", **_ov_evidence(tmp_path))
    tree = _ov_tree(tmp_path / "tree")
    with pytest.raises(islands.IslandError, match="overlay_sha256"):
        islands.place_overlay(root, "demo", tree, run=FakeRun(head=OV_COMMIT))
    assert not (tree / OV_PATH).exists()
    # an edit that keeps the overlay statement-only still changes the sha; one that is not, is seen as such too
    p.write_text(OVERLAY.replace("namespace Demo\n", "namespace Demo\n\ndef three : ℕ := 3\n"))
    assert any("`def` is not allowed" in x for x in islands.island_problems(root, "demo"))


def test_overlay_record_replay_binds_the_overlay_sha(tmp_path):
    root = _ov_island(tmp_path / "repo")
    res = islands.record_replay(root, "demo", date="2026-11-06", comparator_tag="v4.35.0", **_ov_evidence(tmp_path))
    assert res.verdict == "pass", res.problems
    assert islands.status(root, "demo") == "verified"
    doc = tomllib.loads((root / "islands" / "demo" / "island.toml").read_text())
    assert doc["replay"]["overlay_sha256"] == OVERLAY_SHA and "challenge_sha256" not in doc["replay"]
    assert islands.load_island(root, "demo").replay.challenge_sha256 == OVERLAY_SHA


@pytest.mark.parametrize("log,needle", [
    (_ov_log(header="challenge_sha256"), "binds a challenge_sha256"),
    (_ov_log(sha="ab" * 32), "is not the registered"),          # a run on another overlay (a changed statement)
    (_ov_log(drop=("Your solution is okay!",)), "did not accept"),   # Comparator rejecting a statement mismatch
])
def test_overlay_record_replay_refuses_a_log_not_bound_to_the_overlay(tmp_path, log, needle):
    root = _ov_island(tmp_path / "repo")
    res = islands.record_replay(root, "demo", date="2026-11-06", comparator_tag="v4.35.0",
                                **_ov_evidence(tmp_path, log=log))
    assert res.verdict == "fail" and any(needle in p for p in res.problems), res.problems
    assert islands.status(root, "demo") == "self-reported"


def test_upstream_island_refuses_an_overlay_header(tmp_path):
    _, res = _record(tmp_path, log=_log().replace("challenge_sha256=", "overlay_sha256="))
    assert res.verdict == "fail" and any("binds a overlay_sha256" in p for p in res.problems), res.problems


def test_overlay_place_and_check_with_real_git(tmp_path):
    tree = _ov_tree(tmp_path / "tree", git=True)
    head = subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    root = _ov_island(tmp_path / "repo", commit=head)
    with pytest.raises(islands.IslandError, match="exactly the pin plus the overlay"):
        islands.place_overlay(root, "demo", tree, check_only=True)               # not placed yet
    out = islands.place_overlay(root, "demo", tree)
    assert out.startswith("OVERLAY-PLACED demo") and OVERLAY_SHA in out
    assert (tree / OV_PATH).read_text() == OVERLAY
    assert islands.place_overlay(root, "demo", tree, check_only=True).startswith("OVERLAY-CHECKED")
    with pytest.raises(islands.IslandError, match="not clean"):
        islands.place_overlay(root, "demo", tree)                                # never twice into one tree
    # an extra file next to the overlay: refused
    (tree / "Demo" / "Extra.lean").write_text("theorem x : True := trivial\n")
    with pytest.raises(islands.IslandError, match="exactly the pin plus the overlay"):
        islands.place_overlay(root, "demo", tree, check_only=True)
    (tree / "Demo" / "Extra.lean").unlink()
    # an edited upstream file: refused
    (tree / "Demo" / "Main.lean").write_text(OV_UPSTREAM["Demo/Main.lean"].replace("decide", "simp"))
    with pytest.raises(islands.IslandError, match="exactly the pin plus the overlay"):
        islands.place_overlay(root, "demo", tree, check_only=True)
    subprocess.run(["git", "-C", str(tree), "checkout", "-q", "--", "Demo/Main.lean"], check=True)
    # the placed overlay edited: refused by its sha
    (tree / OV_PATH).write_text(OVERLAY + "-- x\n")
    with pytest.raises(islands.IslandError, match="not the registered overlay_sha256"):
        islands.place_overlay(root, "demo", tree, check_only=True)
    # a tree that was not pristine before placing: refused, and nothing is written
    tree2 = _ov_tree(tmp_path / "tree2", {**OV_UPSTREAM, "README": "another commit\n"}, git=True)
    head2 = subprocess.run(["git", "-C", str(tree2), "rev-parse", "HEAD"], capture_output=True,
                           text=True).stdout.strip()
    root2 = _ov_island(tmp_path / "repo2", commit=head2)
    (tree2 / "stray.lean").write_text("x\n")
    with pytest.raises(islands.IslandError, match="not clean"):
        islands.place_overlay(root2, "demo", tree2)
    assert not (tree2 / OV_PATH).exists()
    with pytest.raises(islands.IslandError, match="HEAD"):
        islands.place_overlay(root, "demo", tree2)                               # another commit's tree


class OverlayRun(FakeRun):
    """FakeRun whose `git status` reports what is really in the clone: the overlay once it has been placed."""

    def __call__(self, argv, *, cwd, env=None, timeout):
        if "status" in argv:
            self.calls.append(list(argv))
            extra = sorted(str(p.relative_to(cwd)) for p in Path(cwd).rglob("*.lean")
                           if str(p.relative_to(cwd)) not in OV_UPSTREAM)
            return islands.RunResult(0, "".join(f"?? {p}\n" for p in extra))
        return super().__call__(argv, cwd=cwd, env=env, timeout=timeout)


def _ov_tools(tmp_path) -> Path:
    t = _tools(tmp_path)
    src = t / "islands" / "demo" / "src"
    shutil.rmtree(src / "Challenge")
    _ov_tree(src)
    return t


def test_overlay_replay_places_the_overlay_and_builds_it(tmp_path):
    root = _ov_island(tmp_path / "repo")
    tools = _ov_tools(tmp_path)
    probes = {t: _probe_doc(t, module=OV_MODULE, source_sha256=OVERLAY_SHA) for t in OV_THEOREMS}
    run = OverlayRun(head=OV_COMMIT, comparator="\n".join(_ov_log().splitlines()[4:-1]) + "\n", probes=probes,
                     fp=_fp_doc(OV_THEOREMS, module=OV_MODULE, source_sha256=OVERLAY_SHA))
    res = islands.replay_island(root, "demo", run=run, tools=tools, date="2026-11-06", leanlock=None)
    assert res.verdict == "pass", res.problems
    assert (tools / "islands" / "demo" / "src" / OV_PATH).read_text() == OVERLAY
    log = (tools / "islands" / "demo" / "comparator.log").read_text()
    assert log.splitlines()[0] == f"ISLAND-HEADER island=demo commit={OV_COMMIT} overlay_sha256={OVERLAY_SHA}"
    build = next(c for c in run.calls if "build" in c and "lake" in c)
    assert build[build.index("build") + 1:] == [OV_MODULE]                     # R-1: the challenge only
    probe = next(c for c in run.calls if "probe-negation" in c)
    assert probe[probe.index("--module") + 1] == OV_MODULE and probe[probe.index("--file") + 1].endswith(OV_PATH)
    assert islands.status(root, "demo") == "verified"
    # a second replay on the same clone is refused: the overlay is already there, so it is not a fresh copy
    run2 = OverlayRun(head=OV_COMMIT)
    with pytest.raises(islands.IslandError, match="not clean"):
        islands.replay_island(root, "demo", run=run2, tools=tools, date="2026-11-06", leanlock=None)
    assert not any("lake" in c for c in run2.calls)


def test_overlay_replay_refuses_a_clone_that_does_not_match(tmp_path):
    root = _ov_island(tmp_path / "repo")
    tools = _ov_tools(tmp_path)
    main = tools / "islands" / "demo" / "src" / "Demo" / "Main.lean"
    main.write_text(main.read_text().replace("two = 1 + 1", "two = 2"))     # the pin's statement is not the overlay's
    run = OverlayRun(head=OV_COMMIT)
    with pytest.raises(islands.IslandError, match="differs from upstream"):
        islands.replay_island(root, "demo", run=run, tools=tools, date="2026-11-06", leanlock=None)
    assert not any("lake" in c for c in run.calls)
    assert not (tools / "islands" / "demo" / "src" / OV_PATH).exists()


@pytest.mark.parametrize("patch,needle", [
    ({"overlay_path": "Demo/Elsewhere.lean"}, "must be the challenge module's file"),
    ({"challenge_source": "upstream"}, "must be \"overlay\""),
    ({"overlay_imports": []}, "non-empty array"),
    ({"overlay_imports": ["Mathlib"]}, "Mathlib modules are always allowed"),
    ({"overlay_path": "../Demo/TelperionChallenge.lean"}, "plain relative path"),
    ({"solution_module": OV_MODULE}, "must differ from its solution_module"),
    ({"challenge_sha256": "ab" * 32}, "unknown key 'challenge_sha256'"),
])
def test_overlay_schema_is_strict(tmp_path, patch, needle):
    root = _ov_island(tmp_path / "repo")
    p = root / "islands" / "demo" / "island.toml"
    doc = tomllib.loads(p.read_text())
    doc.update(patch)
    p.write_text("\n".join(f"{k} = {_toml_value(v)}" for k, v in doc.items()) + "\n")
    probs = islands.island_problems(root, "demo")
    assert any(needle in x for x in probs), probs


def test_upstream_island_refuses_overlay_keys(tmp_path):
    root = _island(tmp_path, replay=None, overlay_path=OV_PATH)
    assert any("unknown key 'overlay_path'" in p for p in islands.island_problems(root, "demo"))


def test_existing_islands_are_unchanged():
    # the overlay mode adds keys only to overlay islands: both upstream registrations read and re-serialize byte for
    # byte, and riemann-jensen is still verified
    for name in ("riemann-jensen", "zeta-zeros-v2"):
        isl = islands.load_island(ROOT, name)
        assert not isl.is_overlay and isl.sha_key == "challenge_sha256"
        assert islands._dumps_island(isl, isl.replay) == (ROOT / "islands" / name / "island.toml").read_text()
    assert islands.island_problems(ROOT, "riemann-jensen") == []
    probs = islands.island_problems(ROOT, "zeta-zeros-v2")
    assert len(probs) == 1 and "not replayed" in probs[0], probs


def test_cli_overlay_flags(tmp_path):
    root = _island(tmp_path / "repo", replay=None)
    r = _cli("island", "add", "x", "--source", "https://github.com/AxiomMath/X", "--commit", OV_COMMIT, "--use", "u",
             "--overlay-path", OV_PATH, "--root", str(root))
    assert r.returncode == 1 and "only go with --overlay" in r.stderr
    r = _cli("island", "add", "x", "--source", "https://github.com/AxiomMath/X", "--commit", OV_COMMIT, "--use", "u",
             "--overlay", str(_ov_write(tmp_path)), "--root", str(root))
    assert r.returncode == 1 and "--overlay needs --overlay-path, --overlay-import, --solution-module" in r.stderr
    r = _cli("island", "place-overlay", "demo", "--tree", str(tmp_path), "--root", str(root))
    assert r.returncode == 1 and "not an overlay island" in r.stderr
    tree = _ov_tree(tmp_path / "tree", git=True)
    head = subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    root2 = _ov_island(tmp_path / "repo2", commit=head)
    r = _cli("island", "place-overlay", "demo", "--tree", str(tree), "--root", str(root2))
    assert r.returncode == 0 and r.stdout.startswith("OVERLAY-PLACED"), r.stderr
    r = _cli("island", "place-overlay", "demo", "--tree", str(tree), "--check-only", "--root", str(root2))
    assert r.returncode == 0 and r.stdout.startswith("OVERLAY-CHECKED"), r.stderr


def test_weil_is_registered_as_an_overlay_island():
    # island #3 (owner decision 2026-11-06): AxiomMath/Weil @ 27cdb204, a lead-authored overlay of the two point-count
    # statements; self-reported until the sandbox replay is recorded
    isl = islands.load_island(ROOT, "weil")
    assert isl.is_overlay and isl.commit == "27cdb2049be62ee2911429b47f54774078450e32"
    assert isl.toolchain == "leanprover/lean4:v4.34.0-rc2" and isl.overlay_imports == ("Weil.Definitions",)
    assert isl.theorems == ("Weil.exists_zetaSeries_mul_prod_even_eq_prod_odd",
                            "AlgebraicGeometry.exists_mul_zetaSeries_eq")
    text = (ROOT / "islands" / "weil" / "challenge.lean").read_text()
    assert islands.overlay_problems(text, isl) == []
    assert {t.name: t.upstream for t in islands.parse_overlay(text).theorems} == {
        "Weil.exists_zetaSeries_mul_prod_even_eq_prod_odd":
            ("Weil/AlgebraicGeometry/EtaleCohomology/Trace/WeilRiemannHypothesisForm.lean", 206),
        "AlgebraicGeometry.exists_mul_zetaSeries_eq":
            ("Weil/AlgebraicGeometry/EtaleCohomology/Trace/ZetaRationality.lean", 170)}
    probs = islands.island_problems(ROOT, "weil")
    assert len(probs) == 1 and "not replayed" in probs[0], probs
    assert islands._dumps_island(isl, None) == (ROOT / "islands" / "weil" / "island.toml").read_text()


def test_overlay_matches_an_upstream_lemma_with_an_attribute_on_its_line(tmp_path):
    # `@[simp] lemma` on the declaration's own line: the attribute is not part of the statement, `lemma` is `theorem`
    main = OV_UPSTREAM["Demo/Main.lean"].replace("@[simp]\ntheorem two_eq", "@[simp] lemma two_eq\n")
    main = main.replace("lemma two_eq\n : two", "lemma two_eq : two")
    files = {**OV_UPSTREAM, "Demo/Main.lean": main.replace("/-- Two is one plus one. -/\n", "/-- Two. -/\n\n")}
    assert "@[simp] lemma two_eq : two = 1 + 1 := by" in files["Demo/Main.lean"]
    isl = _ov_add(tmp_path, files=files)
    assert isl.theorems == tuple(OV_THEOREMS)



# --- R-1 / R-2 (bb, REVIEW_OVERLAY_WEIL_236dea6) ----------------------------------------------------------------------

class TouchingRun(FakeRun):
    """FakeRun that writes into the clone as the real steps would: `lake build` leaves the challenge build's artifacts
    (the clone's own and two packages'), and the Comparator step runs *touch* (a solution build)."""

    def __init__(self, *, touch=None, **kw):
        super().__init__(**kw)
        self.touch = touch

    def __call__(self, argv, *, cwd, env=None, timeout):
        if "lake" in argv and "build" in argv:
            for rel in (".lake/build/lib/lean/Challenge/Basic.olean",
                        ".lake/packages/mathlib/.lake/build/lib/lean/M.olean",
                        ".lake/packages/Stacks/.lake/build/lib/lean/S.olean"):
                (Path(cwd) / rel).parent.mkdir(parents=True, exist_ok=True)
                (Path(cwd) / rel).write_bytes(rel.encode())
        if "comparator" in argv and self.touch:
            self.touch(Path(cwd))
        return super().__call__(argv, cwd=cwd, env=env, timeout=timeout)


def test_replay_never_builds_the_solution_before_comparator(tmp_path):
    # R-1: the only pre-build names the challenge; Comparator compiles the solution after its challenge export
    run = FakeRun()
    root, res = _replay(tmp_path, run)
    assert res.verdict == "pass", res.problems
    lake = [c for c in run.calls if "lake" in c]
    assert [c[c.index("lake") + 1:] for c in lake[:2]] == [["exe", "cache", "get"], ["build", "Challenge.Basic"]]
    assert lake[2][lake[2].index("lake") + 1:][:2] == ["env", "comparator"]
    assert not any("Solution.Basic" in a for c in run.calls for a in c)
    log = (tmp_path / "tools" / "islands" / "demo" / "comparator.log").read_text()
    assert any(l.startswith("COMPARATOR_PREBUILD ") for l in log.splitlines())
    assert islands.status(root, "demo") == "verified"


def test_replay_snapshots_the_challenge_build_and_refuses_a_change(tmp_path):
    tools = _tools(tmp_path)
    root, res = _replay(tmp_path, TouchingRun())
    assert res.verdict == "pass", res.problems
    snap = (tools / "islands" / "demo" / "prebuild.sha256").read_text().splitlines()
    assert len(snap) == 3 and any(l.endswith(".lake/build/lib/lean/Challenge/Basic.olean") for l in snap)
    # a solution build that rewrites one of the challenge build's artifacts fails the replay; a new file does not
    def touch(src):
        (src / ".lake/build/lib/lean/Solution.olean").write_bytes(b"new")
        (src / ".lake/packages/Stacks/.lake/build/lib/lean/S.olean").write_bytes(b"rewritten")
    root2, res2 = _replay(tmp_path / "b", TouchingRun(touch=touch))
    assert res2.verdict == "fail" and any("artifact(s) of the challenge build changed" in p and "S.olean" in p
                                          for p in res2.problems), res2.problems
    assert islands.load_island(root2, "demo").replay is None


def test_replay_hands_non_env_packages_to_the_checks(tmp_path):
    run = TouchingRun()
    _replay(tmp_path, run)
    for c in (c for c in run.calls if "probe-negation" in c or "fingerprint" in c):
        dirs = [c[i + 1] for i, a in enumerate(c) if a == "--olean-dir"]
        assert len(dirs) == 1 and dirs[0].endswith(".lake/packages/Stacks/.lake/build/lib/lean"), c


def test_replay_copy_space_gate(tmp_path, monkeypatch):
    # R-2: the private copy of the untrusted closure goes to the temp dir; refuse before copying when it cannot fit
    from telperion.checks import lean_replay
    f = tmp_path / "a.olean"
    f.write_bytes(b"x" * 1000)
    assert lean_replay.copy_space_problem([f], tmp_path) is None
    Usage = type("Usage", (), {})
    u = Usage()
    u.total, u.used, u.free = 10 ** 9, 10 ** 9, 10
    monkeypatch.setattr(lean_replay.shutil, "disk_usage", lambda p: u)
    problem = lean_replay.copy_space_problem([f], tmp_path)
    assert problem and "TMPDIR" in problem and "1000" in problem and str(tmp_path) in problem
