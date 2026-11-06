import os
import re
import subprocess
import sys
import time
from pathlib import Path
import pytest
from telperion.checks.fingerprint import parse_fingerprints, render_fingerprint_callback

sys.path.insert(0, str(Path(__file__).resolve().parent))  # shared lean_env helpers
from lean_env import fake_trusted_env, session_trusted_manifest  # noqa: E402

N = "0123456789abcdef" * 2      # a fixed nonce for the pure parser tests


def test_parse():
    out = (f"noise\nFP-BEGIN {N} foo\n∀ (_ : Nat), ...\nFP-END {N} foo\nFP-BEGIN {N} bar\nX\nFP-END {N} bar\n"
           f"FP-DONE {N}\n")
    fp = parse_fingerprints(out, N)
    assert set(fp) == {"foo", "bar"} and len(fp["foo"]) == 64 and fp["foo"] != fp["bar"]


def test_parse_missing_target_raises():
    with pytest.raises(ValueError, match="baz"):
        parse_fingerprints(f"FP-MISSING {N} baz\nFP-DONE {N}\n", N)


def test_render_mentions_targets_and_roots():
    s = render_fingerprint_callback(["foo"], N)
    assert "`foo" in s and "deltaExpand" in s and "`Mathlib" in s


# Step 5 Task 6: value mode, a `def … : Prop`'s VALUE.
def test_render_selects_the_mode():
    assert "def tpValueMode : Bool := false" in render_fingerprint_callback(["foo"], N)
    assert "def tpValueMode : Bool := true" in render_fingerprint_callback(["foo"], N, mode="value")
    assert "tpFingerprintValue env ci" in render_fingerprint_callback(["foo"], N, mode="value")


def test_render_refuses_an_unknown_mode():
    with pytest.raises(ValueError, match="mode"):
        render_fingerprint_callback(["foo"], N, mode="values")


def test_render_target_named_like_a_placeholder_stays_data():
    # targets are substituted LAST, so a name spelled like a placeholder is never re-scanned
    s = render_fingerprint_callback(["__VALUE_MODE__", "__NONCE__"], N, mode="value")
    assert "[`__VALUE_MODE__, `__NONCE__]" in s and "def tpValueMode : Bool := true" in s


def test_unknown_mode_refused_before_any_lean(tmp_path):
    from telperion.checks.fingerprint import _fingerprint
    with pytest.raises(ValueError, match="mode must be one of"):
        _fingerprint(tmp_path, [], ["t"], None, 1, body="theorem t : True := trivial\n", mode="both")


def test_cli_mode_value_reaches_the_run_and_the_json(monkeypatch, capsys):
    import json
    from telperion import cli
    from telperion.checks import fingerprint as fp_
    seen = {}

    def ok(project, imports, targets, wrapper=None, timeout=0, mode="type", **kw):
        seen["mode"] = mode
        return fp_.Fingerprints({t: "a" * 64 for t in targets}, "b" * 64, [], [], mode)
    monkeypatch.setattr(fp_, "run_fingerprint", ok)
    assert cli.main(["fingerprint", "--project", ".", "--import", "M", "--target", "S", "--mode", "value",
                     "--json"]) == 0
    assert seen["mode"] == "value" and json.loads(capsys.readouterr().out)["mode"] == "value"
    with pytest.raises(SystemExit):
        cli.main(["fingerprint", "--project", ".", "--import", "M", "--target", "S", "--mode", "values"])


# Task 6 fix round 1: the statement module's own declarations (I1) and the trusted env digest (M2).
def test_render_list_declared_takes_the_closure():
    plain = render_fingerprint_callback(["foo"], N)
    listed = render_fingerprint_callback(["foo"], N, list_declared=True)
    assert "def TelperionReplay.callback : TermElabM Unit" in plain and "FP-DECL" not in plain
    assert "def TelperionReplay.callback (c : TelperionReplay.Closure) : TermElabM Unit" in listed
    assert "for n in c.target do" in listed and "n.isInternal" in listed


def test_parse_declared_reads_only_this_runs_lines():
    from telperion.checks.fingerprint import parse_declared
    out = (f"FP-DECL {N} theorem A.main\nFP-DECL {N} propdef S\nFP-DECL {'f' * 32} theorem forged\n"
           f"FP-DECL {N} inductive X\nnoise FP-DECL {N} theorem nope\nFP-DECL {N} other Box.mk\n")
    assert parse_declared(out, N) == {"theorem": ["A.main"], "propdef": ["S"], "other": ["Box.mk"]}


def test_parse_ranges_needs_its_done_line_and_unique_names():
    from telperion.checks.fingerprint import parse_ranges
    out = f"FP-RANGE {N} 3 0 A.main\nFP-RANGE {'f' * 32} 9 0 forged\nFP-RANGE {N} 1 0 S\nFP-RANGES-DONE {N}\n"
    assert parse_ranges(out, N) == {"A.main": (3, 0), "S": (1, 0)}
    with pytest.raises(ValueError, match="did not finish"):
        parse_ranges(f"FP-RANGE {N} 3 0 A.main\n", N)
    with pytest.raises(ValueError, match="twice"):
        parse_ranges(f"FP-RANGE {N} 3 0 A\nFP-RANGE {N} 4 0 A\nFP-RANGES-DONE {N}\n", N)


def test_trusted_env_digest_is_machine_independent(tmp_path):
    from telperion.checks.lean_replay import build_trusted_manifest, pinned_env, trusted_env_digest
    digests = []
    for name in ("one", "two"):
        env, elan, manifest = fake_trusted_env(tmp_path / name)
        digests.append(trusted_env_digest(pinned_env(env, elan), manifest))
    assert digests[0] == digests[1] and len(digests[0]) == 64       # same content, other absolute paths
    env, elan, _m = fake_trusted_env(tmp_path / "three")
    (env / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").write_bytes(b"another mathlib")
    m3 = build_trusted_manifest(env, tmp_path / "three" / "m3.json", elan)
    assert trusted_env_digest(pinned_env(env, elan), m3) != digests[0]


LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set")


@pytest.fixture(autouse=True)
def _trusted_manifest(request):
    # Lean tests: the real env's trusted manifest, built once per process in a temp dir
    if LEAN_ENV and request.node.get_closest_marker("skipif") is not None:
        session_trusted_manifest(LEAN_ENV)


def _fp(tmp_text: str, target: str, **kw) -> str:
    from telperion.checks.fingerprint import run_fingerprint_on_text
    return run_fingerprint_on_text(Path(LEAN_ENV), tmp_text, target, **kw)


@lean
def test_shadowed_definition_changes_hash():                 # MUST-FAIL control
    a = "import Mathlib\ndef bound : ℕ := 5\ntheorem t : ∀ n : ℕ, n < bound → n < 10 := by intro n h; unfold bound at h; omega\n"
    b = a.replace(":= 5", ":= 6")
    assert _fp(a, "t") != _fp(b, "t")


@lean
def test_binder_rename_same_hash():                          # MUST-PASS control
    a = "import Mathlib\ntheorem t : ∀ n : ℕ, n < 3 → n < 10 := by omega\n"
    b = a.replace("∀ n : ℕ, n < 3 → n < 10", "∀ m : ℕ, m < 3 → m < 10")
    assert _fp(a, "t") == _fp(b, "t")


@lean
def test_argument_swap_changes_hash():                       # MUST-FAIL control
    a = "import Mathlib\ntheorem t : ∀ a b : ℕ, a ≤ a + b := by omega\n"
    b = a.replace("a ≤ a + b", "b ≤ a + b")
    assert _fp(a, "t") != _fp(b, "t")


# Fix round 1 (Ruling 6): structural serialization; refuse what deltaExpand cannot unfold.
def test_parse_refused_raises():
    with pytest.raises(ValueError, match="refused.*t Good inductive"):
        parse_fingerprints(f"FP-REFUSED {N} t Good inductive\nFP-DONE {N}\n", N)


def test_parse_empty_serialization_raises():
    with pytest.raises(ValueError, match="empty"):
        parse_fingerprints(f"FP-BEGIN {N} foo\n\nFP-END {N} foo\nFP-DONE {N}\n", N)


def test_parse_hashes_ellipsis_in_string_literal():
    assert len(parse_fingerprints(f'FP-BEGIN {N} foo\n(str "⋯")\nFP-END {N} foo\nFP-DONE {N}\n', N)["foo"]) == 64


def test_parse_unterminated_block_raises():
    with pytest.raises(ValueError, match="foo"):
        parse_fingerprints(f"FP-BEGIN {N} foo\nX\nFP-DONE {N}\n", N)


# Fix round 2 (C1): every marker carries the run's nonce; one result per target; a final FP-DONE.
def test_parse_wrong_nonce_raises():
    other = "f" * 32
    with pytest.raises(ValueError, match="nonce"):
        parse_fingerprints(f"FP-BEGIN {other} t\nX\nFP-END {other} t\nFP-BEGIN {N} t\nY\nFP-END {N} t\nFP-DONE {N}\n", N)


def test_parse_marker_without_nonce_raises():
    with pytest.raises(ValueError, match="nonce"):
        parse_fingerprints(f"FP-BEGIN t\nX\nFP-END t\nFP-DONE {N}\n", N)


def test_parse_duplicate_block_raises():
    with pytest.raises(ValueError, match="duplicate.*t"):
        parse_fingerprints(f"FP-BEGIN {N} t\nX\nFP-END {N} t\nFP-BEGIN {N} t\nY\nFP-END {N} t\nFP-DONE {N}\n", N)


def test_parse_missing_done_raises():
    with pytest.raises(ValueError, match="FP-DONE"):
        parse_fingerprints(f"FP-BEGIN {N} t\nX\nFP-END {N} t\n", N)


def test_parse_marker_after_done_raises():
    with pytest.raises(ValueError, match="FP-DONE"):
        parse_fingerprints(f"FP-DONE {N}\nFP-BEGIN {N} t\nX\nFP-END {N} t\nFP-DONE {N}\n", N)


def test_render_is_structural_and_imports_programmatically():
    # phase 2: the callback runs on the kernel REPLAY (lean_replay); nothing is imported, programmatically or not
    s = render_fingerprint_callback(["t"], N)
    assert "ppExpr" not in s and "pp.all" not in s and "tpSer" in s and "FP-REFUSED" in s
    assert not any(ln.startswith("import") for ln in s.splitlines()) and "importModules" not in s
    assert "def TelperionReplay.callback" in s and "tpFingerprint env ci" in s
    assert N in s and "too-large" in s and "sorry" in s


@pytest.mark.parametrize("spoof", ["Mathlib/Foo.lean", "src/Lean/Bar.lean", "Std.lean"])
def test_library_root_spoof_refused(tmp_path, spoof):
    from telperion.checks.fingerprint import run_fingerprint, run_fingerprint_on_text
    f = tmp_path / spoof
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text("def bound : Nat := 5\n", encoding="utf-8")
    root = spoof.replace(".lean", "").split("/")[-2 if "/" in spoof else 0]
    with pytest.raises(ValueError, match=f"library root.*{root}"):
        run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=["false"])
    with pytest.raises(ValueError, match=f"library root.*{root}"):
        run_fingerprint_on_text(tmp_path, "import Mathlib\ntheorem t : True := trivial\n", "t", wrapper=["false"])
    assert not (tmp_path / ".telperion_fingerprint").exists()


def test_symlinked_dir_refused(tmp_path):
    from telperion.checks.fingerprint import run_fingerprint
    outside = tmp_path / "outside"
    (outside / "Mathlib").mkdir(parents=True)
    (outside / "Mathlib/Evil.lean").write_text("def bound : Nat := 5\n", encoding="utf-8")
    proj = tmp_path / "proj"
    proj.mkdir()
    (proj / "vendor").symlink_to(outside, target_is_directory=True)
    with pytest.raises(ValueError, match="symlink.*vendor"):
        run_fingerprint(proj, ["Mathlib"], ["t"], wrapper=["false"])


def test_spoof_check_ignores_lake_packages(tmp_path):
    from telperion.checks.fingerprint import run_fingerprint
    (tmp_path / ".lake/packages/mathlib/Mathlib").mkdir(parents=True)
    (tmp_path / ".lake/packages/mathlib/Mathlib/Foo.lean").write_text("", encoding="utf-8")
    with pytest.raises(ValueError) as exc:                       # passes the spoof check, then `false` fails
        run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=["false"])
    assert "library root" not in str(exc.value) and "symlink" not in str(exc.value)


@pytest.fixture
def fake_env(tmp_path_factory, monkeypatch):
    """A fake pinned env (outside the test's project dir) with its manifest; ELAN_HOME points at its toolchain."""
    env, elan, manifest = fake_trusted_env(tmp_path_factory.mktemp("trusted"))
    monkeypatch.setenv("ELAN_HOME", str(elan))
    monkeypatch.setenv("TELPERION_TRUSTED_MANIFEST", str(manifest))
    return env


def _fake_lean(monkeypatch, body_for, calls=None):
    """Replace run_lean (phase 2: in fingerprint, for the body compile, and in lean_replay, for the replay run): a
    body compile writes its -o olean; the replay run answers the replay protocol around body_for(nonce). `calls` gets
    (cmd, script text) per call."""
    from telperion.checks import fingerprint as fp_
    from telperion.checks import lean_replay

    from lean_env import fake_replay_output

    def fake(cmd, cwd, timeout, input=None, env=None):
        if "-o" in cmd:
            if calls is not None:
                calls.append((list(cmd), None))
            out = Path(cwd, cmd[cmd.index("-o") + 1])
            out.write_bytes(b"olean")
            return 0, ""
        script = Path(cmd[-1]).read_text(encoding="utf-8")
        if "def listOnly : Bool := true" in script:           # R2: the list run names the closure's files
            return 0, fake_replay_output(script)
        if calls is not None:
            calls.append((list(cmd), script))
        nonce = re.search(r'tpNonce : String := "([0-9a-f]{32})"', script).group(1)
        return 0, fake_replay_output(script, body_for(nonce))
    monkeypatch.setattr(fp_, "run_lean", fake)
    monkeypatch.setattr(lean_replay, "run_lean", fake)
    return fp_


def test_escaped_target_key_is_found(monkeypatch, tmp_path, fake_env):
    # Lean prints `«my thm»`; the caller passes `my thm`
    fp_ = _fake_lean(monkeypatch, lambda n: f'FP-BEGIN {n} «my thm»\n(c _."True" [])\nFP-END {n} «my thm»\nFP-DONE {n}\n')
    assert len(fp_.run_fingerprint(tmp_path, ["Mathlib"], ["my thm"], wrapper=[], trusted_env=fake_env)["my thm"]) == 64


def test_nonce_is_fresh_per_run(monkeypatch, tmp_path, fake_env):
    seen = []
    fp_ = _fake_lean(monkeypatch, lambda n: seen.append(n) or f"FP-BEGIN {n} t\nX\nFP-END {n} t\nFP-DONE {n}\n")
    fp_.run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=[], trusted_env=fake_env)
    fp_.run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=[], trusted_env=fake_env)
    assert len(seen) == 2 and seen[0] != seen[1] and all(re.fullmatch(r"[0-9a-f]{32}", n) for n in seen)


def _env(root: Path, packages) -> Path:
    import json
    env, _elan, _m = fake_trusted_env(root)
    (env / "lake-manifest.json").write_text(json.dumps({"packagesDir": ".lake/packages", "packages": packages}),
                                            encoding="utf-8")
    return env


# Phase 2: the trust anchors are lean_replay.pinned_env's (the pinned toolchain's lib dir and the env's package BUILD
# dirs, found on disk); lake-manifest.json is never read for trust.
def test_trusted_prefixes_from_pinned_env(tmp_path):
    from telperion.checks.lean_replay import pinned_env
    env = _env(tmp_path / "t", [{"name": "mathlib", "type": "git"}])
    p = pinned_env(env, tmp_path / "t" / "elan")
    assert p.prefixes == (os.path.realpath(tmp_path / "t/elan/toolchains/leanprover--lean4---v4.35.0/lib/lean"),
                          os.path.realpath(env / ".lake/packages/mathlib/.lake/build/lib/lean"))


def test_manifest_dir_field_never_widens_trust(tmp_path):
    # I-B: `"dir": "."` or an absolute dir would have trusted the env root (its own build) or anything at all
    from telperion.checks.lean_replay import pinned_env
    env = _env(tmp_path / "t", [{"name": "mathlib", "dir": "."}, {"name": "evil", "dir": "/"}])
    got = pinned_env(env, tmp_path / "t" / "elan").prefixes
    assert os.path.realpath(env) not in got and "/" not in got
    assert got[1:] == (os.path.realpath(env / ".lake/packages/mathlib/.lake/build/lib/lean"),)


@pytest.mark.parametrize("manifest", ['{"packages": "x"}', '{"packages": [{"nam": 1}]}', "[1]", "{not json",
                                      '{"packages": [{"name": "../x"}]}', '{"packages": [{"name": 3}]}',
                                      '{"packagesDir": 7, "packages": []}'])
def test_malformed_manifest_is_value_error(tmp_path, manifest, monkeypatch):
    # phase 2: a malformed lake-manifest.json cannot change what is trusted (it is never parsed for trust); it only
    # changes the default trusted-manifest path, so a manifest built for other pins never matches
    from telperion.checks.lean_replay import default_manifest_path, pinned_env
    monkeypatch.delenv("TELPERION_TRUSTED_MANIFEST", raising=False)     # R2-M5: else the path check is vacuous
    env = _env(tmp_path / "t", [{"name": "mathlib"}])
    before = (pinned_env(env, tmp_path / "t" / "elan").prefixes, default_manifest_path(env))
    (env / "lake-manifest.json").write_text(manifest, encoding="utf-8")
    assert pinned_env(env, tmp_path / "t" / "elan").prefixes == before[0]
    assert default_manifest_path(env) != before[1]


def test_non_env_project_packages_untrusted(tmp_path):
    from telperion.checks.lean_replay import pinned_env, under_prefix
    env = _env(tmp_path / "t", [{"name": "mathlib"}])
    proj = tmp_path / "proj"
    evil = proj / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Evil.olean"
    evil.parent.mkdir(parents=True)
    evil.write_bytes(b"x")
    assert not under_prefix(evil, pinned_env(env, tmp_path / "t" / "elan").prefixes)


def test_trusted_env_required(tmp_path, monkeypatch):
    from telperion.checks.fingerprint import run_fingerprint
    monkeypatch.delenv("TELPERION_LEAN_ENV", raising=False)
    with pytest.raises(ValueError, match="trusted env"):
        run_fingerprint(tmp_path, ["Mathlib"], ["t"], wrapper=[])


def test_trusted_env_defaults_to_lean_env_var(tmp_path, monkeypatch, fake_env):
    from telperion.checks.lean_replay import pinned_env
    calls = []
    fp_ = _fake_lean(monkeypatch, lambda n: f"FP-BEGIN {n} t\nX\nFP-END {n} t\nFP-DONE {n}\n", calls)
    monkeypatch.setenv("TELPERION_LEAN_ENV", str(fake_env))
    proj = tmp_path / "proj"
    proj.mkdir()
    fp_.run_fingerprint(proj, ["Mathlib"], ["t"], wrapper=[])
    # phase 2: one replay run, by the env var's pinned lean, with LEAN_PATH = its trusted entries only
    p = pinned_env(fake_env)
    runs = [c for c, _ in calls]
    assert len(runs) == 1 and p.lean in runs[0] and f"LEAN_PATH={os.pathsep.join(p.entries)}" in runs[0]


def test_body_module_is_random_and_dir_per_run(monkeypatch, tmp_path, fake_env):
    calls = []
    fp_ = _fake_lean(monkeypatch, lambda n: f"FP-BEGIN {n} t\nX\nFP-END {n} t\nFP-DONE {n}\n", calls)
    (tmp_path / ".telperion_fingerprint").mkdir()            # a stale fixed-name dir no longer wedges a run
    for _ in range(2):
        fp_.run_fingerprint_on_text(tmp_path, "theorem t : True := trivial\n", "t", wrapper=[], trusted_env=fake_env)
    compiles = [c for c, _ in calls if "-o" in c]
    mods = [re.search(r"(TelperionFpBody_[0-9a-f]{16})\.olean$", c[c.index("-o") + 1]).group(1) for c in compiles]
    assert len(mods) == 2 and mods[0] != mods[1]
    scripts = [inp for c, inp in calls if inp is not None]
    for mod, script in zip(mods, scripts):
        assert f"`{mod}" in script
        # phase 2/R2: the body olean is compiled in a private temp dir, COPIED into the replay's run dir and
        # replayed from the copy; the script pins the copy's exact path
        assert re.search(rf'\(`{mod}, ".*/telperion_replay_[^/"]+/olean/{mod}\.olean"\)', script)
    assert sorted(p.name for p in tmp_path.iterdir()) == [".telperion_fingerprint"]    # nothing left in the project


# Fix round 2 (I2): the process-group runner.
def test_run_lean_output_and_stdin(tmp_path):
    from telperion.checks.lean_run import run_lean
    assert run_lean(["sh", "-c", "cat; echo err >&2; exit 3"], tmp_path, 10, input="hi\n") == (3, "hi\nerr\n")


def test_run_lean_timeout_kills_grandchild(tmp_path):
    from telperion.checks.lean_run import run_lean
    pidf = tmp_path / "pid"
    with pytest.raises(subprocess.TimeoutExpired):
        run_lean(["sh", "-c", f"sleep 60 & echo $! > {pidf}; wait"], tmp_path, 1)
    pid = int(pidf.read_text())
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return
        time.sleep(0.1)
    pytest.fail(f"grandchild {pid} outlived the timeout")


def test_run_lean_output_is_bounded(tmp_path):
    # final review M4: more than max_output bytes on a stream is OutputLimitExceeded (an OSError: ERROR for callers)
    from telperion.checks.lean_run import OutputLimitExceeded, run_lean
    assert run_lean(["sh", "-c", "echo hi"], tmp_path, 10, max_output=10) == (0, "hi\n")
    with pytest.raises(OutputLimitExceeded):                     # caught at the end of a short run
        run_lean(["sh", "-c", "head -c 2000000 /dev/zero"], tmp_path, 30, max_output=1_000_000)
    with pytest.raises(OutputLimitExceeded):                     # on stderr too
        run_lean(["sh", "-c", "head -c 2000000 /dev/zero >&2"], tmp_path, 30, max_output=1_000_000)
    start = time.monotonic()
    with pytest.raises(OutputLimitExceeded):                     # an endless writer is killed while it runs
        run_lean(["sh", "-c", "yes"], tmp_path, 120, max_output=1_000_000)
    assert time.monotonic() - start < 30
    assert issubclass(OutputLimitExceeded, OSError)


@pytest.mark.parametrize("redirect", [" >/dev/null 2>&1", ""])      # "" : the daemon also holds the pipes
def test_run_lean_reaps_daemon_after_normal_exit(tmp_path, redirect):
    # I-A: a body compile that leaves `sleep 3; touch MARKER` behind and exits 0 must not get to touch MARKER
    from telperion.checks.lean_run import run_lean
    marker = tmp_path / "MARKER"
    start = time.monotonic()
    rc, _ = run_lean(["sh", "-c", f"(sleep 3; touch {marker}){redirect} & exit 0"], tmp_path, 30)
    assert rc == 0 and time.monotonic() - start < 2.5
    time.sleep(4)
    assert not marker.exists()


# Fix round 1 Lean controls. MUST-FAIL: non-def local constants are refused, never hashed by name.
def _refused(text: str, what: str, **kw):
    with pytest.raises(ValueError, match=f"refused.*{what}"):
        _fp(text, "t", **kw)


# Step 6 Task 2b: the declaration closure. A local inductive (structure, mutual group) is hashed by its declaration
# block; a non-library theorem (an elaborator-lifted `_proof_<n>` or a user's lemma: lead ruling 2026-11-05, no name test) by
# its type. Negative controls first: each must give a DIFFERENT hash or a REFUSED.
BOX = "import Mathlib\nstructure Box where\n  val : ℕ\ntheorem t : ∀ b : Box, b.val = b.val := fun _ => rfl\n"
GOOD = "import Mathlib\ninductive Good : ℕ → Prop\n  | mk : Good 5\n  | other : Good 6\ntheorem t : Good 5 := .mk\n"


def _fp_or_refused(text: str, target: str = "t"):
    """The hash, or None when refused (fail closed counts as a distinct outcome)."""
    try:
        return _fp(text, target)
    except ValueError as exc:
        assert "refused" in str(exc), exc
        return None


def _differs(base: str, variant: str, target: str = "t") -> None:
    got = _fp_or_refused(variant, target)
    assert got is None or got != _fp(base, target)


@lean
def test_closure_a_field_type_changed_differs():            # MUST-FAIL control (a)
    _differs(BOX, BOX.replace("val : ℕ", "val : ℤ"))


@lean
def test_closure_b_extra_field_differs():                   # MUST-FAIL control (b)
    _differs(BOX, BOX.replace("val : ℕ\n", "val : ℕ\n  w : ℕ\n"))


@lean
def test_closure_c_renamed_constructor_differs():           # MUST-FAIL control (c)
    _differs(BOX, BOX.replace("Box where\n", "Box where\n  mk' ::\n"))


@lean
def test_closure_d_constructor_order_swapped_differs():     # MUST-FAIL control (d)
    _differs(GOOD, GOOD.replace("  | mk : Good 5\n  | other : Good 6\n", "  | other : Good 6\n  | mk : Good 5\n"))


@lean
def test_closure_e_user_theorem_through_definition_hashes_by_type():    # policy (lead ruling 2026-11-05), was control (e)
    # every non-library theorem is accepted by its TYPE: `⟨3, lem⟩` and `⟨3, by omega⟩` (lifted to `f._proof_1` by
    # the elaborator) are one statement, and a differently typed lemma is another
    a = "import Mathlib\ntheorem lem : 3 < 5 := by omega\ndef f : Fin 5 := ⟨3, lem⟩\ntheorem t : f = f := rfl\n"
    b = "import Mathlib\ndef f : Fin 5 := ⟨3, by omega⟩\ntheorem t : f = f := rfl\n"
    assert len(_fp(a, "t")) == 64 and _fp(a, "t") == _fp(b, "t")
    _differs(a, a.replace("3 < 5 := by omega", "3 < 6 := by omega").replace("Fin 5", "Fin 6"))


@lean
def test_closure_f_axiom_inside_a_structure_field_refused():     # MUST-FAIL control (f), recursion into the block
    _refused("import Mathlib\naxiom ax : ℕ\nstructure B where\n  v : Fin ax\ntheorem t : ∀ b : B, b = b := fun _ => rfl\n",
             "ax axiom")
    # ... and inside a theorem's TYPE, reached only through the proof constant (the statement itself never mentions
    # `ax`: `lem`'s type is `(fun _ => 3 < 5) ax`, defeq to `3 < 5` by beta)
    _refused("import Mathlib\naxiom ax : ℕ\ntheorem lem : (fun _ : ℕ => 3 < 5) ax := by show 3 < 5; omega\n"
             "def f : Fin 5 := ⟨3, lem⟩\ntheorem t : f = f := rfl\n", "ax axiom")


# (g) policy (lead ruling 2026-11-05, following bb's REVIEW_PLAN_FP_CLOSURE 0aefdf7b): a user-declared theorem,
# `foo._proof_1` or any other name, IS accepted, because only its TYPE is hashed (`(prf <type>)`): the name and the
# proof never enter the hash, so it contributes exactly what an elaborator-generated proof of the same proposition
# would. A false-typed lemma cannot change what the statement
# says: a proof of `False` serializes as `(prf (c _."False" []))`, a different statement from the honest one; and
# a sorry in its proof is invisible to the hash and is caught by the proof-side axiom audit; on a body with no
# sorry of its own the replay's axioms (`Fingerprints.axioms`) show it too.
FIN_T = "theorem t : (⟨3, {p}⟩ : Fin 5) = ⟨3, {p}⟩ := rfl\n"


@lean
def test_closure_g_user_named_theorem_hashes_by_type():
    from telperion.checks.fingerprint import _fingerprint
    a = "import Mathlib\ntheorem foo._proof_1 : 3 < 5 := by omega\n" + FIN_T.format(p="foo._proof_1")
    b = "import Mathlib\ntheorem bar.lem : 3 < 5 := Nat.lt_of_sub_eq_succ rfl\n" + FIN_T.format(p="bar.lem")
    c = "import Mathlib\ntheorem foo._proof_1 : 3 < 5 := sorry\n" + FIN_T.format(p="foo._proof_1")
    ha = _fp(a, "t")
    assert len(ha) == 64 and ha == _fp(b, "t")                 # the hash is of the type: name and proof irrelevant
    fa = _fingerprint(Path(LEAN_ENV), [], ["t"], None, 900, body=a)
    fc = _fingerprint(Path(LEAN_ENV), [], ["t"], None, 900, body=c)
    assert fa["t"] == ha and "sorryAx" not in fa.axioms
    assert fc["t"] == ha and "sorryAx" in fc.axioms              # same statement; the sorry is not hidden
    # a false-typed lemma: the statement that uses it is a different statement
    d = "import Mathlib\ntheorem foo._proof_1 : False := sorry\n" + FIN_T.format(p="foo._proof_1.elim")
    assert _fp_or_refused(d) != ha


@lean
def test_closure_sorry_inside_lifted_proof_reported_in_axioms():    # MUST-FAIL control (bb pre-flag 2)
    from telperion.checks.fingerprint import _fingerprint
    honest = "import Mathlib\ndef f : Fin 5 := ⟨3, by omega⟩\ntheorem t : f = f := rfl\n"
    # A sorry'd proof is NEVER lifted to `f._proof_1`: `abstractNestedProofs` skips any proof with `sorry`
    # (`!e.hasSorry`, Lean/Meta/AbstractNestedProofs.lean), so `⟨3, sorry⟩` stays inline in `f`'s value, unfolding
    # puts `sorryAx` in the statement itself, and the fingerprint refuses it (`sorryAx sorry`).
    _refused(honest.replace("by omega", "sorry"), "sorryAx sorry")
    # A lifted proof CAN carry a sorry transitively: `hasSorry` does not see through a constant, so a nested
    # `Nat.lt_trans lem h` with `theorem lem := sorry` IS lifted to `f._proof_1 : 3 < 5`. The fingerprint hashes
    # that proof's TYPE (the honest hash), and the replay's axiom collection over the module reports the sorry.
    sorried = ("import Mathlib\ntheorem lem : 3 < 4 := sorry\n"
               "def f : Fin 5 := ⟨3, Nat.lt_trans lem (by decide)⟩\ntheorem t : f = f := rfl\n")
    fh = _fingerprint(Path(LEAN_ENV), [], ["t"], None, 900, body=honest)
    fs = _fingerprint(Path(LEAN_ENV), [], ["t"], None, 900, body=sorried)
    assert fh["t"] == fs["t"]                                     # the fingerprint hashes the proof's TYPE
    assert "sorryAx" not in fh.axioms and "sorryAx" in fs.axioms  # the replay's axiom collection catches the sorry


@lean
def test_closure_projection_only_field_emits_the_whole_block():     # bb pre-flag 3: `.proj S i` emits S's block
    # `p.b` unfolds to `Expr.proj Pair 1 p`: Pair is reached ONLY through a projection, and the statement never
    # mentions field `a`; the block still carries it, so changing `a`'s type changes the hash
    a = ("import Mathlib\nstructure Pair where\n  a : ℕ\n  b : ℕ\n"
         "theorem t : ∀ p : Pair, p.b = p.b := fun _ => rfl\n")
    assert len(_fp(a, "t")) == 64
    _differs(a, a.replace("a : ℕ", "a : ℤ"))


# Positive controls.
@lean
def test_closure_local_structure_fingerprints():            # MUST-PASS control
    assert len(_fp(BOX, "t")) == 64
    rec = "import Mathlib\nstructure Box where\n  val : ℕ\ntheorem t : ∀ b : Box, b.casesOn (fun v => v) = b.val := fun _ => rfl\n"
    assert len(_fp(rec, "t")) == 64                          # through `Box.casesOn` → `Box.rec`
    assert len(_fp(GOOD, "t")) == 64                          # a constructor of a local inductive


@lean
def test_closure_same_structure_same_name_other_module_hash_equal():     # MUST-PASS control, determinism
    other = BOX.replace("theorem t", "def unrelated : ℕ := 7\ntheorem t")      # another (random-named) module
    assert _fp(BOX, "t") == _fp(other, "t")


@lean
def test_closure_aux_proof_in_definition_value_fingerprints():           # MUST-PASS control
    a = "import Mathlib\ndef f (n : ℕ) : Fin 5 := ⟨n % 5, by omega⟩\ntheorem t : f 3 = f 3 := rfl\n"
    b = a.replace("by omega", "Nat.mod_lt _ (by decide)")                 # another proof of the same proposition
    assert len(_fp(a, "t")) == 64 and _fp(a, "t") == _fp(b, "t")


@lean
def test_closure_nested_local_structures_fingerprint():                  # MUST-PASS + MUST-FAIL (recursion)
    a = ("import Mathlib\nstructure Leaf0 where\n  x : ℕ\nstructure Tree0 where\n  i : Leaf0\n"
         "theorem t : ∀ o : Tree0, o.i.x = o.i.x := fun _ => rfl\n")      # (`Inner` is a Mathlib class)
    assert len(_fp(a, "t")) == 64
    _differs(a, a.replace("x : ℕ", "x : ℤ"))                   # Leaf0's field only reachable through Tree0's block


@lean
def test_closure_mutual_inductive_pair_fingerprints():                   # MUST-PASS + MUST-FAIL
    a = ("import Mathlib\nmutual\ninductive Ev : ℕ → Prop\n  | zero : Ev 0\n  | succ {n} : Od n → Ev (n + 1)\n"
         "inductive Od : ℕ → Prop\n  | succ {n} : Ev n → Od (n + 1)\nend\ntheorem t : Ev 0 := .zero\n")
    assert len(_fp(a, "t")) == 64
    _differs(a, a.replace("Ev n → Od (n + 1)", "Ev n → Od (n + 2)"))     # Od only reachable through Ev's group


# bb's review of 3c49ed0 (REVIEW_TASK2B_3c49ed0 6f8ef0b4), recommended tests.
@lean
def test_closure_nested_inductive_refused_by_the_replay():              # fail closed (known replay limitation)
    # A NESTED local inductive never reaches the serializer: the kernel replay (lean_replay, the same logic as
    # upstream Lean/Replay.lean in v4.35.0) refuses it, since its auxiliary recursor `Rose.rec_1` is not found after
    # re-adding the declaration. The serializer's handling of `numNested > 0` is pinned without the replay, in
    # `test_serializer_injectivity_cases` (NESTED line).
    a = "import Mathlib\ninductive Rose where\n  | node : List Rose → Rose\ntheorem t : ∀ r : Rose, r = r := fun _ => rfl\n"
    with pytest.raises(ValueError, match=r"replay refused.*No such recursor Rose\.rec_1"):
        _fp(a, "t")


@lean
def test_closure_universe_polymorphic_structure():                      # MUST-PASS + MUST-FAIL (level numbering)
    # the block numbers Wrap's levels by ITS OWN levelParams (positionally), the use site carries the instantiation
    a = ("import Mathlib\nstructure Wrap.{u} (α : Type u) where\n  x : α\n"
         "theorem t : ∀ w : Wrap ℕ, w.x = w.x := fun _ => rfl\n")
    b = a.replace(".{u}", ".{v}").replace("Type u", "Type v")             # renamed level: same declaration
    assert len(_fp(a, "t")) == 64 and _fp(a, "t") == _fp(b, "t")
    poly = ("import Mathlib\nstructure Wrap.{u} (α : Type u) where\n  x : α\n"
            "theorem t.{w} : ∀ (β : Type w) (v : Wrap.{w} β), v.x = v.x := fun _ _ => rfl\n")
    fixed = poly.replace("theorem t.{w}", "theorem t").replace("Type w", "Type").replace("Wrap.{w}", "Wrap.{0}")
    assert _fp(poly, "t") != _fp(fixed, "t")                     # (P 0) at the use site vs z
    _differs(a, a.replace("x : α", "x : List α"))


@lean
def test_closure_theorem_type_mentions_local_inductive():               # MUST-PASS + MUST-FAIL (across kinds)
    # `Box` is reached ONLY through `lem`'s TYPE (`(fun _ : Box → ℕ => 3 < 5) Box.val`, defeq to `3 < 5`): the proof
    # constant's type gets fingerprinted, which notes Box's block, so changing Box's field type changes the hash
    a = ("import Mathlib\nstructure Box where\n  val : ℕ\n"
         "theorem lem : (fun _ : Box → ℕ => 3 < 5) Box.val := by show 3 < 5; omega\n"
         "def f : Fin 5 := ⟨3, lem⟩\ntheorem t : f = f := rfl\n")
    assert len(_fp(a, "t")) == 64
    _differs(a, a.replace("val : ℕ", "val : ℤ").replace("Box → ℕ", "Box → ℤ"))


# Requirement 4: hashes recorded by the f90d983 code (scratch baseline, 2026-11-01) for statements with no local
# inductive and no auxiliary proof; the extension must not move them.
PINS = {
    "import Mathlib\ntheorem t : ∀ n : ℕ, n < 3 → n < 10 := by omega\n":
        "f39bccc915e717fbb61dbb0a591acba4e3cb11b114ab363e25cdb9bab50e0d0e",
    "import Mathlib\ntheorem t : True := trivial\n":
        "e4f5ccc4fc8144be2097a5d2d8b4bdc2dab169c6d0b30ae5294f84620bee26c9",
    "import Mathlib\ntheorem t.{u} {α : Sort u} (a : α) : a = a := rfl\n":
        "beac8a0d2e65ba018264ce89caa60e40e20bd5a702852d43db5cb4b123920f28",
    "import Mathlib\ntheorem t : ∀ p : ℕ × ℕ, p.1 + p.2 = p.2 + p.1 := fun p => Nat.add_comm _ _\n":
        "06a9258fb33eb79981413948629be41d7a74bd01b35489868e38841238296222",
    "import Mathlib\ndef bound : ℕ := 5\ntheorem t : ∀ n : ℕ, n < bound → n < 10 := by intro n h; unfold bound at h; omega\n":
        "36b29ce841827823228f39b219402a812873f70c5827a5a558e078642235263f",
}


@lean
def test_regression_pins_f90d983():
    from telperion.checks.fingerprint import _fingerprint
    for body, want in PINS.items():
        assert _fp(body, "t") == want, body
    vb = "import Mathlib\ndef S : Prop := ∀ n : ℕ, n + 0 = n\ntheorem t : S := fun n => rfl\n"
    assert dict(_fingerprint(Path(LEAN_ENV), [], ["S"], None, 900, body=vb, mode="value"))["S"] == \
        "8923733b8a40e2beb506ae45a77f22c6fadbd943885cee0389459abe0738652b"


def test_render_has_declaration_closure_tags():
    from telperion.checks import fingerprint
    s = render_fingerprint_callback(["t"], N)
    for tag in ('"(prf "', '"(ind ', '" (ctor ', '" (grp"', "tpIsProof", "tpBuildCtx", "numNested"):
        assert tag in s, tag
    assert "_proof_" in fingerprint.__doc__ and "(prf" in fingerprint.__doc__ and "lead ruling 2026-11-05" in fingerprint.__doc__
    assert "amendment 1" not in fingerprint.__doc__ and "proof-side axiom audit" in " ".join(fingerprint.__doc__.lower().split())
    assert "tpIsPropType" in s and "non-prop-theorem" in s


@lean
def test_irreducible_def_refused():                          # MUST-FAIL control
    _refused("import Mathlib\nirreducible_def ibound : ℕ := 5\ntheorem t : ∀ n : ℕ, n < ibound → n < ibound := fun _ h => h\n",
             "ibound")


@lean
def test_nat_vs_int_differ_under_pp_explicit_false():        # MUST-FAIL control
    a = "import Mathlib\nset_option pp.explicit false\nset_option pp.all false\ntheorem t : (2 : ℕ) = 2 := rfl\n"
    assert _fp(a, "t") != _fp(a.replace("ℕ", "ℤ"), "t")


@lean
def test_universe_param_rename_same_hash():                  # MUST-PASS control
    a = "import Mathlib\ntheorem t.{u} {α : Sort u} (a : α) : a = a := rfl\n"
    b = a.replace(".{u}", ".{v}").replace("Sort u", "Sort v")
    assert _fp(a, "t") == _fp(b, "t")


@lean
def test_quoted_target_name():                               # MUST-PASS control
    assert len(_fp("import Mathlib\ntheorem «my thm» : True := trivial\n", "my thm")) == 64


# Fix round 2 Lean controls.
FAKE_TRUE = '(c _.\\"True\\" [])'


@lean
@pytest.mark.parametrize("trick", [
    # the reviewer's spoof: a fake block for `True`, then #exit before anything else is checked
    'theorem t : False := sorry\n#eval IO.println "FP-BEGIN {n} t\\n{fake}\\nFP-END {n} t\\nFP-DONE {n}"\n#exit\n',
    'theorem t : False := sorry\n#eval (do IO.println "FP-BEGIN {n} t\\n{fake}\\nFP-END {n} t\\nFP-DONE {n}"; '
    'IO.Process.exit 0 : IO Unit)\n',
    'theorem t : False := sorry\ninitialize IO.println "FP-BEGIN {n} t\\n{fake}\\nFP-END {n} t\\nFP-DONE {n}"\n',
])
def test_body_cannot_spoof_markers(trick):                   # MUST-FAIL control (C1)
    body = "import Mathlib\n" + trick.format(n=N, fake=FAKE_TRUE)
    true_hash = _fp("import Mathlib\ntheorem t : True := trivial\n", "t")
    false_hash = _fp("import Mathlib\ntheorem t : False := sorry\n", "t")
    try:
        got = _fp(body, "t")
    except ValueError:
        return                                              # refused: fine
    assert got == false_hash != true_hash


@lean
def test_doubling_definitions_too_large_fast():              # MUST-FAIL control (I1)
    defs = "def a0 : ℕ := 1\n" + "".join(f"def a{k + 1} : ℕ := a{k} + a{k}\n" for k in range(20))
    start = time.monotonic()
    _refused("import Mathlib\n" + defs + "theorem t : a20 = a20 := rfl\n", "too-large", timeout=60)
    assert time.monotonic() - start < 60


@lean
def test_local_axiom_refused():                              # MUST-FAIL control
    _refused("import Mathlib\naxiom ax : ℕ\ntheorem t : ax = ax := rfl\n", "ax axiom")


@lean
def test_local_opaque_refused():                             # MUST-FAIL control
    _refused("import Mathlib\nopaque op : ℕ\ntheorem t : op = op := rfl\n", "op opaque")


@lean
def test_sorry_in_statement_refused():                       # MUST-FAIL control (M3)
    _refused("import Mathlib\ntheorem t : (sorry : ℕ) = 0 := sorry\n", "sorry")


@lean
def test_local_universe_polymorphic_def_unfolds():           # MUST-PASS control
    a = ("import Mathlib\ndef idf.{w} (α : Sort w) (x : α) : α := x\n"
         "theorem t.{u} {α : Sort u} (a : α) : idf α a = a := rfl\n")
    b = a.replace(".{w}", ".{z}").replace("Sort w", "Sort z").replace(".{u}", ".{v}").replace("Sort u", "Sort v")
    direct = "import Mathlib\ntheorem t.{u} {α : Sort u} (a : α) : a = a := rfl\n"
    assert _fp(a, "t") == _fp(b, "t") == _fp(direct, "t")


@lean
def test_untrusted_library_module_refused():                 # MUST-FAIL control (I3)
    # with no trusted prefixes, every Mathlib/Init module's olean is untrusted: the Lean-side check must fire
    from telperion.checks.fingerprint import _fingerprint
    with pytest.raises(ValueError, match="untrusted-library-module"):
        _fingerprint(Path(LEAN_ENV), [], ["t"], None, 600,
                     body="import Mathlib\ntheorem t : True := trivial\n", trusted=[])


@lean
def test_body_olean_identity_checked():                      # MUST-FAIL control (I-C)
    # the Lean side must refuse when the body module resolves anywhere but this run's build path
    from telperion.checks.fingerprint import _fingerprint
    with pytest.raises(ValueError, match="body-olean-mismatch"):
        _fingerprint(Path(LEAN_ENV), [], ["t"], None, 600, body="import Mathlib\ntheorem t : True := trivial\n",
                     expect_body_olean="/nonexistent/elsewhere.olean")


@lean
def test_serializer_injectivity_cases():                     # serializer unit cases (Lean only, no Mathlib)
    from telperion.checks.fingerprint import HELPERS, ROOTS_DEF
    from telperion.checks.lean_run import run_lean
    from telperion.checks.negation_probe import default_wrapper
    script = "import Lean\nopen Lean Meta\n" + ROOTS_DEF.replace("__ROOTS__", "[`Init]") + HELPERS + r'''
def ser (e : Expr) : String := match (tpSer {} [] e).run {} with
  | .ok ((), st) => st.out
  | .error m => "ERR " ++ m
def nat : Expr := .const ``Nat []
#eval do
  let cases : List (String × Expr × Expr) := [
    ("binderInfo", .forallE `n nat (.bvar 0) .implicit, .forallE `n nat (.bvar 0) .default),
    ("instImplicit", .forallE `n nat (.bvar 0) .instImplicit, .forallE `n nat (.bvar 0) .strictImplicit),
    ("letE nonDep", .letE `x nat (.lit (.natVal 1)) (.bvar 0) true, .letE `x nat (.lit (.natVal 1)) (.bvar 0) false),
    ("quote in name", .const (.str .anonymous "a\"b") [], .const (.str (.str .anonymous "a") "b") []),
    ("» in name", .const (.str .anonymous "a.b»") [], .const (.str (.str .anonymous "a") "b»") []),
    ("str lit", .lit (.strVal "a\" b"), .lit (.strVal "a\\\" b")),
    ("binder name ignored", .lam `x nat (.bvar 0) .default, .lam `y nat (.bvar 0) .default)]
  for (label, x, y) in cases do
    IO.println s!"CASE {label} | {ser x == ser y} | {ser x} | {ser y}"
  IO.println s!"TOSTRING-COLLIDES {(Name.str .anonymous "a.b»").toString == (Name.str (.str .anonymous "a") "b»").toString}"
open Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let all := Expr.forallE `n nat (mkApp3 (.const ``Eq [levelOne]) nat (.bvar 0) (.bvar 0)) .default
  for (label, e) in [("Nat", nat), ("True", Expr.const ``True []), ("forall-eq", all)] do
    IO.println s!"PROP {label} {← tpIsPropType env e}"
inductive TpRose where
  | node : List TpRose → TpRose
open Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let st : Expr := .forallE `r (.const `TpRose []) (mkApp3 (.const ``Eq [levelOne]) (.const `TpRose []) (.bvar 0) (.bvar 0)) .default
  match ← tpFingerprintExpr env [] st with
  | .ok s => IO.println s!"NESTED {s}"
  | .error e => IO.println s!"NESTED-ERR {e}"
'''
    rc, out = run_lean([*default_wrapper(), "lake", "env", "lean", "--stdin"], Path(LEAN_ENV), 600, input=script)
    assert rc == 0, out
    eq = {m.group(1): m.group(2) == "true" for m in re.finditer(r"^CASE (.+?) \| (true|false) \|", out, re.M)}
    assert eq == {"binderInfo": False, "instImplicit": False, "letE nonDep": False, "quote in name": False,
                  "» in name": False, "str lit": False, "binder name ignored": True}, out
    assert "TOSTRING-COLLIDES true" in out          # why tpSerName does not use Name.toString
    # the `(prf …)` premise re-check: a Nat-typed "theorem" is refused (non-prop-theorem), a proposition is not
    assert "PROP Nat false" in out and "PROP True true" in out and "PROP forall-eq true" in out, out
    # a nested inductive (bb's review of 3c49ed0): one block, numParams 0, numIndices 0, numNested 1, its one
    # constructor with its nested field type
    nested = re.search(r"^NESTED (.*)$", out, re.M)
    assert nested, out
    assert '(grp (ind _."TpRose" 0 (s (S z)) 0 0 1 ' in nested.group(1), nested.group(1)
    assert ' (ctor _."TpRose"."node" 1 ' in nested.group(1) and nested.group(1).count("(grp") == 1, nested.group(1)


# CLI (restored: the round-2 rewrite of this file dropped it), with --trusted-env (I-B).
def test_cli_prints_hashes_and_exits_2_on_missing(monkeypatch, capsys):
    from telperion import cli
    from telperion.checks import fingerprint as fp_
    seen = {}

    def ok(project, imports, targets, wrapper=None, timeout=0, trusted_env=None, mode="type"):
        seen["trusted_env"] = trusted_env
        return {t: "a" * 64 for t in targets}
    monkeypatch.setattr(fp_, "run_fingerprint", ok)
    assert cli.main(["fingerprint", "--project", ".", "--import", "Mathlib", "--target", "foo", "--target", "bar",
                     "--trusted-env", "/pinned/env"]) == 0
    assert capsys.readouterr().out == f"foo {'a' * 64}\nbar {'a' * 64}\n" and seen["trusted_env"] == Path("/pinned/env")

    def missing(project, imports, targets, wrapper=None, timeout=0, trusted_env=None, mode="type"):
        raise ValueError("target not found: baz")
    monkeypatch.setattr(fp_, "run_fingerprint", missing)
    assert cli.main(["fingerprint", "--project", ".", "--import", "Mathlib", "--target", "baz",
                     "--trusted-env", "/pinned/env"]) == 2
    assert "baz" in capsys.readouterr().out


def test_cli_without_trusted_env_exits_2(monkeypatch, capsys, tmp_path):
    from telperion import cli
    monkeypatch.delenv("TELPERION_LEAN_ENV", raising=False)
    assert cli.main(["fingerprint", "--project", str(tmp_path), "--import", "Mathlib", "--target", "t"]) == 2
    assert "trusted env" in capsys.readouterr().out


def test_cli_help_says_not_a_sandbox(capsys):
    from telperion import cli
    with pytest.raises(SystemExit):
        cli.main(["fingerprint", "--help"])
    out = " ".join(capsys.readouterr().out.split())
    assert "--trusted-env" in out and "NOT a sandbox" in out


# Phase 2: CLI --json carries the olean binding; the trusted-manifest subcommand; a missing manifest is exit 2.
def test_cli_json_includes_olean_sha256(monkeypatch, capsys):
    import json
    from telperion import cli
    from telperion.checks import fingerprint as fp_

    def ok(project, imports, targets, wrapper=None, timeout=0, **kw):
        return fp_.Fingerprints({t: "a" * 64 for t in targets}, "b" * 64, [["M", "olean", "c" * 64]], ["propext"])
    monkeypatch.setattr(fp_, "run_fingerprint", ok)
    assert cli.main(["fingerprint", "--project", ".", "--import", "M", "--target", "foo", "--json"]) == 0
    assert json.loads(capsys.readouterr().out) == {"fingerprints": {"foo": "a" * 64}, "olean_sha256": "b" * 64,
                                                   "olean_closure": [["M", "olean", "c" * 64]],
                                                   "module": "M", "theorem": "foo", "source_sha256": None,
                                                   "axioms": ["propext"],      # final review I3: the replay's axioms
                                                   "mode": "type",             # step 5 Task 6
                                                   "trusted_env_sha256": None}  # fix round 1 (M2)


def test_cli_trusted_manifest_build_verify(tmp_path, monkeypatch, capsys):
    from telperion import cli
    env, elan, _m = fake_trusted_env(tmp_path / "t")
    monkeypatch.setenv("ELAN_HOME", str(elan))
    out = tmp_path / "m.json"
    assert cli.main(["trusted-manifest", "build", "--env", str(env), "--out", str(out)]) == 0 and out.is_file()
    assert cli.main(["trusted-manifest", "build", "--env", str(env), "--out", str(out)]) == 2       # R2-M4
    assert "already exists" in capsys.readouterr().out
    assert cli.main(["trusted-manifest", "build", "--env", str(env), "--out", str(out), "--force"]) == 0
    assert cli.main(["trusted-manifest", "verify", "--env", str(env), "--out", str(out)]) == 0
    (env / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Evil.olean").write_bytes(b"planted")
    assert cli.main(["trusted-manifest", "verify", "--env", str(env), "--out", str(out)]) == 2
    assert "1 added" in capsys.readouterr().out


def test_cli_missing_manifest_exits_2_naming_the_build_command(tmp_path, monkeypatch, capsys):
    from telperion import cli
    env, elan, _m = fake_trusted_env(tmp_path / "t")
    monkeypatch.setenv("ELAN_HOME", str(elan))
    monkeypatch.setenv("TELPERION_TRUSTED_MANIFEST", str(tmp_path / "absent.json"))
    proj = tmp_path / "proj"
    proj.mkdir()
    assert cli.main(["fingerprint", "--project", str(proj), "--import", "M", "--target", "t",
                     "--trusted-env", str(env)]) == 2
    assert "telperion trusted-manifest build --env" in capsys.readouterr().out
    assert cli.main(["probe-negation", "--project", str(proj), "--module", "M", "--theorem", "t", "--json",
                     "--trusted-env", str(env)]) == 2
    assert "telperion trusted-manifest build --env" in capsys.readouterr().out


# Phase 2 MUST-FAIL control: the evil module (initialize that reads the script for the nonce and forges a block, a
# #eval override, an omega override, a compile-time forging #eval). Replayed, the fingerprint is the TRUE hash of its
# statement (or a refusal), both from text and from a built module.
EVIL = r'''import Mathlib
open Lean Elab Command Tactic
#eval IO.println "FP-BEGIN 00000000000000000000000000000000 TpEvil.t\n(c _.\"True\" [])\nFP-END 00000000000000000000000000000000 TpEvil.t"
initialize do
  IO.println "TPEVIL-INIT"
  for e in ← System.FilePath.readDir "." do
    if let .ok s ← (IO.FS.readFile e.path).toBaseIO then
      for l in s.splitOn "\n" do
        if l.startsWith "def tpNonce : String := " then
          if let _ :: n :: _ := l.splitOn "\"" then
            IO.println s!"FP-BEGIN {n} TpEvil.t\n(c _.\"True\" [])\nFP-END {n} TpEvil.t\nFP-DONE {n}"
@[command_elab Lean.Parser.Command.eval] def tpEvilEval : CommandElab := fun _ => IO.println "TPEVIL-EVAL"
@[tactic Lean.Parser.Tactic.omega] def tpEvilOmega : Tactic := fun _ => do
  IO.println "TPEVIL-TACTIC"
  for g in ← getGoals do g.admit
theorem TpEvil.t : ∀ n : ℕ, n < 3 → n < 10 := fun n h => Nat.lt_trans h (by decide)
'''


@lean
def test_evil_module_gives_the_true_hash(tmp_path):                  # MUST-FAIL control (phase 2)
    from telperion.checks.fingerprint import run_fingerprint
    import hashlib
    from telperion.checks.lean_replay import closure_digest, default_wrapper
    true_hash = _fp("import Mathlib\ntheorem t : ∀ n : ℕ, n < 3 → n < 10 := by omega\n", "t")
    try:
        got = _fp(EVIL, "TpEvil.t")
        assert got == true_hash
    except ValueError:
        pass                                                    # refused: fine
    # a BUILT evil module, replayed from its own dir
    lib = Path(LEAN_ENV) / f".tp_fp_{os.urandom(8).hex()}"
    try:
        (lib / "src").mkdir(parents=True)
        (lib / "src" / "TpEvilFp.lean").write_text(EVIL, encoding="utf-8")
        p = subprocess.run([*default_wrapper(), "lake", "env", "lean", "-R", str(lib / "src"), "-o",
                            str(lib / "TpEvilFp.olean"), str(lib / "src" / "TpEvilFp.lean")], cwd=LEAN_ENV,
                           capture_output=True, text=True, timeout=1800)
        assert p.returncode == 0, p.stdout + p.stderr
        fps = run_fingerprint(Path(LEAN_ENV), ["TpEvilFp"], ["TpEvil.t"], untrusted_paths=[lib])
        assert fps["TpEvil.t"] == true_hash
        closure = [["TpEvilFp", "olean", hashlib.sha256((lib / "TpEvilFp.olean").read_bytes()).hexdigest()]]
        assert fps.olean_closure == closure and fps.olean_sha256 == closure_digest(closure)
    finally:
        import shutil
        shutil.rmtree(lib, ignore_errors=True)


# Step 5 Task 6: value mode. One body, every mode-relevant case, two Lean runs (one per mode).
VALUE_BODY = """import Mathlib
def S : Prop := ∀ n : ℕ, n + 0 = n
theorem t : S := fun n => rfl
theorem t' : ∀ n : ℕ, n + 0 = n := fun n => rfl
theorem h (n : ℕ) (k : n = 0) : n = n := rfl
def SU.{u} : Prop := ∀ (α : Sort u) (a : α), a = a
theorem tu.{v} : SU.{v} := fun _ _ => rfl
theorem tu'.{w} : ∀ (α : Sort w) (a : α), a = a := fun _ _ => rfl
theorem tu0 : SU.{0} := fun _ _ => rfl
"""


def _fps(text: str, targets: list, mode: str) -> dict:
    from telperion.checks.fingerprint import _fingerprint
    return dict(_fingerprint(Path(LEAN_ENV), [], targets, None, 900, body=text, mode=mode))


@lean
def test_value_mode_equals_type_mode_of_a_theorem_of_it():           # MUST-PASS control (Task 6)
    value = _fps(VALUE_BODY, ["S", "SU"], "value")
    typ = _fps(VALUE_BODY, ["t", "t'", "h", "tu", "tu'", "tu0"], "type")
    # `def S : Prop := body` (value) == `theorem t : S` (type) == `theorem t' : body` (type)
    assert value["S"] == typ["t"] == typ["t'"]
    assert typ["h"] != typ["t"]                                     # MUST-FAIL: a helper of another type
    # universe-polymorphic: `def SU.{u}` against `theorem tu.{v} : SU.{v}` and the inlined `tu'.{w}`, each
    # numbered by its own level parameters; `SU.{0}` is another statement
    assert value["SU"] == typ["tu"] == typ["tu'"] != typ["tu0"]


@lean
def test_value_mode_refuses_what_is_not_a_def_of_prop():             # MUST-FAIL control (Task 6)
    body = ("import Mathlib\ntheorem t : True := trivial\nopaque op : ℕ\ndef N : ℕ := 3\n"
            "def F (n : ℕ) : Prop := n = n\ndef T : Type := ℕ\n")
    with pytest.raises(ValueError) as exc:
        _fps(body, ["t", "op", "N", "F", "T", "propext"], "value")
    msg = str(exc.value)
    assert "refused" in msg
    for target, why in [("t", "value-mode-not-a-def theorem"), ("op", "value-mode-not-a-def opaque"),
                        ("N", "value-mode-not-prop"), ("F", "value-mode-not-prop"), ("T", "value-mode-not-prop"),
                        ("propext", "value-mode-not-a-def axiom")]:
        assert f"{target} {why}" in msg, (target, msg)
