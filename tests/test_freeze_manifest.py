"""The frozen-tree manifest (T5): hashing of a Lake project's sources, lake files, toolchain,
dependency git state (HEAD, dirty diff, untracked files, patch reverse-check), tool binaries
and extra files; the digest; verify-after-run; the CLI.

The fixture project is built in tmp_path with a real git repository as the one dependency,
so the git paths are exercised for real (git is available wherever the suite runs).
"""
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.freeze_manifest import (  # noqa: E402
    FORMAT,
    ManifestError,
    ManifestOptions,
    diff_manifests,
    dumps_manifest,
    freeze_manifest,
    load_manifest,
    manifest_digest,
    parse_kv_pairs,
    render_text,
    verify_manifest,
)


def _git(d: Path, *args):
    subprocess.run(["git", "-C", str(d), *args], check=True, capture_output=True,
                   env={**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
                        "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"})


@pytest.fixture
def project(tmp_path: Path) -> Path:
    p = tmp_path / "proj"
    (p / "Lib").mkdir(parents=True)
    (p / "lakefile.toml").write_text('name = "Demo"\ndefaultTargets = ["Demo"]\n')
    # a toolchain nobody has installed: the binary record must be None, not an error
    (p / "lean-toolchain").write_text("leanprover/lean4:v0.0.0-telperion-test\n")
    (p / "Lib" / "A.lean").write_text("theorem a : True := trivial\n")
    (p / "Lib" / "B.lean").write_text("theorem b : True := trivial\n")
    (p / "Demo.lean").write_text("import Lib.A\nimport Lib.B\n")
    (p / "notes.md").write_text("not a lean file\n")
    # a symlinked source (the Positivity.lean -> ../../F1/Positivity.lean case)
    (tmp_path / "outside.lean").write_text("theorem c : True := trivial\n")
    os.symlink(tmp_path / "outside.lean", p / "Lib" / "C.lean")
    # build products must be ignored
    (p / ".lake" / "build").mkdir(parents=True)
    (p / ".lake" / "build" / "X.lean").write_text("ignored\n")
    # one git dependency, with a committed file, a tracked modification and an untracked file
    pkg = p / ".lake" / "packages" / "dep"
    pkg.mkdir(parents=True)
    _git(pkg, "init", "-q")
    (pkg / "Dep.lean").write_text("def d := 1\n")
    (pkg / ".gitignore").write_text("*.log\n")
    _git(pkg, "add", ".")
    _git(pkg, "commit", "-q", "-m", "init")
    (pkg / "Dep.lean").write_text("def d := 2\n")
    (pkg / "New.lean").write_text("def n := 1\n")
    (pkg / "scratch.log").write_text("ignored by git\n")
    (p / "lake-manifest.json").write_text(json.dumps({
        "version": "1.2.0", "packagesDir": ".lake/packages",
        "packages": [{"url": "https://example.invalid/dep", "type": "git", "rev": "deadbeef",
                      "inputRev": "main", "name": "dep"}],
        "name": "Demo"}))
    return p


def _patch_for(project: Path) -> Path:
    """A patch equal to the dependency's current diff (tracked change + the new file), so the
    reverse-check passes and New.lean counts as created by the patch."""
    pkg = project / ".lake" / "packages" / "dep"
    _git(pkg, "add", "-N", "New.lean")  # intent-to-add so `git diff` shows the new file
    diff = subprocess.run(["git", "-C", str(pkg), "diff"], check=True, capture_output=True,
                          text=True).stdout
    _git(pkg, "reset", "-q", "New.lean")
    patch = project.parent / "dep.patch"
    patch.write_text(diff)
    return patch


# ---------------------------------------------------------------- freeze

def test_freeze_records_sources_lake_files_and_skips_build_products(project):
    doc = freeze_manifest(project)
    assert doc["format"] == FORMAT and doc["project"] == "Demo"
    assert set(doc["files"]) == {"Demo.lean", "Lib/A.lean", "Lib/B.lean", "Lib/C.lean"}
    assert set(doc["lake_files"]) == {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
    for rec in doc["files"].values():
        assert len(rec["sha256"]) == 64 and len(rec["md5"]) == 32 and rec["size"] > 0
    assert doc["toolchain"]["file"] == "leanprover/lean4:v0.0.0-telperion-test"
    assert doc["toolchain"]["binary"] is None and doc["toolchain"]["lake_binary"] is None
    assert "created" in doc and doc["digest"] == manifest_digest(doc)


def test_symlink_is_recorded_and_hashed_through(project, tmp_path):
    doc = freeze_manifest(project)
    c = doc["files"]["Lib/C.lean"]
    assert c["symlink"] == str(tmp_path / "outside.lean")
    import hashlib
    assert c["sha256"] == hashlib.sha256((tmp_path / "outside.lean").read_bytes()).hexdigest()


def test_dependency_git_state(project):
    doc = freeze_manifest(project)
    dep = doc["dependencies"]["dep"]
    assert dep["type"] == "git" and dep["rev"] == "deadbeef" and dep["inputRev"] == "main"
    assert dep["present"] and dep["git"] and len(dep["head"]) == 40
    assert dep["dirty"] is True and len(dep["diff_sha256"]) == 64
    assert [u["path"] for u in dep["untracked"]] == ["New.lean"]
    assert "ignored" not in dep  # not asked for
    assert "patch" not in dep


def test_include_ignored_lists_git_ignored_files(project):
    doc = freeze_manifest(project, ManifestOptions(include_ignored=True))
    assert [u["path"] for u in doc["dependencies"]["dep"]["ignored"]] == ["scratch.log"]


def test_patch_reverse_check_and_created_by_patch(project):
    patch = _patch_for(project)
    doc = freeze_manifest(project, ManifestOptions(patches=(("dep", str(patch)),)))
    dep = doc["dependencies"]["dep"]
    assert dep["patch"]["reverse_check"] == "ok"
    assert dep["patch"]["sha256"]
    assert dep["untracked"] == [{**dep["untracked"][0], "created_by_patch": True}]
    # a patch that does not match the tree is reported, not raised
    bad = project.parent / "bad.patch"
    bad.write_text(patch.read_text().replace("def d := 2", "def d := 3"))
    doc2 = freeze_manifest(project, ManifestOptions(patches=(("dep", str(bad)),)))
    assert doc2["dependencies"]["dep"]["patch"]["reverse_check"] == "failed"
    # a missing patch file
    doc3 = freeze_manifest(project, ManifestOptions(patches=(("dep", "nope.patch"),)))
    assert doc3["dependencies"]["dep"]["patch"] == {"path": "nope.patch", "missing": True,
                                                    "reverse_check": "no-patch"}


def test_clean_dependency_has_no_diff(project):
    pkg = project / ".lake" / "packages" / "dep"
    _git(pkg, "checkout", "-q", "--", "Dep.lean")
    (pkg / "New.lean").unlink()
    dep = freeze_manifest(project)["dependencies"]["dep"]
    assert dep["dirty"] is False and "diff_sha256" not in dep and dep["untracked"] == []


def test_tools_and_extras_are_pinned_by_label(project, tmp_path):
    tool = tmp_path / "checker"
    tool.write_bytes(b"\x7fELF fake")
    cfg = project.parent / "real.comparator.json"
    cfg.write_text("{}\n")
    opts = ManifestOptions(tools=(("checker", str(tool)),), extras=(("cfg", "../real.comparator.json"),))
    doc = freeze_manifest(project, opts)
    assert doc["tools"]["checker"]["basename"] == "checker" and doc["tools"]["checker"]["size"] == 9
    assert doc["extras"]["cfg"]["sha256"] and doc["extras"]["cfg"]["path"] == "../real.comparator.json"
    # a missing tool is recorded as missing, not raised
    doc2 = freeze_manifest(project, ManifestOptions(tools=(("gone", "/nonexistent/bin"),)))
    assert doc2["tools"]["gone"]["missing"] is True


def test_options_roundtrip_and_are_recorded(project):
    opts = ManifestOptions(include_globs=("**/*.lean", "*.md"), tools=(("a", "/x"),),
                           include_ignored=True, hash_toolchain_binary=False)
    doc = freeze_manifest(project, opts)
    assert ManifestOptions.from_dict(doc["options"]) == opts
    assert "notes.md" in doc["files"]


def test_missing_project_raises(tmp_path):
    with pytest.raises(ManifestError):
        freeze_manifest(tmp_path / "nope")


# ---------------------------------------------------------------- digest + verify

def test_digest_ignores_timestamp_and_is_stable(project):
    a = freeze_manifest(project, timestamp=True)
    b = freeze_manifest(project, timestamp=False)
    assert "created" in a and "created" not in b
    assert a["digest"] == b["digest"]
    assert diff_manifests(a, b).unchanged


def test_load_manifest_detects_an_edited_file(project, tmp_path):
    doc = freeze_manifest(project)
    f = tmp_path / "m.json"
    f.write_text(dumps_manifest(doc))
    assert load_manifest(f)["digest"] == doc["digest"]
    edited = dict(doc)
    edited["files"] = dict(doc["files"])
    edited["files"]["Lib/A.lean"] = {**doc["files"]["Lib/A.lean"], "sha256": "0" * 64}
    f.write_text(dumps_manifest(edited))
    with pytest.raises(ManifestError, match="edited after"):
        load_manifest(f)
    f.write_text(json.dumps({"format": "other"}))
    with pytest.raises(ManifestError, match="format"):
        load_manifest(f)


def test_verify_unchanged_then_changed(project, tmp_path):
    m = tmp_path / "m.json"
    m.write_text(dumps_manifest(freeze_manifest(project)))
    diff, _ = verify_manifest(m, project)
    assert diff.unchanged and diff.changed == [] and "UNCHANGED" in diff.render()

    (project / "Lib" / "A.lean").write_text("theorem a : True := by trivial\n")
    (project / "Lib" / "D.lean").write_text("theorem d : True := trivial\n")
    (project / "Lib" / "B.lean").unlink()
    pkg = project / ".lake" / "packages" / "dep"
    (pkg / "Dep.lean").write_text("def d := 3\n")
    diff, new = verify_manifest(m, project)
    assert not diff.unchanged
    assert diff.added == ["files/Lib/D.lean"]
    assert diff.removed == ["files/Lib/B.lean"]
    assert diff.changed == ["dependencies/dep", "files/Lib/A.lean"]
    assert diff.old_digest != diff.new_digest == new["digest"]
    text = diff.render()
    assert "CHANGED (1 added, 1 removed, 2 changed)" in text and "~ files/Lib/A.lean" in text


def test_toolchain_lean_and_lake_binaries_are_hashed(project, tmp_path, monkeypatch):
    """An installed elan toolchain: both `lean` and `lake` are hashed, and a changed `lake`
    (it decides what is up to date) is a changed toolchain record."""
    home = tmp_path / "elan"
    bin_dir = home / "toolchains" / "leanprover--lean4---v0.0.0-telperion-test" / "bin"
    bin_dir.mkdir(parents=True)
    (bin_dir / "lean").write_bytes(b"lean-bytes")
    (bin_dir / "lake").write_bytes(b"lake-bytes")
    monkeypatch.setenv("ELAN_HOME", str(home))
    doc = freeze_manifest(project)
    tc = doc["toolchain"]
    assert tc["binary"]["toolchain_dir"] == "leanprover--lean4---v0.0.0-telperion-test"
    assert tc["binary"]["size"] == 10 and tc["lake_binary"]["size"] == 10
    assert tc["binary"]["sha256"] != tc["lake_binary"]["sha256"]
    m = tmp_path / "m.json"
    m.write_text(dumps_manifest(doc))
    (bin_dir / "lake").write_bytes(b"lake-bytes-2")
    diff, _ = verify_manifest(m, project)
    assert diff.changed == ["toolchain"]


def test_verify_with_tool_override_compares_content_not_path(project, tmp_path):
    tool = tmp_path / "t1"
    tool.write_bytes(b"same bytes")
    m = tmp_path / "m.json"
    m.write_text(dumps_manifest(freeze_manifest(project, ManifestOptions(tools=(("t", str(tool)),)))))
    moved = tmp_path / "t2"
    moved.write_bytes(b"same bytes")
    diff, _ = verify_manifest(m, project, tool_overrides={"t": str(moved)})
    assert diff.unchanged
    moved.write_bytes(b"other bytes")
    diff, _ = verify_manifest(m, project, tool_overrides={"t": str(moved)})
    assert diff.changed == ["tools/t"]


# ---------------------------------------------------------------- text + CLI helpers

def test_render_text_lists_every_file_and_dependency(project):
    patch = _patch_for(project)
    doc = freeze_manifest(project, ManifestOptions(patches=(("dep", str(patch)),),
                                                   extras=(("x", "notes.md"),)))
    text = render_text(doc)
    assert "lean binary sha256 not hashed  lake binary sha256 not hashed" in text
    for k, v in {**doc["lake_files"], **doc["files"]}.items():
        assert f"{v['sha256']}  {k}" in text
    assert "Lib/C.lean  -> " in text
    assert "#   dep rev deadbeef head" in text and "dirty" in text
    assert "reverse-check ok" in text
    assert "untracked" in text and "(created by the patch: yes)" in text
    assert "# --- extra files ---" in text and "  x  (notes.md)" in text


def test_parse_kv_pairs():
    assert parse_kv_pairs(["b=/y", "a=/x"], "tool") == (("a", "/x"), ("b", "/y"))
    assert parse_kv_pairs(["/usr/bin/nanoda_bin"], "tool") == (("nanoda_bin", "/usr/bin/nanoda_bin"),)
    with pytest.raises(ManifestError):
        parse_kv_pairs(["a=/x", "a=/y"], "tool")
    with pytest.raises(ManifestError):
        parse_kv_pairs(["=x"], "tool")


def test_cli_freeze_then_verify(project, tmp_path, capsys):
    from telperion.cli import main

    out = tmp_path / "m.json"
    txt = tmp_path / "m.txt"
    rc = main(["freeze-manifest", "--project", str(project), "--out", str(out), "--text", str(txt),
               "--extra", "notes=notes.md", "--no-toolchain-binary"])
    assert rc == 0
    assert "manifest written" in capsys.readouterr().out
    doc = load_manifest(out)
    assert doc["extras"]["notes"]["path"] == "notes.md"
    assert doc["options"]["hash_toolchain_binary"] is False
    assert txt.read_text().startswith(f"# {FORMAT}")

    assert main(["verify-manifest", "--project", str(project), "--manifest", str(out)]) == 0
    (project / "Lib" / "A.lean").write_text("changed\n")
    js = tmp_path / "d.json"
    assert main(["verify-manifest", "--project", str(project), "--manifest", str(out),
                 "--json", str(js)]) == 1
    assert json.loads(js.read_text())["changed"] == ["files/Lib/A.lean"]


def test_cli_freeze_reports_missing_tool(project, tmp_path, capsys):
    from telperion.cli import main

    out = tmp_path / "m.json"
    rc = main(["freeze-manifest", "--project", str(project), "--out", str(out),
               "--tool", "gone=/nonexistent/bin"])
    assert rc == 1
    assert "MISSING: gone" in capsys.readouterr().out
