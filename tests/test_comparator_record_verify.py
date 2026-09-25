"""`_blob_sha256`: the artifact as the judge saw it, not as the working tree has it.

A Comparator record pins `artifact_sha256`.  Computing it from the working tree is only right
when the artifact has not moved since the judged commit, which is the common case but not a
guarantee: a PASS on an older version of the artifact must never be citable for the current
one.  So `comparator-record` hashes the artifact blob at the judged job's own head commit and
requires the two to agree.

These tests use a throwaway git repository, so they need neither network nor the real history.
"""
import hashlib
import shutil
import subprocess
from pathlib import Path

import pytest

_CLI_SRC = Path(__file__).resolve().parents[1] / "src"


@pytest.fixture(scope="module")
def blob_sha256():
    import sys
    sys.path.insert(0, str(_CLI_SRC))
    from telperion.cli import _blob_sha256
    return _blob_sha256


def _git(cwd, *args):
    r = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
    assert r.returncode == 0, f"git {' '.join(args)} failed: {r.stderr}"
    return r.stdout.strip()


@pytest.fixture
def repo(tmp_path):
    if shutil.which("git") is None:  # pragma: no cover
        pytest.skip("git is not available")
    d = tmp_path / "r"
    (d / "lean").mkdir(parents=True)
    _git(d, "init", "-q")
    _git(d, "config", "user.email", "t@example.com")
    _git(d, "config", "user.name", "t")
    art = d / "lean" / "Artifact.lean"
    art.write_text("theorem old : True := trivial\n")
    _git(d, "add", "-A")
    _git(d, "commit", "-q", "-m", "first")
    return d, art, _git(d, "rev-parse", "HEAD")


def test_hashes_the_committed_blob(repo, blob_sha256):
    d, art, sha = repo
    want = hashlib.sha256(art.read_bytes()).hexdigest()
    assert blob_sha256(sha, art) == want


def test_sees_the_judged_version_not_the_working_tree(repo, blob_sha256):
    """The case the check exists for: the artifact changed after the judged commit."""
    d, art, sha = repo
    committed = blob_sha256(sha, art)
    art.write_text("theorem changed : True := trivial\n")
    assert blob_sha256(sha, art) == committed, "must still hash the judged commit"
    assert hashlib.sha256(art.read_bytes()).hexdigest() != committed, "fixture did not change"


def test_short_sha_resolves(repo, blob_sha256):
    d, art, sha = repo
    assert blob_sha256(sha[:9], art) == blob_sha256(sha, art)


def test_unknown_commit_is_none_not_an_exception(repo, blob_sha256):
    """Unresolvable means "cannot check here", which the caller reports rather than failing."""
    d, art, _ = repo
    assert blob_sha256("0" * 40, art) is None


def test_path_outside_the_repository_is_none(repo, blob_sha256, tmp_path):
    d, _, sha = repo
    outside = tmp_path / "elsewhere.lean"
    outside.write_text("x\n")
    assert blob_sha256(sha, outside) is None


def test_missing_path_in_that_commit_is_none(repo, blob_sha256):
    d, _, sha = repo
    assert blob_sha256(sha, d / "lean" / "NeverCommitted.lean") is None
