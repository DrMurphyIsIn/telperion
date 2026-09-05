"""Tests for the hardened structured Lean verifier.

Most tests are OFFLINE: they exercise the pure parsing / returncode-backstop /
axioms_checked logic by monkeypatching ``subprocess.run`` (and by driving the
internal ``_parse_output`` / ``_collect_error_blocks`` directly), so they run in a
fresh clone with no built mathlib.  A single Lean-backed slow test is guarded by
``lean_env_ready`` against ``examples/log_combination/lean`` and skips cleanly when
the env is not built (never triggers a from-scratch rebuild).

The warm-server contract is tested with a FAKE server (no real Lean process):
the point being verified is the FALLBACK guarantee -- an unavailable / raising
server must never change the verdict versus the cold path.

conjecture1_proved = False.
"""
import sys
import types
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))  # shared lean_env guard

import pytest  # noqa: E402

from telperion import verify as V  # noqa: E402
from telperion.verify import (  # noqa: E402
    VerifyResult,
    _collect_error_blocks,
    _parse_output,
    verify_lean,
)
from lean_env import lean_env_ready  # noqa: E402


# --------------------------------------------------------------------------- #
# Cold-path plumbing: monkeypatch subprocess.run so we control lean's output.  #
# --------------------------------------------------------------------------- #

class _FakeProc:
    def __init__(self, stdout="", stderr="", returncode=0):
        self.stdout = stdout
        self.stderr = stderr
        self.returncode = returncode


@pytest.fixture
def fake_lean(monkeypatch, tmp_path):
    """Patch subprocess.run inside verify to return a scripted _FakeProc.

    Yields a setter; call ``fake_lean(stdout=..., returncode=...)`` before
    invoking ``verify_lean`` with ``env_dir=tmp_path``.
    """
    state = {"proc": _FakeProc()}

    def _run(cmd, **kwargs):
        return state["proc"]

    monkeypatch.setattr(V.subprocess, "run", _run)

    def _set(stdout="", stderr="", returncode=0):
        state["proc"] = _FakeProc(stdout=stdout, stderr=stderr, returncode=returncode)

    return _set


# --------------------------------------------------------------------------- #
# #3.2  Multi-line error block collection.                                    #
# --------------------------------------------------------------------------- #

def test_collect_error_blocks_multiline():
    out = (
        "/tmp/x.lean:12:4: error: unsolved goals\n"
        "  x : Real\n"
        "  h : 0 < x\n"
        "  |- x <= 1\n"
        "/tmp/x.lean:20:0: warning: unused variable\n"
    )
    blocks = _collect_error_blocks(out)
    assert len(blocks) == 1
    assert blocks[0].startswith("unsolved goals")
    # continuation lines preserved
    assert "h : 0 < x" in blocks[0]
    assert "|- x <= 1" in blocks[0]
    # warning header is NOT swallowed into the error block
    assert "unused variable" not in blocks[0]


def test_collect_error_blocks_two_errors():
    out = (
        "a.lean:1:0: error: first bad\n"
        "  detail A\n"
        "a.lean:2:0: error: second bad\n"
        "  detail B\n"
    )
    blocks = _collect_error_blocks(out)
    assert len(blocks) == 2
    assert "detail A" in blocks[0] and "detail B" in blocks[1]
    assert "second bad" not in blocks[0]


def test_collect_error_blocks_none():
    assert _collect_error_blocks("all good, nothing here\n") == []


# --------------------------------------------------------------------------- #
# #3.1  Returncode backstop.                                                  #
# --------------------------------------------------------------------------- #

def test_returncode_backstop_synthesizes_error(fake_lean, tmp_path):
    # Nonzero exit, but NO parseable ':L:C: error:' line -> must NOT be okay.
    fake_lean(stdout="lean: fatal: something opaque went wrong\n", returncode=1)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path, decls=["t"])
    assert r.okay is False
    assert r.returncode == 1
    assert len(r.errors) == 1
    assert "exited with code 1" in r.errors[0]


def test_returncode_zero_with_no_errors_is_okay(fake_lean, tmp_path):
    fake_lean(stdout="'t' does not depend on any axioms\n", returncode=0)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path, decls=["t"])
    assert r.okay is True
    assert r.axioms_clean is True
    assert r.axioms_checked is True


def test_parsed_error_with_nonzero_not_double_reported():
    fields = _parse_output(
        "f.lean:1:0: error: real diagnostic\n", returncode=1,
        decls=("t",), permitted=V._MATHLIB_AXIOMS,
    )
    # A genuine error line is present, so no synthetic backstop error is added.
    assert fields["okay"] is False
    assert len(fields["errors"]) == 1
    assert "real diagnostic" in fields["errors"][0]


# --------------------------------------------------------------------------- #
# #3.3  Non-vacuous axioms_clean / explicit axioms_checked.                    #
# --------------------------------------------------------------------------- #

def test_no_decls_is_unchecked_not_clean(fake_lean, tmp_path):
    # Compiles fine but names NO decl -> axioms_checked False, axioms_clean False.
    fake_lean(stdout="", returncode=0)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path)  # no decls
    assert r.okay is True
    assert r.axioms_checked is False
    assert r.axioms_clean is False   # <- the old vacuous-True is now False
    assert "UNCHECKED" in r.summary()


def test_decls_clean_sets_axioms_clean(fake_lean, tmp_path):
    fake_lean(stdout="'t' does not depend on any axioms\n", returncode=0)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path, decls=["t"])
    assert r.axioms_checked is True
    assert r.axioms_clean is True


def test_disallowed_axiom_is_dirty(fake_lean, tmp_path):
    fake_lean(stdout="'t' depends on axioms: [propext, sorryAx]\n", returncode=0)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path, decls=["t"])
    assert r.axioms_checked is True
    assert r.axioms_clean is False
    assert r.disallowed == {"t": ["sorryAx"]}


def test_allow_axioms_widens_permitted(fake_lean, tmp_path):
    fake_lean(stdout="'t' depends on axioms: [propext, sorryAx]\n", returncode=0)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path,
                    decls=["t"], allow_axioms=["sorryAx"])
    assert r.axioms_clean is True
    assert r.disallowed == {}


def test_sorry_marks_unclean_even_with_decls(fake_lean, tmp_path):
    fake_lean(
        stdout="f.lean:1:0: warning: declaration uses 'sorry'\n"
               "'t' does not depend on any axioms\n",
        returncode=0,
    )
    r = verify_lean("theorem t : True := by sorry", env_dir=tmp_path, decls=["t"])
    assert r.sorries is True
    assert r.axioms_clean is False


# --------------------------------------------------------------------------- #
# #5  Warm-server fallback contract (fake server, no real Lean).              #
# --------------------------------------------------------------------------- #

class _FakeServer:
    def __init__(self, *, avail, out="", rc=0, raise_on_elab=False):
        self._avail = avail
        self._out = out
        self._rc = rc
        self._raise = raise_on_elab
        self.elaborate_calls = 0

    def available(self):
        return self._avail

    def elaborate(self, body, *, env_dir=None, timeout=600):
        self.elaborate_calls += 1
        if self._raise:
            raise RuntimeError("worker died")
        return self._out, self._rc


def test_server_used_when_available(fake_lean, tmp_path):
    # Cold path would say okay (rc 0, no errors); make the server DISAGREE so we
    # can prove the server's output is the one used.
    fake_lean(stdout="'t' does not depend on any axioms\n", returncode=0)
    srv = _FakeServer(avail=True, out="f.lean:1:0: error: server-detected\n", rc=1)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path,
                    decls=["t"], server=srv)
    assert srv.elaborate_calls == 1
    assert r.okay is False
    assert "server-detected" in r.errors[0]


def test_unavailable_server_falls_back_to_cold(fake_lean, tmp_path):
    fake_lean(stdout="'t' does not depend on any axioms\n", returncode=0)
    srv = _FakeServer(avail=False)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path,
                    decls=["t"], server=srv)
    assert srv.elaborate_calls == 0     # never asked to elaborate
    assert r.okay is True and r.axioms_clean is True   # cold verdict


def test_raising_server_falls_back_to_cold(fake_lean, tmp_path):
    fake_lean(stdout="'t' does not depend on any axioms\n", returncode=0)
    srv = _FakeServer(avail=True, raise_on_elab=True)
    r = verify_lean("theorem t : True := trivial", env_dir=tmp_path,
                    decls=["t"], server=srv)
    assert srv.elaborate_calls == 1     # tried once
    assert r.okay is True and r.axioms_clean is True   # then fell back, cold verdict


# --------------------------------------------------------------------------- #
# LeanServer offline lifecycle (no real Lean spawned when lake is absent).     #
# --------------------------------------------------------------------------- #

def test_lean_server_construction_never_raises_and_defaults_unavailable(tmp_path):
    from telperion.lean_server import LeanServer
    srv = LeanServer(tmp_path)
    # Not probed yet -> must report unavailable regardless of toolchain.
    assert srv.available() is False
    srv.close()  # idempotent, non-raising even though nothing started
    srv.close()


def test_lean_server_start_is_pure_env_capability_check(tmp_path):
    # start() no longer spawns a worker (single-shot/LSP redesign): it is a pure
    # capability check on env_dir existence. It must never raise.
    from telperion.lean_server import LeanServer
    assert LeanServer(tmp_path).start() is True
    assert LeanServer(tmp_path / "does_not_exist").start() is False


def test_lean_server_spawn_failure_is_recorded(monkeypatch, tmp_path):
    # When the toolchain cannot be spawned (e.g. lake absent), the failure is
    # RECORDED (via probe/elaborate — both the LSP Popen and the single-shot
    # subprocess.run paths) and the server reports unavailable, never raising.
    from telperion import lean_server as LS

    def _boom(*a, **k):
        raise OSError("no lake here")

    monkeypatch.setattr(LS.subprocess, "Popen", _boom)     # LSP warm path
    monkeypatch.setattr(LS.subprocess, "run", _boom)       # single-shot fallback
    srv = LS.LeanServer(tmp_path)
    assert srv.probe() is False
    assert srv.available() is False
    assert srv._start_error is not None


# --------------------------------------------------------------------------- #
# Lean-backed slow test (guarded).                                            #
# --------------------------------------------------------------------------- #

def test_verify_against_built_env_trivial_true():
    env_dir = (Path(__file__).resolve().parents[1]
               / "examples" / "log_combination" / "lean")
    if not lean_env_ready(env_dir):
        pytest.skip("log_combination Mathlib env not built (guard prevents rebuild)")
    src = "import Mathlib\ntheorem tv_probe : (1:Real) = 1 := by norm_num\n"
    r = verify_lean(src, env_dir=env_dir, decls=["tv_probe"])
    assert r.okay, r.summary()
    assert r.axioms_checked is True
    assert r.axioms_clean, r.summary()


def test_verify_against_built_env_catches_error():
    env_dir = (Path(__file__).resolve().parents[1]
               / "examples" / "log_combination" / "lean")
    if not lean_env_ready(env_dir):
        pytest.skip("log_combination Mathlib env not built (guard prevents rebuild)")
    # False statement: must fail to elaborate.
    src = "import Mathlib\ntheorem tv_bad : (1:Real) = 2 := by norm_num\n"
    r = verify_lean(src, env_dir=env_dir, decls=["tv_bad"])
    assert r.okay is False, r.summary()
    assert len(r.errors) >= 1
