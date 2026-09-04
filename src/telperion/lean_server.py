"""Warm long-lived Lean worker -- a fallback-guarded SPIKE for sub-second repeats.

MOTIVATION.  ``verify_lean`` spawns a fresh ``lake env lean <file>`` per call.
On a built mathlib env each spawn pays a cold ~4-9s startup (process launch,
import-graph load) before elaborating even a one-line theorem.  The hottest
beneficiary is :func:`telperion.gap_fill.fill_gap`'s per-gap loop
(``gap_fill.py:262`` -> ``verify_with_repair`` -> ``verify_lean``), which re-pays
that cold start for every gap.  A worker that loads ``import Mathlib`` ONCE and
then elaborates many snippets against the already-resident environment amortises
it away.

DESIGN (defensive, since we cannot run Lean here to confirm the wire protocol on
the pinned toolchain):

  * :class:`LeanServer` owns a persistent ``subprocess.Popen`` worker started with
    ``lake env lean --root=<env_dir> --stdin`` (a stdin-fed elaborator).  Each
    ``elaborate`` writes a snippet framed by a unique end-marker, then reads the
    worker's diagnostics back.  The output format is the SAME textual
    ``<file>:L:C: error:`` diagnostics ``verify_lean`` already parses, so the warm
    and cold paths share :func:`telperion.verify._parse_output`.
  * Everything is behind :meth:`available`.  Construction never raises on a
    missing/old toolchain; it records the failure and reports ``available() ==
    False`` so ``verify_lean(server=...)`` silently uses the cold path.
  * :meth:`probe` does a one-shot capability check (can the worker start and echo
    a trivial elaboration?) and CACHES the verdict.

VALIDATED vs UNVALIDATED ON LEAN 4.32.0 (read before trusting this):

  * VALIDATED (by construction / offline): the fallback contract -- an
    unavailable or misbehaving server never changes a verification's verdict
    versus the cold path; the framing/parse round-trip against synthetic output;
    process lifecycle (spawn/terminate/context-manager).
  * UNVALIDATED on 4.32.0 (REQUIRES a built env to confirm): that
    ``lake env lean --stdin`` on this exact toolchain (a) accepts a whole file on
    stdin, (b) emits the ``:L:C: error:`` diagnostics we parse, and (c) can be
    driven snippet-by-snippet without a per-snippet re-elaboration of the import
    graph.  Lean 4.32.0 ships an LSP server (``lean --server``, JSON-RPC over
    stdio) which is the ROBUST alternative if ``--stdin`` proves single-shot; the
    LSP path is sketched in :meth:`_start_lsp` but left un-wired pending a live
    env.  Because of this uncertainty the server DEFAULTS to unavailable unless a
    successful :meth:`probe` (or ``force_probe=True``) confirms it, so enabling it
    is an explicit, evidence-gated opt-in -- never a silent behaviour change.

NOTE: ``lake env lean --json`` is deliberately NOT used -- 4.32.0 has no usable
``--json`` for file elaboration (per repo constraint), hence the textual-diagnostic
contract shared with the cold path.
"""
from __future__ import annotations

import os
import subprocess
import threading
import uuid
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class LeanServer:
    """Persistent Lean worker with a strict cold-path fallback contract.

    Typical use::

        with LeanServer(env_dir) as srv:
            if srv.available():
                r = verify_lean(src, env_dir=env_dir, decls=[d], server=srv)
            else:
                r = verify_lean(src, env_dir=env_dir, decls=[d])  # cold

    ``available()`` is ``False`` until a successful :meth:`probe`; construction is
    non-raising so callers can always attempt the warm path and fall back.
    """

    env_dir: object
    lean_path_bin: object = None
    start_timeout: float = 60.0
    # Internal state.
    _proc: object = field(default=None, init=False, repr=False)
    _lock: object = field(default_factory=threading.Lock, init=False, repr=False)
    _probed: object = field(default=None, init=False, repr=False)   # None | bool
    _start_error: object = field(default=None, init=False, repr=False)

    def __post_init__(self) -> None:
        self.env_dir = Path(self.env_dir)

    # -- lifecycle -----------------------------------------------------------

    def _env(self) -> dict:
        env = os.environ.copy()
        elan = self.lean_path_bin or str(Path.home() / ".elan" / "bin")
        env["PATH"] = elan + os.pathsep + env.get("PATH", "")
        return env

    def start(self) -> bool:
        """Attempt to spawn the persistent worker.  Never raises.

        Returns ``True`` if a live process was created (NOT that it is proven
        usable -- that is :meth:`probe`'s job).  On any OS-level failure records
        the error and returns ``False``.
        """
        with self._lock:
            if self._proc is not None and self._proc.poll() is None:
                return True
            try:
                self._proc = subprocess.Popen(
                    ["lake", "env", "lean", "--root=.", "--stdin"],
                    cwd=str(self.env_dir),
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    env=self._env(),
                    bufsize=1,
                )
                return True
            except (OSError, ValueError) as e:  # pragma: no cover - env dependent
                self._start_error = repr(e)
                self._proc = None
                return False

    def _start_lsp(self):  # pragma: no cover - unwired, needs a live env
        """Sketch of the ROBUST alternative: the Lean 4 LSP server.

        ``lean --server`` speaks JSON-RPC over stdio (``Content-Length`` framed).
        A production warm path would: spawn it, send ``initialize`` /
        ``initialized``, then per snippet ``textDocument/didOpen`` a virtual doc
        importing Mathlib and read ``textDocument/publishDiagnostics``.  Left
        un-wired here because the diagnostic-to-``:L:C: error:`` mapping and the
        didOpen re-elaboration cost cannot be confirmed without a built 4.32.0
        env; :meth:`elaborate` uses the simpler ``--stdin`` contract instead.
        """
        raise NotImplementedError("LSP warm path is a documented sketch only")

    def probe(self, *, timeout: float = 60.0) -> bool:
        """One-shot capability check; result CACHED in ``_probed``.

        Considers the server usable iff a trivial snippet elaborates and the
        worker echoes SOMETHING back (even empty output at rc 0 counts as a
        healthy no-diagnostics elaboration).  Any exception -> not available.
        """
        if self._probed is not None:
            return bool(self._probed)
        if not self.start():
            self._probed = False
            return False
        try:
            out, rc = self.elaborate(
                "theorem _telperion_probe : True := trivial\n",
                env_dir=self.env_dir, timeout=timeout,
            )
            self._probed = (rc == 0) and ("error:" not in out)
        except Exception as e:  # pragma: no cover - env dependent
            self._start_error = repr(e)
            self._probed = False
        return bool(self._probed)

    def available(self) -> bool:
        """True iff a prior :meth:`probe` confirmed the worker usable.

        Deliberately does NOT auto-probe: enabling the warm path is an explicit,
        evidence-gated step (call :meth:`probe` first).  This keeps
        ``verify_lean(server=...)`` on the cold path by default until proven.
        """
        return self._probed is True and self._proc is not None and self._proc.poll() is None

    def elaborate(self, body: str, *, env_dir=None, timeout: float = 600.0):
        """Feed ``body`` to the warm worker; return ``(combined_output, returncode)``.

        The snippet is framed with a unique sentinel so a single long-lived
        worker's outputs can be demarcated per call.  ``returncode`` is ``0`` for a
        completed elaboration and non-zero if the worker has died (surfacing the
        backstop in :func:`telperion.verify._parse_output`).  Raises on protocol
        failure so ``verify_lean``'s guarded fallback engages.
        """
        if self._proc is None or self._proc.poll() is not None:
            if not self.start():
                raise RuntimeError(f"lean worker not running: {self._start_error!r}")
        proc = self._proc
        sentinel = f"--#telperion-eot-{uuid.uuid4().hex}\n"
        with self._lock:
            if proc.stdin is None or proc.stdout is None:  # pragma: no cover
                raise RuntimeError("lean worker has no stdio pipes")
            # NOTE: the exact stdin framing that 4.32.0's --stdin accepts is the
            # UNVALIDATED piece (see module docstring).  We write the body then a
            # comment sentinel; a real worker would echo diagnostics up to EOF.
            proc.stdin.write(body)
            if not body.endswith("\n"):
                proc.stdin.write("\n")
            proc.stdin.write(sentinel)
            proc.stdin.flush()
            lines: list = []
            for line in proc.stdout:
                if line.strip() == sentinel.strip():
                    break
                lines.append(line.rstrip("\n"))
            rc = 0 if proc.poll() is None else (proc.returncode or 1)
        return "\n".join(lines), rc

    def close(self) -> None:
        """Terminate the worker if running.  Idempotent and non-raising."""
        with self._lock:
            proc = self._proc
            self._proc = None
        if proc is None:
            return
        try:
            if proc.stdin is not None:
                try:
                    proc.stdin.close()
                except Exception:
                    pass
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:  # pragma: no cover
                proc.kill()
        except Exception:  # pragma: no cover - best effort teardown
            pass

    # -- context manager -----------------------------------------------------

    def __enter__(self) -> "LeanServer":
        self.start()
        return self

    def __exit__(self, *exc) -> None:
        self.close()
