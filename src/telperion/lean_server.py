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

VALIDATED ON LEAN 4.32.0 (empirical, 2026-09-04 — the earlier "unvalidated" note
is now resolved):

  * ``lake env lean --stdin`` (a) accepts a whole file on stdin and (b) emits the
    ``<file>:L:C: error:`` diagnostics the cold path already parses.  BUT (c) it is
    SINGLE-SHOT: it emits nothing until stdin EOF, elaborates the whole input once,
    then exits — it CANNOT be driven snippet-by-snippet, and each call re-imports
    Mathlib (no warm benefit).  The earlier sentinel-framed persistent-worker design
    would have HUNG on the read.  :meth:`elaborate` now uses the correct single-shot
    contract (write, close stdin, read all) — safe and correct, but not faster than
    the cold path.
  * The genuine warm tier is the LSP server (``lean --server``, JSON-RPC over
    stdio), whose environment IS resident across ``didOpen`` calls.  Its concrete,
    now-empirically-grounded implementation plan is in :meth:`_start_lsp` — the
    scoped next unit.  Because the single-shot path yields no latency win, the
    server still DEFAULTS to unavailable unless a
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
        """Capability check: is ``lake env lean`` invokable in ``env_dir``?  Never
        raises.  (There is no persistent worker under the ``--stdin`` contract — see
        the EMPIRICAL FINDING in :meth:`elaborate`; each call spawns a fresh
        single-shot process.)  Returns ``False`` on a missing env dir."""
        return Path(self.env_dir).exists()

    def _start_lsp(self):  # pragma: no cover - the real warm path, scoped next unit
        """The genuine warm path: the Lean 4 LSP server (``lean --server``).

        EMPIRICALLY GROUNDED PLAN (the ``--stdin`` contract is single-shot — see
        :meth:`elaborate` — so residency requires the LSP).  ``lean --server`` speaks
        JSON-RPC over stdio, ``Content-Length``-framed.  Concrete steps for 4.32.0:

        1. spawn ``lake env lean --server`` (inherits the built env / oleans);
        2. send ``initialize`` (rootUri = env_dir) then ``initialized``;
        3. per snippet: ``textDocument/didOpen`` a virtual ``file://`` doc whose text
           is ``import Mathlib\n<snippet>`` — the FIRST didOpen pays the Mathlib load,
           subsequent ones reuse the resident environment (the win);
        4. read ``textDocument/publishDiagnostics`` for that uri; completion is
           signalled by ``$/lean/fileProgress`` reaching an empty processing set, so
           wait on that before taking diagnostics as final;
        5. map each diagnostic ``{range:{start:{line,character}}, severity, message}``
           to the shared ``<file>:L:C: error:`` text so
           :func:`telperion.verify._parse_output` is reused verbatim;
        6. ``textDocument/didClose`` (or bump the version via ``didChange``) between
           snippets to avoid unbounded doc accumulation.

        Deferred as its own unit: robust async-diagnostic completion detection
        (steps 4-5) is the finicky part and must be validated against real 4.32.0
        output before it can replace the cold path.
        """
        raise NotImplementedError("LSP warm path — scoped next unit (see docstring)")

    def probe(self, *, timeout: float = 60.0) -> bool:
        """One-shot capability check; result CACHED in ``_probed``.

        Elaborates a trivial snippet via the single-shot contract; usable iff it
        exits 0 with no ``error:``.  NOTE: a ``True`` here means the single-shot path
        WORKS, not that it is warm — see :meth:`elaborate`.  ``available()`` still
        gates enabling it; the latency win requires :meth:`_start_lsp`.
        """
        if self._probed is not None:
            return bool(self._probed)
        if not self.start():
            self._start_error = f"env_dir does not exist: {self.env_dir!r}"
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
        """True iff a prior :meth:`probe` confirmed elaboration works.

        Deliberately does NOT auto-probe: enabling the ``server=`` path is an
        explicit, evidence-gated step.  Under the single-shot contract this path is
        correct but NOT faster than the cold path; the true warm tier is the LSP
        path (:meth:`_start_lsp`), which is the scoped next unit.
        """
        return self._probed is True

    def elaborate(self, body: str, *, env_dir=None, timeout: float = 600.0):
        """Elaborate ``body`` against the built env; return ``(combined_output, rc)``.

        EMPIRICAL FINDING (validated on Lean 4.32.0, 2026-09-04): ``lake env lean
        --stdin`` is SINGLE-SHOT — it reads the whole of stdin as one file until EOF,
        elaborates once, emits ``<file>:L:C: error:`` diagnostics (the same textual
        format the cold path parses), then EXITS.  It emits NOTHING before EOF, so it
        CANNOT be driven snippet-by-snippet with a resident environment: the earlier
        sentinel-framed read loop would hang, and even correctly driven it re-imports
        Mathlib each call (no warm benefit).  This method therefore uses the honest
        single-shot contract — write ``body``, close stdin, read all — spawning a
        fresh process per call.  The residency win lives in :meth:`_start_lsp`.

        ``returncode`` is the process exit code; raises on OS/timeout failure so
        ``verify_lean``'s guarded fallback engages.
        """
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", "--stdin"],
                cwd=str(self.env_dir),
                input=body if body.endswith("\n") else body + "\n",
                capture_output=True, text=True, env=self._env(), timeout=timeout,
            )
        except subprocess.TimeoutExpired as e:
            raise RuntimeError(f"lean --stdin timed out after {timeout}s") from e
        out = (proc.stdout or "") + (proc.stderr or "")
        return out, proc.returncode

    def close(self) -> None:
        """No persistent process under the single-shot contract; idempotent no-op
        (kept for the context-manager API and the future LSP worker)."""
        with self._lock:
            proc = self._proc
            self._proc = None
        if proc is None:
            return
        try:  # pragma: no cover - only exercised once the LSP worker lands
            proc.terminate()
            proc.wait(timeout=5)
        except Exception:
            pass

    # -- context manager -----------------------------------------------------

    def __enter__(self) -> "LeanServer":
        self.start()
        return self

    def __exit__(self, *exc) -> None:
        self.close()
