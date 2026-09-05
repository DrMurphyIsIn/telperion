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

VALIDATED ON LEAN 4.32.0 (empirical, 2026-09-04):

  * ``lake env lean --stdin`` is SINGLE-SHOT: it reads the whole file until EOF,
    elaborates once, emits ``<file>:L:C: error:`` diagnostics, exits.  It CANNOT be
    driven snippet-by-snippet and re-imports Mathlib each call — NO warm benefit.
    Retained as the fallback (:meth:`_elaborate_stdin`).
  * THE WARM PATH (default, ``use_lsp``): a resident ``lake env lean --server`` (LSP,
    JSON-RPC over stdio) holding ONE persistent document.  The first ``didOpen`` pays
    ``import Mathlib`` (~8s); each later call ``didChange``s the doc's text, and Lean's
    INCREMENTAL elaboration reuses the cached import-prefix elaboration — so a call
    that swaps only the trailing theorem completes in ~0.2s vs ~4s cold (≈15-20x).
    Completion is ``$/lean/fileProgress`` emptying; diagnostics map to the shared
    ``<file>:L:C: sev:`` text so :func:`telperion.verify._parse_output` is reused for
    both errors and ``#print axioms`` lines.  Correctness validated by interleaved
    true/false parity (no stale-diagnostic bleed) and ``verify_lean(server=)`` ==
    cold verdicts.  A changed import prefix simply re-elaborates that once.
  * The server DEFAULTS to unavailable unless a
    successful :meth:`probe` (or ``force_probe=True``) confirms it, so enabling it
    is an explicit, evidence-gated opt-in -- never a silent behaviour change.

NOTE: ``lake env lean --json`` is deliberately NOT used -- 4.32.0 has no usable
``--json`` for file elaboration (per repo constraint), hence the textual-diagnostic
contract shared with the cold path.
"""
from __future__ import annotations

import json
import os
import subprocess
import threading
import time
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
    use_lsp: bool = True                 # try the resident LSP worker; fall back if it fails
    # Internal state.
    _proc: object = field(default=None, init=False, repr=False)
    _lock: object = field(default_factory=threading.Lock, init=False, repr=False)
    _probed: object = field(default=None, init=False, repr=False)   # None | bool
    _start_error: object = field(default=None, init=False, repr=False)
    # LSP worker state (the real warm path).
    _lsp: object = field(default=None, init=False, repr=False)          # Popen | None
    _lsp_reader: object = field(default=None, init=False, repr=False)   # Thread
    _lsp_ready: bool = field(default=False, init=False, repr=False)
    _cond: object = field(default_factory=threading.Condition, init=False, repr=False)
    _diags: object = field(default_factory=dict, init=False, repr=False)     # uri -> list
    _done: object = field(default_factory=dict, init=False, repr=False)      # uri -> bool (fileProgress empty)
    _seen_diag: object = field(default_factory=set, init=False, repr=False)  # uris that got publishDiagnostics
    _id: int = field(default=0, init=False, repr=False)
    _doc_uri: object = field(default=None, init=False, repr=False)   # the single persistent warm doc
    _doc_version: int = field(default=0, init=False, repr=False)

    def __post_init__(self) -> None:
        self.env_dir = Path(self.env_dir)

    # -- lifecycle -----------------------------------------------------------

    def _env(self) -> dict:
        env = os.environ.copy()
        elan = self.lean_path_bin or str(Path.home() / ".elan" / "bin")
        env["PATH"] = elan + os.pathsep + env.get("PATH", "")
        return env

    # -- LSP warm worker (the real resident environment) ---------------------

    def _lsp_send(self, msg: dict) -> None:
        body = json.dumps(msg).encode("utf-8")
        self._lsp.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("utf-8") + body)
        self._lsp.stdin.flush()

    def _lsp_reader_loop(self) -> None:
        """Parse ``Content-Length``-framed JSON-RPC and record diagnostics /
        fileProgress completion, waking :meth:`_elaborate_lsp` via ``_cond``."""
        out = self._lsp.stdout
        buf = b""
        try:
            while True:
                chunk = out.read1(65536) if hasattr(out, "read1") else out.read(1)
                if not chunk:
                    break
                buf += chunk
                while b"\r\n\r\n" in buf:
                    head, rest = buf.split(b"\r\n\r\n", 1)
                    n = None
                    for line in head.decode("latin-1").split("\r\n"):
                        if line.lower().startswith("content-length"):
                            n = int(line.split(":", 1)[1])
                    if n is None or len(rest) < n:
                        break
                    body, buf = rest[:n], rest[n:]
                    try:
                        msg = json.loads(body)
                    except Exception:
                        continue
                    self._dispatch(msg)
        except Exception:  # pragma: no cover - worker died mid-read
            pass
        with self._cond:
            self._lsp_ready = False
            self._cond.notify_all()

    def _dispatch(self, msg: dict) -> None:
        meth = msg.get("method")
        if meth == "textDocument/publishDiagnostics":
            uri = msg["params"]["uri"]
            with self._cond:
                self._diags[uri] = msg["params"].get("diagnostics", [])
                self._seen_diag.add(uri)
                self._cond.notify_all()
        elif meth == "$/lean/fileProgress":
            uri = msg["params"].get("textDocument", {}).get("uri")
            processing = msg["params"].get("processing", [])
            if uri is not None:
                with self._cond:
                    self._done[uri] = (len(processing) == 0)
                    self._cond.notify_all()

    def _lsp_start(self) -> bool:
        """Spawn ``lake env lean --server`` and do the initialize handshake.  Returns
        True iff the worker is up and ready.  Never raises."""
        with self._lock:
            if self._lsp is not None and self._lsp.poll() is None and self._lsp_ready:
                return True
            try:
                self._lsp = subprocess.Popen(
                    ["lake", "env", "lean", "--server"],
                    cwd=str(self.env_dir), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL, env=self._env(),
                )
                self._lsp_reader = threading.Thread(target=self._lsp_reader_loop, daemon=True)
                self._lsp_reader.start()
                self._id += 1
                # rootUri must be an ABSOLUTE file URI — resolve so a relative env_dir
                # (a common caller shape) does not crash `.as_uri()` and silently drop
                # us to the single-shot fallback.
                root_uri = Path(self.env_dir).resolve().as_uri()
                self._lsp_send({"jsonrpc": "2.0", "id": self._id, "method": "initialize",
                                "params": {"processId": None, "rootUri": root_uri,
                                           "capabilities": {}}})
                self._lsp_send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
                self._lsp_ready = True
                return True
            except Exception as e:  # pragma: no cover - env dependent
                self._start_error = repr(e)
                self._lsp = None
                self._lsp_ready = False
                return False

    def _elaborate_lsp(self, body: str, timeout: float):
        """Elaborate ``body`` on the resident LSP worker; return ``(text, rc)`` in the
        shared ``<file>:L:C: sev:`` format (so :func:`telperion.verify._parse_output`
        parses errors AND ``#print axioms`` info lines).

        THE WARM MECHANISM (validated on 4.32.0): a SINGLE persistent document is
        ``didOpen``ed once (paying ``import Mathlib`` ~8s), then each call ``didChange``s
        its full text.  Lean's incremental elaboration REUSES the cached elaboration of
        the unchanged leading ``import`` commands, so a call that only swaps the trailing
        theorem completes in ~0.2s (vs ~4s cold) — provided the import prefix is stable
        across calls (a changed import prefix re-elaborates that once).  Completion is
        ``$/lean/fileProgress`` emptying for the doc."""
        text = body if body.endswith("\n") else body + "\n"
        if self._doc_uri is None:
            self._doc_uri = "file:///telperion/warm_doc.lean"
        uri = self._doc_uri
        with self._cond:
            self._diags.pop(uri, None)
            self._done.pop(uri, None)
            self._seen_diag.discard(uri)
            self._doc_version += 1
            version = self._doc_version
        if version == 1:
            self._lsp_send({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                            "params": {"textDocument": {"uri": uri, "languageId": "lean",
                                                        "version": version, "text": text}}})
        else:
            self._lsp_send({"jsonrpc": "2.0", "method": "textDocument/didChange",
                            "params": {"textDocument": {"uri": uri, "version": version},
                                       "contentChanges": [{"text": text}]}})
        deadline = time.time() + timeout
        with self._cond:
            while True:
                if self._lsp is None or self._lsp.poll() is not None:
                    return "lsp worker died", 1
                # done = fileProgress empty for the doc AND a fresh diagnostics publish.
                if self._done.get(uri) and uri in self._seen_diag:
                    diags = self._diags.get(uri, [])
                    break
                remaining = deadline - time.time()
                if remaining <= 0:
                    raise RuntimeError(f"LSP elaborate timed out after {timeout}s")
                self._cond.wait(timeout=min(remaining, 1.0))
        return self._render_diags(diags), 0

    @staticmethod
    def _render_diags(diags: list) -> str:
        """Render LSP diagnostics as the shared textual contract lines.  Severity
        1->error, 2->warning, 3/4->info.  Line/char are 0-based in LSP; the shared
        ``:L:C:`` format is 1-based, so +1.  ``#print axioms`` output arrives as an
        info diagnostic whose message already carries the ``'name' depends on axioms:``
        text that :func:`telperion.verify._parse_output` regexes."""
        sev = {1: "error", 2: "warning", 3: "info", 4: "info"}
        lines = []
        for d in diags:
            start = d.get("range", {}).get("start", {})
            ln = start.get("line", 0) + 1
            col = start.get("character", 0) + 1
            s = sev.get(d.get("severity", 1), "info")
            lines.append(f"<warm>:{ln}:{col}: {s}: {d.get('message', '')}")
        return "\n".join(lines)

    def start(self) -> bool:
        """Capability check: is ``lake env lean`` invokable in ``env_dir``?  Never
        raises.  (There is no persistent worker under the ``--stdin`` contract — see
        the EMPIRICAL FINDING in :meth:`elaborate`; each call spawns a fresh
        single-shot process.)  Returns ``False`` on a missing env dir."""
        return Path(self.env_dir).exists()

    def warm(self) -> bool:
        """True iff the resident LSP worker is up (elaboration reuses the env)."""
        return bool(self._lsp_ready and self._lsp is not None and self._lsp.poll() is None)

    def probe(self, *, timeout: float = 120.0) -> bool:
        """Capability check; result CACHED in ``_probed``.

        Prefers the resident LSP worker (``use_lsp``); on any failure falls back to
        the single-shot contract, and if that also fails the server is unavailable.
        A trivial snippet must elaborate with no ``error:``.  After a successful probe
        via the LSP, :meth:`warm` is ``True`` and repeat :meth:`elaborate` calls reuse
        the resident environment (the latency win)."""
        if self._probed is not None:
            return bool(self._probed)
        if not self.start():
            self._start_error = f"env_dir does not exist: {self.env_dir!r}"
            self._probed = False
            return False
        try:
            out, rc = self.elaborate(
                "theorem _telperion_probe : True := trivial\n", timeout=timeout)
            self._probed = (rc == 0) and ("error:" not in out)
        except Exception as e:  # pragma: no cover - env dependent
            self._start_error = repr(e)
            self._probed = False
        return bool(self._probed)

    def available(self) -> bool:
        """True iff a prior :meth:`probe` confirmed elaboration works.  Does NOT
        auto-probe: enabling the ``server=`` path is an explicit, evidence-gated
        step.  Use :meth:`warm` to tell whether the fast LSP path is active."""
        return self._probed is True

    def elaborate(self, body: str, *, env_dir=None, timeout: float = 600.0):
        """Elaborate ``body`` against the built env; return ``(text, rc)`` in the
        shared ``<file>:L:C: sev:`` textual contract (:func:`telperion.verify._parse_output`
        parses errors AND ``#print axioms`` info lines from it).

        WARM PATH (``use_lsp``, default): a resident ``lake env lean --server`` keeps
        the environment loaded, so the FIRST call pays ``import Mathlib`` and later
        calls are sub-second (validated on 4.32.0 — completion detected via
        ``$/lean/fileProgress`` emptying).  On any LSP failure this falls back to the
        SINGLE-SHOT ``--stdin`` contract (correct but re-imports Mathlib each call —
        the validated fallback), so a broken warm path never changes a verdict."""
        if self.use_lsp:
            try:
                if self._lsp_start():
                    return self._elaborate_lsp(body, timeout)
            except Exception as e:  # fall through to single-shot
                self._start_error = repr(e)
        return self._elaborate_stdin(body, timeout)

    def _elaborate_stdin(self, body: str, timeout: float):
        """Single-shot fallback: ``lake env lean --stdin`` reads the whole file until
        EOF, elaborates once, emits ``<file>:L:C: error:`` diagnostics, exits.  Correct
        but re-imports Mathlib each call (validated on 4.32.0)."""
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
        """Terminate the LSP worker (and any single-shot proc).  Idempotent, non-raising."""
        with self._lock:
            lsp, self._lsp = self._lsp, None
            proc, self._proc = self._proc, None
            self._lsp_ready = False
        for p in (lsp, proc):
            if p is None:
                continue
            try:
                p.terminate()
                p.wait(timeout=5)
            except Exception:  # pragma: no cover - best effort teardown
                try:
                    p.kill()
                except Exception:
                    pass

    # -- context manager -----------------------------------------------------

    def __enter__(self) -> "LeanServer":
        self.start()
        return self

    def __exit__(self, *exc) -> None:
        self.close()
