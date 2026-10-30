"""Run a Lean command (``[wrapper..., <pinned lean>, ...]``) so that nothing it spawns outlives it. The one runner of
the checks (negation_probe, fingerprint, lean_replay). Two properties, both so that a daemon left behind by a compiled
body cannot act after the run:

* the process GROUP is reaped after EVERY run (SIGTERM, a short grace, SIGKILL), not only on timeout;
* only the leader is waited for. Output goes to unnamed temporary files, not pipes, so a daemon that inherited
  stdout cannot keep the run open (``communicate`` would wait for its EOF, i.e. for the daemon to finish its work).
  Stdin, when given, is fed through a pipe by a thread, so it is never on disk.

A process that calls ``setsid`` leaves the group and is not reaped: this is not a sandbox.
"""
from __future__ import annotations

import os
import signal
import subprocess
import tempfile
import threading
import time
from pathlib import Path


def _feed(pipe, data: str) -> None:
    try:
        pipe.write(data.encode("utf-8"))
        pipe.close()
    except (BrokenPipeError, OSError):
        pass


def reap_group(pgid: int, grace: float) -> None:
    """SIGTERM the process group, wait up to `grace` s for it to empty, then SIGKILL it (and wait again).

    EPERM counts as empty: macOS returns it when the only members left are zombies (an unwaited leader), and a group
    with any live member of ours accepts the signal."""
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(pgid, sig)
        except (ProcessLookupError, PermissionError):
            return
        deadline = time.monotonic() + grace
        while time.monotonic() < deadline:
            try:
                os.killpg(pgid, 0)
            except (ProcessLookupError, PermissionError):
                return
            time.sleep(0.05)


#: The most output a run may write, per stream (final review M4); more is OutputLimitExceeded.
MAX_OUTPUT = 64 * 1024 * 1024


class OutputLimitExceeded(OSError):
    """A run wrote more than its output bound to stdout or stderr; the run was killed. Callers that catch OSError
    report it as ERROR, like a run that did not finish."""


def run_lean(cmd: list[str], cwd: Path, timeout: int, input: str | None = None,
             env: dict[str, str] | None = None, max_output: int = MAX_OUTPUT) -> tuple[int, str]:
    """(returncode, stdout + stderr) of `cmd` in its own session, with `input` on stdin if given and `env` as its
    environment if given. When the leader exits, the rest of its process group is reaped (1 s grace). On the
    wall-clock timeout the whole group gets SIGTERM (leanlock's trap then frees its slot) and, 5 s later, SIGKILL;
    TimeoutExpired is then re-raised. Output is bounded: once stdout or stderr holds more than `max_output` bytes
    (checked every 0.2 s while the run lasts, and at its end) the group is reaped the same way and
    OutputLimitExceeded is raised."""
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdin=subprocess.PIPE if input is not None else subprocess.DEVNULL,
                             stdout=out, stderr=err, start_new_session=True)
        feeder = None
        if input is not None:
            feeder = threading.Thread(target=_feed, args=(p.stdin, input), daemon=True)
            feeder.start()

        def too_big() -> bool:
            return max(os.fstat(out.fileno()).st_size, os.fstat(err.fileno()).st_size) > max_output
        deadline = time.monotonic() + timeout
        try:
            while True:
                try:
                    p.wait(timeout=max(0.0, min(0.2, deadline - time.monotonic())))
                    break
                except subprocess.TimeoutExpired:
                    if too_big():
                        reap_group(p.pid, 5.0)
                        p.wait()
                        raise OutputLimitExceeded(f"the run wrote more than {max_output} bytes of output") from None
                    if time.monotonic() >= deadline:
                        reap_group(p.pid, 5.0)
                        p.wait()
                        raise subprocess.TimeoutExpired(cmd, timeout) from None
        finally:
            if feeder is not None:
                feeder.join(timeout=5)
        reap_group(p.pid, 1.0)
        if too_big():
            raise OutputLimitExceeded(f"the run wrote more than {max_output} bytes of output")
        out.seek(0)
        err.seek(0)
        text = out.read().decode("utf-8", "replace") + err.read().decode("utf-8", "replace")
    return p.returncode, text
