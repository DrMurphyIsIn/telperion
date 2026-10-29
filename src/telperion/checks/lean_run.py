"""Run a Lean command (usually ``[wrapper..., "lake", "env", "lean", ...]``) so that nothing it spawns outlives a timeout.

The logic is negation_probe._run's (copied, not imported, while that module is being rewritten; to be consolidated).
"""
from __future__ import annotations

import os
import signal
import subprocess
from pathlib import Path


def run_lean(cmd: list[str], cwd: Path, timeout: int, input: str | None = None) -> tuple[int, str]:
    """(returncode, stdout + stderr) of `cmd` in its own session, with `input` on stdin if given. On the wall-clock
    timeout the whole process group gets SIGTERM (leanlock's trap then frees its slot) and, 5 s later, SIGKILL, so no
    lake or lean child under the wrapper outlives the run; TimeoutExpired is then re-raised."""
    p = subprocess.Popen(cmd, cwd=cwd, stdin=subprocess.PIPE if input is not None else subprocess.DEVNULL,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, err = p.communicate(input=input, timeout=timeout)
    except subprocess.TimeoutExpired:
        for sig in (signal.SIGTERM, signal.SIGKILL):
            try:
                os.killpg(p.pid, sig)
            except ProcessLookupError:
                break
            try:
                p.communicate(timeout=5)
                break
            except subprocess.TimeoutExpired:
                continue
        p.wait()
        raise
    return p.returncode, out + err
