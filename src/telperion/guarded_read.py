"""The one guarded reader of a working-tree file that a check must not trust blindly.

Factored out of `missions.process` (Controller Ruling 8: `_load_freeze_safe`, `_load_deviations_safe`) for the
island registry (step 6), so the refusals are written once. Refused, in this order, before anything is read
through the path: a symlink (its target can be any file at all); anything else that is not a regular file (a
directory, e.g. a submodule checkout, or a special file); a file over *max_bytes*. The open uses O_NOFOLLOW, so a
symlink swapped in after the lstat is refused too, not followed, and O_NONBLOCK, so a FIFO swapped in cannot hang
the read before the fstat refuses it. Decoding and parsing are the caller's.
"""
from __future__ import annotations

import os
import stat
from pathlib import Path
from typing import Optional, Tuple


def read_guarded(path: Path, *, label: str, max_bytes: int) -> Tuple[Optional[bytes], Optional[str]]:
    """`(data, None)`; `(None, None)` when nothing at all is at *path* (not even a dangling symlink); or
    `(None, problem)`, a sentence naming *label*, when the path exists but cannot be trusted. Never raises."""
    path = Path(path)
    try:
        st = path.lstat()
    except FileNotFoundError:
        return None, None
    except (OSError, ValueError) as exc:     # ValueError: an embedded NUL byte in the path
        return None, f"{label} could not be read ({getattr(exc, 'strerror', None) or exc})."
    if stat.S_ISLNK(st.st_mode):
        return None, f"{label} is a symlink in the working tree; refusing to trust it."
    if not stat.S_ISREG(st.st_mode):
        return None, (f"{label} in the working tree is not a regular file (a directory, e.g. a submodule "
                      "checkout, or a special file); refusing to trust it.")
    if st.st_size > max_bytes:
        return None, f"{label} is larger than {max_bytes} bytes; refusing to trust it."
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0))
        with os.fdopen(fd, "rb") as fh:
            if not stat.S_ISREG(os.fstat(fh.fileno()).st_mode):
                return None, f"{label} changed while being read; refusing to trust it."
            data = fh.read(max_bytes + 1)
    except OSError as exc:
        return None, f"{label} could not be read ({exc.strerror or exc})."
    if len(data) > max_bytes:
        return None, f"{label} is larger than {max_bytes} bytes; refusing to trust it."
    return data, None
