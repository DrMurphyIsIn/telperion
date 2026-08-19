from __future__ import annotations

import contextlib
import hashlib
import io
import subprocess
from pathlib import Path

from .. import DirectPolyaEmitter, LeanProfile, ValidationReport, certify, emit


def kernel_check_family(family, lean_project: str, namespace=("ProbeEvolve",)):
    """Certify a family, emit via DirectPolyaEmitter, run lake env lean, return green status.

    Args:
        family: InequalityFamily to check.
        lean_project: Path to Lean project with prebuilt Mathlib.
        namespace: Tuple of namespace names for the emitted Lean.

    Returns:
        Tuple (green: bool, artifacts: dict with 'lean' and 'stderr' keys).
        green=True iff lake env lean returned 0.
    """
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        cert = certify(family)
        res = emit(cert, LeanProfile(namespace=tuple(namespace)),
                   [DirectPolyaEmitter()], ValidationReport(checks=(("spot", True),)))
    src = next(iter(res.files.values()))
    # Unique per-candidate filename (content-hashed): concurrent Tier-3 checks
    # into the same lean_project must not clobber each other's file, and two
    # identical candidates deterministically map to the same name (harmless).
    # `lake env lean <file>` checks a standalone file, so the basename need not
    # match the namespace.
    out = Path(lean_project) / f"ProbeEvolve_{hashlib.sha1(src.encode()).hexdigest()[:12]}.lean"
    out.write_text(src)
    try:
        proc = subprocess.run(["lake", "env", "lean", str(out)], cwd=lean_project,
                              capture_output=True, text=True)
        return proc.returncode == 0, {"lean": src, "stderr": proc.stderr[:400]}
    finally:
        out.unlink(missing_ok=True)
