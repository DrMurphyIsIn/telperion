from __future__ import annotations

import contextlib
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
    out = Path(lean_project) / "ProbeEvolve.lean"
    out.write_text(src)
    try:
        proc = subprocess.run(["lake", "env", "lean", str(out)], cwd=lean_project,
                              capture_output=True, text=True)
        return proc.returncode == 0, {"lean": src, "stderr": proc.stderr[:400]}
    finally:
        out.unlink(missing_ok=True)
