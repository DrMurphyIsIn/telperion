"""Structured Lean verification against a PERSISTENT pre-built environment.

Replaces the ad-hoc ``worktree add`` + ``lake exe cache get`` + ``lake build`` +
``grep 'Build completed'`` + separate ``#print axioms`` dance with ONE typed call:

    r = verify_lean(content, env_dir=Path("examples/log_combination/lean"),
                    decls=["log79_add_fstar"])
    assert r.okay and r.axioms_clean

The ``env_dir`` is a pre-built Lake project (its ``.lake`` already holds the
mathlib olean cache and any project deps), so verification ELABORATES the given
source against that environment via ``lake env lean`` WITHOUT re-fetching the
cache or rebuilding dependencies — the "persistent environment" (cf. AXLE's
reusable ``environment``).  A warm long-lived Lean server for sub-second repeat
verification is a natural follow-up; this MVP already removes the per-call
cache-get + dependency rebuild.

Trust model note: ``okay`` is the COMPILATION gate (no Lean errors).
``axioms_clean`` is the stronger TRUSTED gate — every checked declaration's axiom
set excludes ``sorryAx`` (and any axiom outside the allow-list).  This mirrors
AXLE's ``check`` (compile-only) vs ``verify_proof`` (rejects sorry/axioms) split,
and Telperion's untrusted-generator / trusted-kernel boundary.
"""
from __future__ import annotations

import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

# Axioms Mathlib itself is built on — always permitted.
_MATHLIB_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

_ERR_LINE = re.compile(r":\d+:\d+: error:")
_WARN_LINE = re.compile(r":\d+:\d+: warning: (.*)")
_SORRY = re.compile(r"declaration uses ['`]sorry['`]")
_AXIOMS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
_NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")


@dataclass
class VerifyResult:
    """Structured result of elaborating Lean source against a built environment."""

    okay: bool                                   # no Lean errors
    axioms_clean: bool                           # no sorryAx / disallowed axiom in checked decls
    errors: list = field(default_factory=list)   # Lean error messages
    warnings: list = field(default_factory=list) # Lean warnings
    sorries: bool = False                        # any "declaration uses 'sorry'"
    axioms: dict = field(default_factory=dict)   # decl -> sorted list of axiom names
    disallowed: dict = field(default_factory=dict)  # decl -> axioms outside the allow-set
    elapsed_s: float = 0.0
    raw: str = ""

    def summary(self) -> str:
        tag = "OK" if (self.okay and self.axioms_clean) else "FAIL"
        ax = "; axioms " + (
            "clean" if self.axioms_clean
            else "DIRTY " + repr(self.disallowed)
        ) if self.axioms else ""
        errs = "" if self.okay else f"; {len(self.errors)} error(s): {self.errors[:2]}"
        return f"[{tag}] elaborated in {self.elapsed_s:.1f}s{ax}{errs}"


def verify_lean(
    content: str,
    *,
    env_dir,
    decls=(),
    allow_axioms=(),
    lean_path_bin=None,
    timeout=600,
) -> VerifyResult:
    """Elaborate ``content`` against the built Lake project at ``env_dir``.

    ``decls``: declaration names to axiom-check (``#print axioms`` appended).
    ``allow_axioms``: extra axiom names to permit beyond mathlib's three
    (e.g. a named ``sorryAx`` you are deliberately tolerating during dev).
    Returns a :class:`VerifyResult`.
    """
    env_dir = Path(env_dir)
    permitted = _MATHLIB_AXIOMS | frozenset(allow_axioms)

    body = content.rstrip() + "\n"
    for d in decls:
        body += f"#print axioms {d}\n"

    # temp file INSIDE env_dir so `import` resolves against the project's oleans.
    fd, tmp = tempfile.mkstemp(suffix=".lean", dir=str(env_dir))
    os.close(fd)
    Path(tmp).write_text(body, encoding="utf-8")
    try:
        env = os.environ.copy()
        elan = lean_path_bin or str(Path.home() / ".elan" / "bin")
        env["PATH"] = elan + os.pathsep + env.get("PATH", "")
        t0 = time.time()
        proc = subprocess.run(
            ["lake", "env", "lean", tmp],
            cwd=str(env_dir), capture_output=True, text=True, env=env, timeout=timeout,
        )
        elapsed = time.time() - t0
        out = (proc.stdout or "") + (proc.stderr or "")
    finally:
        os.unlink(tmp)

    errors = [line.split("error:", 1)[1].strip()
              for line in out.splitlines() if _ERR_LINE.search(line)]
    warnings = [m.group(1).strip() for line in out.splitlines()
                if (m := _WARN_LINE.search(line))]
    sorries = bool(_SORRY.search(out))

    axioms: dict = {}
    for m in _AXIOMS.finditer(out):
        name = m.group(1)
        axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
        axioms[name] = sorted(axs)
    for m in _NO_AXIOMS.finditer(out):
        axioms[m.group(1)] = []

    disallowed = {
        d: [a for a in axs if a not in permitted]
        for d, axs in axioms.items()
        if any(a not in permitted for a in axs)
    }
    okay = len(errors) == 0
    axioms_clean = (len(disallowed) == 0) and not (sorries and not decls)

    return VerifyResult(
        okay=okay, axioms_clean=axioms_clean, errors=errors, warnings=warnings,
        sorries=sorries, axioms=axioms, disallowed=disallowed,
        elapsed_s=elapsed, raw=out,
    )


def _main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description="Structured Lean verify against a built env.")
    ap.add_argument("file", help="Lean source file to verify")
    ap.add_argument("--env", required=True, help="pre-built Lake project dir (the environment)")
    ap.add_argument("--decl", action="append", default=[], help="declaration to axiom-check")
    ap.add_argument("--allow-axiom", action="append", default=[])
    a = ap.parse_args(argv)
    content = Path(a.file).read_text(encoding="utf-8")
    r = verify_lean(content, env_dir=a.env, decls=a.decl, allow_axioms=a.allow_axiom)
    print(r.summary())
    if r.axioms:
        for d, axs in r.axioms.items():
            mark = "clean" if d not in r.disallowed else f"DIRTY {r.disallowed[d]}"
            print(f"  {d}: {mark}")
    return 0 if (r.okay and r.axioms_clean) else 1


if __name__ == "__main__":
    raise SystemExit(_main())
