"""Structured Lean verification against a PERSISTENT pre-built environment.

Replaces the ad-hoc ``worktree add`` + ``lake exe cache get`` + ``lake build`` +
``grep 'Build completed'`` + separate ``#print axioms`` dance with ONE typed call:

    r = verify_lean(content, env_dir=Path("examples/log_combination/lean"),
                    decls=["log79_add_fstar"])
    assert r.okay and r.axioms_clean

The ``env_dir`` is a pre-built Lake project (its ``.lake`` already holds the
mathlib olean cache and any project deps), so verification ELABORATES the given
source against that environment via ``lake env lean`` WITHOUT re-fetching the
cache or rebuilding dependencies -- the "persistent environment" (cf. AXLE's
reusable ``environment``).  A warm long-lived Lean server for sub-second repeat
verification is available as an OPTIONAL, fallback-guarded fast path: pass a live
:class:`telperion.lean_server.LeanServer` via ``server=`` (see #5 below).

Trust model note: ``okay`` is the COMPILATION gate (no Lean errors AND a zero
subprocess exit code).  ``axioms_clean`` is the stronger TRUSTED gate -- every
CHECKED declaration's axiom set excludes ``sorryAx`` (and any axiom outside the
allow-list).  This mirrors AXLE's ``check`` (compile-only) vs ``verify_proof``
(rejects sorry/axioms) split, and Telperion's untrusted-generator /
trusted-kernel boundary.

Three hardening properties this module guarantees (previously bugs):

1. RETURNCODE BACKSTOP.  A nonzero ``lake env lean`` exit whose output carries no
   parseable ``:L:C: error:`` line no longer slips through as ``okay=True``.
   When ``returncode != 0`` and no error was parsed, a synthetic error is
   recorded and ``okay`` is forced ``False`` (same discipline as
   :mod:`telperion.evolve.kernel`, which gates on ``proc.returncode == 0``).

2. MULTI-LINE ERROR BLOCKS.  Lean diagnostics routinely span several lines
   (the goal state, the offending term, hints).  Errors are collected as the
   FULL block from a ``:L:C: error:`` header up to the next diagnostic header
   (``error:`` / ``warning:`` / ``info:`` at a ``:L:C:`` position) or EOF, not a
   single ``'error:'``-split line.

3. NON-VACUOUS ``axioms_clean``.  ``axioms_checked`` records whether ANY decl was
   actually axiom-checked.  When ``decls`` is empty nothing was certified, so
   ``axioms_clean`` is ``False`` -- callers must NAME what they certify.  A
   compile-only pass (no decls) is still expressible as ``r.okay`` alone.
"""
from __future__ import annotations

import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

# Axioms Mathlib itself is built on -- always permitted.
_MATHLIB_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# A diagnostic HEADER: `<file>:<line>:<col>: <severity>:`  We anchor on the
# `:L:C: <severity>:` tail so paths with colons (unlikely here) do not confuse us.
_DIAG_HEAD = re.compile(r":\d+:\d+: (error|warning|info): ?(.*)")
_ERR_LINE = re.compile(r":\d+:\d+: error:")
_WARN_LINE = re.compile(r":\d+:\d+: warning: (.*)")
_SORRY = re.compile(r"declaration uses ['`]sorry['`]")
_AXIOMS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
_NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")


@dataclass
class VerifyResult:
    """Structured result of elaborating Lean source against a built environment.

    ``axioms_clean`` is a strict TRUSTED gate: it is ``True`` only when decls were
    actually axiom-checked (``axioms_checked``), none used a disallowed axiom, and
    no ``sorry`` was reported.  With no decls (``axioms_checked=False``) it is
    ``False`` by construction -- an unaudited pass is never silently "clean".
    Use ``r.okay`` alone to gate a COMPILE-ONLY pass.
    """

    okay: bool                                   # no Lean errors AND zero exit code
    axioms_clean: bool                           # decls checked AND no sorryAx/disallowed axiom
    axioms_checked: bool = False                 # were ANY decls axiom-checked at all?
    errors: list = field(default_factory=list)   # Lean error blocks (may be multi-line)
    warnings: list = field(default_factory=list) # Lean warnings
    sorries: bool = False                        # any "declaration uses 'sorry'"
    axioms: dict = field(default_factory=dict)   # decl -> sorted list of axiom names
    disallowed: dict = field(default_factory=dict)  # decl -> axioms outside the allow-set
    returncode: int = 0                          # subprocess exit code (backstop signal)
    elapsed_s: float = 0.0
    raw: str = ""

    def summary(self) -> str:
        tag = "OK" if (self.okay and self.axioms_clean) else "FAIL"
        if not self.axioms_checked:
            ax = "; axioms UNCHECKED (no decls named)"
        elif self.axioms_clean:
            ax = "; axioms clean"
        else:
            ax = "; axioms DIRTY " + repr(self.disallowed)
        errs = "" if self.okay else f"; {len(self.errors)} error(s): {self.errors[:2]}"
        rc = "" if self.returncode == 0 else f"; rc={self.returncode}"
        return f"[{tag}] elaborated in {self.elapsed_s:.1f}s{ax}{errs}{rc}"


def _collect_error_blocks(out: str) -> list:
    """Collect FULL error blocks from Lean output.

    An error block begins at a ``:L:C: error:`` header and runs until the next
    diagnostic header (``error``/``warning``/``info`` at a ``:L:C:`` position) or
    EOF.  This preserves the goal-state / offending-term lines Lean prints under
    an error, which a single ``'error:'``-split line would discard.  The leading
    ``<file>:L:C: error: `` prefix is stripped from each block's first line so the
    message reads cleanly; continuation lines are kept verbatim.
    """
    lines = out.splitlines()
    blocks: list = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = _DIAG_HEAD.search(line)
        if m and m.group(1) == "error":
            # First line: drop everything up to and including the `error: `.
            first = line.split("error:", 1)[1].strip()
            block = [first] if first else []
            i += 1
            # Accumulate continuation lines until the next diagnostic header/EOF.
            while i < n and not _DIAG_HEAD.search(lines[i]):
                block.append(lines[i])
                i += 1
            blocks.append("\n".join(block).rstrip())
        else:
            i += 1
    return blocks


def _parse_output(out: str, returncode: int, *, decls, permitted) -> dict:
    """Pure parse of raw Lean output into the VerifyResult field values.

    Split out so both the cold ``lake env lean`` path and the warm-server path
    feed identical parsing/gating logic (and so it is unit-testable offline).
    """
    errors = _collect_error_blocks(out)
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

    # (#3.1) Returncode backstop: a nonzero exit with no parseable error line must
    # NOT read as okay.  Synthesize a diagnostic so callers see WHY it failed.
    if returncode != 0 and not errors:
        errors = errors + [
            f"lake env lean exited with code {returncode} but emitted no parseable "
            f"':L:C: error:' line (backstop). Raw output tail:\n"
            + "\n".join(out.splitlines()[-8:])
        ]

    okay = (len(errors) == 0) and (returncode == 0)

    # (#3.3) axioms_checked is the explicit UNCHECKED state.  When no decls were
    # named nothing was certified -> axioms_clean is False (never vacuously true).
    axioms_checked = len(tuple(decls)) > 0
    axioms_clean = (
        axioms_checked
        and len(disallowed) == 0
        and not sorries
    )

    return dict(
        okay=okay, axioms_clean=axioms_clean, axioms_checked=axioms_checked,
        errors=errors, warnings=warnings, sorries=sorries, axioms=axioms,
        disallowed=disallowed, returncode=returncode, raw=out,
    )


def verify_lean(
    content: str,
    *,
    env_dir,
    decls=(),
    allow_axioms=(),
    lean_path_bin=None,
    timeout=600,
    server=None,
) -> VerifyResult:
    """Elaborate ``content`` against the built Lake project at ``env_dir``.

    ``decls``: declaration names to axiom-check (``#print axioms`` appended).
    Naming at least one decl is what flips ``axioms_checked`` on; with an empty
    ``decls`` the result reports ``axioms_clean=False`` (UNCHECKED) and callers
    should gate on ``r.okay`` alone for a compile-only pass.
    ``allow_axioms``: extra axiom names to permit beyond mathlib's three
    (e.g. a named axiom you are deliberately tolerating during dev).
    ``server``: an optional live :class:`telperion.lean_server.LeanServer`.  When
    supplied AND healthy, the warm worker is used (avoids the cold ~4-9s
    ``lake env lean`` startup); if it is ``None`` or reports itself unavailable,
    this transparently falls back to the cold path.  See ``lean_server`` for the
    validated-vs-unvalidated-on-4.32.0 caveats.
    Returns a :class:`VerifyResult`.
    """
    env_dir = Path(env_dir)
    permitted = _MATHLIB_AXIOMS | frozenset(allow_axioms)

    body = content.rstrip() + "\n"
    for d in decls:
        body += f"#print axioms {d}\n"

    # (#5) Warm-server fast path -- fully fallback-guarded.  Any failure to obtain
    # output from the server drops us to the cold path below.
    if server is not None:
        try:
            if server.available():
                t0 = time.time()
                out, returncode = server.elaborate(body, env_dir=env_dir, timeout=timeout)
                elapsed = time.time() - t0
                fields = _parse_output(out, returncode, decls=decls, permitted=permitted)
                return VerifyResult(elapsed_s=elapsed, **fields)
        except Exception:
            # Defensive: a broken warm path must never fail a verification that the
            # cold path could complete.  Fall through.
            pass

    # Cold path: temp file INSIDE env_dir so `import` resolves against the
    # project's oleans.
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
        returncode = proc.returncode
    finally:
        os.unlink(tmp)

    fields = _parse_output(out, returncode, decls=decls, permitted=permitted)
    return VerifyResult(elapsed_s=elapsed, **fields)


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
    # Gate: a compile-only pass (no decls) succeeds on okay alone; a decl-checked
    # pass additionally requires axioms_clean.
    ok = r.okay and (r.axioms_clean or not r.axioms_checked)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main())
