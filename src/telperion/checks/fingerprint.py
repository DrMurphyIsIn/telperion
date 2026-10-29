"""Statement fingerprint: a sha256 of what a theorem SAYS, insensitive to how its binders are named.

The canonical string is the theorem's type with every constant outside the library roots delta-unfolded
(``Lean.Meta.deltaExpand``, never ``whnf``, which would unfold library constants too), every binder name erased to
``_``, and the result pretty-printed with ``pp.all``. So renaming a bound variable keeps the hash, while changing a
local definition the statement depends on (``def bound : ℕ := 5`` to ``6``) changes it, even though the statement's
surface text is the same. Constants declared in the elaborated file itself have no module index, so they are never
library and always unfold.

``pp.all`` does not lift ``pp.maxSteps``: past its limit the printer writes ``⋯``, and two different statements could
then print alike. The script raises the limit, and ``parse_fingerprints`` refuses any canonical string that still
contains ``⋯`` rather than hash an elided term.
"""
from __future__ import annotations

import hashlib
import shutil
import subprocess
from pathlib import Path

from ..closure_audit import DEFAULT_LIBRARY_ROOTS, lean_name_literal
from .negation_probe import default_wrapper

LIBRARY_ROOTS: tuple[str, ...] = DEFAULT_LIBRARY_ROOTS
FINGERPRINT_DIR = ".telperion_fingerprint"
ELIDED = "⋯"

_SCRIPT = """__IMPORTS__
import Lean

__BODY__

open Lean Meta

partial def tpEraseNames : Expr → Expr
  | .forallE _ t b bi => .forallE `_ (tpEraseNames t) (tpEraseNames b) bi
  | .lam _ t b bi => .lam `_ (tpEraseNames t) (tpEraseNames b) bi
  | .letE _ t v b nd => .letE `_ (tpEraseNames t) (tpEraseNames v) (tpEraseNames b) nd
  | .app f a => .app (tpEraseNames f) (tpEraseNames a)
  | .mdata _ e => tpEraseNames e
  | .proj s i e => .proj s i (tpEraseNames e)
  | e => e

def tpRoots : List Name := __ROOTS__

def tpIsLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => tpRoots.any (·.isPrefixOf (env.header.moduleNames[idx.toNat]!))
  | none => false

#eval show MetaM Unit from do
  let env ← getEnv
  for t in (__TARGETS__ : List Name) do
    match env.find? t with
    | none => IO.println s!"FP-MISSING {t}"
    | some ci =>
      let e ← deltaExpand ci.type (fun n => !tpIsLib env n)
      let s ← withOptions (fun o => (o.setBool `pp.all true).set `pp.maxSteps (1000000000 : Nat))
        (ppExpr (tpEraseNames e))
      IO.println s!"FP-BEGIN {t}\\n{s}\\nFP-END {t}"
"""


def _names(names) -> str:
    return "[" + ", ".join(lean_name_literal(n) for n in names) + "]"


def render_fingerprint_script(imports: list[str], targets: list[str],
                              library_roots: tuple[str, ...] = LIBRARY_ROOTS, body: str = "") -> str:
    """The Lean script that prints each target's canonical statement between ``FP-BEGIN``/``FP-END`` markers.

    ``body`` is Lean source elaborated after the imports and before the script's own definitions; that is how
    ``run_fingerprint_on_text`` puts the declarations under test in the same file."""
    return (_SCRIPT.replace("__IMPORTS__", "\n".join(f"import {m}" for m in imports))
            .replace("__BODY__", body)
            .replace("__ROOTS__", _names(library_roots))
            .replace("__TARGETS__", _names(targets)))


def parse_fingerprints(output: str) -> dict[str, str]:
    """Map each target to the sha256 hex of its canonical string (the text between the markers, stripped).

    Raises ValueError naming any ``FP-MISSING`` target, any unterminated block, and any elided (``⋯``) string."""
    lines = output.splitlines()
    missing = [ln[len("FP-MISSING "):].strip() for ln in lines if ln.startswith("FP-MISSING ")]
    if missing:
        raise ValueError(f"target not found: {', '.join(missing)}")
    out: dict[str, str] = {}
    i = 0
    while i < len(lines):
        if not lines[i].startswith("FP-BEGIN "):
            i += 1
            continue
        target = lines[i][len("FP-BEGIN "):].strip()
        try:
            end = lines.index(f"FP-END {target}", i + 1)
        except ValueError:
            raise ValueError(f"unterminated fingerprint block for {target}") from None
        canon = "\n".join(lines[i + 1:end]).strip()
        if ELIDED in canon:
            raise ValueError(f"canonical statement of {target} is elided ({ELIDED}); refusing to hash it")
        out[target] = hashlib.sha256(canon.encode("utf-8")).hexdigest()
        i = end + 1
    return out


def _run_script(project: Path, script: str, targets: list[str], wrapper: list[str] | None,
                timeout: int) -> dict[str, str]:
    """Write the script to ``<project>/.telperion_fingerprint/``, run it with ``lake env lean``, delete the dir.

    The directory must not already exist (a concurrent or stale run). A nonzero exit is an error even if the markers
    were printed: the declarations may not have elaborated as written."""
    project = Path(project)
    prefix = default_wrapper() if wrapper is None else list(wrapper)
    fdir = project / FINGERPRINT_DIR
    try:
        fdir.mkdir()
    except FileExistsError:
        raise ValueError(f"fingerprint dir {fdir} already exists; remove it if no other run is going") from None
    try:
        f = fdir / "Fingerprint.lean"
        f.write_text(script, encoding="utf-8")
        try:
            p = subprocess.run([*prefix, "lake", "env", "lean", str(f.relative_to(project))], cwd=project,
                               capture_output=True, text=True, timeout=timeout)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise ValueError(f"fingerprint run did not finish: {exc}") from None
    finally:
        shutil.rmtree(fdir, ignore_errors=True)
    output = p.stdout + p.stderr
    fps = parse_fingerprints(output)
    if p.returncode != 0:
        raise ValueError(f"lean exited {p.returncode}:\n{output[-4000:]}")
    absent = [t for t in targets if t not in fps]
    if absent:
        raise ValueError(f"no fingerprint printed for {', '.join(absent)}:\n{output[-4000:]}")
    return {t: fps[t] for t in targets}


def run_fingerprint(project: Path, imports: list[str], targets: list[str], wrapper: list[str] | None = None,
                    timeout: int = 1800) -> dict[str, str]:
    """Fingerprint ``targets`` after importing ``imports`` in the built Lake project ``project``."""
    return _run_script(project, render_fingerprint_script(imports, targets), targets, wrapper, timeout)


def _split_header(text: str) -> tuple[list[str], str]:
    """(imported modules, the rest) of a Lean file: its leading ``import`` lines, past blanks and ``--`` comments."""
    lines = text.splitlines()
    imports: list[str] = []
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if s.startswith("import "):
            imports.extend(s.split()[1:])
        elif s and not s.startswith("--"):
            break
        i += 1
    return imports, "\n".join(lines[i:])


def run_fingerprint_on_text(project: Path, text: str, target: str, wrapper: list[str] | None = None,
                            timeout: int = 1800) -> str:
    """Fingerprint ``target`` as declared in the Lean source ``text``, elaborated as a temp file in ``project``."""
    imports, body = _split_header(text)
    script = render_fingerprint_script(imports, [target], body=body)
    return _run_script(project, script, [target], wrapper, timeout)[target]
