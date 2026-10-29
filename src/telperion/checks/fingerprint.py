"""Statement fingerprint: a sha256 of what a theorem SAYS, insensitive to how its binders and universes are named.

WHAT IS HASHED. The theorem's type, after ``Lean.Meta.deltaExpand`` has unfolded every DEFINITION (``defnInfo``) that
lies outside the library roots, serialized STRUCTURALLY by ``tpSer``: an explicitly tagged, injective rendering of the
``Expr`` tree. Bound variables are de Bruijn indices, so binder names never appear. Binder info (default, implicit,
strict implicit, instance) is kept, because it is part of the meaning. Universe levels are serialized structurally
(zero, succ, max, imax), and level parameters are numbered by position in the target's ``levelParams``, so renaming
``u`` to ``v`` keeps the hash. Constant names are serialized component by component, each one quoted, and ``mdata`` is
dropped. Nothing goes through the pretty-printer, so pp options a file sets, ``pp.maxSteps`` elision and hygienic
``✝`` names cannot reach the hash. Constants declared in the elaborated file itself have no module index, so they are
never library and always unfold. ``whnf`` is never used, because it would unfold library constants too.

WHAT IS REFUSED (fail closed, ``FP-REFUSED``, a ValueError). ``deltaExpand`` unfolds definitions only. Any non-library
constant still left after unfolding would be hashed by its NAME alone: a local inductive, constructor, recursor,
structure (also through a projection's structure name), axiom, opaque, quotient or theorem, and an ``irreducible_def``
(whose wrapper is an opaque structure). Such a target is refused rather than hashed. So is a free or meta variable, or
a level parameter that is not one of the target's own. Hashing an inductive's full declaration closure would let these
through, but that is a later extension.

TRUST BOUNDARY. "Library" means "declared in a module whose name starts with a library root". Before running, the
project is searched (outside ``.lake`` and ``.git``) for a directory or ``.lean`` file named after a root: a project
file at ``Mathlib/Foo.lean`` would otherwise be module ``Mathlib.Foo`` and be trusted, folded and never unfolded. That
is refused. The fingerprint is NOT a defence against a malicious Lean environment: an imported module that registers
elaborators, or rewrites the environment, is inside the trust boundary. Comparator and closure_audit check that.
"""
from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
from pathlib import Path

from ..closure_audit import DEFAULT_LIBRARY_ROOTS, lean_name_literal
from .negation_probe import default_wrapper

LIBRARY_ROOTS: tuple[str, ...] = DEFAULT_LIBRARY_ROOTS
FINGERPRINT_DIR = ".telperion_fingerprint"

_SCRIPT = """__IMPORTS__
import Lean

__BODY__

open Lean Meta

def tpRoots : List Name := __ROOTS__

def tpIsLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => tpRoots.any (·.isPrefixOf (env.header.moduleNames[idx.toNat]!))
  | none => false

def tpIsDef (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo _) => true
  | _ => false

def tpKind : Option ConstantInfo → String
  | some (.axiomInfo _) => "axiom"
  | some (.defnInfo _) => "def"
  | some (.thmInfo _) => "theorem"
  | some (.opaqueInfo _) => "opaque"
  | some (.quotInfo _) => "quot"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _) => "constructor"
  | some (.recInfo _) => "recursor"
  | none => "unknown"

/-- The first thing left after unfolding that cannot be hashed: a non-library constant or projection structure, or a
free or meta variable. -/
partial def tpOffense (env : Environment) : Expr → Option (String × String)
  | .const n _ => if tpIsLib env n then none else some (n.toString, tpKind (env.find? n))
  | .proj s _ e => if tpIsLib env s then tpOffense env e else some (s.toString, tpKind (env.find? s))
  | .fvar _ => some ("free-variable", "fvar")
  | .mvar _ => some ("metavariable", "mvar")
  | .app f a => tpOffense env f <|> tpOffense env a
  | .lam _ t b _ => tpOffense env t <|> tpOffense env b
  | .forallE _ t b _ => tpOffense env t <|> tpOffense env b
  | .letE _ t v b _ => tpOffense env t <|> tpOffense env v <|> tpOffense env b
  | .mdata _ e => tpOffense env e
  | _ => none

/-- Injective: every component is self-delimiting (a quoted string, or `#` and a number). -/
partial def tpSerName : Name → String
  | .anonymous => "_"
  | .str p s => tpSerName p ++ "." ++ s.quote
  | .num p n => tpSerName p ++ "#" ++ toString n

partial def tpSerLevel (lps : List Name) : Level → Except String String
  | .zero => pure "z"
  | .succ l => do return s!"(S {← tpSerLevel lps l})"
  | .max a b => do return s!"(M {← tpSerLevel lps a} {← tpSerLevel lps b})"
  | .imax a b => do return s!"(I {← tpSerLevel lps a} {← tpSerLevel lps b})"
  | .param n => match lps.idxOf? n with
    | some i => pure s!"(P {i})"
    | none => throw s!"level-param-{n}"
  | .mvar _ => throw "level-metavariable"

def tpSerBi : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

partial def tpSer (lps : List Name) : Expr → Except String String
  | .bvar i => pure s!"(b {i})"
  | .fvar _ => throw "free-variable"
  | .mvar _ => throw "metavariable"
  | .sort u => do return s!"(s {← tpSerLevel lps u})"
  | .const n us => do
    let ls ← us.mapM (tpSerLevel lps)
    return s!"(c {tpSerName n} [{" ".intercalate ls}])"
  | .app f a => do return s!"(a {← tpSer lps f} {← tpSer lps a})"
  | .lam _ t b bi => do return s!"(l {tpSerBi bi} {← tpSer lps t} {← tpSer lps b})"
  | .forallE _ t b bi => do return s!"(p {tpSerBi bi} {← tpSer lps t} {← tpSer lps b})"
  | .letE _ t v b nd => do return s!"(t {← tpSer lps t} {← tpSer lps v} {← tpSer lps b} {nd})"
  | .lit (.natVal n) => pure s!"(n {n})"
  | .lit (.strVal s) => pure s!"(str {s.quote})"
  | .mdata _ e => tpSer lps e
  | .proj s i e => do return s!"(j {tpSerName s} {i} {← tpSer lps e})"

#eval show MetaM Unit from do
  let env ← getEnv
  for t in (__TARGETS__ : List Name) do
    match env.find? t with
    | none => IO.println s!"FP-MISSING {t}"
    | some ci =>
      let e ← deltaExpand ci.type (fun n => !tpIsLib env n && tpIsDef env n)
      match tpOffense env e with
      | some (c, k) =>
        let uses := ci.type.getUsedConstants.filter (!tpIsLib env ·) |>.toList.map toString
        IO.println s!"FP-REFUSED {t} {c} {k} (statement uses: {", ".intercalate uses})"
      | none =>
        match tpSer ci.levelParams e with
        | .error msg => IO.println s!"FP-REFUSED {t} {msg} unserializable"
        | .ok s => IO.println s!"FP-BEGIN {t}\\n{s}\\nFP-END {t}"
"""


def _names(names) -> str:
    return "[" + ", ".join(lean_name_literal(n) for n in names) + "]"


def render_fingerprint_script(imports: list[str], targets: list[str],
                              library_roots: tuple[str, ...] = LIBRARY_ROOTS, body: str = "") -> str:
    """The Lean script that prints each target's serialized statement between ``FP-BEGIN``/``FP-END`` markers, or
    ``FP-REFUSED``/``FP-MISSING``.

    ``body`` is Lean source elaborated after the imports and before the script's own definitions; that is how
    ``run_fingerprint_on_text`` puts the declarations under test in the same file."""
    return (_SCRIPT.replace("__IMPORTS__", "\n".join(f"import {m}" for m in imports))
            .replace("__BODY__", body)
            .replace("__ROOTS__", _names(library_roots))
            .replace("__TARGETS__", _names(targets)))


def parse_fingerprints(output: str) -> dict[str, str]:
    """Map each target to the sha256 hex of its serialization (the text between the markers, stripped).

    Raises ValueError naming any ``FP-MISSING`` or ``FP-REFUSED`` target, any unterminated block, and any empty
    serialization."""
    lines = output.splitlines()
    missing = [ln[len("FP-MISSING "):].strip() for ln in lines if ln.startswith("FP-MISSING ")]
    if missing:
        raise ValueError(f"target not found: {', '.join(missing)}")
    refused = [ln[len("FP-REFUSED "):].strip() for ln in lines if ln.startswith("FP-REFUSED ")]
    if refused:
        raise ValueError("refused (<target> <constant> <kind> (statement uses: ...); a non-library constant deltaExpand cannot unfold "
                         "would be hashed by name): " + "; ".join(refused))
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
        if not canon:
            raise ValueError(f"empty serialization for {target}")
        out[target] = hashlib.sha256(canon.encode("utf-8")).hexdigest()
        i = end + 1
    return out


def _spoofed_roots(project: Path, library_roots: tuple[str, ...]) -> list[Path]:
    """Directories and ``.lean`` files in the project (outside ``.lake``/``.git``) named after a library root."""
    hits: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(project):
        dirnames[:] = sorted(d for d in dirnames if d not in (".lake", ".git"))
        hits += [Path(dirpath, d) for d in dirnames if d in library_roots]
        hits += [Path(dirpath, f) for f in sorted(filenames) if f.endswith(".lean") and f[:-5] in library_roots]
    return hits


def _escaped(target: str) -> str:
    """The target as Lean prints a Name (``Foo.«bar baz»``)."""
    try:
        return lean_name_literal(target)[1:]
    except ValueError:
        return target


def _run_script(project: Path, script: str, targets: list[str], wrapper: list[str] | None,
                timeout: int) -> dict[str, str]:
    """Write the script to ``<project>/.telperion_fingerprint/``, run it with ``lake env lean``, delete the dir.

    A project that declares modules under a library root is refused first (see the module docstring). The directory
    must not already exist (a concurrent or stale run). A nonzero exit is an error even if the markers
    were printed: the declarations may not have elaborated as written."""
    project = Path(project)
    spoofed = _spoofed_roots(project, LIBRARY_ROOTS)
    if spoofed:
        raise ValueError(f"project declares modules under a library root ({', '.join(map(str, spoofed))}); they would "
                         "be trusted as library and never unfolded")
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
    keys = {t: t if t in fps else _escaped(t) for t in targets}
    absent = [t for t, k in keys.items() if k not in fps]
    if absent:
        raise ValueError(f"no fingerprint printed for {', '.join(absent)}:\n{output[-4000:]}")
    return {t: fps[k] for t, k in keys.items()}


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
