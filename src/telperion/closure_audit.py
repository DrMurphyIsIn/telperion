"""Dependency-closure audit of a Lean theorem: a kernel-level census, not a text scan.

:mod:`telperion.audit` reads Lean SOURCE (``sorry``, a smuggled ``axiom``, a reflexive
statement).  A green build still says nothing about what the proof TERM of a theorem
actually reaches: which modules it pulls in, whether a negative-control module leaked into
the real closure, whether a constant named after the argument the proof claims to avoid is
in there, which axioms the kernel accepted.  This module renders a small Lean metaprogram
(a ``CoreM``/``MetaM`` ``#eval``) that answers those questions from the ELABORATED
ENVIRONMENT, runs it with ``lake env lean`` inside a built Lake project, and parses its
output into a JSON-friendly :class:`AuditResult`.

What the audit does
-------------------
* the transitive constant closure of the target theorems, walked through every constant's
  TYPE and, for theorems, definitions and opaques, its VALUE (proof term / body); for an
  inductive, its constructors and (by default) its ``.rec`` recursor;
* a census of that closure by root module (``Mathlib``, ``Init``, ``Lean``, ...);
* EVERY constant outside the declared library roots, listed by module;
* a case-insensitive substring scan of every closure constant's name and module for the
  caller's patterns (e.g. ``heegner``), and the same scan over every imported module name;
* an absence check: named constants (``sorryAx`` by default) and module prefixes (e.g. a
  negative-control library) that must NOT appear in the closure;
* ``collectAxioms`` per target against an allowed list (``propext``, ``Classical.choice``,
  ``Quot.sound`` by default) -- the machine-checked form of ``#print axioms``;
* the non-library modules that are IMPORTED into the environment but contribute nothing to
  the closure (an imported-but-unused module is not a soundness problem; it is listed so a
  reviewer can ask why it is there).

What it does NOT guarantee
--------------------------
* It audits the elaborated environment of THIS build of the project, not the export an
  independent checker (Comparator, lean4export) saw.  The two describe the same proof only
  when the tree did not change between the two runs; :mod:`telperion.freeze_manifest` is
  how that condition is recorded.
* The name scan is a substring match.  It cannot see a renamed argument, and a hit is not a
  verdict: ``Mathlib.NumberTheory.NumberField.ClassNumber.classNumber_eq_one_iff`` hits
  ``classnumber_eq_one`` and is a PID criterion, not a classification theorem.  Hits are
  reported, never auto-failed, unless ``fail_on_scan_hit`` is set.
* It says nothing about the CONTENT of the library constants it counts.  A dependency that
  is itself unsound is invisible to a census.
* The walk is over the kernel environment's constants.  ``native_decide`` leaves a trace (an
  axiom outside the allowed set: a generated ``<thm>._native.native_decide.ax_*`` on v4.32.0,
  ``Lean.ofReduceBool`` on later toolchains) but ``implemented_by`` / ``extern`` bodies and
  the compiled code they run are not inspected.

The recursor option
-------------------
An independent reviewer's walk used Lean's ``ConstantInfo.getUsedConstantsAsSet`` (type +
``value?`` + constructors for an inductive + ``all`` for a recursor) and its count differed
from ours only by the ``*.rec`` recursors our walk adds for every inductive it meets.
``include_recursors=False`` reproduces the reviewer's walk; the default keeps the
recursors, because a recursor is a genuine kernel constant the inductive brings along.
"""
from __future__ import annotations

import json
import os
import re
import shlex
import subprocess
import tempfile
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Sequence

from .comparator import CLEAN_AXIOMS

#: Root modules that count as "library": their constants are tallied, not listed.
DEFAULT_LIBRARY_ROOTS: tuple[str, ...] = (
    "Init", "Lean", "Std", "Batteries", "Mathlib", "Aesop", "Qq", "ProofWidgets",
    "Plausible", "LeanSearchClient", "ImportGraph", "Lake", "Cli",
)

#: Constants that must never be in a real closure.
DEFAULT_ABSENT_CONSTANTS: tuple[str, ...] = ("sorryAx",)

#: The output-protocol prefix the Lean script uses for machine-readable lines.
PROTOCOL_PREFIX = "@@"
PROTOCOL_VERSION = "telperion-closure-audit/1"

_IDENT_COMPONENT = re.compile(r"^[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏][\w'!?Ͱ-Ͽἀ-῿℀-⅏₀-₉ₐ-ₜᵢ-ᵪ]*$")


class ClosureAuditError(Exception):
    """The audit could not be run or its output could not be read."""


# --------------------------------------------------------------------------------------
# Spec and rendering
# --------------------------------------------------------------------------------------

@dataclass(frozen=True)
class AuditSpec:
    """Everything the Lean script is parameterised by."""
    #: Modules to ``import`` so the targets are in the environment.
    imports: tuple[str, ...]
    #: Fully qualified names of the theorems (or definitions) whose closure is audited.
    targets: tuple[str, ...]
    library_roots: tuple[str, ...] = DEFAULT_LIBRARY_ROOTS
    #: Lower-cased substrings searched in every closure constant and module name.
    scan_patterns: tuple[str, ...] = ()
    absent_constants: tuple[str, ...] = DEFAULT_ABSENT_CONSTANTS
    #: Module-name prefixes (e.g. ``CN1NegControls``) that must be absent from the closure.
    absent_module_prefixes: tuple[str, ...] = ()
    allowed_axioms: tuple[str, ...] = CLEAN_AXIOMS
    include_recursors: bool = True
    #: Where the script writes the full ``module<TAB>constant`` listing; None = nowhere.
    closure_out: str | None = None

    def __post_init__(self):
        if not self.imports:
            raise ValueError("AuditSpec.imports is empty: nothing would be in the environment")
        if not self.targets:
            raise ValueError("AuditSpec.targets is empty: nothing to audit")
        for name in (*self.imports, *self.targets, *self.library_roots, *self.absent_constants,
                     *self.absent_module_prefixes, *self.allowed_axioms):
            if not name or not name.strip():
                raise ValueError("empty Lean name in AuditSpec")
        for pat in self.scan_patterns:
            if not pat.strip():
                raise ValueError("empty scan pattern in AuditSpec")
        object.__setattr__(self, "scan_patterns", tuple(p.lower() for p in self.scan_patterns))


def lean_name_literal(name: str) -> str:
    """A backtick ``Name`` literal for a dotted Lean name, guillemet-quoting any component
    that is not a plain identifier (``\\`Foo.«bar baz».qux``).  Single backtick: the name
    need not exist at elaboration time, so a missing target is REPORTED, not a Lean error."""
    parts = name.split(".")
    if any(p == "" for p in parts):
        raise ValueError(f"malformed Lean name {name!r}")
    out = []
    for p in parts:
        if _IDENT_COMPONENT.match(p) and not p[0].isdigit():
            out.append(p)
        else:
            if "»" in p:
                raise ValueError(f"cannot quote Lean name component {p!r}")
            out.append(f"«{p}»")
    return "`" + ".".join(out)


def lean_string_literal(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def _name_list(names: Iterable[str]) -> str:
    items = [lean_name_literal(n) for n in names]
    return "[" + ", ".join(items) + "]"


def _string_list(strings: Iterable[str]) -> str:
    return "[" + ", ".join(lean_string_literal(s) for s in strings) + "]"


# The metaprogram.  Placeholders are __UPPER__ tokens replaced by `render_audit_script`;
# nothing else in the text is substituted, so braces and backslashes are safe.  It uses only
# API present from Lean v4.32.0 through v4.35.0 (checked against the toolchain sources:
# Expr.getUsedConstants, ConstantInfo.getUsedConstantsAsSet, collectAxioms,
# Environment.header.moduleNames, getModuleIdxFor?, Std.HashMap, NameSet).
_TEMPLATE = """\
__IMPORTS__
import Lean

/-!
Telperion closure audit (generated by `telperion.closure_audit`; do not edit by hand).

Walks the transitive constant closure of the target constants through types and values,
reports a census by root module, lists every non-library constant, scans names, checks
absences and axioms.  Lines starting with `@@` are the machine-readable protocol; the rest is
for a reader.  See docs/CLOSURE_AUDIT_MANIFEST_DESIGN_2026-10-22.md for what this does and
does not guarantee.
-/

open Lean Meta

namespace TelperionClosureAudit

def targets : List Name := __TARGETS__
def libraryRoots : List Name := __LIBRARY_ROOTS__
def scanPatterns : List String := __SCAN_PATTERNS__
def absentConstants : List Name := __ABSENT_CONSTANTS__
def absentModulePrefixes : List Name := __ABSENT_MODULE_PREFIXES__
def allowedAxioms : List Name := __ALLOWED_AXIOMS__
def includeRecursors : Bool := __INCLUDE_RECURSORS__
def closureOut : Option String := __CLOSURE_OUT__

def rootOf (n : Name) : Name :=
  match n.components with
  | r :: _ => r
  | [] => Name.anonymous

def isPrefixName (p n : Name) : Bool := p.components.isPrefixOf n.components

def matchesScan (s : String) : Bool :=
  let l := s.toLower
  scanPatterns.any (fun w => (l.splitOn w).length > 1)

def kindOf : ConstantInfo -> String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- The closure walk.  `includeRecursors = true` is Telperion's walk: an inductive brings its
constructors AND its `.rec`.  `false` reproduces `ConstantInfo.getUsedConstantsAsSet`
(type + value + constructors; a recursor contributes `all`), the independent reviewer's walk. -/
def closureOf (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := roots.toArray
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let cs : Array Name :=
        if includeRecursors then
          let base := ci.type.getUsedConstants
          match ci with
          | .thmInfo v => base ++ v.value.getUsedConstants
          | .defnInfo v => base ++ v.value.getUsedConstants
          | .opaqueInfo v => base ++ v.value.getUsedConstants
          | .inductInfo ii => base ++ ii.ctors.toArray ++ #[Name.mkStr n "rec"]
          | _ => base
        else
          ci.getUsedConstantsAsSet.toArray
      for c in cs do
        if !visited.contains c then stack := stack.push c
  return visited

def emit (key : String) (fields : List String) : IO Unit :=
  IO.println ("@@" ++ key ++ String.join (fields.map (fun f => "\\t" ++ f)))

end TelperionClosureAudit

open TelperionClosureAudit in
#eval show MetaM Unit from do
  let env <- getEnv
  emit "protocol" ["__PROTOCOL_VERSION__"]
  emit "lean_version" [Lean.versionString]
  emit "include_recursors" [toString includeRecursors]
  let mut failures : Array String := #[]
  -- targets: existence, kind, statement
  let mut found : List Name := []
  for t in targets do
    match env.find? t with
    | none =>
      emit "target" [toString t, "missing", ""]
      failures := failures.push s!"target {t} not found"
    | some ci =>
      let ty <- ppExpr ci.type
      let s := (toString ty).replace "\\n" " "
      emit "target" [toString t, kindOf ci, s]
      found := found ++ [t]
  let visited := closureOf env found
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => `_current_file
  let mut perRoot : Std.HashMap Name Nat := {}
  let mut nonLib : Std.HashMap Name (Array Name) := {}
  let mut closureMods : NameSet := {}
  let mut hits : Array (Name × Name) := #[]
  let mut allLines : Array String := #[]
  let mut absentModCount : Std.HashMap Name Nat := {}
  for p in absentModulePrefixes do absentModCount := absentModCount.insert p 0
  for n in visited.toList do
    let md := modOf n
    let r := rootOf md
    allLines := allLines.push s!"{md}\\t{n}"
    perRoot := perRoot.insert r (perRoot.getD r 0 + 1)
    closureMods := closureMods.insert md
    if !(libraryRoots.contains r) then
      nonLib := nonLib.insert md ((nonLib.getD md #[]).push n)
    if matchesScan (toString n ++ " " ++ toString md) then hits := hits.push (md, n)
    for p in absentModulePrefixes do
      if isPrefixName p md then absentModCount := absentModCount.insert p (absentModCount.getD p 0 + 1)
  emit "closure_size" [toString visited.size]
  IO.println s!"closure of {targets}: {visited.size} constants"
  IO.println "-- constants per root module --"
  for (r, k) in perRoot.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    emit "per_root" [toString r, toString k]
    IO.println s!"  {r}: {k}"
  IO.println "-- EVERY constant outside the library roots, by module --"
  for (md, cs) in nonLib.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    emit "nonlib_module" [toString md, toString cs.size]
    IO.println s!"[{md}] ({cs.size})"
    for c in cs.qsort (fun a b => a.toString < b.toString) do
      emit "nonlib_const" [toString md, toString c]
      IO.println s!"    {c}"
  IO.println s!"-- name scan for {scanPatterns} --"
  for (md, n) in hits.qsort (fun a b => a.2.toString < b.2.toString) do
    emit "scan_hit" [toString md, toString n]
    IO.println s!"  HIT {md} :: {n}"
  emit "scan_hits" [toString hits.size]
  -- imported MODULES (whole environment) whose names match, and the environment census
  let mut envRoots : Std.HashMap Name Nat := {}
  let mut unusedNonLib : Array Name := #[]
  for md in env.header.moduleNames do
    let r := rootOf md
    envRoots := envRoots.insert r (envRoots.getD r 0 + 1)
    if matchesScan (toString md) then
      emit "scan_module_hit" [toString md]
      IO.println s!"  MODULE HIT {md}"
    if !(libraryRoots.contains r) && !(closureMods.contains md) then unusedNonLib := unusedNonLib.push md
  for (r, k) in envRoots.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    emit "env_modules_per_root" [toString r, toString k]
  for md in unusedNonLib.qsort (fun a b => a.toString < b.toString) do
    emit "unused_nonlib_module" [toString md]
  -- absences
  for c in absentConstants do
    let present := visited.contains c
    emit "absent_const" [toString c, toString present]
    if present then failures := failures.push s!"forbidden constant {c} is in the closure"
  for p in absentModulePrefixes do
    let k := absentModCount.getD p 0
    emit "absent_module" [toString p, toString k]
    if k > 0 then failures := failures.push s!"{k} constant(s) from forbidden module prefix {p} in the closure"
  -- axioms per target
  for t in found do
    let axs <- collectAxioms t
    let axs := axs.qsort (fun a b => a.toString < b.toString)
    let bad := axs.filter (fun a => !(allowedAxioms.contains a))
    emit "axioms" ([toString t] ++ (axs.map toString).toList)
    IO.println s!"'{t}' depends on axioms: {axs}"
    if !bad.isEmpty then failures := failures.push s!"{t} uses non-allowed axioms {bad}"
  match closureOut with
  | some path =>
    IO.FS.writeFile path (String.intercalate "\\n" (allLines.qsort (· < ·)).toList ++ "\\n")
    emit "closure_written" [path]
  | none => pure ()
  for f in failures do emit "failure" [f]
  emit "verdict" [if failures.isEmpty then "PASS" else "FAIL"]
"""


def render_audit_script(spec: AuditSpec) -> str:
    """The Lean source of the audit, with the spec baked in."""
    imports = "\n".join(f"import {m}" for m in spec.imports)
    out = _TEMPLATE
    repl = {
        "__IMPORTS__": imports,
        "__TARGETS__": _name_list(spec.targets),
        "__LIBRARY_ROOTS__": _name_list(spec.library_roots),
        "__SCAN_PATTERNS__": _string_list(spec.scan_patterns),
        "__ABSENT_CONSTANTS__": _name_list(spec.absent_constants),
        "__ABSENT_MODULE_PREFIXES__": _name_list(spec.absent_module_prefixes),
        "__ALLOWED_AXIOMS__": _name_list(spec.allowed_axioms),
        "__INCLUDE_RECURSORS__": "true" if spec.include_recursors else "false",
        "__CLOSURE_OUT__": ("some " + lean_string_literal(spec.closure_out)
                            if spec.closure_out else "none"),
        "__PROTOCOL_VERSION__": PROTOCOL_VERSION,
    }
    for k, v in repl.items():
        out = out.replace(k, v)
    return out


# --------------------------------------------------------------------------------------
# Output parsing
# --------------------------------------------------------------------------------------

@dataclass
class TargetInfo:
    name: str
    kind: str            # "theorem" | "definition" | ... | "missing"
    statement: str
    axioms: list[str] = field(default_factory=list)


@dataclass
class AuditResult:
    protocol: str = ""
    lean_version: str = ""
    include_recursors: bool = True
    targets: list[TargetInfo] = field(default_factory=list)
    closure_size: int = 0
    per_root: dict[str, int] = field(default_factory=dict)
    nonlib_modules: dict[str, list[str]] = field(default_factory=dict)
    scan_hits: list[dict[str, str]] = field(default_factory=list)
    scan_module_hits: list[str] = field(default_factory=list)
    env_modules_per_root: dict[str, int] = field(default_factory=dict)
    unused_nonlib_modules: list[str] = field(default_factory=list)
    absent_constants: dict[str, bool] = field(default_factory=dict)   # name -> present?
    absent_modules: dict[str, int] = field(default_factory=dict)      # prefix -> count
    closure_written: str | None = None
    failures: list[str] = field(default_factory=list)
    verdict: str = ""            # "PASS" | "FAIL" | "" (no verdict line: the script died)
    lean_exit_code: int | None = None
    raw_tail: str = ""           # last lines of the Lean output, for a reader

    @property
    def ok(self) -> bool:
        return self.verdict == "PASS" and self.lean_exit_code in (0, None)

    def to_dict(self) -> dict:
        d = asdict(self)
        d["ok"] = self.ok
        return d

    def to_json(self, **kw) -> str:
        return json.dumps(self.to_dict(), indent=2, sort_keys=False, **kw)

    def render(self) -> str:
        """A short human summary (the JSON is the record)."""
        lines = [f"closure audit: {self.verdict or 'NO VERDICT'}"
                 f" (lean {self.lean_version or '?'}, recursors={'on' if self.include_recursors else 'off'})"]
        for t in self.targets:
            lines.append(f"  target {t.name}: {t.kind}; axioms {t.axioms}")
        lines.append(f"  closure: {self.closure_size} constants; per root "
                     + ", ".join(f"{k}={v}" for k, v in sorted(self.per_root.items())))
        n_nonlib = sum(len(v) for v in self.nonlib_modules.values())
        lines.append(f"  non-library constants: {n_nonlib} in {len(self.nonlib_modules)} module(s)")
        lines.append(f"  scan hits: {len(self.scan_hits)} constant(s), {len(self.scan_module_hits)} module(s)")
        for name, present in self.absent_constants.items():
            lines.append(f"  {name} in closure: {str(present).lower()} (must be false)")
        for pfx, k in self.absent_modules.items():
            lines.append(f"  {pfx}.* constants in closure: {k} (must be 0)")
        if self.unused_nonlib_modules:
            lines.append(f"  imported non-library modules not in the closure: "
                         f"{len(self.unused_nonlib_modules)}")
        for f in self.failures:
            lines.append(f"  FAIL: {f}")
        return "\n".join(lines)


def parse_audit_output(text: str) -> AuditResult:
    """Read the ``@@`` protocol lines out of the Lean output.  Everything else (warnings,
    the human listing) is ignored; the last 20 lines are kept in ``raw_tail``."""
    res = AuditResult()
    by_name: dict[str, TargetInfo] = {}
    for raw in text.splitlines():
        if not raw.startswith(PROTOCOL_PREFIX):
            continue
        parts = raw[len(PROTOCOL_PREFIX):].split("\t")
        key, args = parts[0], parts[1:]
        try:
            if key == "protocol":
                res.protocol = args[0]
            elif key == "lean_version":
                res.lean_version = args[0]
            elif key == "include_recursors":
                res.include_recursors = args[0] == "true"
            elif key == "target":
                ti = TargetInfo(name=args[0], kind=args[1], statement=args[2] if len(args) > 2 else "")
                res.targets.append(ti)
                by_name[ti.name] = ti
            elif key == "closure_size":
                res.closure_size = int(args[0])
            elif key == "per_root":
                res.per_root[args[0]] = int(args[1])
            elif key == "nonlib_module":
                res.nonlib_modules.setdefault(args[0], [])
            elif key == "nonlib_const":
                res.nonlib_modules.setdefault(args[0], []).append(args[1])
            elif key == "scan_hit":
                res.scan_hits.append({"module": args[0], "constant": args[1]})
            elif key == "scan_hits":
                pass  # the count is len(scan_hits)
            elif key == "scan_module_hit":
                res.scan_module_hits.append(args[0])
            elif key == "env_modules_per_root":
                res.env_modules_per_root[args[0]] = int(args[1])
            elif key == "unused_nonlib_module":
                res.unused_nonlib_modules.append(args[0])
            elif key == "absent_const":
                res.absent_constants[args[0]] = args[1] == "true"
            elif key == "absent_module":
                res.absent_modules[args[0]] = int(args[1])
            elif key == "axioms":
                if args[0] in by_name:
                    by_name[args[0]].axioms = list(args[1:])
            elif key == "closure_written":
                res.closure_written = args[0]
            elif key == "failure":
                res.failures.append(args[0])
            elif key == "verdict":
                res.verdict = args[0]
            # unknown keys from a newer script are ignored, not fatal
        except (IndexError, ValueError) as exc:
            raise ClosureAuditError(f"malformed protocol line {raw!r}: {exc}") from exc
    res.raw_tail = "\n".join(text.splitlines()[-20:])
    return res


# --------------------------------------------------------------------------------------
# Running
# --------------------------------------------------------------------------------------

def _lean_env() -> dict[str, str]:
    env = os.environ.copy()
    elan = str(Path.home() / ".elan" / "bin")
    if elan not in env.get("PATH", ""):
        env["PATH"] = elan + os.pathsep + env.get("PATH", "")
    return env


def run_closure_audit(
    spec: AuditSpec,
    project_dir: str | Path,
    *,
    wrapper: str | Sequence[str] | None = None,
    timeout: int = 3600,
    script_path: str | Path | None = None,
    keep_script: bool = False,
) -> AuditResult:
    """Render the audit, run ``lake env lean <script>`` in ``project_dir`` (which must be a
    built Lake project whose environment provides ``spec.imports``), and parse the result.

    ``wrapper`` is a command prefix (a string, split like a shell would, or a sequence)
    placed before ``lake``: a machine-wide build lock, ``nice``, a sandbox.  The script is
    written to ``script_path`` (default: a temp file inside the project, removed afterwards
    unless ``keep_script``).  A non-zero Lean exit is recorded, not raised; a missing
    ``lake`` raises :class:`ClosureAuditError`.
    """
    project_dir = Path(project_dir)
    if not project_dir.is_dir():
        raise ClosureAuditError(f"project directory {project_dir} does not exist")
    text = render_audit_script(spec)
    if script_path is None:
        fd, tmp = tempfile.mkstemp(prefix="telperion_closure_audit_", suffix=".lean",
                                   dir=str(project_dir))
        os.close(fd)
        script = Path(tmp)
        remove = not keep_script
    else:
        # absolute: `lake env lean` runs with cwd = project_dir, so a path relative to the
        # caller's cwd would be looked up in the wrong place (seen on the example: "no such
        # file or directory" for examples/closure_audit/lean/Audit.lean)
        script = Path(script_path).resolve()
        script.parent.mkdir(parents=True, exist_ok=True)
        remove = False
    script.write_text(text, encoding="utf-8")
    if isinstance(wrapper, str):
        prefix = shlex.split(wrapper)
    else:
        prefix = list(wrapper or [])
    cmd = [*prefix, "lake", "env", "lean", str(script)]
    try:
        proc = subprocess.run(cmd, cwd=str(project_dir), capture_output=True, text=True,
                              env=_lean_env(), timeout=timeout)
    except FileNotFoundError as exc:
        raise ClosureAuditError(f"could not run {cmd[0]!r}: {exc}") from exc
    except subprocess.TimeoutExpired as exc:
        raise ClosureAuditError(f"closure audit timed out after {timeout}s") from exc
    finally:
        if remove:
            try:
                script.unlink()
            except OSError:
                pass
    out = (proc.stdout or "") + (proc.stderr or "")
    res = parse_audit_output(out)
    res.lean_exit_code = proc.returncode
    if proc.returncode != 0 and not res.verdict:
        res.failures.append(f"lean exited {proc.returncode} before a verdict")
    return res
