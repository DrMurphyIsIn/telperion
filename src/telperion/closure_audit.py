"""Dependency-closure audit of a Lean theorem: a kernel-level census, not a text scan.

:mod:`telperion.audit` reads Lean SOURCE (``sorry``, a smuggled ``axiom``, a reflexive
statement).  A green build still says nothing about what the proof TERM of a theorem
actually reaches: which modules it pulls in, whether a negative-control module leaked into
the real closure, whether a constant named after the argument the proof claims to avoid is
in there, which axioms the kernel accepted.  This module renders a small Lean metaprogram
that answers those questions from the ELABORATED ENVIRONMENT and parses its output into a
JSON-friendly :class:`AuditResult`.

Two ways to run it
------------------
* REPLAYED (the default, step 5 Task 7): :func:`run_closure_audit_replayed` renders the walk
  as a ``TelperionReplay.callback`` (:func:`render_audit_callback`) and runs it through
  :mod:`telperion.checks.lean_replay`, like the negation probe and the fingerprint: the Lean
  process imports trusted modules only, from the pinned env checked against its trusted
  manifest; the submission's oleans are read as data from private copies and kernel-replayed;
  an untrusted axiom is refused by the replay itself (Ruling 10, an audit FAIL naming it); the
  result carries ``olean_sha256``/``olean_closure``, the digest of exactly the bytes replayed,
  and ``isolated: true``; no ``lake`` runs.  The submission's initializers, elaborators and
  lakefile never run in the audit process, so they cannot forge its verdict.  Every name and
  string of the spec reaches the callback as string DATA (components fed to ``Name.mkStr``),
  never as syntax.
* LEGACY (``--legacy-import``): :func:`run_closure_audit` renders a script that IMPORTS the
  submission (:func:`render_audit_script`) and runs it with ``lake env lean`` inside the built
  Lake project.  NOT ISOLATED: see "What it does NOT guarantee".  ``isolated`` is false, and
  ``mission checks-record`` refuses this output for nodes created on or after the cutoff.

What the replayed run sees differently: replay transfers constants only, so a replayed
constant has no module index; its module comes from the replay's own closure (the module whose
.olean declared it), and it is never counted as library, whatever its module is named.  The
environment census is the trusted imports' modules plus the replayed ones.  The target
STATEMENT strings are pretty-printed without the untrusted modules' extensions, so a statement
that uses the submission's own notation or unexpanders prints in plain form; they are for a
reader, and nothing compares them.  Per-target ``collectAxioms`` re-walks a replayed constant
instead of reading a cached record, so the consistency cross-check compares two walks.  When an
untrusted module declares a theorem identical (name, type, universe parameters) to a trusted
one already present, replay keeps the trusted constant, so the audit walks the TRUSTED proof
and counts it as library: sound for the statement, but the absence checks then describe that
proof, not the submission's.  A bare-digit name component in the spec is a numeric one (the
``0`` of ``_private.Foo.0.Foo.bar``), as ``Name.toString`` prints it; see `lean_name_data`.

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
* every ``axiomInfo`` the walk reached, against an allowed list (``propext``,
  ``Classical.choice``, ``Quot.sound`` by default) -- the independent axiom check, since it
  follows the values the environment holds;
* ``collectAxioms`` per target against the same list -- the machine-checked form of
  ``#print axioms`` -- and a cross-check that the union of those records equals the
  closure's axioms.  For an imported declaration ``collectAxioms`` reads the axioms its module
  recorded at compile time (``exportedAxiomsExt`` through ``getModuleIdxFor?``), not a
  re-walk, so a module that RE-DECLARES a target's name with another proof makes the two
  disagree: the audit then fails with "inconsistent environment" (an independent reviewer
  demonstrated exactly this with a ``native_decide`` control re-declaring the CN-1 theorem);
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
  axiom outside the allowed set: a generated ``<thm>._native.native_decide.ax_*`` on v4.32.0
  and v4.34.1, ``Lean.ofReduceBool`` on older toolchains) but ``implemented_by`` /
  ``extern`` bodies and the compiled code they run are not inspected.
* The per-target axiom list is the compiler's cached record from the ``.olean``; the
  closure-based list is the independent one, and the two are required to agree.
* The LEGACY path is UNSANDBOXED and NOT ISOLATED.  ``lake env lean`` runs inside the
  audited project with the caller's privileges, the project's lakefile runs, imported
  modules' initializers run at import time, and their ``command_elab``/``tactic`` overrides
  elaborate the audit's own commands: a module that replaces ``#eval`` can read the nonce out
  of the script's definitions and print a forged PASS (tests/test_closure_audit_replay.py
  demonstrates it).  The per-run nonce on every protocol line and the one-protocol-line /
  one-verdict-line / PASS-means-no-failures check stop only a STRAY line from being read as
  ours.  The replayed path closes this; like the other checks it is still not a sandbox (the
  submission's BUILD runs its code, and the .olean reader trusts its bytes; see
  checks/lean_replay.py).
* A negative-control module must NEVER re-declare a target's name.  Lean imports two
  modules declaring the same constant without complaint; ``env.find?`` then returns one of
  the proofs and ``collectAxioms`` the other module's cached record.  The consistency check
  catches this, but only as a failure: it cannot tell you which proof you meant.

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
import secrets
import shlex
import subprocess
import tempfile
from dataclasses import asdict, dataclass, field, replace
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
/-- Per-run token the runner generated; every protocol line carries it, so a line printed by
anything other than this script (an import-time initializer, say) is not mistaken for ours. -/
def nonce : String := __NONCE__

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
  IO.println ("@@" ++ nonce ++ "\\t" ++ key ++ String.join (fields.map (fun f => "\\t" ++ f)))

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
  -- axioms IN THE CLOSURE: every axiomInfo the walk reached.  This is the independent check:
  -- it follows the values the environment actually holds, not a cached record.
  let mut axiomAcc : Array Name := #[]
  for n in visited.toList do
    match env.find? n with
    | some (.axiomInfo _) => axiomAcc := axiomAcc.push n
    | _ => pure ()
  let closureAxioms := axiomAcc.qsort (fun a b => a.toString < b.toString)
  emit "closure_axioms" (closureAxioms.map toString).toList
  IO.println s!"axioms in the closure: {closureAxioms}"
  let badClosure := closureAxioms.filter (fun a => !(allowedAxioms.contains a))
  if !badClosure.isEmpty then
    failures := failures.push s!"closure contains non-allowed axioms {badClosure}"
  -- axioms per target, as `#print axioms` reports them.  For an IMPORTED declaration
  -- `collectAxioms` reads the axioms its module recorded at compile time (exportedAxiomsExt via
  -- getModuleIdxFor?), so this is the compiler's cached record, not a re-walk; a module that
  -- re-declares a target's name under another proof makes it disagree with the closure above.
  let mut reported : NameSet := {}
  for t in found do
    let axs <- collectAxioms t
    let axs := axs.qsort (fun a b => a.toString < b.toString)
    for a in axs do reported := reported.insert a
    let bad := axs.filter (fun a => !(allowedAxioms.contains a))
    emit "axioms" ([toString t] ++ (axs.map toString).toList)
    IO.println s!"'{t}' depends on axioms: {axs}"
    if !bad.isEmpty then failures := failures.push s!"{t} uses non-allowed axioms {bad}"
  -- cross-check: the union of the per-target records must be exactly the closure's axioms
  let reportedArr := reported.toArray.qsort (fun a b => a.toString < b.toString)
  let consistent := reportedArr == closureAxioms
  emit "axioms_consistent" [toString consistent]
  if !consistent then
    failures := failures.push s!"inconsistent environment (duplicate declaration or stale .olean): collectAxioms over the targets gives {reportedArr}, the closure contains {closureAxioms}"
  match closureOut with
  | some path =>
    IO.FS.writeFile path (String.intercalate "\\n" (allLines.qsort (· < ·)).toList ++ "\\n")
    emit "closure_written" [path]
  | none => pure ()
  for f in failures do emit "failure" [f]
  emit "verdict" [if failures.isEmpty then "PASS" else "FAIL"]
"""


#: The nonce a rendering gets when none is supplied.  A script rendered with it is for
#: READING (the committed example scripts); `run_closure_audit` always renders with a fresh
#: random nonce and parses only lines that carry it.
PLACEHOLDER_NONCE = "EXAMPLE"


def render_audit_script(spec: AuditSpec, *, nonce: str = PLACEHOLDER_NONCE) -> str:
    """The Lean source of the audit, with the spec and the run nonce baked in."""
    if not re.fullmatch(r"[A-Za-z0-9]+", nonce):
        raise ValueError("nonce must be alphanumeric")
    imports = "\n".join(f"import {m}" for m in spec.imports)
    out = _TEMPLATE
    repl = {
        "__IMPORTS__": imports,
        "__NONCE__": lean_string_literal(nonce),
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


# The same walk as a replay callback (checks/lean_replay.py, `callback_takes_closure`).  It is elaborated against the
# trusted imports BEFORE the replay, so it can name an untrusted constant only as data.  Placeholders are __UPPER__
# tokens replaced in ONE pass by `render_audit_callback` (a value is never rescanned), and every value is a Lean string
# literal or a list of them: names travel as their components, joined by `Name.mkStr` at run time.  The comments avoid
# backquotes and the strings avoid nesting, so a test can check that nothing outside a string literal came from the
# spec.
_CALLBACK = r"""
/-!
Telperion closure audit as a kernel-replay callback (generated by telperion.closure_audit.render_audit_callback; do not
edit by hand).  The walk of the import-based audit script, run on the replayed environment, so the submission is not
loaded by an import.  Every protocol line goes out through TelperionReplay.line and carries the audit nonce.
-/

namespace TelperionClosureAudit
open Lean Meta

/-- One name component as the renderer passes it, as data: a string, or a number (a bare-digit component, which is
how Name.toString prints a numeric one, such as the 0 of a private name). -/
inductive NameComp where
  | str (s : String)
  | num (n : Nat)

/-- A name from its components, never from syntax. -/
def mkName (cs : List NameComp) : Name :=
  cs.foldl (fun n c => match c with
    | .str s => Name.mkStr n s
    | .num k => Name.mkNum n k) Name.anonymous

def targets : List Name := (__TARGETS__ : List (List NameComp)).map mkName
def libraryRoots : List Name := (__LIBRARY_ROOTS__ : List (List NameComp)).map mkName
def scanPatterns : List String := __SCAN_PATTERNS__
def absentConstants : List Name := (__ABSENT_CONSTANTS__ : List (List NameComp)).map mkName
def absentModulePrefixes : List Name := (__ABSENT_MODULE_PREFIXES__ : List (List NameComp)).map mkName
def allowedAxioms : List Name := (__ALLOWED_AXIOMS__ : List (List NameComp)).map mkName
def includeRecursors : Bool := __INCLUDE_RECURSORS__
def closureOut : Option String := __CLOSURE_OUT__
def nonce : String := __NONCE__
def protocolVersion : String := __PROTOCOL_VERSION__
/-- The module the legacy script reports for a constant of its own file; no replayed constant should need it. -/
def currentFile : Name := Name.mkSimple "_current_file"

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

/-- The closure walk of the import-based script, unchanged: with includeRecursors an inductive brings its
constructors AND its recursor; without, ConstantInfo.getUsedConstantsAsSet (the independent reviewer's walk). -/
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
  TelperionReplay.line ("@@" ++ nonce ++ "\t" ++ key ++
    String.join (fields.map (fun f => "\t" ++ f.replace "\t" " ")))

end TelperionClosureAudit

open TelperionClosureAudit in
def TelperionReplay.callback (c : TelperionReplay.Closure) : TermElabM Unit := do
  let env <- getEnv
  emit "protocol" [protocolVersion]
  emit "lean_version" [Lean.versionString]
  emit "include_recursors" [toString includeRecursors]
  let mut failures : Array String := #[]
  -- targets: existence, kind, statement (pretty-printed for a reader only)
  let mut found : List Name := []
  for t in targets do
    match env.find? t with
    | none =>
      emit "target" [toString t, "missing", ""]
      failures := failures.push s!"target {t} not found"
    | some ci =>
      let ty <- ppExpr ci.type
      emit "target" [toString t, kindOf ci, toString ty]
      found := found ++ [t]
  let visited := closureOf env found
  -- A trusted constant's module is its import's; a replayed constant has no module index, so its module is the
  -- untrusted one whose .olean declared it, as the replay read it.  Only a trusted constant can be library.
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => c.moduleOf.getD n currentFile
  let isLib (n md : Name) : Bool := (env.getModuleIdxFor? n).isSome && libraryRoots.contains (rootOf md)
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
    allLines := allLines.push s!"{md}\t{n}"
    perRoot := perRoot.insert r (perRoot.getD r 0 + 1)
    closureMods := closureMods.insert md
    if !(isLib n md) then
      nonLib := nonLib.insert md ((nonLib.getD md #[]).push n)
    if matchesScan (toString n ++ " " ++ toString md) then hits := hits.push (md, n)
    for p in absentModulePrefixes do
      if isPrefixName p md then absentModCount := absentModCount.insert p (absentModCount.getD p 0 + 1)
  emit "closure_size" [toString visited.size]
  for (r, k) in perRoot.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    emit "per_root" [toString r, toString k]
  for (md, cs) in nonLib.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    emit "nonlib_module" [toString md, toString cs.size]
    for k in cs.qsort (fun a b => a.toString < b.toString) do
      emit "nonlib_const" [toString md, toString k]
  for (md, n) in hits.qsort (fun a b => a.2.toString < b.2.toString) do
    emit "scan_hit" [toString md, toString n]
  emit "scan_hits" [toString hits.size]
  -- the environment's modules: the trusted imports (the header) and the replayed untrusted ones
  let mut envRoots : Std.HashMap Name Nat := {}
  let mut unusedNonLib : Array Name := #[]
  for md in env.header.moduleNames do
    let r := rootOf md
    envRoots := envRoots.insert r (envRoots.getD r 0 + 1)
    if matchesScan (toString md) then emit "scan_module_hit" [toString md]
    if !(libraryRoots.contains r) && !(closureMods.contains md) then unusedNonLib := unusedNonLib.push md
  for md in c.modules do
    let r := rootOf md
    envRoots := envRoots.insert r (envRoots.getD r 0 + 1)
    if matchesScan (toString md) then emit "scan_module_hit" [toString md]
    if !(closureMods.contains md) then unusedNonLib := unusedNonLib.push md
  for (r, k) in envRoots.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    emit "env_modules_per_root" [toString r, toString k]
  for md in unusedNonLib.qsort (fun a b => a.toString < b.toString) do
    emit "unused_nonlib_module" [toString md]
  -- absences
  for k in absentConstants do
    let present := visited.contains k
    emit "absent_const" [toString k, toString present]
    if present then failures := failures.push s!"forbidden constant {k} is in the closure"
  for p in absentModulePrefixes do
    let k := absentModCount.getD p 0
    emit "absent_module" [toString p, toString k]
    if k > 0 then failures := failures.push s!"{k} constant(s) from forbidden module prefix {p} in the closure"
  -- axioms IN THE CLOSURE: every axiomInfo the walk reached
  let mut axiomAcc : Array Name := #[]
  for n in visited.toList do
    match env.find? n with
    | some (.axiomInfo _) => axiomAcc := axiomAcc.push n
    | _ => pure ()
  let closureAxioms := axiomAcc.qsort (fun a b => a.toString < b.toString)
  emit "closure_axioms" (closureAxioms.map toString).toList
  let badClosure := closureAxioms.filter (fun a => !(allowedAxioms.contains a))
  if !badClosure.isEmpty then
    failures := failures.push s!"closure contains non-allowed axioms {badClosure}"
  -- axioms per target, as the print-axioms command reports them; a replayed target is re-walked
  let mut reported : NameSet := {}
  for t in found do
    let axs <- collectAxioms t
    let axs := axs.qsort (fun a b => a.toString < b.toString)
    for a in axs do reported := reported.insert a
    let bad := axs.filter (fun a => !(allowedAxioms.contains a))
    emit "axioms" ([toString t] ++ (axs.map toString).toList)
    if !bad.isEmpty then failures := failures.push s!"{t} uses non-allowed axioms {bad}"
  let reportedArr := reported.toArray.qsort (fun a b => a.toString < b.toString)
  let consistent := reportedArr == closureAxioms
  emit "axioms_consistent" [toString consistent]
  if !consistent then
    failures := failures.push s!"inconsistent environment (duplicate declaration or stale .olean): collectAxioms over the targets gives {reportedArr}, the closure contains {closureAxioms}"
  match closureOut with
  | some path =>
    IO.FS.writeFile path (String.intercalate "\n" (allLines.qsort (· < ·)).toList ++ "\n")
    emit "closure_written" [path]
  | none => pure ()
  for f in failures do emit "failure" [f]
  emit "verdict" [if failures.isEmpty then "PASS" else "FAIL"]
"""


def lean_name_data(name: str) -> str:
    """Lean source for the components of the dotted name `name`, as DATA the callback joins into a ``Name``: a list
    of ``.str "<literal>"`` and ``.num <digits>`` components.

    A bare-digit component is a NUMERIC component (``Name.mkNum``). That is how Lean's ``Name.toString`` prints one,
    and how the audit's own output names one: the ``0`` of a private constant ``_private.Foo.0.Foo.bar`` is a
    ``Name.num``, and a STRING component ``"0"`` would print as ``«0»``. As a string it could never match, so an
    absence check on such a name would pass vacuously. A digit string with a leading zero (``007``) is printed by
    ``Name.toString`` for neither kind, so it is refused rather than guessed. Any other character may appear in a
    string component; only an empty component is refused."""
    from .checks.negation_probe import _lean_string
    parts = name.split(".")
    if any(p == "" for p in parts):
        raise ValueError(f"malformed Lean name {name!r}")
    comps = []
    for p in parts:
        if re.fullmatch(r"[0-9]+", p):
            if p != str(int(p)):
                raise ValueError(f"Lean name {name!r}: component {p!r} has a leading zero, so it is neither a "
                                 "numeric component nor a string one as Lean prints names; refusing")
            comps.append(f".num {int(p)}")
        else:
            comps.append(".str " + _lean_string(p))
    return "[" + ", ".join(comps) + "]"


def render_audit_callback(spec: AuditSpec, nonce: str) -> str:
    """The Lean source of the replay callback (``TelperionReplay.callback : TelperionReplay.Closure → TermElabM
    Unit``) that runs the audit's walk on the replayed environment and prints the protocol lines, tagged with
    `nonce`.  `spec.imports` are not rendered: they are the replay's targets and trusted imports."""
    from .checks.negation_probe import _lean_string
    if not re.fullmatch(r"[A-Za-z0-9]+", nonce):
        raise ValueError("nonce must be alphanumeric")

    def names(ns: Iterable[str]) -> str:
        return "[" + ", ".join(lean_name_data(n) for n in ns) + "]"

    repl = {
        "__TARGETS__": names(spec.targets),
        "__LIBRARY_ROOTS__": names(spec.library_roots),
        "__SCAN_PATTERNS__": "[" + ", ".join(_lean_string(w) for w in spec.scan_patterns) + "]",
        "__ABSENT_CONSTANTS__": names(spec.absent_constants),
        "__ABSENT_MODULE_PREFIXES__": names(spec.absent_module_prefixes),
        "__ALLOWED_AXIOMS__": names(spec.allowed_axioms),
        "__INCLUDE_RECURSORS__": "true" if spec.include_recursors else "false",
        "__CLOSURE_OUT__": "some " + _lean_string(spec.closure_out) if spec.closure_out else "none",
        "__NONCE__": _lean_string(nonce),
        "__PROTOCOL_VERSION__": _lean_string(PROTOCOL_VERSION),
    }
    return re.sub(r"__[A-Z_]+__", lambda m: repl[m.group(0)], _CALLBACK)


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
    #: every axiomInfo the walk reached (the independent axiom check)
    closure_axioms: list[str] = field(default_factory=list)
    #: True iff the union of the per-target collectAxioms records equals closure_axioms
    axioms_consistent: bool | None = None
    nonce: str = ""
    closure_written: str | None = None
    failures: list[str] = field(default_factory=list)
    verdict: str = ""            # "PASS" | "FAIL" | "" (no verdict line: the script died)
    lean_exit_code: int | None = None
    raw_tail: str = ""           # last lines of the Lean output, for a reader
    #: True when the audit ran as a kernel-replay callback (`run_closure_audit_replayed`): the submission was never
    #: imported. False on the legacy import path (`run_closure_audit`), whose output the submission's code can forge.
    isolated: bool = False
    #: lean_replay.closure_digest of the replayed untrusted closure, and its sorted [module, part, sha256] list: the
    #: same binding the probe and the fingerprint report (None / [] when nothing was replayed, and on the legacy path).
    olean_sha256: str | None = None
    olean_closure: list = field(default_factory=list)

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
        if self.isolated:
            lines.append(f"  isolation: kernel replay, olean_sha256 {(self.olean_sha256 or 'none')[:16]}")
        else:
            lines.append("  isolation: NOT ISOLATED (the legacy path imported the submission)")
        for t in self.targets:
            lines.append(f"  target {t.name}: {t.kind}; axioms {t.axioms}")
        lines.append(f"  closure: {self.closure_size} constants; per root "
                     + ", ".join(f"{k}={v}" for k, v in sorted(self.per_root.items())))
        n_nonlib = sum(len(v) for v in self.nonlib_modules.values())
        lines.append(f"  non-library constants: {n_nonlib} in {len(self.nonlib_modules)} module(s)")
        lines.append(f"  scan hits: {len(self.scan_hits)} constant(s), {len(self.scan_module_hits)} module(s)")
        lines.append(f"  axioms in closure: {self.closure_axioms}; consistent with the per-target "
                     f"records: {self.axioms_consistent}")
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


def parse_audit_output(text: str, *, nonce: str = PLACEHOLDER_NONCE) -> AuditResult:
    """Read the ``@@<nonce>`` protocol lines out of the Lean output.  Everything else
    (warnings, the human listing, a line with another or no nonce) is ignored; the last 20
    lines are kept in ``raw_tail``.

    Integrity: exactly one ``protocol`` line and exactly one ``verdict`` line must be present,
    and a ``PASS`` verdict must come with no ``failure`` line.  Anything else makes the result
    a FAIL with an ``integrity`` failure recorded, because the audit runs UNSANDBOXED inside
    the audited project and an import-time initializer could print lines of its own.
    """
    res = AuditResult(nonce=nonce)
    by_name: dict[str, TargetInfo] = {}
    prefix = PROTOCOL_PREFIX + nonce + "\t"
    n_protocol = n_verdict = 0
    for raw in text.splitlines():
        if not raw.startswith(prefix):
            continue
        parts = raw[len(prefix):].split("\t")
        key, args = parts[0], parts[1:]
        try:
            if key == "protocol":
                n_protocol += 1
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
            elif key == "closure_axioms":
                res.closure_axioms = list(args)
            elif key == "axioms_consistent":
                res.axioms_consistent = args[0] == "true"
            elif key == "closure_written":
                res.closure_written = args[0]
            elif key == "failure":
                res.failures.append(args[0])
            elif key == "verdict":
                n_verdict += 1
                res.verdict = args[0]
            # unknown keys from a newer script are ignored, not fatal
        except (IndexError, ValueError) as exc:
            raise ClosureAuditError(f"malformed protocol line {raw!r}: {exc}") from exc
    res.raw_tail = "\n".join(text.splitlines()[-20:])
    if n_verdict:
        problems = []
        if n_protocol != 1:
            problems.append(f"{n_protocol} protocol lines (expected 1)")
        if n_verdict != 1:
            problems.append(f"{n_verdict} verdict lines (expected 1)")
        if res.verdict == "PASS" and res.failures:
            problems.append("verdict PASS with failure lines present")
        if res.verdict not in ("PASS", "FAIL"):
            problems.append(f"unknown verdict {res.verdict!r}")
        if problems:
            res.failures.append("integrity: " + "; ".join(problems))
            res.verdict = "FAIL"
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
    nonce = secrets.token_hex(16)
    text = render_audit_script(spec, nonce=nonce)
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
    res = parse_audit_output(out, nonce=nonce)
    res.lean_exit_code = proc.returncode
    if proc.returncode != 0 and not res.verdict:
        res.failures.append(f"lean exited {proc.returncode} before a verdict")
    return res


# --------------------------------------------------------------------------------------
# Running as a kernel-replay callback (step 5 Task 7)
# --------------------------------------------------------------------------------------

#: `run_closure_audit_replayed`'s memory_mb default: lean_replay's own (DEFAULT_MEMORY_MB), which this module cannot
#: import at load time (lean_replay imports this module).
_REPLAY_DEFAULT = object()


def replayed_audit_result(r, nonce: str) -> AuditResult:
    """The AuditResult of a replay run (a ``lean_replay.ReplayResult``) of `render_audit_callback`'s callback.

    OK: the callback's lines must ALL be this audit's protocol lines (``@@<nonce>``), the verdict line must be the
    last, and `parse_audit_output`'s integrity rules apply; anything else is an ``integrity`` FAIL. A malformed
    protocol line gives no verdict (never an exception). The result carries
    the replay's ``olean_sha256``/``olean_closure``. A refused replay is a FAIL: an untrusted axiom (Ruling 10: the
    replay refuses it before anything runs) is named, as is a kernel rejection or a re-declared constant. A module
    that is not built, or a replay that did not run (no trusted env or manifest, a Lean crash, a failed callback),
    gives no verdict. Every result is ``isolated``."""
    tail = "\n".join((r.output or "").splitlines()[-20:])
    if r.status == "OK":
        prefix = PROTOCOL_PREFIX + nonce + "\t"
        try:
            res = parse_audit_output("\n".join(r.lines), nonce=nonce)
        except ClosureAuditError as exc:
            res = AuditResult(nonce=nonce, isolated=True, raw_tail=tail)
            res.failures.append(f"the audit callback printed a malformed protocol line, so no verdict is read: {exc}")
            return res
        problems = []
        stray = [ln for ln in r.lines if not ln.startswith(prefix)]
        if stray:
            problems.append(f"{len(stray)} callback line(s) outside the audit protocol (first: {stray[0][:200]!r})")
        if res.verdict and not r.lines[-1].startswith(prefix + "verdict\t"):
            problems.append("the verdict line is not the last callback line")
        if problems:
            res.failures.append("integrity: " + "; ".join(problems))
            res.verdict = "FAIL"
        if not res.verdict:
            res.failures.append("the audit callback printed no verdict")
        res.lean_exit_code = 0
        res.olean_sha256, res.olean_closure = r.olean_sha256, [list(e) for e in r.olean_closure]
    else:
        res = AuditResult(nonce=nonce)
        if r.status == "FAILED" and "build it first" not in r.detail:
            res.verdict, res.lean_exit_code = "FAIL", 0
            ax = re.search(r"the untrusted module (\S+) declares the axiom (\S+); refusing", r.detail)
            if ax:
                res.failures.append(f"untrusted axiom {ax.group(2)} declared by module {ax.group(1)} in the replayed "
                                    "closure: refused by replay (Ruling 10: no untrusted axiom enters the environment)")
            else:
                res.failures.append(f"the replay refused the closure: {r.detail[:2000]}")
        else:
            what = "the replay could not run" if r.status == "FAILED" else "the replayed audit did not run"
            res.failures.append(f"{what}: {r.detail[:2000]}")
    res.isolated = True
    res.raw_tail = tail
    return res


def run_closure_audit_replayed(
    spec: AuditSpec,
    project: str | Path | None = None,
    *,
    trusted_env=None,
    manifest=None,
    wrapper: Sequence[str] | None = None,
    timeout: int = 3600,
    memory_mb=_REPLAY_DEFAULT,
    untrusted_paths=(),
    elan_home=None,
    heartbeats: int = 200000,
) -> AuditResult:
    """Run the audit as a kernel-replay callback (checks/lean_replay.py): the submission is never imported.

    `spec.imports` that resolve to a trusted .olean of the pinned `trusted_env` (default ``$TELPERION_LEAN_ENV``) are
    imported; every other one is replayed, with its untrusted closure, from `project`'s ``.lake/build/lib/lean`` and
    `untrusted_paths`. The trusted files are checked against `manifest` first; the replay reads private copies only,
    refuses untrusted axioms (always: Ruling 10) and binds the result to the copies (``olean_sha256``). `sorryAx` is
    let through the replay so that the audit's own absence and axiom checks report it. `wrapper` is the command
    prefix before the pinned ``lean`` (None: leanlock when present); `memory_mb` its ``--memory`` bound (default
    lean_replay's; None for none). No ``lake`` runs. A relative ``closure_out`` is resolved against the caller's cwd
    (the replay runs in a private temp dir that is removed afterwards). Never raises for a run that fails: the
    result has no verdict and says why (see `replayed_audit_result`)."""
    from .checks import lean_replay

    nonce = secrets.token_hex(16)
    try:
        pinned = lean_replay.pinned_env(trusted_env, elan_home)
        # a project that IS the pinned env adds no submission dir: its own build dir is a trusted prefix
        proj = None if project is None or os.path.realpath(project) == pinned.root else project
        untrusted = lean_replay.submission_paths(proj, untrusted_paths)
        search = [*pinned.entries, pinned.libdir, *untrusted]
        trusted, replayed = [], []
        for m in spec.imports:
            f = lean_replay.resolve_olean(search, m)
            (trusted if f and lean_replay.under_prefix(f, pinned.prefixes) else replayed).append(m)
        if spec.closure_out:
            spec = replace(spec, closure_out=os.path.abspath(spec.closure_out))
        callback = render_audit_callback(spec, nonce)
    except (OSError, ValueError) as exc:
        res = AuditResult(nonce=nonce, isolated=True)
        res.failures.append(f"the replayed audit could not be set up: {exc}")
        return res
    kw = {} if memory_mb is _REPLAY_DEFAULT else {"memory_mb": memory_mb}
    r = lean_replay.run_replay(replayed, callback, project=None, untrusted_paths=untrusted, trusted_imports=trusted,
                               trusted_env=pinned.root, manifest=manifest, elan_home=elan_home, wrapper=wrapper,
                               timeout=timeout, heartbeats=heartbeats, allow_sorry=True, callback_takes_closure=True,
                               **kw)
    return replayed_audit_result(r, nonce)
