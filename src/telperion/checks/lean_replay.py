"""Kernel-replay loader: put an UNTRUSTED module's constants in front of a check without running any of its code.

WHY. A check that writes ``import <the theorem's module>`` hands that module the check process: Lean runs its
``initialize`` blocks while importing, and its ``@[command_elab ...]``, ``@[tactic ...]``, macro and attribute
registrations then elaborate the check's own commands. A security re-review showed such a module reading the per-run
nonce from the check's source and printing forged result lines. No nonce or output filter helps against code that runs
in the same process.

TRUST ANCHORS. Everything trusted comes from a PINNED env (``trusted_env``, default ``$TELPERION_LEAN_ENV``), never
from the project under test: the absolute ``lean`` binary of the toolchain its ``lean-toolchain`` names, that
toolchain's ``lib/lean``, and the realpaths of ``<env>/.lake/packages/*/.lake/build/lib/lean`` and
``<env>/.lake/build/lib/lean``. A sha256 manifest of every file Lean loads from there (``.olean*``, ``.ir*``, shared
libraries, and the binary; ``build_trusted_manifest``, stored by default OUTSIDE the env, see ``default_manifest_path``)
is verified before each run, and any change, addition or removal refuses the run. Each target's .olean is resolved and
hashed in Python before the run, Lean must resolve it to that same file, and it must hash the same afterwards: the
result's ``olean_sha256`` binds the check to the bytes it replayed. The submission's own dirs (``<project>/.lake/build/lib/lean`` and any ``untrusted_paths``) must lie
under no trusted prefix. No ``lake`` runs, and the script and the process's cwd are in a private 0700 temp dir.

HOW (the Comparator / lean4checker approach). The generated script imports TRUSTED modules only and runs as the pinned
``lean`` with a LEAN_PATH of trusted entries only, so no ``import`` can reach an untrusted ``.olean``. Inside one
``#eval`` it then does the following:

1. checks that every module the process imported resolves to an ``.olean`` under a trusted prefix;
2. walks the target module's import closure over the full search path (trusted entries, then the submission's), given
   to the script as DATA and resolved as a real ``import`` would resolve it (``SearchPath.findWithExt``: the first entry
   holding the module's package ROOT). An ``.olean`` that only a later entry holds is refused, not read.
   - A module whose ``.olean`` realpath is under a trusted prefix is trusted and must already be imported, from that
     same file. If it is not imported, the script asks for it (``REPLAY NEEDS``) and Python reruns once with it added.
   - Every other module is UNTRUSTED, whatever its name, and its data is read without running anything.
     ``CompactedRegion.read`` reads one part for a plain file, or the exported, server and private parts of a
     ``module`` file, each mapped once, with the earlier parts as dependency regions
     (``Lean/Environment.lean:2079-2093``). The parts must agree on their imports. Every exported or server constant
     must exist in the private part with the same type and universe parameters, and the same kind, except that a
     theorem, definition or opaque may be exported as an axiom. The PRIVATE part's constants are used: in the exported
     part a public theorem is an axiom.
   - An ``axiom`` anywhere in the untrusted closure is refused;
3. adds the untrusted constants by the replay loop of ``Lean.Kernel.Environment.replay`` (toolchain
   ``src/lean/Lean/Replay.lean:74-190``), ported into the script so that it adds to the ELABORATOR's environment through
   ``Lean.Environment.addDeclCore`` (``Lean/Environment.lean:699``, ``doCheck := true``). Every declaration goes to the
   kernel, and constructors and recursors are compared with the ones the kernel generates. (The upstream function
   returns a ``Kernel.Environment``, and the only way back, ``Environment.ofKernelEnv`` at ``Lean/Environment.lean:643``,
   drops the import's realization context: ``omega`` then fails with ``Environment.realizeConst: realizedImportedConsts
   is empty``.)
   - Afterwards every replayed constant must be found exactly as its ``.olean`` gives it (types and values compared
     with ``Expr.equal``). The one exception is upstream's skip: a theorem identical in name, type, universe parameters
     and ``all`` to one already present keeps the present one.
   - The axioms of the target module's constants (``collectAxioms``) go on the OK line, and ``sorryAx`` among them is
     refused.
   - A kernel rejection or any refusal is ``REPLAY FAILED``;
4. runs the caller's callback, a ``TermElabM Unit`` named ``TelperionReplay.callback``, in the replayed environment.

WHAT IS NOT LOADED, ON PURPOSE. Replay transfers constants only. The untrusted modules' environment extensions are
never read: no initializers, elaborators, macros, syntax, attributes, instances, simp lemmas, notation or docstrings.
So a callback sees the untrusted constants but none of their registrations, and a probe can only get WEAKER (a tactic
that needed a local instance or simp lemma fails). Callers must read that as fail-closed (PROBE_ONLY, or a fingerprint,
which hashes Exprs and is unaffected). Unsafe and ``partial`` constants are skipped by replay (``Replay.lean:180-183``),
and anything that uses one then fails to replay. The callback itself is elaborated BEFORE the replay, against the
trusted environment only, so it cannot name an untrusted constant except as a ``Name`` literal.

PROTOCOL. Every line the script prints starts with ``<nonce>-``, a 128-bit per-run tag, and messages are flattened to
one line. There is exactly one ``REPLAY OK|FAILED|NEEDS`` line, then the callback's lines, then exactly one final
``DONE``. Anything else is ERROR. Since no untrusted code runs, the tag is meaningful. Callers must still derive results
from values their callback computed, never from logged text.

REQUIRED FOR UNTRUSTED SUBMISSIONS: A SANDBOX (the owner's decision, not provided here). The ``.olean`` reader trusts
its input, which it maps as a memory image, so a crafted ``.olean`` is a memory-safety attack on this process. The
submission's BUILD runs the submission's code, and unsandboxed it could rewrite the trusted files between the manifest
check and the run. The manifest catches only tampering that is done before the check.
"""
from __future__ import annotations

import concurrent.futures
import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from ..closure_audit import lean_name_literal
from .lean_run import run_lean

STATUSES = ("OK", "FAILED", "ERROR")
MANIFEST_VERSION = 1
# The files Lean loads from a trusted prefix: module data, IR (run by the interpreter for initializers), shared libraries.
TRUSTED_SUFFIXES = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig", ".dylib", ".so")

_MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
_TOOLCHAIN_RE = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+:[A-Za-z0-9_.+-]+")


@dataclass
class ReplayResult:
    status: str                        # OK (replayed, callback ran), FAILED (replay refused), ERROR (no verdict)
    detail: str
    lines: list[str] = field(default_factory=list)   # the callback's lines, tag stripped, in order
    output: str = ""
    axioms: list[str] | None = None    # OK only: the axioms of the target modules' constants
    declared: list[str] = field(default_factory=list)          # OK only: axioms the untrusted closure declares
    olean_sha256: dict[str, str] = field(default_factory=dict)  # OK only: per target module, see olean_sha256()


@dataclass(frozen=True)
class PinnedEnv:
    """The trust anchors of a pinned Lean env, all realpaths."""
    root: str
    toolchain: str
    lean: str                          # the absolute lean binary
    libdir: str                        # its lib/lean (Init, Std, Lean, Lake; lean adds it to every search path)
    entries: tuple[str, ...]           # the trusted LEAN_PATH: package build dirs, then the env's own build dir

    @property
    def prefixes(self) -> tuple[str, ...]:
        return (self.libdir, *self.entries)


def _module(name: str) -> str:
    if not _MODULE_RE.fullmatch(name):
        raise ValueError(f"not a plain Lean module name: {name!r}")
    return name


def _lean_strings(items) -> str:
    return "[" + ", ".join(json.dumps(str(s), ensure_ascii=False) for s in items) + "]"


def _realpath(p) -> str:
    return os.path.realpath(os.fspath(p))


def under_prefix(path, prefixes) -> bool:
    """Whether realpath(`path`) is one of `prefixes` or lies below one (path-component boundary, not a string
    prefix: `/a/lib-evil` is not under `/a/lib`). The prefixes are realpath'd too."""
    r = _realpath(path)
    for pre in prefixes:
        pre = _realpath(pre)
        if r == pre or r.startswith(pre.rstrip("/") + "/"):
            return True
    return False


def split_search_path(entries, prefixes) -> tuple[list[str], list[str]]:
    """(trusted, untrusted) search-path entries, order kept. Empty entries are dropped."""
    trusted, untrusted = [], []
    for e in entries:
        if e:
            (trusted if under_prefix(e, prefixes) else untrusted).append(e)
    return trusted, untrusted


def _elan_home(elan_home) -> Path:
    return Path(elan_home or os.environ.get("ELAN_HOME") or os.path.expanduser("~/.elan"))


def pinned_env(trusted_env=None, elan_home=None) -> PinnedEnv:
    """The trust anchors of `trusted_env` (default ``$TELPERION_LEAN_ENV``). The toolchain is the one its
    ``lean-toolchain`` names, found under `elan_home` (``$ELAN_HOME``, else ``~/.elan``) as elan lays it out."""
    env = trusted_env if trusted_env is not None else os.environ.get("TELPERION_LEAN_ENV")
    if not env:
        raise ValueError("no trusted env: pass trusted_env or set TELPERION_LEAN_ENV to the pinned Lean env")
    root = Path(_realpath(env))
    try:
        toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    except OSError as exc:
        raise ValueError(f"trusted env {root} has no readable lean-toolchain: {exc}") from None
    if not _TOOLCHAIN_RE.fullmatch(toolchain):
        raise ValueError(f"trusted env {root}: unexpected lean-toolchain {toolchain!r} (want origin/repo:version)")
    tdir = _elan_home(elan_home) / "toolchains" / toolchain.replace("/", "--").replace(":", "---")
    lean, libdir = tdir / "bin" / "lean", tdir / "lib" / "lean"
    if not os.access(lean, os.X_OK) or not libdir.is_dir():
        raise ValueError(f"toolchain {toolchain} of the trusted env is not installed at {tdir}")
    entries = sorted(_realpath(d) for d in root.glob(".lake/packages/*/.lake/build/lib/lean") if d.is_dir())
    own = root / ".lake" / "build" / "lib" / "lean"
    if own.is_dir():
        entries.append(_realpath(own))
    return PinnedEnv(str(root), toolchain, _realpath(lean), _realpath(libdir), tuple(entries))


def _trusted_files(pinned: PinnedEnv) -> list[str]:
    """The binary, then every file with a TRUSTED_SUFFIXES suffix under a trusted prefix (realpaths, sorted)."""
    files = {pinned.lean}
    for pre in pinned.prefixes:
        for dirpath, dirnames, filenames in os.walk(pre):
            dirnames.sort()
            for f in filenames:
                if f.endswith(TRUSTED_SUFFIXES):
                    files.add(_realpath(os.path.join(dirpath, f)))
    return sorted(files)


def _sha256(path: str) -> str:
    with open(path, "rb") as fh:
        return hashlib.file_digest(fh, "sha256").hexdigest()


def _hash_all(files: list[str]) -> dict[str, str]:
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        return dict(zip(files, pool.map(_sha256, files)))


def build_trusted_manifest(trusted_env=None, path=None, elan_home=None) -> Path:
    """Write the sha256 manifest of the pinned env's trusted files to `path` (default `default_manifest_path`) and
    return its path. Run it once, by the owner, on the env as pinned. The manifest must be stored where no submission
    build can write, like the trusted files themselves."""
    pinned = pinned_env(trusted_env, elan_home)
    out = Path(path) if path is not None else default_manifest_path(pinned.root)
    out.parent.mkdir(parents=True, exist_ok=True)
    data = {"version": MANIFEST_VERSION, "toolchain": pinned.toolchain, "lean": pinned.lean,
            "prefixes": list(pinned.prefixes), "files": _hash_all(_trusted_files(pinned))}
    tmp = out.with_name(out.name + f".tmp{secrets.token_hex(4)}")
    tmp.write_text(json.dumps(data, indent=1, sort_keys=True), encoding="utf-8")
    os.replace(tmp, out)
    return out


def verify_trusted_manifest(pinned: PinnedEnv, path) -> None:
    """Raise ValueError unless the trusted files are exactly the manifest's: the same toolchain, binary and prefixes,
    the same set of files and the same sha256 of each."""
    try:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ValueError(f"no readable trusted manifest at {path} (build it with build_trusted_manifest): {exc}") from None
    want = {"version": MANIFEST_VERSION, "toolchain": pinned.toolchain, "lean": pinned.lean,
            "prefixes": list(pinned.prefixes)}
    for k, v in want.items():
        if data.get(k) != v:
            raise ValueError(f"trusted manifest {path}: {k} is {data.get(k)!r}, the env has {v!r}")
    recorded = data.get("files")
    if not isinstance(recorded, dict):
        raise ValueError(f"trusted manifest {path} has no file list")
    files = _trusted_files(pinned)
    added = sorted(set(files) - set(recorded))
    removed = sorted(set(recorded) - set(files))
    if added or removed:
        raise ValueError(f"trusted files changed since the manifest: {len(added)} added (e.g. {added[:3]}), "
                         f"{len(removed)} removed (e.g. {removed[:3]})")
    changed = sorted(f for f, h in _hash_all(files).items() if recorded[f] != h)
    if changed:
        raise ValueError(f"trusted files changed since the manifest: {len(changed)} differ (e.g. {changed[:3]})")


_SCRIPT = r"""__IMPORTS__
import Lean

open Lean Meta Elab Term

namespace TelperionReplay

def tag : String := __TAG__
def targetModules : List Name := __TARGETS__
/-- The realpath Python resolved and hashed for each target module ("" when it found none). -/
def expectOleans : List (Name × String) := __EXPECT__
def allowAxioms : Bool := __ALLOW_AXIOMS__
def allowSorry : Bool := __ALLOW_SORRY__
def trustedPrefixes : List String := __PREFIXES__
def searchPath : List System.FilePath := (__SEARCH__ : List String).map System.FilePath.mk

/-- One protocol line: the tag, then `s` flattened to a single line. -/
def line (s : String) : IO Unit :=
  IO.println s!"{tag}-{(s.replace "\n" " ").replace "\r" " "}"

def isTrustedFile (f : System.FilePath) : IO Bool := do
  let r := (← IO.FS.realPath f).toString
  return trustedPrefixes.any fun pre =>
    r == pre || r.startsWith (if pre.endsWith "/" then pre else pre ++ "/")

/-- `m`'s `.olean` as an `import` resolves it (`SearchPath.findWithExt`: the first entry holding the package root),
or none. An `.olean` that only a later entry holds would not be imported; it is refused, not read. -/
def locate (m : Name) : ExceptT String IO (Option System.FilePath) := do
  if let some f ← SearchPath.findWithExt searchPath "olean" m then
    if ← f.pathExists then return some f
  for d in searchPath do
    let f := modToFilePath d m "olean"
    if ← f.pathExists then
      throw s!"module {m}: an import would not find {f} (an earlier search-path entry holds the package root {m.getRoot}); refusing"
  return none

/-- Why this process's own imports are not all trusted, if they are not. -/
def checkLoaded (env : Environment) : IO (Option String) := do
  for m in env.header.moduleNames do
    let f ← findOLean m
    unless ← isTrustedFile f do
      return some s!"untrusted-library-module {m} {f}: the check imported it from outside the trusted prefixes"
  return none

/-- The parts of a module's `.olean`, each mapped once: one for a plain file; exported, server and private for a
`module`, read with the earlier parts as dependency regions as `Lean/Environment.lean:2079-2093` does. -/
def readParts (f : System.FilePath) : IO (Array ModuleData) := do
  let main ← unsafe CompactedRegion.read (α := ModuleData) f #[]
  if !main.1.isModule then return #[main.1]
  let server ← unsafe CompactedRegion.read (α := ModuleData) (OLeanLevel.server.adjustFileName f) #[main.2]
  let priv ← unsafe CompactedRegion.read (α := ModuleData) (OLeanLevel.private.adjustFileName f) #[main.2, server.2]
  return #[main.1, server.1, priv.1]

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- The private (last) part, after checking that the parts agree: the same imports and module flag, and every
constant of an earlier part in the private one with the same type and universe parameters and the same kind, except
that a theorem, definition or opaque may be exported as an axiom. -/
def checkParts (f : System.FilePath) (parts : Array ModuleData) : Except String ModuleData := do
  let some priv := parts.back? | throw s!"{f}: no module data"
  let mut byName : Std.HashMap Name ConstantInfo := {}
  for c in priv.constants do
    byName := byName.insert c.name c
  for d in parts.pop do
    unless d.isModule == priv.isModule && d.imports == priv.imports do
      throw s!"{f}: its parts disagree on the module flag or the imports"
    for c in d.constants do
      let some p := byName[c.name]?
        | throw s!"{f}: {c.name} is in an exported part but not in the private part"
      unless c.levelParams == p.levelParams && c.type.equal p.type do
        throw s!"{f}: {c.name} has a different type or universe parameters in an exported part"
      unless kind c == kind p || (kind c == "axiom" && ["theorem", "def", "opaque"].contains (kind p)) do
        throw s!"{f}: {c.name} is a {kind c} in an exported part but a {kind p} in the private part"
  return priv

structure Closure where
  modules : Array Name := #[]                       -- untrusted, in discovery order
  consts : Std.HashMap Name ConstantInfo := {}
  target : Array Name := #[]                        -- the target modules' own constants
  declared : Array Name := #[]                      -- axioms declared in the untrusted closure (allowAxioms only)
  needs : Array Name := #[]                         -- trusted modules this process did not import

/-- The target's import closure: trusted modules stop the walk, untrusted ones are read as data. -/
def collect (env : Environment) : ExceptT String IO Closure := do
  let mut todo : Array Name := targetModules.toArray.reverse
  let mut seen : NameSet := {}
  let mut out : Closure := {}
  repeat
    let some m := todo.back? | break
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    let some f ← locate m
      | throw s!"module {m} has no .olean in the search path (build it first)"
    if targetModules.contains m then
      let real := (← IO.FS.realPath f).toString
      let expected := ((expectOleans.find? (·.1 == m)).map (·.2)).getD ""
      unless real == expected do
        throw s!"olean-mismatch {m} resolves to {real}, expected {expected}; refusing"
    if ← isTrustedFile f then
      if targetModules.contains m then
        throw s!"target module {m} resolves to the trusted .olean {f}; refusing"
      if (env.getModuleIdx? m).isNone then
        out := { out with needs := out.needs.push m }
      else
        let g ← findOLean m
        if (← IO.FS.realPath g) != (← IO.FS.realPath f) then
          throw s!"module {m}: the closure resolves it to {f} but the check imported {g}"
      continue
    if (env.getModuleIdx? m).isSome then
      throw s!"untrusted .olean {f} has the name of the trusted module {m}"
    let data ← match checkParts f (← readParts f) with
      | .ok d => pure d
      | .error e => throw e
    for i in data.imports do
      todo := todo.push i.module
    for c in data.constants do
      if out.consts.contains c.name then
        throw s!"constant {c.name} is declared twice in the untrusted closure"
      if let .axiomInfo _ := c then
        unless allowAxioms do
          throw s!"the untrusted module {m} declares the axiom {c.name}; refusing"
        out := { out with declared := out.declared.push c.name }
      out := { out with consts := out.consts.insert c.name c }
      if targetModules.contains m then
        out := { out with target := out.target.push c.name }
    out := { out with modules := out.modules.push m }
  return out

/-!
The replay loop below is ported from Lean v4.35.0 `src/lean/Lean/Replay.lean` (`Lean.Kernel.Environment.replay`,
Copyright (c) 2023 Kim Morrison, released under Apache 2.0). Two changes:
- it adds to the elaborator's `Environment` through `Lean.Environment.addDeclCore` (`Lean/Environment.lean:699`,
  `doCheck := true`, which runs the kernel check), instead of to a bare `Kernel.Environment`. The reason is that
  `Environment.ofKernelEnv` drops the import's realization context, and tactics then fail
  (`Environment.realizeConst: realizedImportedConsts is empty`). Every declaration still goes to the kernel, and
  constructors and recursors are compared with the kernel-generated ones;
- a lookup that upstream does with `[n]!` or `unreachable!` throws instead of panicking with a default value.
-/
namespace Replay

structure State where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT (Std.HashMap Name ConstantInfo) <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def lookup (n : Name) (why : String) : M ConstantInfo := do
  match (← read)[n]? with
  | some ci => pure ci
  | none => throw <| .userError s!"{n} ({why}) is not in the untrusted closure"

def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 0 d none with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throw <| .userError <| (← ex.toMessageData {} |>.toString)

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let ci ← lookup name "a constant to replay"
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo   info => addDecl (Declaration.defnDecl   info)
        | .thmInfo    info =>
          -- A theorem identical to one already present is skipped, as upstream (the present one stays).
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name && info.type == info'.type &&
              info.levelParams == info'.levelParams && info.all == info'.all then
              return
          addDecl (Declaration.thmDecl    info)
        | .axiomInfo  info => addDecl (Declaration.axiomDecl  info)
        | .opaqueInfo info => addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => lookup n s!"in the block of {name}"
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            let .inductInfo v := ci
              | throw <| .userError s!"{ci.name} in the block of {name} is not an inductive"
            pure (ci, ← v.ctors.mapM fun n => lookup n s!"a constructor of {ci.name}")
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (Declaration.inductDecl lparams nparams types false)
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayConstant `Eq
          addDecl (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read)[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read)[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

/-- Replay `newConstants` into `env`, kernel-checking each; unsafe and `partial` constants are skipped. -/
def replay (newConstants : Std.HashMap Name ConstantInfo) (env : Environment) : IO Environment := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := newConstants) do
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  return s.env

end Replay

/-- `a` and `b` are the same constant: equal as `ConstantInfo`s (whose `BEq` compares Exprs up to binder
annotations), with the type and the value also `Expr.equal`. -/
def sameConst (a b : ConstantInfo) : Bool :=
  a == b && a.type.equal b.type &&
    match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
    | some x, some y => x.equal y
    | none, none => true
    | _, _ => false

/-- Every replayed (not skipped) constant is in `after` exactly as `consts` gives it. The one exception is upstream's
skip: a theorem identical in name, type, universe parameters and `all` to one in `before` keeps that one. -/
def fidelity (before after : Environment) (consts : Std.HashMap Name ConstantInfo) : Except String Unit := do
  for (n, ci) in consts.toList do
    if ci.isUnsafe || ci.isPartial then continue
    let some ci' := after.find? n | throw s!"{n} is missing after replay"
    if sameConst ci ci' then continue
    if let (.thmInfo t, some (.thmInfo t0)) := (ci, before.find? n) then
      if t.name == t0.name && t.type == t0.type && t.levelParams == t0.levelParams && t.all == t0.all &&
          sameConst (.thmInfo t0) ci' then
        continue
    throw s!"{n}: the replayed {kind ci'} differs from the {kind ci} in its .olean"

end TelperionReplay

__CALLBACK__

set_option maxHeartbeats 0 in
#eval show TermElabM Unit from do
  let env ← getEnv
  if let some e ← TelperionReplay.checkLoaded env then
    TelperionReplay.line s!"REPLAY FAILED {e}"
  else
    match ← (TelperionReplay.collect env).run.toBaseIO with
    | .error e => TelperionReplay.line s!"REPLAY FAILED reading the closure: {e}"
    | .ok (.error e) => TelperionReplay.line s!"REPLAY FAILED {e}"
    | .ok (.ok c) =>
      if !c.needs.isEmpty then
        TelperionReplay.line s!"REPLAY NEEDS {" ".intercalate (c.needs.toList.map toString)}"
      else
        match ← (TelperionReplay.Replay.replay c.consts env).toBaseIO with
        | .error e => TelperionReplay.line s!"REPLAY FAILED {e}"
        | .ok env' =>
          if let .error e := TelperionReplay.fidelity env env' c.consts then
            TelperionReplay.line s!"REPLAY FAILED fidelity: {e}"
          else
            setEnv env'
            let mut axs : Array Name := #[]
            for n in c.target do
              if env'.contains n then
                for a in ← collectAxioms n do
                  unless axs.contains a do axs := axs.push a
            let axList := (axs.map toString).qsort (· < ·)
            let declared := (c.declared.map toString).qsort (· < ·)
            if axs.contains ``sorryAx && !TelperionReplay.allowSorry then
              TelperionReplay.line s!"REPLAY FAILED the target module uses sorryAx (axioms={axList.toList})"
            else
              TelperionReplay.line (s!"REPLAY OK modules={c.modules.toList} constants={c.consts.size} " ++
                s!"declared={declared.toList} axioms={axList.toList}")
              -- A fresh heartbeat budget (replay's allocations must not use it up); a runtime exception (heartbeats,
              -- deep recursion) is caught too, so that DONE is still printed.
              withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := __HEARTBEATS__ * 1000 }) do
                withCurrHeartbeats do
                  tryCatchRuntimeEx TelperionReplay.callback fun ex => do
                    TelperionReplay.line s!"CALLBACK FAILED {← ex.toMessageData.toString}"
  TelperionReplay.line "DONE"
"""


def _targets(target_module) -> list[str]:
    return [target_module] if isinstance(target_module, str) else list(target_module)


def render_replay_script(trusted_imports, target_module, trusted_prefixes, callback_src: str, nonce: str,
                         search_path=(), heartbeats: int = 200000, *, expect_oleans=None, allow_axioms: bool = False,
                         allow_sorry: bool = False) -> str:
    """The Lean script that replays `target_module`'s untrusted closure and then runs `callback_src`.

    `callback_src` is trusted Lean source (ours, never the module's) that must define
    ``TelperionReplay.callback : Lean.Elab.Term.TermElabM Unit``; it prints through ``TelperionReplay.line``.
    `target_module` is a module name or a list of them. `expect_oleans` maps each target to the realpath its .olean
    must resolve to (anything else, or no entry, is ``olean-mismatch``). `allow_axioms` lets the untrusted closure
    declare axioms (listed as ``declared=[...]``) and `allow_sorry` lets the targets use ``sorryAx``; both are refused
    otherwise. `search_path` is the full olean search path, in order, that the closure is resolved over. It is DATA here and is
    never this process's LEAN_PATH. The callback runs with a fresh budget of `heartbeats` (thousands, as the
    ``maxHeartbeats`` option), and an exception it raises, a runtime one included, is reported as ``CALLBACK FAILED``."""
    if not re.fullmatch(r"[A-Za-z0-9]+", nonce):
        raise ValueError(f"nonce must be alphanumeric: {nonce!r}")
    imports = "\n".join(f"import {_module(m)}" for m in trusted_imports)
    targets = [_module(m) for m in _targets(target_module)]
    expect = expect_oleans or {}
    pairs = ", ".join(f"({lean_name_literal(m)}, {json.dumps(str(expect.get(m, '')))})" for m in targets)
    return (_SCRIPT.replace("__IMPORTS__", imports)
            .replace("__TAG__", json.dumps(nonce))
            .replace("__TARGETS__", "[" + ", ".join(lean_name_literal(m) for m in targets) + "]")
            .replace("__EXPECT__", f"[{pairs}]")
            .replace("__ALLOW_AXIOMS__", "true" if allow_axioms else "false")
            .replace("__ALLOW_SORRY__", "true" if allow_sorry else "false")
            .replace("__PREFIXES__", _lean_strings(_realpath(p).rstrip("/") or "/" for p in trusted_prefixes))
            .replace("__SEARCH__", _lean_strings(search_path))
            .replace("__HEARTBEATS__", str(int(heartbeats)))
            .replace("__CALLBACK__", callback_src))


def parse_replay_output(output: str, nonce: str, rc: int = 0) -> tuple[str, str, list[str], list[str]]:
    """(status, detail, callback lines, needed modules) from a run's output. Only lines carrying `nonce` count.

    The status is OK, FAILED, NEEDS or ERROR. It is ERROR when the protocol is broken (not exactly one REPLAY line
    first, not exactly one DONE as the last tagged line, a callback line without REPLAY OK, an OK line without an
    axiom list), on a nonzero exit, and on a ``CALLBACK FAILED`` line (the callback lines are then still returned)."""
    if rc != 0:
        return "ERROR", f"lean exited {rc}: {output.strip()[-1500:]!r}", [], []
    tagged = [m.group(1) for m in re.finditer(rf"(?m)^{re.escape(nonce)}-(.*)$", output)]
    replay = [t for t in tagged if re.match(r"REPLAY (OK|FAILED|NEEDS)\b", t)]
    if len(replay) != 1:
        return "ERROR", f"printed {len(replay)} REPLAY lines (want exactly one): {output.strip()[-1500:]!r}", [], []
    if tagged.count("DONE") != 1 or tagged[-1] != "DONE" or tagged[0] != replay[0]:
        return "ERROR", f"protocol broken (no single final DONE after a first REPLAY line): {output.strip()[-1500:]!r}", [], []
    kind, _, rest = replay[0][len("REPLAY "):].partition(" ")
    body = tagged[1:-1]
    if kind == "NEEDS":
        return ("ERROR", "callback lines after REPLAY NEEDS", [], []) if body else ("NEEDS", rest, [], rest.split())
    if kind == "FAILED":
        return ("ERROR", "callback lines after REPLAY FAILED", [], []) if body else ("FAILED", rest, [], [])
    if parse_axioms(rest) is None:
        return "ERROR", f"REPLAY OK line without an axiom list: {rest!r}", [], []
    failed = [t for t in body if t.startswith("CALLBACK FAILED")]
    if failed:
        return "ERROR", f"the callback failed: {failed[0][len('CALLBACK FAILED '):]}", body, []
    return "OK", rest, body, []


def parse_axioms(detail: str) -> list[str] | None:
    """The ``axioms=[a, b]`` list at the end of a REPLAY OK detail, or None."""
    m = re.search(r"\baxioms=\[([^\]]*)\]$", detail)
    if not m:
        return None
    return [a.strip() for a in m.group(1).split(",") if a.strip()]


def parse_declared(detail: str) -> list[str]:
    """The ``declared=[...]`` list of a REPLAY OK detail (axioms the untrusted closure declares), or []."""
    m = re.search(r"\bdeclared=\[([^\]]*)\]", detail)
    return [a.strip() for a in m.group(1).split(",") if a.strip()] if m else []


def default_wrapper() -> list[str]:
    lock = os.path.expanduser("~/hodge-engine/leanlock.sh")
    return ["env", "ARDA_LEAN_SLOTS=1", lock] if os.path.exists(lock) else []


def submission_paths(project=None, untrusted_paths=()) -> list[str]:
    """The submission's olean dirs (realpaths): `<project>/.lake/build/lib/lean`, if it exists, then `untrusted_paths`."""
    out = []
    if project is not None:
        own = Path(project) / ".lake" / "build" / "lib" / "lean"
        if own.is_dir():
            out.append(_realpath(own))
    out += [_realpath(p) for p in untrusted_paths]
    return list(dict.fromkeys(out))


def _check_disjoint(pinned: PinnedEnv, untrusted: list[str]) -> None:
    for u in untrusted:
        if under_prefix(u, pinned.prefixes):
            raise ValueError(f"submission dir {u} lies under a trusted prefix; refusing")
        if any(under_prefix(t, [u]) for t in pinned.prefixes):
            raise ValueError(f"submission dir {u} contains a trusted prefix; refusing")


def resolve_olean(search, module: str) -> str | None:
    """The realpath of `module`'s .olean as an import resolves it (``SearchPath.findWithExt``: the first entry holding
    the package root, as a directory or as ``<root>.olean``), or None when that file does not exist."""
    parts = _module(module).split(".")
    for d in search:
        if os.path.isdir(os.path.join(d, parts[0])) or os.path.exists(os.path.join(d, parts[0] + ".olean")):
            f = os.path.join(d, *parts) + ".olean"
            return _realpath(f) if os.path.isfile(f) else None
    return None


def olean_sha256(olean) -> str:
    """sha256 of a module's .olean parts concatenated in order: the .olean, then .olean.server and .olean.private
    when they exist (a ``module`` file has all three)."""
    h = hashlib.sha256()
    for part in (str(olean), f"{olean}.server", f"{olean}.private"):
        if part == str(olean) or os.path.isfile(part):
            with open(part, "rb") as fh:
                for chunk in iter(lambda: fh.read(1 << 20), b""):
                    h.update(chunk)
    return h.hexdigest()


def default_manifest_path(trusted_env=None) -> Path:
    """Where the trusted manifest of `trusted_env` lives by default: ``$TELPERION_TRUSTED_MANIFEST`` if set, else
    ``~/telperion-tools/trusted-manifests/<sha256 of lean-toolchain + lake-manifest.json>.json``, OUTSIDE the env, so
    that no build in the env (or in a submission) writes it."""
    if os.environ.get("TELPERION_TRUSTED_MANIFEST"):
        return Path(os.environ["TELPERION_TRUSTED_MANIFEST"])
    env = trusted_env if trusted_env is not None else os.environ.get("TELPERION_LEAN_ENV")
    if not env:
        raise ValueError("no trusted env: pass trusted_env or set TELPERION_LEAN_ENV to the pinned Lean env")
    h = hashlib.sha256()
    for name in ("lean-toolchain", "lake-manifest.json"):
        f = Path(env) / name
        h.update(name.encode() + b"\0" + (f.read_bytes() if f.is_file() else b"") + b"\0")
    return Path(os.path.expanduser("~/telperion-tools/trusted-manifests")) / f"{h.hexdigest()}.json"


MANIFEST_HINT = "build it with `telperion trusted-manifest build --env {env}`"


def run_replay(target_module, callback_src: str, *, project=None, untrusted_paths=(),
               trusted_imports=("Mathlib",), trusted_env=None, manifest=None, elan_home=None,
               wrapper: list[str] | None = None, timeout: int = 1800, heartbeats: int = 200000,
               allow_axioms: bool = False, allow_sorry: bool = False, expect_oleans=None,
               prefixes_override=None) -> ReplayResult:
    """Replay `target_module` (a name, or a list of names) from the submission's olean dirs (see `submission_paths`)
    into a process that imports only `trusted_imports` from the pinned `trusted_env`, then run `callback_src` (see
    render_replay_script).

    Before running, the trusted files are checked against `manifest` (default `default_manifest_path`), and each
    target's .olean is resolved and hashed here; Lean must resolve it to the same file, and it must hash the same
    after the run (`ReplayResult.olean_sha256`). The script runs as the pinned ``lean`` (through `wrapper`, leanlock by
    default) in a private temp dir, with LEAN_PATH = the trusted entries only. If the closure needs a trusted module
    that is not imported, it is added and the run is repeated once. `expect_oleans` and `prefixes_override` replace
    the resolved oleans and the trusted prefixes given to the script (tests only)."""
    prefix = default_wrapper() if wrapper is None else list(wrapper)
    targets = _targets(target_module)
    try:
        pinned = pinned_env(trusted_env, elan_home)
        # a project that IS the pinned env adds no submission dir: its own build dir is a trusted prefix
        proj = None if project is not None and _realpath(project) == pinned.root else project
        untrusted = submission_paths(proj, untrusted_paths)
        _check_disjoint(pinned, untrusted)
        mpath = Path(manifest) if manifest is not None else default_manifest_path(pinned.root)
        if not mpath.is_file():
            raise ValueError(f"no readable trusted manifest at {mpath}; " + MANIFEST_HINT.format(env=pinned.root))
        verify_trusted_manifest(pinned, mpath)
        for m in targets:
            _module(m)
    except (OSError, ValueError) as exc:
        return ReplayResult("ERROR", f"cannot set up the replay: {exc}")
    search = [*pinned.entries, pinned.libdir, *untrusted]
    resolved = {m: resolve_olean(search, m) for m in targets}
    before = {m: olean_sha256(f) for m, f in resolved.items() if f}
    expect = dict(expect_oleans) if expect_oleans is not None else {m: f or "" for m, f in resolved.items()}
    prefixes = pinned.prefixes if prefixes_override is None else tuple(prefixes_override)
    env = {k: v for k, v in os.environ.items() if not k.startswith("LEAN")}
    imports = list(dict.fromkeys(trusted_imports))
    rdir = Path(tempfile.mkdtemp(prefix="telperion_replay_"))        # 0700, outside any project
    try:
        for _attempt in range(2):
            nonce = f"TR{secrets.token_hex(16)}"
            try:
                src = render_replay_script(imports, targets, prefixes, callback_src, nonce, search, heartbeats,
                                           expect_oleans=expect, allow_axioms=allow_axioms, allow_sorry=allow_sorry)
            except ValueError as exc:
                return ReplayResult("ERROR", str(exc))
            f = rdir / "Replay.lean"
            f.write_text(src, encoding="utf-8")
            try:
                rc, out = run_lean([*prefix, "env", f"LEAN_PATH={os.pathsep.join(pinned.entries)}", pinned.lean,
                                    str(f)], rdir, timeout, env=env)
            except (OSError, subprocess.TimeoutExpired) as exc:
                return ReplayResult("ERROR", f"replay did not finish: {exc}")
            status, detail, lines, needs = parse_replay_output(out, nonce, rc)
            if status == "NEEDS":
                if any(n in imports for n in needs):
                    return ReplayResult("ERROR", f"replay still needs {needs} after importing them", [], out)
                imports += needs
                continue
            res = ReplayResult(status, detail, lines, out, parse_axioms(detail) if status == "OK" else None)
            if status == "OK":
                res.declared = parse_declared(detail)
                after = {m: olean_sha256(f) for m, f in resolved.items() if f}
                if after != before or len(before) != len(targets):
                    return ReplayResult("ERROR", "a target .olean changed during the run, or was not resolved", lines,
                                        out)
                res.olean_sha256 = after
            return res
        return ReplayResult("ERROR", f"replay needs more trusted modules after one retry: {detail}", [], out)
    finally:
        shutil.rmtree(rdir, ignore_errors=True)
