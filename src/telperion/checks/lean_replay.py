"""Kernel-replay loader: put an UNTRUSTED module's constants in front of a check without running any of its code.

WHY. A check that writes ``import <the theorem's module>`` hands that module the check process: Lean runs its
``initialize`` blocks while importing, and its ``@[command_elab ...]``, ``@[tactic ...]``, macro and attribute
registrations then elaborate the check's own commands. A security re-review showed such a module reading the per-run
nonce from the check's source and printing forged result lines. No nonce or output filter helps against code that runs
in the same process.

HOW (the Comparator / lean4checker approach). The generated script imports TRUSTED modules only (Mathlib, Plausible,
Lean, ...) and is run by ``lean`` with a LEAN_PATH that holds only trusted directories, so no ``import`` can reach an
untrusted ``.olean``. Inside one ``#eval`` it then:

1. checks that every module the process imported resolves to an ``.olean`` whose realpath lies under a trusted
   prefix (``lean --print-libdir`` plus the env's pinned package build dirs, passed in by Python);
2. walks the target module's import closure over the FULL search path, given to the script as data. A module whose
   ``.olean`` realpath is under a trusted prefix is trusted and must already be imported (the same file); if it is
   not, the script asks for it (``REPLAY NEEDS``) and Python reruns once with it added. Every other module is
   UNTRUSTED, whatever its name (``Mathlib.Evil`` outside the prefixes is untrusted), and is read with
   ``Lean.readModuleData`` (all three parts for a ``module``-system file): data only, nothing is executed;
3. adds the untrusted constants by the replay loop of ``Lean.Kernel.Environment.replay`` (toolchain
   ``src/lean/Lean/Replay.lean:74-190``), ported into the script so that it adds to the ELABORATOR's environment
   through ``Lean.Environment.addDeclCore`` (``Lean/Environment.lean:699``, ``doCheck := true``). Every declaration
   goes to the kernel, and constructors and recursors are compared with the ones the kernel generates. A kernel
   rejection is ``REPLAY FAILED``. (The upstream function returns a ``Kernel.Environment``, and the only way back,
   ``Environment.ofKernelEnv`` at ``Lean/Environment.lean:643``, drops the import's realization context: ``omega``
   then fails with ``Environment.realizeConst: realizedImportedConsts is empty``.);
4. runs the caller's callback, a ``TermElabM Unit`` named ``TelperionReplay.callback``, in the replayed environment.

WHAT IS NOT LOADED, ON PURPOSE. Replay transfers constants only. The untrusted modules' environment extensions are
never read: no initializers, elaborators, macros, syntax, attributes, instances, simp lemmas, notation or docstrings.
So a callback sees the untrusted constants but none of their registrations, and a probe can only get WEAKER (a tactic
that needed a local instance or simp lemma fails), which callers must read as fail-closed (PROBE_ONLY, or a
fingerprint, which hashes Exprs and is unaffected). Unsafe and ``partial`` constants are skipped by replay
(``Replay.lean:180-183``); anything that uses one then fails to replay. The callback itself is elaborated BEFORE the
replay, against the trusted environment only, so it cannot name an untrusted constant except as a ``Name`` literal.

PROTOCOL. Every line the script prints starts with ``<nonce>-``, a 128-bit per-run tag that exists only after every
untrusted file was written, and messages are flattened to one line. Exactly one ``REPLAY OK|FAILED|NEEDS`` line, then
the callback's lines, then exactly one final ``DONE``. Anything else is ERROR. Since no untrusted code runs, the tag is
now meaningful; callers must still derive results from values their callback computed, never from logged text.

OUT OF SCOPE. The ``.olean`` reader trusts its input (it is a memory image); a crafted ``.olean`` is a memory-safety
attack on this process, and the build that produced it must be sandboxed so that it cannot rewrite the trusted
oleans either. Comparator's export-to-text route closes the first; this loader does not.
"""
from __future__ import annotations

import json
import os
import re
import secrets
import shutil
import signal
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from ..closure_audit import lean_name_literal

# Mathlib's pinned dependency set; their build dirs under `<project>/.lake/packages/` are trusted.
TRUSTED_PACKAGES = ("mathlib", "batteries", "aesop", "plausible", "Qq", "proofwidgets", "importGraph",
                    "LeanSearchClient", "Cli")
REPLAY_DIR_PREFIX = ".telperion_replay_"
STATUSES = ("OK", "FAILED", "ERROR")

_MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


@dataclass
class ReplayResult:
    status: str                        # OK (replayed, callback ran), FAILED (replay refused), ERROR (no verdict)
    detail: str
    lines: list[str] = field(default_factory=list)   # the callback's lines, tag stripped, in order
    output: str = ""


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


_SCRIPT = r"""__IMPORTS__
import Lean

open Lean Meta Elab Term

namespace TelperionReplay

def tag : String := __TAG__
def targetModule : Name := __TARGET__
def trustedPrefixes : List String := __PREFIXES__
def searchPath : List System.FilePath := (__SEARCH__ : List String).map System.FilePath.mk

/-- One protocol line: the tag, then `s` flattened to a single line. -/
def line (s : String) : IO Unit :=
  IO.println s!"{tag}-{(s.replace "\n" " ").replace "\r" " "}"

def isTrustedFile (f : System.FilePath) : IO Bool := do
  let r := (← IO.FS.realPath f).toString
  return trustedPrefixes.any fun pre =>
    r == pre || r.startsWith (if pre.endsWith "/" then pre else pre ++ "/")

/-- The first search-path entry that holds `m`'s `.olean` (per file, not per package root). -/
def locate (m : Name) : IO (Option System.FilePath) := do
  for d in searchPath do
    let f := modToFilePath d m "olean"
    if ← f.pathExists then return some f
  return none

/-- Why this process's own imports are not all trusted, if they are not. -/
def checkLoaded (env : Environment) : IO (Option String) := do
  for m in env.header.moduleNames do
    let f ← findOLean m
    unless ← isTrustedFile f do
      return some s!"the check imported {m} from {f}, outside the trusted prefixes"
  return none

/-- All parts of a module's `.olean`: one for a plain file, three (exported, server, private) for a `module`. -/
def readParts (f : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let main ← readModuleData f
  if !main.1.isModule then return #[main]
  readModuleDataParts #[f, OLeanLevel.server.adjustFileName f, OLeanLevel.private.adjustFileName f]

structure Closure where
  modules : Array Name := #[]                       -- untrusted, in discovery order
  consts : Std.HashMap Name ConstantInfo := {}
  needs : Array Name := #[]                         -- trusted modules this process did not import

/-- The target's import closure: trusted modules stop the walk, untrusted ones are read as data. -/
def collect (env : Environment) : ExceptT String IO Closure := do
  let mut todo : Array Name := #[targetModule]
  let mut seen : NameSet := {}
  let mut out : Closure := {}
  repeat
    let some m := todo.back? | break
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    let some f ← locate m
      | throw s!"module {m} has no .olean in the search path (build it first)"
    if ← isTrustedFile f then
      if m == targetModule then
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
    let parts ← readParts f
    let some (data, _) := parts.back? | throw s!"{f}: no module data"
    for i in data.imports do
      todo := todo.push i.module
    for c in data.constants do
      if out.consts.contains c.name then
        throw s!"constant {c.name} is declared twice in the untrusted closure"
      out := { out with consts := out.consts.insert c.name c }
    out := { out with modules := out.modules.push m }
  return out

/-!
The replay loop below is ported from Lean v4.35.0 `src/lean/Lean/Replay.lean` (`Lean.Kernel.Environment.replay`,
Copyright (c) 2023 Kim Morrison, released under Apache 2.0). The one change: it adds to the elaborator's
`Environment` through `Lean.Environment.addDeclCore` (`Lean/Environment.lean:699`, `doCheck := true`, which runs the
kernel check) instead of to a bare `Kernel.Environment`, because `Environment.ofKernelEnv` drops the import's
realization context and tactics then fail (`Environment.realizeConst: realizedImportedConsts is empty`). Every
declaration still goes to the kernel; constructors and recursors are compared with the kernel-generated ones.
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

def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 0 d none with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throw <| .userError <| (← ex.toMessageData {} |>.toString)

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read)[name]? | unreachable!
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
          let all ← info.all.mapM fun n => do pure <| ((← read)[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do pure ((← read)[n]!))
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
          setEnv env'
          TelperionReplay.line s!"REPLAY OK modules={c.modules.toList} constants={c.consts.size}"
          -- A fresh heartbeat budget (replay's allocations must not use it up); a runtime exception (heartbeats,
          -- deep recursion) is caught too, so that DONE is still printed.
          withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := __HEARTBEATS__ * 1000 }) do
            withCurrHeartbeats do
              tryCatchRuntimeEx TelperionReplay.callback fun ex => do
                TelperionReplay.line s!"CALLBACK FAILED {← ex.toMessageData.toString}"
  TelperionReplay.line "DONE"
"""


def render_replay_script(trusted_imports, target_module: str, trusted_prefixes, callback_src: str, nonce: str,
                         search_path=(), heartbeats: int = 200000) -> str:
    """The Lean script that replays `target_module`'s untrusted closure and then runs `callback_src`.

    `callback_src` is trusted Lean source (ours, never the module's) that must define
    ``TelperionReplay.callback : Lean.Elab.Term.TermElabM Unit``; it prints through ``TelperionReplay.line``.
    `search_path` is the full olean search path, in order, that the closure is resolved over; it is DATA here and is
    never this process's LEAN_PATH. The callback runs with a fresh budget of `heartbeats` (thousands, as the
    ``maxHeartbeats`` option); an exception it raises, a runtime one included, is reported as ``CALLBACK FAILED``."""
    if not re.fullmatch(r"[A-Za-z0-9]+", nonce):
        raise ValueError(f"nonce must be alphanumeric: {nonce!r}")
    imports = "\n".join(f"import {_module(m)}" for m in trusted_imports)
    return (_SCRIPT.replace("__IMPORTS__", imports)
            .replace("__TAG__", json.dumps(nonce))
            .replace("__TARGET__", lean_name_literal(_module(target_module)))
            .replace("__PREFIXES__", _lean_strings(_realpath(p).rstrip("/") or "/" for p in trusted_prefixes))
            .replace("__SEARCH__", _lean_strings(search_path))
            .replace("__HEARTBEATS__", str(int(heartbeats)))
            .replace("__CALLBACK__", callback_src))


def parse_replay_output(output: str, nonce: str, rc: int = 0) -> tuple[str, str, list[str], list[str]]:
    """(status, detail, callback lines, needed modules) from a run's output. Only lines carrying `nonce` count.

    status is OK, FAILED, NEEDS or ERROR. ERROR when the protocol is broken: not exactly one REPLAY line first, not
    exactly one DONE as the last tagged line, a callback line without REPLAY OK, a nonzero exit, or a
    ``CALLBACK FAILED`` line (the callback lines are still returned)."""
    tagged = [m.group(1) for m in re.finditer(rf"(?m)^{re.escape(nonce)}-(.*)$", output)]
    replay = [t for t in tagged if re.match(r"REPLAY (OK|FAILED|NEEDS)\b", t)]
    if len(replay) != 1:
        return "ERROR", f"printed {len(replay)} REPLAY lines (want exactly one): {output.strip()[-1500:]!r}", [], []
    if tagged.count("DONE") != 1 or tagged[-1] != "DONE" or tagged[0] != replay[0]:
        return "ERROR", f"protocol broken (no single final DONE after a first REPLAY line): {output.strip()[-1500:]!r}", [], []
    if rc != 0:
        return "ERROR", f"lean exited {rc}: {output.strip()[-1500:]!r}", [], []
    kind, _, rest = replay[0][len("REPLAY "):].partition(" ")
    body = tagged[1:-1]
    if kind == "NEEDS":
        return ("ERROR", "callback lines after REPLAY NEEDS", [], []) if body else ("NEEDS", rest, [], rest.split())
    if kind == "FAILED":
        return ("ERROR", "callback lines after REPLAY FAILED", [], []) if body else ("FAILED", rest, [], [])
    failed = [t for t in body if t.startswith("CALLBACK FAILED")]
    if failed:
        return "ERROR", f"the callback failed: {failed[0][len('CALLBACK FAILED '):]}", body, []
    return "OK", rest, body, []


def _run(cmd: list[str], cwd: Path, timeout: int) -> tuple[int, str]:
    """(returncode, stdout + stderr) of `cmd` in its own session; on the wall-clock timeout the whole process group
    gets SIGTERM, then SIGKILL 5 s later, and TimeoutExpired is re-raised. The same logic as lean_run.run_lean
    (uncommitted when this was written); to be consolidated onto it."""
    p = subprocess.Popen(cmd, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    try:
        out, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        for sig in (signal.SIGTERM, signal.SIGKILL):
            try:
                os.killpg(p.pid, sig)
            except ProcessLookupError:
                break
            try:
                p.communicate(timeout=5)
                break
            except subprocess.TimeoutExpired:
                continue
        p.wait()
        raise
    return p.returncode, out + err


def default_wrapper() -> list[str]:
    lock = os.path.expanduser("~/hodge-engine/leanlock.sh")
    return ["env", "ARDA_LEAN_SLOTS=1", lock] if os.path.exists(lock) else []


def trusted_prefixes(project: Path, packages=TRUSTED_PACKAGES, timeout: int = 120) -> list[str]:
    """realpaths of the toolchain's lib dir (``lean --print-libdir`` in `project`) and of each listed package's
    build dir under `<project>/.lake/packages/` that exists."""
    rc, out = _run(["lean", "--print-libdir"], Path(project), timeout)
    libdir = out.strip().splitlines()[-1] if out.strip() else ""
    if rc != 0 or not os.path.isdir(libdir):
        raise ValueError(f"lean --print-libdir failed in {project}: {out.strip()[-500:]!r}")
    out_dirs = [_realpath(libdir)]
    for pkg in packages:
        d = Path(project) / ".lake" / "packages" / pkg / ".lake" / "build" / "lib" / "lean"
        if d.is_dir():
            out_dirs.append(_realpath(d))
    return out_dirs


def project_search_path(project: Path, extra_lean_path: str = "", timeout: int = 300) -> list[str]:
    """The olean search path `lake env` gives in `project` (with `extra_lean_path` appended, as lake does)."""
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    if extra_lean_path:
        env["LEAN_PATH"] = extra_lean_path
    p = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, env=env, capture_output=True,
                       text=True, timeout=timeout)
    if p.returncode != 0:
        raise ValueError(f"lake env failed in {project}: {(p.stdout + p.stderr).strip()[-500:]!r}")
    return [e for e in p.stdout.strip().split(os.pathsep) if e]


def run_replay(project: Path, target_module: str, callback_src: str, trusted_imports=("Mathlib",),
               extra_lean_path: str = "", wrapper: list[str] | None = None, timeout: int = 1800,
               prefixes: list[str] | None = None, heartbeats: int = 200000) -> ReplayResult:
    """Replay `target_module` (built somewhere on `project`'s lake search path plus `extra_lean_path`) into a process
    that imports only `trusted_imports`, then run `callback_src` (see render_replay_script).

    The script runs as ``lean`` (through `wrapper`, leanlock by default) with LEAN_PATH set to the TRUSTED search-path
    entries only. If the closure needs a trusted module that is not imported, it is added and the run repeated once."""
    project = Path(project)
    prefix = default_wrapper() if wrapper is None else list(wrapper)
    try:
        prefixes = trusted_prefixes(project) if prefixes is None else list(prefixes)
        search = project_search_path(project, extra_lean_path)
    except (OSError, subprocess.TimeoutExpired, ValueError) as exc:
        return ReplayResult("ERROR", f"cannot set up the replay: {exc}")
    trusted, _untrusted = split_search_path(search, prefixes)
    imports = list(dict.fromkeys(trusted_imports))
    rdir = Path(tempfile.mkdtemp(prefix=REPLAY_DIR_PREFIX, dir=project))
    try:
        for _attempt in range(2):
            nonce = f"TR{secrets.token_hex(16)}"
            try:
                src = render_replay_script(imports, target_module, prefixes, callback_src, nonce, search, heartbeats)
            except ValueError as exc:
                return ReplayResult("ERROR", str(exc))
            f = rdir / "Replay.lean"
            f.write_text(src, encoding="utf-8")
            try:
                rc, out = _run([*prefix, "env", f"LEAN_PATH={os.pathsep.join(trusted)}", "lean", str(f)], project,
                               timeout)
            except (OSError, subprocess.TimeoutExpired) as exc:
                return ReplayResult("ERROR", f"replay did not finish: {exc}")
            status, detail, lines, needs = parse_replay_output(out, nonce, rc)
            if status != "NEEDS":
                return ReplayResult(status, detail, lines, out)
            if any(n in imports for n in needs):
                return ReplayResult("ERROR", f"replay still needs {needs} after importing them", [], out)
            imports += needs
        return ReplayResult("ERROR", f"replay needs more trusted modules after one retry: {detail}", [], out)
    finally:
        shutil.rmtree(rdir, ignore_errors=True)
