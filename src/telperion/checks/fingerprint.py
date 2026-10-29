"""Statement fingerprint: a sha256 of what a theorem SAYS, insensitive to how its binders and universes are named.

WHAT IS HASHED. The theorem's type, after ``Lean.Meta.deltaExpand`` has unfolded every DEFINITION (``defnInfo``) that
lies outside the library roots, serialized STRUCTURALLY by ``tpSer``: an explicitly tagged, injective rendering of the
``Expr`` tree. Bound variables are de Bruijn indices, so binder names never appear. Binder info (default, implicit,
strict implicit, instance) is kept, because it is part of the meaning. Universe levels are serialized structurally
(zero, succ, max, imax), and level parameters are numbered by position in the target's ``levelParams``, so renaming
``u`` to ``v`` keeps the hash. Constant names are serialized component by component, each one quoted (not with
``Name.toString``, which prints a component containing ``»`` raw and so is not injective), and ``mdata`` is dropped.
Nothing goes through the pretty-printer. Constants declared in a non-library module always unfold. ``whnf`` is never
used, because it would unfold library constants too.

WHAT IS REFUSED (fail closed, ``FP-REFUSED``, a ValueError).
  * Any non-library constant still left after unfolding, which would be hashed by its NAME alone: a local inductive,
    constructor, recursor, structure (also through a projection's structure name), axiom, opaque, quotient or theorem,
    and an ``irreducible_def`` (whose wrapper is an opaque structure). Hashing an inductive's full declaration closure
    would let these through, but that is a later extension.
  * ``sorryAx`` anywhere in the statement; a free or meta variable; a level parameter that is not the target's own.
  * An unfolded statement of more than ``2^22`` nodes (``too-large``), counted DAG-linearly before serializing, so a
    chain of doubling definitions is refused in seconds instead of serialized exponentially.
  * A refused replay (below): an untrusted module whose constants the kernel rejects, a target .olean that does not
    resolve to the file Python hashed (``body-olean-mismatch`` for a body), or a process import outside the trusted
    prefixes (``untrusted-library-module``).

REPLAY ISOLATION (owner decision "Replay-isolate", Ruling 9). The fingerprint never imports an untrusted module. The
targets' modules are loaded by ``lean_replay.run_replay``: the script imports only trusted modules from the PINNED env
(``trusted_env``, default ``$TELPERION_LEAN_ENV``, checked against its trusted manifest), the untrusted modules'
constants are KERNEL-REPLAYED into it (no initializers, elaborators, attributes or other extensions), and
``tpFingerprint`` runs as the replay's callback. A module counts as library only when it is one of the trusted imports
(``getModuleIdxFor?``); a replayed constant has no module index, so it is never library and always unfolds. Missing
extensions cannot change the hash, which is a function of the kernel's Exprs. Imports given by name that resolve to a
trusted .olean are imported; every other import is a replay target. As a cheap pre-check, the project (outside
``.lake`` and ``.git``) must contain no symlink and no directory or ``.lean`` file named after a library root.

OLEAN BINDING. Each replayed target's .olean parts are hashed before and after the run (``olean_sha256``); the Lean
side must resolve the module to exactly that file. ``run_fingerprint`` returns a ``Fingerprints`` dict whose
``olean_sha256`` maps each replayed module to that hash.

SEPARATION AND NONCE. ``run_fingerprint_on_text`` compiles the submitted text as its OWN module first, under a random
per-run name in a private 0700 temp dir (``<pinned lean> -R <dir>/src -o <dir>/build/TelperionFpBody_<id>.olean``),
so its ``#eval``, ``#exit`` and ``IO.Process.exit`` run at that compile and never in the fingerprint run, and it
cannot branch on a predictable module name. It then REPLAYS that olean like any other target. Every Lean call reaps
its whole process group when it returns (``lean_run``). A fresh 128-bit nonce is generated AFTER the body compile and
carried by every marker; Python requires exactly one nonce'd result per target and a final ``FP-DONE <nonce>``, and
refuses duplicates and foreign markers.

TRUST BOUNDARY: THIS IS NOT A SANDBOX. ``run_fingerprint_on_text``, like any build of untrusted Lean, RUNS that code
with the caller's permissions: it can read and rewrite any file the caller can (the trusted env's oleans included,
which the manifest check then catches only if it happened before the check), open network connections, or ``setsid``
a daemon that the group reaping cannot see. Untrusted text must only be fingerprinted inside a sandbox (e.g.
Comparator's Linux sandbox in CI). Nor is the fingerprint a defence against a malicious pinned env; closure_audit
checks closures.
"""
from __future__ import annotations

import hashlib
import os
import secrets
import shutil
import subprocess
import tempfile
from pathlib import Path

from ..closure_audit import DEFAULT_LIBRARY_ROOTS, lean_name_literal
from . import lean_replay
from .lean_replay import default_wrapper, pinned_env, resolve_olean, submission_paths, under_prefix
from .lean_run import run_lean

LIBRARY_ROOTS: tuple[str, ...] = DEFAULT_LIBRARY_ROOTS
BODY_MODULE = "TelperionFpBody"
SIZE_CAP = 2 ** 22

ROOTS_DEF = "def tpRoots : List Name := __ROOTS__\n"

# The Lean helpers, shared by the script and the serializer unit test. They need `tpRoots` in scope.
HELPERS = """
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

def tpCap : Nat := __CAP__

abbrev TpSizeM := StateM (Std.HashMap Expr Nat × Std.HashMap Level Nat)

/-- Tree size of a level, memoized (DAG-linear), saturating at `tpCap + 1`. -/
partial def tpLevelSize (l : Level) : TpSizeM Nat := do
  if let some n := (← get).2[l]? then return n
  let n ← match l with
    | .succ a => pure <| 1 + (← tpLevelSize a)
    | .max a b => pure <| 1 + (← tpLevelSize a) + (← tpLevelSize b)
    | .imax a b => pure <| 1 + (← tpLevelSize a) + (← tpLevelSize b)
    | _ => pure 1
  let n := min n (tpCap + 1)
  modify fun (m, lm) => (m, lm.insert l n)
  return n

/-- Tree size of an expression (what `tpSer` would walk), memoized (DAG-linear), saturating at `tpCap + 1`. -/
partial def tpSize (e : Expr) : TpSizeM Nat := do
  if let some n := (← get).1[e]? then return n
  let n ← match e with
    | .app f a => pure <| 1 + (← tpSize f) + (← tpSize a)
    | .lam _ t b _ => pure <| 1 + (← tpSize t) + (← tpSize b)
    | .forallE _ t b _ => pure <| 1 + (← tpSize t) + (← tpSize b)
    | .letE _ t v b _ => pure <| 1 + (← tpSize t) + (← tpSize v) + (← tpSize b)
    | .mdata _ b => tpSize b
    | .proj _ _ b => pure <| 1 + (← tpSize b)
    | .sort u => pure <| 1 + (← tpLevelSize u)
    | .const _ us => pure <| 1 + (← us.foldlM (fun acc u => do pure (acc + (← tpLevelSize u))) 0)
    | _ => pure 1
  let n := min n (tpCap + 1)
  modify fun (m, lm) => (m.insert e n, lm)
  return n

/-- The first thing left after unfolding that cannot be hashed: `sorryAx`, a non-library constant or projection
structure, or a free or meta variable. Memoized on visited subterms. -/
partial def tpOffense (env : Environment) (e : Expr) : StateM (Std.HashSet Expr) (Option (String × String)) := do
  if (← get).contains e then return none
  modify (·.insert e)
  match e with
  | .const n _ =>
    if n == ``sorryAx then return some ("sorryAx", "sorry")
    return if tpIsLib env n then none else some (n.toString, tpKind (env.find? n))
  | .proj s _ b =>
    if tpIsLib env s then tpOffense env b else return some (s.toString, tpKind (env.find? s))
  | .fvar _ => return some ("free-variable", "fvar")
  | .mvar _ => return some ("metavariable", "mvar")
  | .app f a => return (← tpOffense env f) <|> (← tpOffense env a)
  | .lam _ t b _ => return (← tpOffense env t) <|> (← tpOffense env b)
  | .forallE _ t b _ => return (← tpOffense env t) <|> (← tpOffense env b)
  | .letE _ t v b _ => return (← tpOffense env t) <|> (← tpOffense env v) <|> (← tpOffense env b)
  | .mdata _ b => tpOffense env b
  | _ => return none

/-- Injective: every component is self-delimiting (a quoted string, or `#` and a number). -/
partial def tpSerName : Name → String
  | .anonymous => "_"
  | .str p s => tpSerName p ++ "." ++ s.quote
  | .num p n => tpSerName p ++ "#" ++ toString n

abbrev TpSerM := StateT String (Except String)

def tpEmit (s : String) : TpSerM Unit := modify (· ++ s)

partial def tpSerLevel (lps : List Name) : Level → TpSerM Unit
  | .zero => tpEmit "z"
  | .succ l => do tpEmit "(S "; tpSerLevel lps l; tpEmit ")"
  | .max a b => do tpEmit "(M "; tpSerLevel lps a; tpEmit " "; tpSerLevel lps b; tpEmit ")"
  | .imax a b => do tpEmit "(I "; tpSerLevel lps a; tpEmit " "; tpSerLevel lps b; tpEmit ")"
  | .param n => match lps.idxOf? n with
    | some i => tpEmit s!"(P {i})"
    | none => throw s!"level-param-{n}"
  | .mvar _ => throw "level-metavariable"

def tpSerBi : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Appends to the state string (linear, so a deep term is not re-copied at every level). -/
partial def tpSer (lps : List Name) : Expr → TpSerM Unit
  | .bvar i => tpEmit s!"(b {i})"
  | .fvar _ => throw "free-variable"
  | .mvar _ => throw "metavariable"
  | .sort u => do tpEmit "(s "; tpSerLevel lps u; tpEmit ")"
  | .const n us => do
    tpEmit s!"(c {tpSerName n} ["
    let mut first := true
    for u in us do
      unless first do tpEmit " "
      first := false
      tpSerLevel lps u
    tpEmit "])"
  | .app f a => do tpEmit "(a "; tpSer lps f; tpEmit " "; tpSer lps a; tpEmit ")"
  | .lam _ t b bi => do tpEmit s!"(l {tpSerBi bi} "; tpSer lps t; tpEmit " "; tpSer lps b; tpEmit ")"
  | .forallE _ t b bi => do tpEmit s!"(p {tpSerBi bi} "; tpSer lps t; tpEmit " "; tpSer lps b; tpEmit ")"
  | .letE _ t v b nd => do
    tpEmit "(t "; tpSer lps t; tpEmit " "; tpSer lps v; tpEmit " "; tpSer lps b; tpEmit s!" {nd})"
  | .lit (.natVal n) => tpEmit s!"(n {n})"
  | .lit (.strVal s) => tpEmit s!"(str {s.quote})"
  | .mdata _ e => tpSer lps e
  | .proj s i e => do tpEmit s!"(j {tpSerName s} {i} "; tpSer lps e; tpEmit ")"

/-- The fingerprint of `ci`'s statement in `env`: `.ok <serialization>` or `.error "<what> <why>"` (a refusal).
Self-contained: it needs only `env` and `tpRoots`, so a loader that builds `env` some other way can call it. -/
def tpFingerprint (env : Environment) (ci : ConstantInfo) : IO (Except String String) := do
  let (e, _) ← (deltaExpand ci.type (fun n => !tpIsLib env n && tpIsDef env n)).toIO
    { fileName := "<fingerprint>", fileMap := default, maxRecDepth := 100000 } { env }
  let n := Id.run ((tpSize e).run' ({}, {}))
  if n > tpCap then
    return .error s!"too-large {n} nodes (counted up to the cap {tpCap} + 1)"
  match Id.run ((tpOffense env e).run' {}) with
  | some (c, k) =>
    let uses := ci.type.getUsedConstants.filter (!tpIsLib env ·) |>.toList.map toString
    return .error s!"{c} {k} (statement uses: {", ".intercalate uses})"
  | none =>
    match (tpSer ci.levelParams e).run "" with
    | .error msg => return .error s!"{msg} unserializable"
    | .ok ((), s) => return .ok s
""".replace("__CAP__", str(SIZE_CAP))

_CALLBACK = """
def tpNonce : String := "__NONCE__"

open Lean Meta Elab Term in
def TelperionReplay.callback : TermElabM Unit := do
  let env ← getEnv
  for t in (__TARGETS__ : List Name) do
    match env.find? t with
    | none => IO.println s!"FP-MISSING {tpNonce} {t}"
    | some ci =>
      match ← tpFingerprint env ci with
      | .error why => IO.println s!"FP-REFUSED {tpNonce} {t} {why}"
      | .ok s => IO.println s!"FP-BEGIN {tpNonce} {t}\\n{s}\\nFP-END {tpNonce} {t}"
  IO.println s!"FP-DONE {tpNonce}"
"""


def _names(names) -> str:
    return "[" + ", ".join(lean_name_literal(n) for n in names) + "]"


def render_fingerprint_callback(targets: list[str], nonce: str,
                                library_roots: tuple[str, ...] = LIBRARY_ROOTS) -> str:
    """The replay callback that prints, per target, one nonce'd ``FP-BEGIN``/``FP-END`` block, ``FP-REFUSED`` or
    ``FP-MISSING``, then ``FP-DONE <nonce>``. Trusted code, elaborated before the replay."""
    return (ROOTS_DEF.replace("__ROOTS__", _names(library_roots)) + HELPERS
            + _CALLBACK.replace("__NONCE__", nonce).replace("__TARGETS__", _names(targets)))


def parse_fingerprints(output: str, nonce: str) -> dict[str, str]:
    """Map each target to the sha256 hex of its serialization (the text between its markers, stripped).

    Every line starting with ``FP-`` is a marker and must carry ``nonce``; the last marker must be the only
    ``FP-DONE``. Raises ValueError on a foreign marker, a missing or early ``FP-DONE``, a duplicate block, an
    ``FP-MISSING`` or ``FP-REFUSED`` target, an unterminated block, or an empty serialization."""
    lines = output.splitlines()
    marks = [(i, ln.split(" ", 2)) for i, ln in enumerate(lines) if ln.startswith("FP-")]
    foreign = [lines[i] for i, parts in marks if len(parts) < 2 or parts[1] != nonce]
    if foreign:
        raise ValueError(f"marker without this run's nonce (spoofed output?): {foreign[0][:200]!r}")
    dones = [i for i, parts in marks if parts[0] == "FP-DONE"]
    if len(dones) != 1 or dones[0] != marks[-1][0]:
        raise ValueError(f"expected exactly one FP-DONE {nonce}, after every other marker; got {len(dones)}")
    rest = {i: parts[2] if len(parts) > 2 else "" for i, parts in marks}
    missing = [rest[i] for i, parts in marks if parts[0] == "FP-MISSING"]
    if missing:
        raise ValueError(f"target not found: {', '.join(missing)}")
    refused = [rest[i] for i, parts in marks if parts[0] == "FP-REFUSED"]
    if refused:
        raise ValueError("refused (fail closed: the statement cannot be hashed faithfully; <target> <what> <why>): "
                         + "; ".join(refused))
    out: dict[str, str] = {}
    begins = [i for i, parts in marks if parts[0] == "FP-BEGIN"]
    for i in begins:
        target = rest[i]
        try:
            end = lines.index(f"FP-END {nonce} {target}", i + 1)
        except ValueError:
            raise ValueError(f"unterminated fingerprint block for {target}") from None
        if any(i < j < end for j, _ in marks):
            raise ValueError(f"marker inside the fingerprint block for {target}")
        canon = "\n".join(lines[i + 1:end]).strip()
        if not canon:
            raise ValueError(f"empty serialization for {target}")
        if target in out:
            raise ValueError(f"duplicate fingerprint block for {target}")
        out[target] = hashlib.sha256(canon.encode("utf-8")).hexdigest()
    return out


def _precheck(project: Path, library_roots: tuple[str, ...]) -> None:
    """Refuse a project (outside ``.lake``/``.git``) with a symlink, or a directory or ``.lean`` file named after a
    library root. Under replay such modules could only be untrusted targets anyway; this check is cheap and runs
    first."""
    for dirpath, dirnames, filenames in os.walk(project):
        dirnames[:] = sorted(d for d in dirnames if d not in (".lake", ".git"))
        for name in dirnames + sorted(filenames):
            p = Path(dirpath, name)
            if p.is_symlink():
                raise ValueError(f"project contains a symlink ({p}); refusing, since it could bring in modules under "
                                 "a library root")
        spoofed = [Path(dirpath, d) for d in dirnames if d in library_roots]
        spoofed += [Path(dirpath, f) for f in filenames if f.endswith(".lean") and f[:-5] in library_roots]
        if spoofed:
            raise ValueError(f"project declares modules under a library root ({', '.join(map(str, spoofed))}); they "
                             "would be trusted as library and never unfolded")


class Fingerprints(dict):
    """target -> sha256 of its serialized statement; ``olean_sha256`` maps each replayed module to its olean hash."""

    def __init__(self, fps=(), olean_sha256=None):
        super().__init__(fps)
        self.olean_sha256: dict[str, str] = dict(olean_sha256 or {})


def _compile_body(body: str, module: str, cdir: Path, search: list[str], prefix: list[str], lean: str,
                  timeout: int) -> Path:
    """Compile `body` as `module` into `cdir/build` with the pinned lean (no lake); return the olean."""
    (cdir / "src").mkdir()
    (cdir / "build").mkdir()
    src = cdir / "src" / f"{module}.lean"
    src.write_text(body, encoding="utf-8")
    olean = cdir / "build" / f"{module}.olean"
    env = {k: v for k, v in os.environ.items() if not k.startswith("LEAN")}
    try:
        rc, out = run_lean([*prefix, "env", f"LEAN_PATH={os.pathsep.join(search)}", lean, "-R", str(cdir / "src"),
                            "-o", str(olean), str(src)], cdir, timeout, env=env)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValueError(f"body compile did not finish: {exc}") from None
    if rc != 0 or not olean.is_file():
        raise ValueError(f"body did not compile (exit {rc}{'' if olean.is_file() else ', no olean written'}):"
                         f"\n{out[-4000:]}")
    return olean


def _fingerprint(project: Path, imports: list[str], targets: list[str], wrapper: list[str] | None, timeout: int,
                 body: str | None = None, trusted: list[str] | None = None, trusted_env: Path | None = None,
                 expect_body_olean: str | None = None, manifest=None, untrusted_paths=(),
                 elan_home=None) -> Fingerprints:
    """Compile ``body`` (if given) as a randomly named module in a private temp dir, then replay the untrusted
    imports (or the body) and fingerprint ``targets`` in the replay callback. ``trusted`` and ``expect_body_olean``
    override the trusted prefixes given to the script and the expected body olean (tests only)."""
    project = Path(project)
    _precheck(project, LIBRARY_ROOTS)
    pinned = pinned_env(trusted_env, elan_home)
    prefix = default_wrapper() if wrapper is None else list(wrapper)
    # a project that IS the pinned env adds no submission dir: its own build dir is a trusted prefix
    proj = None if os.path.realpath(project) == pinned.root else project
    untrusted = submission_paths(proj, untrusted_paths)
    cdir = Path(tempfile.mkdtemp(prefix="telperion_fp_")) if body is not None else None
    try:
        expect = None
        if body is not None:
            module = f"{BODY_MODULE}_{secrets.token_hex(8)}"
            olean = _compile_body(body, module, cdir, [*pinned.entries, *untrusted], prefix, pinned.lean, timeout)
            untrusted = [os.path.realpath(cdir / "build"), *untrusted]
            imports = [module]
            if expect_body_olean is not None:
                expect = {module: expect_body_olean}
        search = [*pinned.entries, pinned.libdir, *untrusted]
        trusted_imps, replayed = [], []
        for m in imports:
            f = resolve_olean(search, m)
            (trusted_imps if f and under_prefix(f, pinned.prefixes) else replayed).append(m)
        nonce = secrets.token_hex(16)                           # only now: the body compile cannot have seen it
        r = lean_replay.run_replay(replayed, render_fingerprint_callback(targets, nonce), project=None,
                                   untrusted_paths=untrusted, trusted_imports=["Mathlib", *trusted_imps],
                                   trusted_env=pinned.root, manifest=manifest, elan_home=elan_home, wrapper=prefix,
                                   timeout=timeout, allow_axioms=True, allow_sorry=True, expect_oleans=expect,
                                   prefixes_override=trusted)
    finally:
        if cdir is not None:
            shutil.rmtree(cdir, ignore_errors=True)
    if r.status == "FAILED":
        detail = r.detail.replace("olean-mismatch", "body-olean-mismatch") if body is not None else r.detail
        raise ValueError(f"replay refused: {detail}")
    if r.status != "OK":
        raise ValueError(f"fingerprint run failed: {r.detail}")
    fps = parse_fingerprints(r.output, nonce)
    keys = {t: t if t in fps else _escaped(t) for t in targets}
    absent = [t for t, k in keys.items() if k not in fps]
    if absent:
        raise ValueError(f"no fingerprint printed for {', '.join(absent)}:\n{r.output[-4000:]}")
    return Fingerprints({t: fps[k] for t, k in keys.items()}, r.olean_sha256)


def _escaped(target: str) -> str:
    """The target as Lean prints a Name (``Foo.«bar baz»``)."""
    try:
        return lean_name_literal(target)[1:]
    except ValueError:
        return target


def run_fingerprint(project: Path, imports: list[str], targets: list[str], wrapper: list[str] | None = None,
                    timeout: int = 1800, trusted_env: Path | None = None, manifest=None,
                    untrusted_paths=()) -> Fingerprints:
    """Fingerprint ``targets`` declared in ``imports`` (modules built in ``project``'s ``.lake/build/lib/lean`` or in
    ``untrusted_paths``; an import that resolves to a trusted .olean is imported instead), trusting only the pinned
    ``trusted_env`` (default ``$TELPERION_LEAN_ENV``)."""
    return _fingerprint(project, imports, targets, wrapper, timeout, trusted_env=trusted_env, manifest=manifest,
                        untrusted_paths=untrusted_paths)


def run_fingerprint_on_text(project: Path, text: str, target: str, wrapper: list[str] | None = None,
                            timeout: int = 1800, trusted_env: Path | None = None, manifest=None) -> str:
    """Fingerprint ``target`` as declared in the Lean source ``text``, compiled as its own module and then replayed.

    NOT A SANDBOX: compiling ``text`` runs its code with the caller's permissions (see the module docstring)."""
    return _fingerprint(project, [], [target], wrapper, timeout, body=text, trusted_env=trusted_env,
                        manifest=manifest)[target]
