"""Negation probe: a cheap, one-sided sanity check on a theorem STATEMENT, run on the ELABORATED CONSTANT.

ISOLATION (owner decision "Replay-isolate", Ruling 9). The probe never imports the theorem's module: importing it
would run the module's ``initialize`` blocks and let its ``command_elab``/``tactic`` overrides elaborate the probe
itself, which a re-review used to forge verdicts. Instead, ``lean_replay.run_replay`` loads the module's constants by
KERNEL REPLAY into a process that imports only trusted modules (Mathlib, from the pinned env), and the probe runs as a
callback on that replayed environment. None of the module's code, extensions, instances, simp lemmas or notation is
loaded, so the probe can only get WEAKER (a missing instance means PROBE_ONLY, never a verdict). The statement is the
constant's type exactly as the kernel accepted it, so local definitions, `variable`s, erased instances and
namespace-first name resolution are as they were when the file was compiled. An earlier version re-rendered the
statement as TEXT and refuted true theorems (`open Nat` read a local `factorial` as `Nat.factorial`); no text denylist
could be made sound. The module must be built; an unbuilt module is ERROR ("build <module> first").

THE TARGET AND ITS STATEMENT (final review C1, C2). The theorem name reaches the generated Lean only as DATA: its
components are validated as plain identifiers and passed as JSON-escaped string literals to `Name.mkStr`, so no text
from a submission is ever spliced into the callback's source as syntax (`qualify` reads the artifact with comments and
string/char literals blanked, and refuses a namespace that is not a plain identifier). The target must be a theorem
(`thmInfo`); anything else is ERROR. Its type is then taken with every NON-library definition at its head, and at the
head of every ∀-body, delta-expanded (`unfoldHeads`; library = imported from a module under the fingerprint's roots, so
a replayed definition always unfolds): `theorem foo : Stmt` with `def Stmt : Prop := ∀ n, n < 0 → n = 7` is probed as
the ∀-statement, not as an opaque `Stmt` with nothing to probe. This deliberately narrows Ruling 8 ("do not reduce")
for non-library heads only: `¬`, `≠`, `⊆` and every other library head still stay closed (for the `false` probe and
the first witness check; the second witness check, ``reduced``, reduces them, which can only take WITNESSED away).

One replay run executes three probes in the callback (the witness probe in two checks), each check with its own budget
of 200000 heartbeats:

* ``false``    -- opens the (head-unfolded) type with ``forallBoundedTelescope`` over its PREMISES (below), runs a
  fixed tactic battery on a fresh goal ``False`` in that local context, kernel-checks the closed proof as an auxiliary
  theorem (synchronously: ``Elab.async`` off, so FALSE PROVED is printed only after the kernel accepted it) and
  collects its axioms. VACUOUS (the hypotheses contradict each other) needs a closed proof with no
  metavariables, no ``sorry`` and only ``comparator.CLEAN_AXIOMS``.
* ``negation`` -- plausible's API, called directly: ``Plausible.Testable.checkIO`` on the decorated type, through a
  trusted wrapper (``TelperionProbe.runCheck``) that maps plausible's ``TestResult`` VALUE to ``success``,
  ``gaveUp n`` or ``failure <counterexample>`` and is evaluated with ``evalExpr``. REFUTED is the ``failure``
  constructor of that value (whose type carries a proof of ``¬ p``), never a scan of printed text: nothing a module
  or a message prints can produce it. No ``Testable`` instance is PROBE_ONLY with a note. A statement that cannot be
  evaluated on the replayed environment (its decidability needs compiled code for a replayed definition, which replay
  never provides) is PROBE_ONLY with a note too. plausible's seed is fixed (``PLAUSIBLE_SEED``, named in a REFUTED's
  detail), so a REFUTED is reproducible.
* ``witness``  -- only with a caller-supplied term: the ∃-closure of the FULL ∀-telescope of the head-unfolded type
  (every ∀/→ binder, the conclusion's arrows included; ``¬`` and ``≠`` stay closed, as they are not ∀-binders) is
  built as an Expr, the witness is parsed and elaborated against it, kernel-checked (synchronously, as above) and
  axiom-audited the same way. WITNESSED says every antecedent is jointly satisfiable, so it needs at least one
  Prop-typed binder in that telescope: with none (`True`, a bare conjunction) there is nothing to witness, and it is
  ``WITNESS NOANTECEDENT``, PROBE_ONLY with a note. It does NOT use the premise split below, which the author controls
  (`theorem arrow (n) : n < 0 → n = 7` with ⟨0, trivial⟩ would otherwise be WITNESSED). A witness that does not
  elaborate, or that the kernel rejects, is ERROR. The witness is TRUSTED input: it is elaborated with the full
  elaborator in the check process (`by run_tac ...` can do arbitrary IO there), so it must never be pasted from a
  submission unread.
* ``reduced``  -- with a witness, a second, DOWNGRADE-ONLY check (step 6 Task 0, the step-4 C2 residual). The
  non-reducing telescope stops at any conclusion head that is not a ∀ and not a non-library definition, so a vacuous
  part under it was invisible: in `∀ m : ℕ, m = m → id (∀ n : ℕ, n < 0 → n = 7)` the pad `⟨0, rfl, trivial⟩` closed
  `∃ m, ∃ _ : m = m, True` and gave WITNESSED. So the SAME witness must also close the ∃-closure over the REDUCING
  telescope of the head-unfolded type (``reducedClosure``: ``forallTelescopeReducing`` at default transparency, which
  opens `id`, `¬`, `≠`, `let`, beta-redexes and every other head that whnf can unfold, descending into `∧` and `↔`,
  which whnf leaves closed), kernel-checked synchronously and axiom-audited like the first. Anything but ``REDUCED
  PROVED`` with clean axioms (a witness that does not elaborate there because reduction exposed an antecedent it does
  not cover, a timeout, a missing line) makes it PROBE_ONLY, "witness does not survive reduction"; it never makes
  anything WITNESSED and never touches the ``false`` probe (Ruling 8's premise split stays non-reducing). A cost: a
  true statement whose conclusion reduces to a negation (`¬ P`, `a ≠ b`) exposes `P` as an antecedent that cannot hold
  together with the others, so it is never WITNESSED and needs a sign-off. A witness can cover both closures at once
  with a tactic block, `by first | exact <for the first> | exact <for the reduced one>`. The reduced closure is built
  from ``expandLocal ty`` (every non-library definition delta-expanded everywhere), the same term ``allow`` walks.
* ``allow``    -- with a witness, the ATOMIC allowlist (fix rounds 2-3, Rulings 4-5; ``allowlistProblem``, in its
  own budget), which replaced fix round 1's denylist of unopened heads and round 2's "logical positions" rule, both
  beaten by reviews. Over the same reducing telescope and ∧ / ↔ descent: (1) every hypothesis is an atom or a
  conjunction of atoms; (2) every conclusion is an atom, and not all are `True`; (3) every data binder has a library
  type, and no binder is a proposition or predicate variable. An atom is a head in ``okHeads`` (`=`, `≤`, `<`, `≥`,
  `>`, `True`, `Nat.le`, `∣`) applied to library data with no proposition or predicate inside, and not an `=` between
  functions (funext can hide an empty domain; bundled maps are not covered). ``ALLOW OK`` is needed
  for WITNESSED; ``ALLOW OUTSIDE <why>`` is PROBE_ONLY "outside the WITNESSED allowlist", and a failed or timed-out
  walk (or a missing line) is PROBE_ONLY "allowlist check failed". Library definitions are trusted text, not walked.

PREMISES. In an elaborated type a binder `(h : P)` and an arrow `P → Q` in the conclusion are both ∀-binders; the
elaborator names an arrow's binder `a._@._internal._hyg.N`: in v4.35.0's `MacroScopesView`, name `a`, ctx exactly
`_internal` and no module (a macro's binders have ctx `_hygCtx` and the macro's module, measured). The
premises, used by the `false` probe only, are the leading binders up to the first explicit binder with exactly that
name (so `theorem t (h : P) : Q → False` has the premise `h` only, and `Q` stays in the conclusion). Binders a macro
introduced carry the macro's module instead, so they count as premises.
The telescope does not reduce: `¬ P`, `a ≠ b` and `s ⊆ t` in a conclusion stay closed (reducing would turn
`x + 1 ≠ 0` into the premise `x + 1 = 0`, prove False from it, and call a true theorem VACUOUS). A conclusion written
with NAMED binders (`: ∀ (m : ℕ) (h : m < 0), False`) is read as premises.

PROTOCOL. The callback prints, through the replay's nonce'd lines, ``PREMISES n``, exactly one ``FALSE``, one
``NEGATION`` and (with a witness) one ``WITNESS``, one ``REDUCED`` and one ``ALLOW`` result line (a missing
``REDUCED`` or ``ALLOW`` line is no WITNESSED, not an ERROR); the replay protocol around them (one REPLAY line, one
final DONE, all under a 128-bit per-run tag) is checked by ``lean_replay``. Anything else is ERROR. No untrusted code
with effects runs in the process (the negation probe evaluates the statement only through compiled TRUSTED code, and
a pure term has no IO bridge; see lean_replay), so nothing else can print under the tag.

ONE-SIDED BY DESIGN. VACUOUS and REFUTED rest on positive evidence (a kernel-checked proof of ``False``, a
counterexample value). Everything else is PROBE_ONLY: the battery failing to derive ``False`` and plausible failing to
find a counterexample say nothing about truth. ERROR means a probe failed for a reason other than its purpose (an
unbuilt module, an unknown constant, a witness that does not elaborate, a refused replay), so no verdict could be read.
A maxHeartbeats timeout in any probe is not an ERROR: that probe is inconclusive, and the verdict falls through to
PROBE_ONLY with a note. Exceeding Lean's ``--memory`` bound (lean_replay, default 8192 MB) inside a probe is caught by
that probe's budget like any other exception that escapes it: ``FALSE FAILED`` or ``NEGATION UNAVAILABLE`` (PROBE_ONLY
with a note), ``WITNESS FAILED`` (ERROR) or ``REDUCED FAILED`` (PROBE_ONLY), never VACUOUS, REFUTED or WITNESSED;
exceeding it in the replay itself is ERROR. An axiom declared anywhere in the module's untrusted closure is refused by
the replay (Ruling 10: no untrusted axiom ever enters an environment that tactics run in), which is ERROR naming the
axiom.

KNOWN LIMITATION. A `private` theorem's constant has a mangled name and is not found by its source name (ERROR).
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from ..closure_audit import DEFAULT_LIBRARY_ROOTS, lean_name_literal
from ..comparator import CLEAN_AXIOMS
from . import lean_replay
from .lean_replay import ReplayResult, default_wrapper  # noqa: F401  (default_wrapper: shared by the checks)

VERDICTS = ("VACUOUS", "REFUTED", "PROBE_ONLY", "WITNESSED", "ERROR")

FALSE_TACTIC = "first | (exfalso; omega) | linarith | (simp_all; done) | (norm_num at *; done) | aesop"
NUM_INST = 200
PLAUSIBLE_SEED = 271828          # fixed, so a REFUTED is reproducible
HEARTBEATS = 200000
TACTIC_IMPORTS = ("Mathlib",)

# The result statuses each probe may print. TIMEOUT (a maxHeartbeats exception) makes that probe inconclusive.
STATUSES = {
    "FALSE": ("PROVED", "FAILED", "INCOMPLETE", "TIMEOUT"),
    "NEGATION": ("SUCCESS", "GAVEUP", "FAILURE", "NO_TESTABLE", "UNAVAILABLE", "TIMEOUT"),
    "WITNESS": ("PROVED", "FAILED", "INCOMPLETE", "NOANTECEDENT", "TIMEOUT"),
    "REDUCED": ("PROVED", "FAILED", "INCOMPLETE", "TIMEOUT"),
    "ALLOW": ("OK", "OUTSIDE", "FAILED", "TIMEOUT"),
}
SURVIVE = "witness does not survive reduction"
ALLOWLIST = "outside the WITNESSED allowlist"


@dataclass
class ProbeResult:
    verdict: str
    detail: str
    olean_sha256: str | None = None   # lean_replay.closure_digest of the whole replayed untrusted closure
    olean_closure: list | None = None  # its sorted [module, part, sha256] list
    axioms: list | None = None         # the replay's collectAxioms over the target module's constants

    def to_json(self) -> dict:
        out = {"verdict": self.verdict, "detail": self.detail}
        if self.olean_sha256 is not None:
            out["olean_sha256"] = self.olean_sha256
            out["olean_closure"] = self.olean_closure
            out["axioms"] = self.axioms
        return out


@dataclass
class ProbeSpec:
    module: str                      # the theorem's own module, built in the project
    theorem: str                     # the constant's full name
    witness: str | None = None
    imports: tuple[str, ...] = field(default=TACTIC_IMPORTS)


# A Lean identifier component as the probe accepts it: a letter-like first character (letters, `_`, the Greek and
# letterlike-symbol ranges Lean allows; not λ, Π, Σ) and then letters, digits, `_`, `'`, `!`, `?` or subscripts.
# Anything else, including a «»-quoted component, is refused: the name only ever reaches Lean as DATA (string
# literals fed to `Name.mkStr`), but a component that is not a plain identifier never came from a real declaration.
_IDENT_START = r"[^\W\d]|[\u2100-\u214F\u1D00-\u1DBF]"
_IDENT_REST = r"[\w'!?\u2080-\u209C\u2100-\u214F\u1D00-\u1DBF]"
_IDENT_RE = re.compile(rf"(?:{_IDENT_START})(?:{_IDENT_REST})*")


def name_components(name: str) -> list[str]:
    """The components of a dotted Lean name, each validated as a plain identifier; ValueError otherwise."""
    parts = name.split(".")
    for c in parts:
        if not _IDENT_RE.fullmatch(c) or any(ch in c for ch in "λΠΣ"):
            raise ValueError(f"not a plain Lean name: {name!r} (component {c!r}); refusing it")
    return parts


def _lean_name_expr(name: str) -> str:
    """Lean source for the `Name` `name`, built from JSON-escaped string literals: data, never syntax."""
    comps = ", ".join(json.dumps(c, ensure_ascii=False) for c in name_components(name))
    return f"(([{comps}] : List String).foldl Lean.Name.mkStr Lean.Name.anonymous)"


def _lean_string(s: str) -> str:
    """A Lean string literal for `s`, using only escapes Lean's parser accepts (`\\\\`, `\\"`, `\\n`, `\\t`, `\\r`,
    `\\xHH`). JSON escaping is NOT a subset of Lean's: JSON writes U+0008 and U+000C as `\\b` and `\\f`, which Lean
    rejects (`isQuotableCharDefault`, Parser/Basic.lean), so every other control character goes out as `\\xHH`."""
    out = []
    for ch in s:
        if ch in '"\\':
            out.append("\\" + ch)
        elif ch in "\n\t\r":
            out.append({"\n": "\\n", "\t": "\\t", "\r": "\\r"}[ch])
        elif ord(ch) < 0x20 or ord(ch) == 0x7F:
            out.append(f"\\x{ord(ch):02x}")
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


# The callback's trusted helpers: the premise count (module docstring), plausible's result as a plain value, and a
# per-probe heartbeat budget that reports a maxHeartbeats exception as TIMEOUT and any other exception as `err`.
_HELPERS = """\
namespace TelperionProbe
open Lean Meta Elab Term

/-- Leading premise binders of a theorem type: up to the first explicit binder carrying the elaborator's arrow name
`a._@._internal._hyg.*` exactly. A macro's own scoped binder (`a._@.<Module>..._hygCtx...`) is a premise. -/
partial def premises : Expr → Nat
  | .forallE n _ b bi =>
    let v := extractMacroScopes n
    if bi == .default && n.hasMacroScopes && v.name == `a && v.ctx == `_internal && v.imported.isAnonymous then 0
    else premises b + 1
  | .mdata _ e => premises e
  | _ => 0

/-- The library roots (the fingerprint's): a constant is library iff it was imported from a module under one. -/
def roots : List Name := __ROOTS__

def isLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => roots.any (·.isPrefixOf (env.header.moduleNames[idx.toNat]!))
  | none => false

/-- The statement with every NON-library definition at its head, and at the head of every ∀-body, delta-expanded
(at most `fuel` steps along any path). A replayed definition has no module index, so it is never library and always
unfolds. `none` when the fuel runs out at a non-library definition head: the probe then refuses (fail closed) rather
than stop the telescope early. -/
partial def unfoldHeads (env : Environment) (fuel : Nat) : Expr → Option Expr
  | .forallE n t b bi => do return .forallE n t (← unfoldHeads env fuel b) bi
  | .mdata _ e => unfoldHeads env fuel e
  | e =>
    match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.defnInfo d) =>
        if isLib env c then some e
        else match fuel with
          | 0 => none
          | fuel + 1 => unfoldHeads env fuel ((d.value.instantiateLevelParams d.levelParams us).beta e.getAppArgs)
      | _ => some e
    | _ => some e

/-- `p ∧ q`, dropping a side that is `True` (it has nothing to witness). -/
def conj (p q : Expr) : MetaM Expr :=
  if p.isConstOf ``True then pure q else if q.isConstOf ``True then pure p else mkAppM ``And #[p, q]

/-- The ∃-closure of `e` over its REDUCING ∀-telescope: `forallTelescopeReducing`, so a body that is not a ∀ is put in
whnf at the ambient transparency (the callback sets default) and opened if that exposes one (`id`, `¬`, `let`, a
beta-redex, any unfoldable head). A body that whnf leaves as `∧` or `↔` (inductives, which reduction cannot open) is
descended into, `a ↔ b` as `(a → b) ∧ (b → a)`. Every binder, data or proof, gets an `∃`, as in the witness probe. -/
partial def reducedClosure (e : Expr) : MetaM Expr :=
  forallTelescopeReducing e fun xs body => do
    let inner ← match (← whnf body).getAppFnArgs with
      | (``And, #[a, b]) => conj (← reducedClosure a) (← reducedClosure b)
      | (``Iff, #[a, b]) => conj (← reducedClosure (← mkArrow a b)) (← reducedClosure (← mkArrow b a))
      | _ => pure (mkConst ``True)
    let mut out := inner
    for x in xs.reverse do
      out ← mkAppM ``Exists #[← mkLambdaFVars #[x] out]
    return out

/-! The witness allowlist (fix rounds 2-3, Rulings 4-5): ATOMIC. A witness counts only if the statement, expanded by
`expandLocal` (the same term the reduced closure is built from) and walked like `reducedClosure` (the same reducing
telescope, the same ∧ / ↔ descent), has: (1) every hypothesis an atom or a conjunction of atoms, (2) every conclusion
an atom, and not all of them `True`, (3) every data binder of a library type, and no binder that is a proposition or
a predicate. An atom is a head in `okHeads` applied to library data with no proposition or predicate inside. -/

/-- The statement with every NON-library definition delta-expanded everywhere (the fingerprint's predicate), so a
local definition or instance cannot hide a proposition: the one term both the reduced closure and the walk use. -/
def expandLocal (ty : Expr) : MetaM Expr := do
  let env ← getEnv
  deltaExpand ty fun n => !isLib env n && env.find? n matches some (.defnInfo _)

/-- The heads an atom may have. -/
def okHeads : List Name := [``Eq, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``True, ``Nat.le, ``Dvd.dvd]

def nonLib (n : Name) : MetaM (Option String) := do
  return if isLib (← getEnv) n then none else some s!"the non-library constant {n}"

/-- Why the data term `e` is not plain library data, or `none`: a subterm that is a proposition or a predicate (by its
type), or a non-library constant or structure. A proof is skipped (it carries no data); binders are instantiated, so
`inferType` never sees a loose bound variable. -/
partial def dataProblem (e : Expr) : MetaM (Option String) := do
  let ty ← inferType e
  if ← isProp ty then return none
  if ← isPropFormerType ty then return some s!"the proposition or predicate `{← ppExpr e}` inside data"
  match e with
  | .const n _ => nonLib n
  | .app .. =>
    for a in e.getAppArgs do
      if let some w ← dataProblem a then return some w
    match e.getAppFn with
    | .const n _ => nonLib n
    | .fvar _ => return none
    | f => dataProblem f
  | .lam n d b bi | .forallE n d b bi =>
    if let some w ← dataProblem d then return some w
    withLocalDecl n bi d fun x => dataProblem (b.instantiate1 x)
  | .letE _ t v b _ =>
    if let some w ← dataProblem t then return some w
    if let some w ← dataProblem v then return some w
    dataProblem (b.instantiate1 v)
  | .mdata _ b => dataProblem b
  | .proj sn _ b =>
    if let some w ← nonLib sn then return some w
    dataProblem b
  | _ => return none

/-- Why the proposition `t` is not an atom (a head in `okHeads` applied to library data), or `none`. -/
def atomProblem (what : String) (t : Expr) : MetaM (Option String) := do
  let t := t.consumeMData
  let .const n _ := t.getAppFn
    | return some s!"{what} `{← ppExpr t}` is not an atom (an allowed head applied to data)"
  unless okHeads.contains n do
    return some s!"{what} `{← ppExpr t}` is not an atom: its head {n} is not allowed"
  if n == ``Eq && t.getAppNumArgs == 3 && (← whnf t.appFn!.appFn!.appArg!).isForall then
    return some s!"{what} `{← ppExpr t}` is a function equality (funext can hide an empty domain)"
  for a in t.getAppArgs do
    if let some w ← dataProblem a then return some s!"{what} `{← ppExpr t}` has {w}"
  return none

/-- Rule 1: a hypothesis is an atom or a conjunction of atoms (no →, ↔, ¬, ∀, ∃, ∨ inside). -/
partial def hypProblem (t : Expr) : MetaM (Option String) := do
  match t.consumeMData.getAppFnArgs with
  | (``And, #[a, b]) =>
    if let some w ← hypProblem a then return some w
    hypProblem b
  | _ => atomProblem "a hypothesis" t

/-- Rules 1 and 3 for the type `t` of a binder of the telescope. -/
def binderProblem (t : Expr) : MetaM (Option String) := do
  if ← isProp t then hypProblem t
  else if ← isPropFormerType t then
    return some s!"a binder of type `{← ppExpr t}` (a proposition or predicate variable)"
  else match ← dataProblem t with
    | some w => return some s!"a binder type `{← ppExpr t}` has {w}"
    | none => return none

/-- The first rule `e` breaks, and whether some conclusion it reached is not `True`; walked like `reducedClosure`. -/
partial def allowWalk (e : Expr) : MetaM (Option String × Bool) :=
  forallTelescopeReducing e fun xs body => do
    for x in xs do
      if let some w ← binderProblem (← inferType x) then return (some w, false)
    match (← whnf body).getAppFnArgs with
    | (``And, #[a, b]) =>
      let (w, s) ← allowWalk a
      if w.isSome then return (w, s)
      let (w', s') ← allowWalk b
      return (w', s || s')
    | (``Iff, #[a, b]) =>
      let (w, s) ← allowWalk (← mkArrow a b)
      if w.isSome then return (w, s)
      let (w', s') ← allowWalk (← mkArrow b a)
      return (w', s || s')
    | _ =>
      let c := body.consumeMData
      return (← atomProblem "the conclusion" c, !c.isConstOf ``True)

/-- Why the expanded statement `e` is outside the witness allowlist, or `none` (rule 2 includes: not only `True`). -/
def allowlistProblem (e : Expr) : MetaM (Option String) := withTransparency .default do
  let (w, said) ← allowWalk e
  if w.isSome then return w
  if !said then return some "the conclusion is `True`: it says nothing"
  return none

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- plausible's `TestResult`, as a value with no proof in it. -/
inductive Outcome where
  | success
  | gaveUp (n : Nat)
  | failure (xs : List String)

def outcome {p : Prop} : Plausible.TestResult p → Outcome
  | .success _ => .success
  | .gaveUp n => .gaveUp n
  | .failure _ xs _ => .failure xs

/-- Run plausible's test suite on `p` and return its result's constructor. -/
def runCheck (p : Prop) [Plausible.Testable p] (cfg : Plausible.Configuration) : IO Outcome := do
  return outcome (← Plausible.Testable.checkIO p cfg)

/-- Run `x` with a fresh budget of __HEARTBEATS__ heartbeats. A maxHeartbeats exception prints `<kind> TIMEOUT`, any
other exception that escapes `x` prints `<kind> <err>`. -/
def budget (kind err : String) (x : TermElabM Unit) : TermElabM Unit :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := __HEARTBEATS__ * 1000 }) do
    withCurrHeartbeats do
      tryCatchRuntimeEx x fun ex => do
        let msg ← ex.toMessageData.toString
        if ex.isMaxHeartbeat then TelperionReplay.line s!"{kind} TIMEOUT {msg}"
        else TelperionReplay.line s!"{kind} {err} {msg}"

end TelperionProbe
""".replace("__HEARTBEATS__", str(HEARTBEATS)).replace(
    "__ROOTS__", "[" + ", ".join(lean_name_literal(r) for r in DEFAULT_LIBRARY_ROOTS) + "]")


def render_callback(theorem: str, witness: str | None) -> str:
    """The Lean source of the replay callback (``TelperionReplay.callback``) that runs the three probes on
    `theorem`'s constant. Trusted code: it is elaborated against the trusted imports before the replay."""
    target = _lean_name_expr(theorem)
    line = "TelperionReplay.line"
    sync = "withOptions (fun o => Elab.async.set o false) do"      # kernel-check BEFORE printing PROVED
    src = (
        f"{_HELPERS}\n"
        f"def TelperionProbe.target : Lean.Name := {target}\n\n"
        "open Lean Meta Elab Term in\n"
        "def TelperionReplay.callback : TermElabM Unit := do\n"
        f"  let some info := (← getEnv).find? TelperionProbe.target\n"
        f'    | {line} "MISSING"\n'
        f"  unless info matches .thmInfo _ do\n"
        f'    {line} s!"NOTTHEOREM {{TelperionProbe.kind info}}"\n'
        f"    return\n"
        f"  let some ty := TelperionProbe.unfoldHeads (← getEnv) 1000 info.type\n"
        f'    | {line} "UNFOLD_EXHAUSTED"\n'
        f"  let n := TelperionProbe.premises ty\n"
        f'  {line} s!"PREMISES {{n}}"\n'
        f'  TelperionProbe.budget "FALSE" "FAILED" do\n'
        f"    forallBoundedTelescope ty (some n) fun xs _ => do\n"
        f"      let g ← mkFreshExprMVar (Lean.mkConst ``False) .syntheticOpaque\n"
        f"      let msgs := (← getThe Core.State).messages\n"
        f"      try\n"
        f"        let tac ← `(tactic| {FALSE_TACTIC})\n"
        f"        let rest ← Tactic.run g.mvarId! (Tactic.evalTactic tac)\n"
        f"        synthesizeSyntheticMVarsNoPostponing\n"
        f"        let pf ← instantiateMVars g\n"
        f"        if !rest.isEmpty || pf.hasMVar || pf.hasSorry then\n"
        f'          {line} s!"FALSE INCOMPLETE goals={{rest.length}} mvars={{pf.hasMVar}} sorry={{pf.hasSorry}}"\n'
        f"        else\n"
        f"          let ty ← mkForallFVars xs (Lean.mkConst ``False)\n"
        f"          let val ← mkLambdaFVars xs pf\n"
        f"          {sync}\n"
        f"            addDecl (.thmDecl {{ name := `_telperion_probe_false, levelParams := info.levelParams,\n"
        f"                                type := ty, value := val }})\n"
        f"          let axs ← collectAxioms `_telperion_probe_false\n"
        f'          {line} s!"FALSE PROVED axioms={{axs.toList}}"\n'
        f"      catch ex =>\n"
        f'        {line} s!"FALSE FAILED {{← ex.toMessageData.toString}}"\n'
        f"      modifyThe Core.State fun s => {{ s with messages := msgs }}\n"
        f'  TelperionProbe.budget "NEGATION" "UNAVAILABLE" do\n'
        f"    let tgt' ← Plausible.Decorations.addDecorations ty\n"
        f"    let inst? ← try some <$> synthInstance (← mkAppM ``Plausible.Testable #[tgt']) catch _ => pure none\n"
        f"    match inst? with\n"
        f'    | none => {line} "NEGATION NO_TESTABLE"\n'
        f"    | some inst =>\n"
        f"      let cfg : Plausible.Configuration := {{ numInst := {NUM_INST}, quiet := true,\n"
        f"                                               randomSeed := some {PLAUSIBLE_SEED} }}\n"
        f"      let e ← mkAppOptM ``TelperionProbe.runCheck #[tgt', inst, toExpr cfg]\n"
        f"      let act ← unsafe evalExpr (IO TelperionProbe.Outcome)\n"
        f"        (mkApp (mkConst ``IO) (mkConst ``TelperionProbe.Outcome)) e\n"
        f"      match ← act with\n"
        f'      | .success => {line} "NEGATION SUCCESS"\n'
        f'      | .gaveUp k => {line} s!"NEGATION GAVEUP {{k}}"\n'
        f'      | .failure cs => {line} s!"NEGATION FAILURE {{"; ".intercalate cs}}"\n'
    )
    if witness is not None:
        src += (
            f'  TelperionProbe.budget "WITNESS" "FAILED" do\n'
            f"    let (ex, anyProp) ← forallTelescope ty fun xs _ => do\n"
            f"      let mut body := Lean.mkConst ``True\n"
            f"      for x in xs.reverse do\n"
            f"        body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]\n"
            f"      pure (body, ← xs.anyM fun x => do isProp (← inferType x))\n"
            f"    unless anyProp do\n"
            f'      {line} "WITNESS NOANTECEDENT"\n'
            f"      return\n"
            + _witness_check("WITNESS", "_telperion_probe_witness", witness)
            # step 6 Task 0: the same witness against the ∃-closure of the REDUCING telescope (downgrade only), built
            # from the expanded statement that the allowlist then walks in its own budget (fix round 3: R3, M7)
            + f"  let expanded ← IO.mkRef (none : Option Expr)\n"
            f'  TelperionProbe.budget "REDUCED" "FAILED" do\n'
            f"    let e ← TelperionProbe.expandLocal ty\n"
            f"    expanded.set (some e)\n"
            f"    let ex ← withTransparency .default (TelperionProbe.reducedClosure e)\n"
            + _witness_check("REDUCED", "_telperion_probe_reduced", witness)
            + f'  TelperionProbe.budget "ALLOW" "FAILED" do\n'
            f"    match ← expanded.get with\n"
            f'    | none => {line} "ALLOW FAILED the statement was not expanded (the reduced check stopped first)"\n'
            f"    | some e =>\n"
            f"      match ← TelperionProbe.allowlistProblem e with\n"
            f'      | some why => {line} s!"ALLOW OUTSIDE {{why}}"\n'
            f'      | none => {line} "ALLOW OK"\n'
        )
    return src


def _witness_check(kind: str, decl: str, witness: str) -> str:
    """The Lean lines, inside a probe's budget with the ∃-closure bound to `ex`, that parse the witness (a string
    literal: data), elaborate it against `ex`, add it as the auxiliary theorem `decl` (kernel-checked synchronously,
    before PROVED is printed), collect its axioms and print one `<kind>` result line."""
    line = "TelperionReplay.line"
    sync = "withOptions (fun o => Elab.async.set o false) do"
    return (
        f"    let msgs := (← getThe Core.State).messages\n"
        f"    try\n"
        f"      let stx ← match Parser.runParserCategory (← getEnv) `term {_lean_string(witness)} with\n"
        f"        | .ok s => pure s\n"
        f"        | .error e => throwError e\n"
        f"      let w ← withoutErrToSorry (elabTermEnsuringType stx (some ex))\n"
        f"      synthesizeSyntheticMVarsNoPostponing\n"
        f"      let w ← instantiateMVars w\n"
        f"      if w.hasMVar || w.hasSorry then\n"
        f'        {line} s!"{kind} INCOMPLETE mvars={{w.hasMVar}} sorry={{w.hasSorry}}"\n'
        f"      else\n"
        f"        {sync}\n"
        f"          addDecl (.thmDecl {{ name := `{decl}, levelParams := info.levelParams,\n"
        f"                              type := ex, value := w }})\n"
        f"        let axs ← collectAxioms `{decl}\n"
        f'        {line} s!"{kind} PROVED axioms={{axs.toList}}"\n'
        f"    catch e =>\n"
        f'      {line} s!"{kind} FAILED {{← e.toMessageData.toString}}"\n'
        f"    modifyThe Core.State fun s => {{ s with messages := msgs }}\n"
    )


def _axiom_problem(key: str, rest: str) -> str | None:
    """Why proved probe `key` does not count on axiom grounds (an axiom outside CLEAN_AXIOMS, or no readable list),
    or None when it counts."""
    m = re.match(r"axioms=\[([^\]]*)\]", rest)
    if not m:
        return f"probe '{key}' printed no axiom list; not counted"
    bad = [a.strip() for a in m.group(1).split(",") if a.strip() and a.strip() not in CLEAN_AXIOMS]
    return f"probe '{key}' used non-standard axioms {bad}; not counted" if bad else None


def _reduced_problem(reduced: list[tuple[str, str]]) -> str | None:
    """Why a witness that closed the non-reducing ∃-closure does not count after the reducing check (its `REDUCED`
    result line, at most one), or None when the same witness closed the reducing ∃-closure too, kernel-checked with
    clean axioms. Every other outcome, a missing line included, keeps it from WITNESSED (fail closed)."""
    if not reduced:
        return f"{SURVIVE}: the reducing check printed no REDUCED result line; not counted"
    status, rest = reduced[0]
    if status == "PROVED":
        bad = _axiom_problem("reduced", rest)
        return f"{SURVIVE}: {bad}" if bad else None
    if status == "TIMEOUT":
        return f"{SURVIVE}: the reducing check timed out at maxHeartbeats {HEARTBEATS} (inconclusive); not counted"
    if status == "INCOMPLETE":
        return f"{SURVIVE}: it left metavariables or sorry against the reducing telescope ({rest}); not counted"
    return (f"{SURVIVE}: it does not close the ∃-closure over the reducing telescope, so reduction exposes an "
            f"antecedent it does not cover: {rest[:300]}; not counted")


def _allow_problem(allow: list[tuple[str, str]]) -> str | None:
    """Why the statement keeps a checked witness from WITNESSED on allowlist grounds (its `ALLOW` line, at most one),
    or None for `ALLOW OK`. A missing line, a failure or a timeout of the walk is no WITNESSED either (fail closed)."""
    if not allow:
        return "allowlist check failed: no ALLOW result line; not counted"
    status, rest = allow[0]
    if status == "OK":
        return None
    if status == "OUTSIDE":
        return (f"{ALLOWLIST}: {rest[:300]}; the witness is not counted (anything outside the allowlist needs a "
                "sign-off)")
    if status == "TIMEOUT":
        return f"allowlist check failed: it timed out at maxHeartbeats {HEARTBEATS} (inconclusive); not counted"
    return f"allowlist check failed: {rest[:300]}; not counted"


def _results(lines: list[str], kind: str) -> list[tuple[str, str]]:
    out = []
    for ln in lines:
        m = re.match(rf"{kind} ([A-Z_]+)\b[ \t]*(.*)$", ln)
        if m:
            out.append((m.group(1), m.group(2)))
    return out


def classify(lines: list[str], witness: bool = False) -> ProbeResult:
    """The verdict from the callback's lines (tag already stripped): ERROR, then VACUOUS, REFUTED, WITNESSED,
    PROBE_ONLY. A probe with a TIMEOUT line is inconclusive and its other lines are not read; otherwise it must have
    exactly one result line with a known status. The `REDUCED` line (at most one, known status) is read only to
    decide whether a WITNESSED stands; see `_reduced_problem`."""
    if "MISSING" in lines:
        return ProbeResult("ERROR", "the constant is not in the replayed module (unknown or private name)")
    if "UNFOLD_EXHAUSTED" in lines:
        return ProbeResult("ERROR", "the statement's non-library definitions did not unfold within 1000 steps; "
                                    "refusing (an early stop could hide antecedents from the witness)")
    nothm = [ln for ln in lines if ln.startswith("NOTTHEOREM")]
    if nothm:
        return ProbeResult("ERROR", f"the target is a {nothm[0][len('NOTTHEOREM '):]}, not a theorem; probe the "
                                    "theorem that states it")
    kinds = ("FALSE", "NEGATION", "WITNESS") if witness else ("FALSE", "NEGATION")
    got: dict[str, tuple[str, str] | None] = {}
    timed_out = []
    for kind in kinds:
        res = _results(lines, kind)
        if any(st == "TIMEOUT" for st, _ in res):
            timed_out.append(kind.lower())
            got[kind] = None
            continue
        if not res:
            return ProbeResult("ERROR", f"{kind.lower()} probe printed no {kind} result line")
        if len(res) > 1:
            return ProbeResult("ERROR", f"{kind.lower()} probe printed {len(res)} {kind} result lines; "
                                        "refusing a duplicated protocol")
        if res[0][0] not in STATUSES[kind]:
            return ProbeResult("ERROR", f"{kind.lower()} probe printed an unknown status {res[0][0]!r}")
        got[kind] = res[0]
    reduced = _results(lines, "REDUCED") if witness else []     # optional: it can only take WITNESSED away
    if len(reduced) > 1:
        return ProbeResult("ERROR", f"reduced witness probe printed {len(reduced)} REDUCED result lines; refusing a "
                                    "duplicated protocol")
    if reduced and reduced[0][0] not in STATUSES["REDUCED"]:
        return ProbeResult("ERROR", f"reduced witness probe printed an unknown status {reduced[0][0]!r}")
    allow = _results(lines, "ALLOW") if witness else []
    if len(allow) > 1:
        return ProbeResult("ERROR", f"allowlist check printed {len(allow)} ALLOW result lines; refusing a duplicated "
                                    "protocol")
    if allow and allow[0][0] not in STATUSES["ALLOW"]:
        return ProbeResult("ERROR", f"allowlist check printed an unknown status {allow[0][0]!r}")
    if got.get("WITNESS") and got["WITNESS"][0] == "FAILED":
        return ProbeResult("ERROR", f"the witness does not check: {got['WITNESS'][1][:500]}")
    notes = [f"probe '{key}' timed out at maxHeartbeats {HEARTBEATS} (inconclusive)" for key in timed_out]
    prem = [m.group(1) for m in (re.fullmatch(r"PREMISES (\d+)", ln) for ln in lines) if m]
    premises = f"the {prem[-1]} premise(s)" if prem else "the premises"
    line = got["FALSE"]
    if line and line[0] == "PROVED":
        bad = _axiom_problem("false", line[1])
        if not bad:
            return ProbeResult("VACUOUS", f"{premises} alone prove False (kernel-checked, clean axioms)")
        notes.append(bad)
    elif line and line[0] == "INCOMPLETE":
        notes.append(f"probe 'false' left goals, metavariables or sorry ({line[1]}); not counted")
    neg = got["NEGATION"]
    if neg and neg[0] == "FAILURE":
        return ProbeResult("REFUTED", f"plausible found a counterexample (seed {PLAUSIBLE_SEED}): {neg[1]}")
    wline = got.get("WITNESS")
    if wline and wline[0] == "PROVED":
        bad = _axiom_problem("witness", wline[1]) or _reduced_problem(reduced) or _allow_problem(allow)
        if not bad:
            return ProbeResult("WITNESSED", f"the witness proves {premises} satisfiable, over the reducing telescope "
                               "too (kernel-checked, clean axioms); no counterexample found")
        notes.append(bad)
    elif wline and wline[0] == "INCOMPLETE":
        notes.append(f"probe 'witness' left metavariables or sorry ({wline[1]}); not counted")
    elif wline and wline[0] == "NOANTECEDENT":
        notes.append("probe 'witness' had nothing to witness: the statement (with its non-library definitions "
                     "unfolded) has no Prop-typed antecedent; not counted")
    if neg and neg[0] == "NO_TESTABLE":
        notes.append("negation probe did not run: no testable instance (e.g. ℝ), so no counterexample was searched for")
    elif neg and neg[0] == "UNAVAILABLE":
        notes.append("negation probe could not evaluate the statement on the replayed environment (module "
                     f"definitions have no compiled code there): {neg[1][:300]}")
    return ProbeResult("PROBE_ONLY", "; ".join(notes + [f"no contradiction derived from {premises} and no "
                                                        "counterexample found; one-sided, not evidence the claim is "
                                                        "true"]))


def classify_replay(r: ReplayResult, spec: ProbeSpec) -> ProbeResult:
    """The verdict of a replay run of the probe callback."""
    if r.status == "FAILED":
        ax = re.search(r"declares the axiom (\S+); refusing", r.detail)
        if ax:
            return ProbeResult("ERROR", f"module declares axiom {ax.group(1)}; untrusted axioms are refused by replay")
        if "build it first" in r.detail:
            return ProbeResult("ERROR", f"build {spec.module} first (lake build {spec.module}): {r.detail[:300]}")
        return ProbeResult("ERROR", f"the replay refused the module: {r.detail[:500]}")
    if r.status != "OK":
        return ProbeResult("ERROR", f"probe did not run: {r.detail[:1500]}")
    res = classify(r.lines, spec.witness is not None)
    res.olean_sha256, res.olean_closure, res.axioms = r.olean_sha256, r.olean_closure, r.axioms
    return res


def run_probe(spec: ProbeSpec, project: Path | None = None, wrapper: list[str] | None = None, timeout: int = 1800, *,
              untrusted_paths=(), trusted_env=None, manifest=None, elan_home=None,
              memory_mb: int | None = lean_replay.DEFAULT_MEMORY_MB) -> ProbeResult:
    """Replay `spec.module` (built in `project`'s ``.lake/build/lib/lean`` or in one of `untrusted_paths`) into the
    pinned `trusted_env` (default ``$TELPERION_LEAN_ENV``, checked against its trusted `manifest`) and run the probes
    as a callback; see the module docstring."""
    try:
        callback = render_callback(spec.theorem, spec.witness)
    except ValueError as exc:
        return ProbeResult("ERROR", str(exc))
    r = lean_replay.run_replay(spec.module, callback, project=project, untrusted_paths=untrusted_paths,
                               trusted_imports=spec.imports, trusted_env=trusted_env, manifest=manifest,
                               elan_home=elan_home, wrapper=wrapper, timeout=timeout, allow_sorry=True,
                               memory_mb=memory_mb)
    return classify_replay(r, spec)


def qualify(module_text: str, theorem: str) -> str:
    """`theorem` qualified by the namespace the file declares it in, when the file declares exactly one theorem/lemma
    of that (short) name; otherwise `theorem` unchanged. Only LOCATES the constant: the statement itself is always
    read from the elaborated constant, never from this text. The text is read with its comments AND string/char
    literals blanked (a `namespace` line inside a string is not a command), and the result must be a plain dotted
    identifier (ValueError otherwise): untrusted text never reaches the callback's source as syntax."""
    from ..missions import judge

    ga = judge._guard_anchors()
    name_components(theorem)
    code = ga.blank_lean_code(module_text)       # the shared lexer: comments and string/char literals blanked
    pat = re.compile(r"(?<![\w.'])(?:theorem|lemma)\s+" + re.escape(theorem) + r"(?![\w.'])")
    names = {".".join([*ga._namespace_at(code, m.start()), theorem]) for m in pat.finditer(code)}
    out = names.pop() if len(names) == 1 else theorem
    name_components(out)
    return out
