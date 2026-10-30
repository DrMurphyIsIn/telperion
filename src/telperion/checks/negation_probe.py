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
for non-library heads only: `¬`, `≠`, `⊆` and every other library head still stay closed.

One replay run executes three probes in the callback, each with its own budget of 200000 heartbeats:

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
``NEGATION`` and (with a witness) one ``WITNESS`` result line; the replay protocol around them (one REPLAY line, one
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
with a note), or ``WITNESS FAILED`` (ERROR), never VACUOUS, REFUTED or WITNESSED; exceeding it in the replay itself is
ERROR. An axiom declared anywhere in the module's untrusted closure is refused by the replay (Ruling
10: no untrusted axiom ever enters an environment that tactics run in), which is ERROR naming the axiom.

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
}


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
    """A Lean string literal for `s` (JSON escaping is a subset of Lean's string escapes)."""
    return json.dumps(s, ensure_ascii=False)


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
(at most `fuel` steps). A replayed definition has no module index, so it is never library and always unfolds. -/
partial def unfoldHeads (env : Environment) (fuel : Nat) : Expr → Expr
  | .forallE n t b bi => .forallE n t (unfoldHeads env fuel b) bi
  | .mdata _ e => unfoldHeads env fuel e
  | e =>
    match fuel, e.getAppFn with
    | fuel + 1, .const c us =>
      match env.find? c with
      | some (.defnInfo d) =>
        if isLib env c then e
        else unfoldHeads env fuel ((d.value.instantiateLevelParams d.levelParams us).beta e.getAppArgs)
      | _ => e
    | _, _ => e

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
        f"  let ty := TelperionProbe.unfoldHeads (← getEnv) 1000 info.type\n"
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
            f"    let msgs := (← getThe Core.State).messages\n"
            f"    try\n"
            f"      let stx ← match Parser.runParserCategory (← getEnv) `term {_lean_string(witness)} with\n"
            f"        | .ok s => pure s\n"
            f"        | .error e => throwError e\n"
            f"      let w ← withoutErrToSorry (elabTermEnsuringType stx (some ex))\n"
            f"      synthesizeSyntheticMVarsNoPostponing\n"
            f"      let w ← instantiateMVars w\n"
            f"      if w.hasMVar || w.hasSorry then\n"
            f'        {line} s!"WITNESS INCOMPLETE mvars={{w.hasMVar}} sorry={{w.hasSorry}}"\n'
            f"      else\n"
            f"        {sync}\n"
            f"          addDecl (.thmDecl {{ name := `_telperion_probe_witness, levelParams := info.levelParams,\n"
            f"                              type := ex, value := w }})\n"
            f"        let axs ← collectAxioms `_telperion_probe_witness\n"
            f'        {line} s!"WITNESS PROVED axioms={{axs.toList}}"\n'
            f"    catch e =>\n"
            f'      {line} s!"WITNESS FAILED {{← e.toMessageData.toString}}"\n'
            f"    modifyThe Core.State fun s => {{ s with messages := msgs }}\n"
        )
    return src


def _axiom_problem(key: str, rest: str) -> str | None:
    """Why proved probe `key` does not count on axiom grounds (an axiom outside CLEAN_AXIOMS, or no readable list),
    or None when it counts."""
    m = re.match(r"axioms=\[([^\]]*)\]", rest)
    if not m:
        return f"probe '{key}' printed no axiom list; not counted"
    bad = [a.strip() for a in m.group(1).split(",") if a.strip() and a.strip() not in CLEAN_AXIOMS]
    return f"probe '{key}' used non-standard axioms {bad}; not counted" if bad else None


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
    exactly one result line with a known status."""
    if "MISSING" in lines:
        return ProbeResult("ERROR", "the constant is not in the replayed module (unknown or private name)")
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
        bad = _axiom_problem("witness", wline[1])
        if not bad:
            return ProbeResult("WITNESSED", f"the witness proves {premises} satisfiable (kernel-checked, clean "
                               "axioms); no counterexample found")
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


def _code_only(text: str) -> str:
    """Lean source with comments and string/char literals blanked (newlines kept, so line starts stay line starts).
    One left-to-right pass in Lean's lexing order: `--` and nested `/- -/` comments, `"..."` with escapes, raw strings
    `r#*"..."#*`, and char literals `'x'` / `'\\x'` (so `'"'` does not open a string)."""
    out, i, n = [], 0, len(text)

    def blank(seg: str) -> str:
        return "".join("\n" if ch == "\n" else " " for ch in seg)
    while i < n:
        ch = text[i]
        prev = text[i - 1] if i else " "
        ident_prev = prev.isalnum() or prev in "_'!?.»"
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(text[i:j]))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(text[i:j]))
            i = j
        elif ch == "r" and not ident_prev and re.match(r'r#*"', text[i:]):
            hashes = re.match(r"r(#*)", text[i:]).group(1)
            start = i + 1 + len(hashes) + 1
            end = text.find('"' + hashes, start)
            j = n if end < 0 else end + 1 + len(hashes)
            out.append('""' + blank(text[start:max(start, j - 1 - len(hashes))]))
            i = j
        elif ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""' + blank(text[i + 1:j]))
            i = j + 1
        elif ch == "'" and not ident_prev and re.match(r"'(?:\\.|\\u\{[0-9a-fA-F]+\}|[^\\'])'", text[i:]):
            m = re.match(r"'(?:\\.|\\u\{[0-9a-fA-F]+\}|[^\\'])'", text[i:])
            out.append("' '")
            i += m.end()
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def qualify(module_text: str, theorem: str) -> str:
    """`theorem` qualified by the namespace the file declares it in, when the file declares exactly one theorem/lemma
    of that (short) name; otherwise `theorem` unchanged. Only LOCATES the constant: the statement itself is always
    read from the elaborated constant, never from this text. The text is read with its comments AND string/char
    literals blanked (a `namespace` line inside a string is not a command), and the result must be a plain dotted
    identifier (ValueError otherwise): untrusted text never reaches the callback's source as syntax."""
    from ..missions import judge

    ga = judge._guard_anchors()
    name_components(theorem)
    code = _code_only(module_text)
    pat = re.compile(r"(?<![\w.'])(?:theorem|lemma)\s+" + re.escape(theorem) + r"(?![\w.'])")
    names = {".".join([*ga._namespace_at(code, m.start()), theorem]) for m in pat.finditer(code)}
    out = names.pop() if len(names) == 1 else theorem
    name_components(out)
    return out
