"""Negation probe: a cheap, one-sided sanity check on a theorem STATEMENT, run on the ELABORATED CONSTANT.

The probe imports the theorem's own BUILT module (plus Mathlib, for the tactics) and takes the statement from the
constant's type, so nothing from the source is re-elaborated. Local definitions, notation, `local`/`scoped` attributes,
erased instances, `variable`s and namespace-first name resolution are therefore exactly as they were when the file
was compiled: the type the probe sees is the type the kernel accepted. An earlier version re-rendered the binders and
conclusion as TEXT in a re-created `namespace`/`open` context; in `namespace Foo; open Nat; def factorial ...` that
text read `factorial` as `Nat.factorial` and refuted a true theorem, and no text denylist of "dangerous" commands
could be made sound (`public def`, two commands on one line, `with_weak_namespace`, a `'"'` literal, `run_cmd`,
`attribute [-instance]`, ...). The module must be built in the project; an unbuilt module is ERROR ("build <module>
first").

Three small Lean files are run with `lake env lean` in that project:

* ``false``    -- a MetaM metaprogram. It opens the constant's type with ``forallBoundedTelescope`` over its PREMISES
  (below), runs a fixed tactic battery on a fresh goal ``False`` in that local context, kernel-checks the closed proof
  as an auxiliary theorem and collects its axioms. VACUOUS (the hypotheses contradict each other) needs a closed proof
  with no metavariables, no ``sorry`` and only ``comparator.CLEAN_AXIOMS``.
* ``negation`` -- ``example : type_of% @T := by plausible``. ``type_of% @T`` elaborates to exactly the constant's type.
  If plausible's error opens with its ``Found a counter-example!`` banner, the claim is REFUTED at a concrete point.
* ``witness``  -- only with a caller-supplied term: the ∃-closure of the premises (``∃ x₁ … xₙ, True``) is built as an
  Expr, the witness is parsed and elaborated against it, kernel-checked and axiom-audited the same way. WITNESSED says
  the hypotheses are jointly satisfiable. A witness that does not elaborate is ERROR.

PREMISES. In an elaborated type a binder `(h : P)` and an arrow `P → Q` in the conclusion are both ∀-binders; the
elaborator names an arrow's binder with a hygienic `a✝`. The premises are the leading binders up to the first explicit
binder with that name (so `theorem t (h : P) : Q → False` has the premise `h` only, and `Q` stays in the conclusion).
The telescope does not reduce: `¬ P`, `a ≠ b` and `s ⊆ t` in a conclusion stay closed (reducing would turn
`x + 1 ≠ 0` into the premise `x + 1 = 0`, prove False from it, and call a true theorem VACUOUS). A conclusion written
with NAMED binders (`: ∀ (m : ℕ) (h : m < 0), False`) is read as premises.

The metaprograms report through lines `<tag>-FALSE PROVED axioms=[...]`, `<tag>-FALSE FAILED <msg>`,
`<tag>-FALSE INCOMPLETE ...` (and `-WITNESS` likewise), then a final `<tag>-DONE`, where the tag carries a 128-bit
per-run nonce. A line with any other tag is ignored (the imported module's own `#eval`s ran at ITS compile, not here,
and the nonce makes that structural); a probe without exactly one result line and exactly one final DONE is ERROR.

ONE-SIDED BY DESIGN. VACUOUS and REFUTED rest on positive evidence (a kernel-checked proof of ``False``, a printed
counterexample). Everything else is PROBE_ONLY: the battery failing to derive ``False`` and plausible failing to find a
counterexample say nothing about truth. ERROR means a probe failed for a reason other than its purpose (an unbuilt
module, an unknown constant, a witness that does not elaborate), so no verdict could be read. A maxHeartbeats timeout in
any probe is not an ERROR: that probe is inconclusive, and the verdict falls through to PROBE_ONLY with a note.

KNOWN LIMITATION. A `private` theorem's constant has a mangled name and is not found by its source name (ERROR).
"""
from __future__ import annotations

import os
import re
import secrets
import shutil
import signal
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from ..comparator import CLEAN_AXIOMS

VERDICTS = ("VACUOUS", "REFUTED", "PROBE_ONLY", "WITNESSED", "ERROR")

FALSE_TACTIC = "first | (exfalso; omega) | linarith | (simp_all; done) | (norm_num at *; done) | aesop"
PLAUSIBLE = "plausible (config := { numInst := 200 })"
COUNTEREXAMPLE = "Found a counter-example!"
NO_TESTABLE = "Failed to create a `testable` instance"
PROBE_DIR = ".telperion_probe"
TACTIC_IMPORTS = ("Mathlib",)

# Errors the `negation` probe is EXPECTED to produce when it finds nothing: plausible giving up, finding no
# counterexample, or having no `Testable` instance for the claim (a real variable, an undecidable hypothesis). The
# last one is raised only after the statement elaborated, so it never hides an elaboration error. The counterexample
# itself is reported as an error too, and is the probe's purpose (matched on its banner, see `_banner`).
NEGATION_PURPOSE_ERRORS = (
    "Gave up",
    "gave up",
    "Unable to find",
    NO_TESTABLE,
)

# The `false` and `witness` metaprograms catch their own tactic/elaboration failures and report them on protocol
# lines, so any error Lean prints for them is unrelated to their purpose.
PURPOSE_ERRORS = {"false": (), "negation": NEGATION_PURPOSE_ERRORS, "witness": ()}

# A maxHeartbeats timeout in ANY probe makes that probe inconclusive, never an ERROR: hypotheses that are merely hard
# for the battery must not block a grant. The metaprograms' `try`/`catch` does not catch it (a runtime exception), so
# it surfaces as an error of the probe file. A timed-out probe is never read as proved, refuted or witnessed.
TIMEOUT_ERROR = "maximum number of heartbeats"

# Lean's report of an `import` it cannot find: the module was never built in this project.
_UNBUILT_RE = re.compile(r"unknown module prefix|object file .* does not exist|No directory .* or file .*\.olean")

# A message header: `file:line:col: error:` from lean, or a bare `error:` from lake. v4.35.0 also tags some messages
# with a code, `error(lean.unknownIdentifier):`; missing those would let an error pass unnoticed.
_MSG_RE = re.compile(r"(?m)^(?:\S[^\n]*?:\d+:\d+: )?(error|warning|info)(?:\([^)\n]*\))?:")
# plausible's counterexample error opens with a rule of `=` and then the banner; the phrase anywhere else (a string
# literal in the statement, say) is not a counterexample.
_BANNER_RE = re.compile(r"\s*(?:=+\s*)?" + re.escape(COUNTEREXAMPLE))


@dataclass
class ProbeResult:
    verdict: str
    detail: str

    def to_json(self) -> dict:
        return {"verdict": self.verdict, "detail": self.detail}


@dataclass
class ProbeSpec:
    module: str                      # the theorem's own module, built in the project
    theorem: str                     # the constant's full name
    witness: str | None = None
    imports: tuple[str, ...] = field(default=TACTIC_IMPORTS)


def _lean_name(name: str) -> str:
    """`name` with every component in «», so any component spelling is a valid identifier."""
    if "«" in name:
        return name
    return ".".join(f"«{c}»" for c in name.split("."))


def _lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


# Shared by the `false` and `witness` metaprograms: the number of leading premise binders (module docstring).
_PREMISES = """\
namespace TelperionProbe
open Lean in
/-- Leading premise binders of a theorem type: up to the first explicit binder named like an arrow's (`a✝`). -/
partial def premises : Expr → Nat
  | .forallE n _ b bi =>
    if bi == .default && n.hasMacroScopes && n.eraseMacroScopes == `a then 0 else premises b + 1
  | .mdata _ e => premises e
  | _ => 0
end TelperionProbe
"""


def render_probes(module: str, theorem: str, witness: str | None, imports: tuple[str, ...] = TACTIC_IMPORTS,
                  tag: str = "TP") -> dict[str, str]:
    """Lean source for each probe, keyed "false", "negation" and (with a witness) "witness"."""
    head = "".join(f"import {m}\n" for m in (*imports, module) if m) + "\n"
    opts = "set_option maxHeartbeats 200000 in\n"
    t = _lean_name(theorem)
    meta = "open Lean Meta Elab Term in\n" + opts + "#eval show TermElabM Unit from do\n"
    false_src = (
        f"{head}{_PREMISES}\n{meta}"
        f"  let info ← getConstInfo `{t}\n"
        f"  let n := TelperionProbe.premises info.type\n"
        f'  IO.println s!"{tag}-PREMISES {{n}}"\n'
        f"  forallBoundedTelescope info.type (some n) fun xs _ => do\n"
        f"    let g ← mkFreshExprMVar (Lean.mkConst ``False) .syntheticOpaque\n"
        f"    let msgs := (← getThe Core.State).messages\n"
        f"    try\n"
        f"      let tac ← `(tactic| {FALSE_TACTIC})\n"
        f"      let rest ← Tactic.run g.mvarId! (Tactic.evalTactic tac)\n"
        f"      synthesizeSyntheticMVarsNoPostponing\n"
        f"      let pf ← instantiateMVars g\n"
        f"      if !rest.isEmpty || pf.hasMVar || pf.hasSorry then\n"
        f'        IO.println s!"{tag}-FALSE INCOMPLETE goals={{rest.length}} mvars={{pf.hasMVar}} '
        f'sorry={{pf.hasSorry}}"\n'
        f"      else\n"
        f"        let ty ← mkForallFVars xs (Lean.mkConst ``False)\n"
        f"        let val ← mkLambdaFVars xs pf\n"
        f"        addDecl (.thmDecl {{ name := `_telperion_probe_false, levelParams := info.levelParams,\n"
        f"                            type := ty, value := val }})\n"
        f"        let axs ← collectAxioms `_telperion_probe_false\n"
        f'        IO.println s!"{tag}-FALSE PROVED axioms={{axs.toList}}"\n'
        f"    catch ex =>\n"
        f'      IO.println s!"{tag}-FALSE FAILED {{(← ex.toMessageData.toString).replace "\\n" " "}}"\n'
        f"    modifyThe Core.State fun s => {{ s with messages := msgs }}\n"
        f'  IO.println "{tag}-DONE"\n'
    )
    src = {
        "false": false_src,
        "negation": f"{head}{opts}example : type_of% @{t} := by {PLAUSIBLE}\n",
    }
    if witness is not None:
        src["witness"] = (
            f"{head}{_PREMISES}\n{meta}"
            f"  let info ← getConstInfo `{t}\n"
            f"  let n := TelperionProbe.premises info.type\n"
            f"  let ex ← forallBoundedTelescope info.type (some n) fun xs _ => do\n"
            f"    let mut body := Lean.mkConst ``True\n"
            f"    for x in xs.reverse do\n"
            f"      body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]\n"
            f"    pure body\n"
            f"  let msgs := (← getThe Core.State).messages\n"
            f"  try\n"
            f"    let stx ← match Parser.runParserCategory (← getEnv) `term {_lean_string(witness)} with\n"
            f"      | .ok s => pure s\n"
            f"      | .error e => throwError e\n"
            f"    let w ← withoutErrToSorry (elabTermEnsuringType stx (some ex))\n"
            f"    synthesizeSyntheticMVarsNoPostponing\n"
            f"    let w ← instantiateMVars w\n"
            f"    if w.hasMVar || w.hasSorry then\n"
            f'      IO.println s!"{tag}-WITNESS INCOMPLETE mvars={{w.hasMVar}} sorry={{w.hasSorry}}"\n'
            f"    else\n"
            f"      addDecl (.thmDecl {{ name := `_telperion_probe_witness, levelParams := info.levelParams,\n"
            f"                          type := ex, value := w }})\n"
            f"      let axs ← collectAxioms `_telperion_probe_witness\n"
            f'      IO.println s!"{tag}-WITNESS PROVED axioms={{axs.toList}}"\n'
            f"  catch e =>\n"
            f'    IO.println s!"{tag}-WITNESS FAILED {{(← e.toMessageData.toString).replace "\\n" " "}}"\n'
            f"  modifyThe Core.State fun s => {{ s with messages := msgs }}\n"
            f'  IO.println "{tag}-DONE"\n'
        )
    return src


def _errors(output: str) -> list[str]:
    """Each error message in a lean/lake output, header line plus its continuation lines."""
    heads = list(_MSG_RE.finditer(output))
    msgs = []
    for k, m in enumerate(heads):
        if m.group(1) == "error":
            end = heads[k + 1].start() if k + 1 < len(heads) else len(output)
            msgs.append(output[m.start():end].strip())
    return msgs


def _banner(err: str) -> bool:
    """Whether error message `err` is plausible's counterexample report: its body opens with the banner."""
    m = _MSG_RE.match(err)
    return bool(m and _BANNER_RE.match(err, m.end()))


def _purpose(key: str, err: str) -> bool:
    if TIMEOUT_ERROR in err:
        return True
    if key == "negation" and _banner(err):
        return True
    return any(a in err for a in PURPOSE_ERRORS.get(key, ()))


def _unrelated(key: str, rc: int, output: str, module: str) -> str | None:
    """The first error in probe `key`'s output that is not one its purpose explains, or None."""
    errs = _errors(output)
    if rc != 0 and not errs:
        return f"{key} probe exited {rc} with no error message: {output.strip()[-300:]!r}"
    for e in errs:
        if not _purpose(key, e):
            if _UNBUILT_RE.search(e):
                return f"build {module} first (lake build {module}): {key} probe: {e[:300]}"
            return f"{key} probe: {e[:500]}"
    return None


def _timed_out(output: str) -> bool:
    return any(TIMEOUT_ERROR in e for e in _errors(output))


def _result_line(output: str, tag: str, kind: str) -> tuple[str, str] | str:
    """(status, rest) of the ONE `<tag>-<kind> <status> <rest>` line, or why the protocol was broken: no result line,
    more than one, or no single `<tag>-DONE` as the last tagged line. Only lines carrying this run's tag count."""
    tagged = [m.group(1) for m in re.finditer(rf"(?m)^{re.escape(tag)}-(.*)$", output)]
    results = [m for m in (re.match(rf"{kind} (PROVED|FAILED|INCOMPLETE)\b[ \t]*(.*)$", t) for t in tagged) if m]
    if not results:
        return f"printed no {tag}-{kind} result line"
    if len(results) > 1:
        return f"printed {len(results)} {tag}-{kind} result lines; refusing a duplicated protocol"
    if tagged.count("DONE") != 1 or tagged[-1] != "DONE":
        return f"did not end with exactly one {tag}-DONE line; refusing an incomplete or duplicated protocol"
    return results[0].group(1), results[0].group(2)


def _axiom_problem(key: str, rest: str) -> str | None:
    """Why proved probe `key` does not count on axiom grounds (an axiom outside CLEAN_AXIOMS, or no readable list),
    or None when it counts."""
    m = re.match(r"axioms=\[([^\]]*)\]", rest)
    if not m:
        return f"probe '{key}' printed no axiom list; not counted"
    bad = [a.strip() for a in m.group(1).split(",") if a.strip() and a.strip() not in CLEAN_AXIOMS]
    return f"probe '{key}' used non-standard axioms {bad}; not counted" if bad else None


def classify(outputs: dict[str, tuple[int, str]], tag: str = "TP", module: str = "<module>") -> ProbeResult:
    """The verdict from each probe's (returncode, output): ERROR, then VACUOUS, REFUTED, WITNESSED, PROBE_ONLY."""
    for key in ("false", "negation"):
        if key not in outputs:
            return ProbeResult("ERROR", f"{key} probe did not run")
    for key, (rc, out) in outputs.items():
        bad = _unrelated(key, rc, out, module)
        if bad:
            return ProbeResult("ERROR", bad)
    timed_out = [key for key, (_rc, out) in outputs.items() if _timed_out(out)]
    lines = {}
    for key in ("false", "witness"):
        if key not in outputs:
            continue
        line = _result_line(outputs[key][1], tag, key.upper())
        if isinstance(line, str):
            if key not in timed_out:
                return ProbeResult("ERROR", f"{key} probe {line}")
            line = None                     # a timed-out probe is inconclusive, its protocol is not read
        lines[key] = line
        if line and line[0] == "FAILED" and key == "witness":
            return ProbeResult("ERROR", f"the witness does not check: {line[1][:500]}")
    notes = [f"probe '{key}' timed out at maxHeartbeats 200000 (inconclusive)" for key in timed_out]
    prem = re.findall(rf"(?m)^{re.escape(tag)}-PREMISES (\d+)$", outputs["false"][1])
    premises = f"the {prem[-1]} premise(s)" if prem else "the premises"
    line = lines["false"]
    if "false" not in timed_out and line and line[0] == "PROVED":
        bad = _axiom_problem("false", line[1])
        if not bad:
            return ProbeResult("VACUOUS", f"{premises} alone prove False (kernel-checked, clean axioms)")
        notes.append(bad)
    elif line and line[0] == "INCOMPLETE":
        notes.append(f"probe 'false' left goals, metavariables or sorry ({line[1]}); not counted")
    neg = outputs["negation"][1]
    banners = [e for e in _errors(neg) if _banner(e)]
    if "negation" not in timed_out and banners:
        body = banners[0][_MSG_RE.match(banners[0]).end():]
        return ProbeResult("REFUTED", "plausible found a counterexample: "
                           + " ".join(body.strip().lstrip("=").split("-------------------")[0].split()))
    wline = lines.get("witness")
    if "witness" not in timed_out and wline and wline[0] == "PROVED":
        bad = _axiom_problem("witness", wline[1])
        if not bad:
            return ProbeResult("WITNESSED", f"the witness proves {premises} satisfiable (kernel-checked, clean "
                               "axioms); no counterexample found")
        notes.append(bad)
    elif wline and wline[0] == "INCOMPLETE":
        notes.append(f"probe 'witness' left metavariables or sorry ({wline[1]}); not counted")
    if NO_TESTABLE in neg:
        notes.append("negation probe did not run: no testable instance (e.g. ℝ), so no counterexample was searched for")
    return ProbeResult("PROBE_ONLY", "; ".join(notes + [f"no contradiction derived from {premises} and no "
                                                        "counterexample found; one-sided, not evidence the claim is "
                                                        "true"]))


def default_wrapper() -> list[str]:
    lock = os.path.expanduser("~/hodge-engine/leanlock.sh")
    return ["env", "ARDA_LEAN_SLOTS=1", lock] if os.path.exists(lock) else []


def _run(cmd: list[str], cwd: Path, timeout: int) -> tuple[int, str]:
    """(returncode, stdout + stderr) of `cmd` in its own session. On the wall-clock timeout the whole process group
    gets SIGTERM (leanlock's trap then frees its slot) and, 5 s later, SIGKILL, so no lake or lean child under the
    wrapper outlives the probe; TimeoutExpired is then re-raised."""
    p = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
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


def run_probe(spec: ProbeSpec, project: Path, wrapper: list[str] | None = None,
              timeout: int = 1800) -> ProbeResult:
    """Write the probes to `<project>/.telperion_probe/`, run each with `lake env lean`, classify, delete the dir.

    The directory must not already exist: a second probe running in the same project, or a stale one, is reported
    as ERROR rather than overwritten."""
    project = Path(project)
    prefix = default_wrapper() if wrapper is None else list(wrapper)
    tag = f"TP{secrets.token_hex(16)}"     # 128-bit per-run nonce on every protocol line
    srcs = render_probes(spec.module, spec.theorem, spec.witness, spec.imports, tag=tag)
    pdir = project / PROBE_DIR
    try:
        pdir.mkdir()
    except FileExistsError:
        return ProbeResult("ERROR", f"probe dir {pdir} already exists; remove it if no other probe is running")
    except OSError as exc:
        return ProbeResult("ERROR", f"cannot create {pdir}: {exc}")
    outputs: dict[str, tuple[int, str]] = {}
    try:
        for key, src in srcs.items():
            f = pdir / f"{key}.lean"
            f.write_text(src, encoding="utf-8")
            try:
                outputs[key] = _run([*prefix, "lake", "env", "lean", str(f.relative_to(project))], project, timeout)
            except (OSError, subprocess.TimeoutExpired) as exc:
                return ProbeResult("ERROR", f"{key} probe did not finish: {exc}")
    finally:
        shutil.rmtree(pdir, ignore_errors=True)
    return classify(outputs, tag=tag, module=spec.module)


def qualify(module_text: str, theorem: str) -> str:
    """`theorem` qualified by the namespace the file declares it in, when the file declares exactly one theorem/lemma
    of that (short) name; otherwise `theorem` unchanged. Only LOCATES the constant: the statement itself is always
    read from the elaborated constant, never from this text."""
    from ..missions import judge

    ga = judge._guard_anchors()
    code = ga.strip_lean_comments(module_text)
    pat = re.compile(r"(?<![\w.'])(?:theorem|lemma)\s+" + re.escape(theorem) + r"(?![\w.'])")
    names = {".".join([*ga._namespace_at(code, m.start()), theorem]) for m in pat.finditer(code)}
    return names.pop() if len(names) == 1 else theorem
