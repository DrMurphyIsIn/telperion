"""Negation probe: a cheap, one-sided sanity check on a theorem STATEMENT, run before anyone proves it.

Three small Lean files are elaborated next to the statement, in a built Lake project:

* ``false``    -- ``example <binders> : False`` closed by a fixed tactic battery. If it compiles, the hypotheses
  contradict each other and the theorem is VACUOUS (true of nothing).
* ``negation`` -- ``example : ∀ <binders>, <conclusion>`` handed to ``plausible``. If plausible prints
  ``Found a counter-example!``, the claim is REFUTED at a concrete point.
* ``witness``  -- only with a caller-supplied term: ``example : ∃ <binders>, True := <witness>``. If it compiles, the
  hypotheses are jointly satisfiable, so the theorem is WITNESSED non-vacuous.

ONE-SIDED BY DESIGN. VACUOUS and REFUTED rest on positive evidence (a compiled proof of ``False``, a printed
counterexample). Everything else is PROBE_ONLY: the battery failing to derive ``False`` and plausible failing to find a
counterexample say nothing about truth. ERROR means a probe failed for a reason other than its purpose (an unknown
identifier, a missing import, a parse error), so neither verdict could be read. A maxHeartbeats timeout in any probe
is not an ERROR: that probe is inconclusive, and the verdict falls through to PROBE_ONLY with a note saying so.

LOCAL DEFINITIONS. The probes import modules; they do not re-declare anything. A statement that uses a `def` from its
own file elaborates only if that file's MODULE is imported (`telperion probe-negation --import <Module>`), not just the
file's own imports; otherwise the name is unknown and the verdict is ERROR. Section `variable`s are not reproduced
either, so binders must be explicit.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

VERDICTS = ("VACUOUS", "REFUTED", "PROBE_ONLY", "WITNESSED", "ERROR")

FALSE_TACTIC = "first | (exfalso; omega) | linarith | (simp_all; done) | (norm_num at *; done) | aesop"
PLAUSIBLE = "plausible (config := { numInst := 200 })"
COUNTEREXAMPLE = "Found a counter-example!"
NO_TESTABLE = "Failed to create a `testable` instance"
PROBE_DIR = ".telperion_probe"

# Errors the `false` probe is EXPECTED to produce when the hypotheses are consistent: the battery's tactics giving up.
# `first` reports only the last alternative's failure, which is aesop's ("Tactic `aesop` failed, made no progress" on
# v4.35.0); the others are kept for a battery that stops earlier. Any other error (unknown identifier, type mismatch in
# a binder, parse error) means the hypotheses did not elaborate, so the probe proved nothing.
FALSE_PURPOSE_ERRORS = (
    "linarith failed",
    "omega could not prove",
    "aesop: failed",
    "Tactic `aesop` failed",
    "simp made no progress",
    "norm_num failed",
    "unsolved goals",
)

# Errors the `negation` probe is EXPECTED to produce when it finds nothing: plausible giving up, finding no
# counterexample, or having no `Testable` instance for the claim (a real variable, an undecidable hypothesis). The
# last one is raised only after the statement elaborated, so it never hides an elaboration error. The counterexample
# itself is reported as an error too, and is the probe's purpose.
NEGATION_PURPOSE_ERRORS = (
    COUNTEREXAMPLE,
    "Gave up",
    "gave up",
    "Unable to find",
    NO_TESTABLE,
)

# The witness probe has no expected errors: a witness that does not check is the caller's mistake, reported as ERROR.
PURPOSE_ERRORS = {"false": FALSE_PURPOSE_ERRORS, "negation": NEGATION_PURPOSE_ERRORS, "witness": ()}

# A maxHeartbeats timeout in ANY probe makes that probe inconclusive, never an ERROR: hypotheses that are merely hard
# for the battery must not block a grant. `first` does not catch it, so it ends the `false` battery where it struck.
# A timed-out probe is never read as compiled or as a counterexample, so a timeout cannot produce a positive verdict.
TIMEOUT_ERROR = "maximum number of heartbeats"

# A message header: `file:line:col: error:` from lean, or a bare `error:` from lake. v4.35.0 also tags some messages
# with a code, `error(lean.unknownIdentifier):`; missing those would let an elaboration error pass as a tactic failure.
_MSG_RE = re.compile(r"(?m)^(?:\S[^\n]*?:\d+:\d+: )?(error|warning|info)(?:\([^)\n]*\))?:")
_SORRY_RE = re.compile(r"declaration uses [`']sorry[`']")


@dataclass
class ProbeResult:
    verdict: str
    detail: str

    def to_json(self) -> dict:
        return {"verdict": self.verdict, "detail": self.detail}


@dataclass
class ProbeSpec:
    imports: list[str]
    prelude: str
    binders: str
    conclusion: str
    witness: str | None = None


def _exists_binders(binders: str) -> str:
    """`binders` with every top-level `{..}`, `⦃..⦄` and `[..]` group rewritten as `(..)`, since `∃` accepts only
    explicit binders. An anonymous instance `[C]` becomes `(_ : C)`."""
    out, i, n = [], 0, len(binders)
    pairs = {"{": "}", "⦃": "⦄", "[": "]", "(": ")"}
    while i < n:
        ch = binders[i]
        if ch not in pairs:
            out.append(ch)
            i += 1
            continue
        close, depth, j = pairs[ch], 0, i
        while j < n:
            if binders[j] == ch:
                depth += 1
            elif binders[j] == close:
                depth -= 1
                if depth == 0:
                    break
            j += 1
        inner = binders[i + 1:j]
        if ch == "[" and ":" not in inner:
            inner = f"_ : {inner}"
        out.append(f"({inner})")
        i = j + 1
    return "".join(out)


def render_probes(imports: list[str], prelude: str, binders: str, conclusion: str,
                  witness: str | None) -> dict[str, str]:
    """Lean source for each probe, keyed "false", "negation" and (with a witness) "witness".

    `autoImplicit` is off in every probe, so an unknown identifier in the statement is an error, never a fresh
    variable that makes the hypotheses trivially consistent."""
    head = "".join(f"import {m}\n" for m in imports) + "\n" + (prelude.rstrip() + "\n\n" if prelude.strip() else "")
    opts = "set_option maxHeartbeats 200000 in\nset_option autoImplicit false in\n"
    sig = f" {binders}" if binders.strip() else ""
    prop = f"∀ {binders}, {conclusion}" if binders.strip() else conclusion
    src = {
        "false": f"{head}{opts}example{sig} : False := by\n  {FALSE_TACTIC}\n",
        "negation": f"{head}{opts}example : {prop} := by {PLAUSIBLE}\n",
    }
    if witness is not None:
        ex = f"∃ {_exists_binders(binders)}, True" if binders.strip() else "True"
        src["witness"] = f"{head}{opts}example : {ex} :=\n  {witness}\n"
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


def _unrelated(key: str, rc: int, output: str) -> str | None:
    """The first error in probe `key`'s output that is not one its purpose explains, or None."""
    errs = _errors(output)
    if rc != 0 and not errs:
        return f"{key} probe exited {rc} with no error message: {output.strip()[-300:]!r}"
    allowed = PURPOSE_ERRORS.get(key, ()) + (TIMEOUT_ERROR,)
    for e in errs:
        if not any(a in e for a in allowed):
            if "autoImplicit" in e:
                return f"statement relies on autoImplicit; make binders explicit ({key} probe: {e[:500]})"
            return f"{key} probe: {e[:500]}"
    return None


def _timed_out(output: str) -> bool:
    return any(TIMEOUT_ERROR in e for e in _errors(output))


def _compiled(rc: int, output: str) -> bool:
    return rc == 0 and not _errors(output) and not _SORRY_RE.search(output)


def classify(outputs: dict[str, tuple[int, str]]) -> ProbeResult:
    """The verdict from each probe's (returncode, output): ERROR, then VACUOUS, REFUTED, WITNESSED, PROBE_ONLY."""
    for key in ("false", "negation"):
        if key not in outputs:
            return ProbeResult("ERROR", f"{key} probe did not run")
    for key, (rc, out) in outputs.items():
        bad = _unrelated(key, rc, out)
        if bad:
            return ProbeResult("ERROR", bad)
    timed_out = [key for key, (_rc, out) in outputs.items() if _timed_out(out)]
    if "false" not in timed_out and _compiled(*outputs["false"]):
        return ProbeResult("VACUOUS", "the hypotheses alone prove False (the `false` probe compiled)")
    neg = outputs["negation"][1]
    if "negation" not in timed_out and COUNTEREXAMPLE in neg:
        at = neg.index(COUNTEREXAMPLE)
        return ProbeResult("REFUTED", "plausible found a counterexample: "
                           + " ".join(neg[at:].split("-------------------")[0].split()))
    if "witness" in outputs and "witness" not in timed_out and _compiled(*outputs["witness"]):
        return ProbeResult("WITNESSED", "the witness proves the hypotheses satisfiable; no counterexample found")
    notes = [f"probe '{key}' timed out at maxHeartbeats 200000 (inconclusive)" for key in timed_out]
    if NO_TESTABLE in neg:
        notes.append("negation probe did not run: no testable instance (e.g. ℝ), so no counterexample was searched for")
    return ProbeResult("PROBE_ONLY", "; ".join(notes + ["no contradiction in the hypotheses and no counterexample "
                                                        "found; one-sided, not evidence the claim is true"]))


def default_wrapper() -> list[str]:
    lock = os.path.expanduser("~/hodge-engine/leanlock.sh")
    return ["env", "ARDA_LEAN_SLOTS=1", lock] if os.path.exists(lock) else []


def run_probe(spec: ProbeSpec, project: Path, wrapper: list[str] | None = None,
              timeout: int = 1800) -> ProbeResult:
    """Write the probes to `<project>/.telperion_probe/`, run each with `lake env lean`, classify, delete the dir.

    The directory must not already exist: a second probe running in the same project, or a stale one, is reported
    as ERROR rather than overwritten."""
    project = Path(project)
    prefix = default_wrapper() if wrapper is None else list(wrapper)
    srcs = render_probes(spec.imports, spec.prelude, spec.binders, spec.conclusion, spec.witness)
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
                p = subprocess.run([*prefix, "lake", "env", "lean", str(f.relative_to(project))], cwd=project,
                                   capture_output=True, text=True, timeout=timeout)
            except (OSError, subprocess.TimeoutExpired) as exc:
                return ProbeResult("ERROR", f"{key} probe did not finish: {exc}")
            outputs[key] = (p.returncode, p.stdout + p.stderr)
    finally:
        shutil.rmtree(pdir, ignore_errors=True)
    return classify(outputs)


_COMMAND_START_RE = re.compile(
    r"(?m)^(?:@\[|theorem\b|lemma\b|def\b|abbrev\b|instance\b|example\b|structure\b|inductive\b|class\b|axiom\b"
    r"|opaque\b|noncomputable\b|private\b|protected\b|variable\b|universe\b|namespace\b|section\b|end\b|open\b"
    r"|set_option\b|attribute\b|mutual\b|#)")


def read_signature(module_text: str, theorem: str) -> tuple[list[str], str, str, str]:
    """(import lines, prelude, binders, conclusion) of `theorem` (fully qualified) as `module_text` declares it.

    The prelude re-creates the declaration's context: its `namespace` and the `open` lines above it, found with the
    judge's `decl_context`. The declaration runs from its keyword to the next column-0 command; everything from its
    first top-level `:=` after the signature colon is replaced by `:= by sorry`, so a `have _ := _` in the proof cannot
    be read as part of the conclusion, and the result is split with the judge's `split_signature`. Raises JudgeError."""
    from ..missions import judge

    ga = judge._guard_anchors()
    ns, opens = judge.decl_context(module_text, theorem)
    short = theorem.rsplit(".", 1)[-1]
    code = ga.strip_lean_comments(module_text)
    pat = re.compile(r"(?<![\w.'])(theorem|lemma)\s+" + re.escape(short) + r"(?![\w.'])")
    for m in pat.finditer(code):
        if ".".join(ga._namespace_at(code, m.start())) != ns:
            continue
        nxt = _COMMAND_START_RE.search(code, m.end())
        decl = code[m.start():nxt.start() if nxt else len(code)]
        colon = judge._scan_depth0(decl[m.end() - m.start():], ":")
        if colon < 0:
            break
        head_len = m.end() - m.start() + colon + 1
        assign = judge._scan_depth0(decl[head_len:], ":=")
        sig = decl if assign < 0 else decl[:head_len + assign]
        _short, binders, concl = judge.split_signature(sig + " := by sorry")
        imports = [ln.split(None, 1)[1].strip() for ln in module_text.splitlines()
                   if ln.startswith("import ") and len(ln.split()) > 1]
        prelude = "\n".join(([f"namespace {ns}"] if ns else []) + opens)
        return imports, prelude, binders, concl
    raise judge.JudgeError(f"module does not declare `{theorem}` with a signature")
