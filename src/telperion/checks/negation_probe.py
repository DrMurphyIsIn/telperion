"""Negation probe: a cheap, one-sided sanity check on a theorem STATEMENT, run before anyone proves it.

Three small Lean files are elaborated next to the statement, in a built Lake project:

* ``false``    -- ``theorem _tp_false <binders> : False`` closed by a fixed tactic battery. If it compiles, the
  hypotheses contradict each other and the theorem is VACUOUS (true of nothing).
* ``negation`` -- ``example : ∀ <binders>, <conclusion>`` handed to ``plausible``. If plausible's error opens with its
  ``Found a counter-example!`` banner, the claim is REFUTED at a concrete point.
* ``witness``  -- only with a caller-supplied term: ``theorem _tp_witness : ∃ <binders>, True := <witness>``. If it
  compiles, the hypotheses are jointly satisfiable, so the theorem is WITNESSED non-vacuous.

The two probes that can produce VACUOUS or WITNESSED are named theorems followed by ``#print axioms``, and they count
only when every reported axiom is in ``comparator.CLEAN_AXIOMS``. An axiom in scope (``axiom bad : False`` registered
as an aesop rule, say), a ``sorry`` or a missing axiom line all mean the probe is not counted.

ONE-SIDED BY DESIGN. VACUOUS and REFUTED rest on positive evidence (a compiled proof of ``False``, a printed
counterexample). Everything else is PROBE_ONLY: the battery failing to derive ``False`` and plausible failing to find a
counterexample say nothing about truth. ERROR means a probe failed for a reason other than its purpose (an unknown
identifier, a missing import, a parse error), so neither verdict could be read. A maxHeartbeats timeout in any probe
is not an ERROR: that probe is inconclusive, and the verdict falls through to PROBE_ONLY with a note saying so.

LOCAL DECLARATIONS CAN CHANGE THE STATEMENT SILENTLY. The probes import modules and re-create the theorem's
`namespace` and `open` lines; they do not re-declare anything from the file. Lean resolves a name in the current
namespace BEFORE the opened ones, so in `namespace Foo; open Nat; def factorial ...` the theorem's `factorial` is
`Foo.factorial`, but in a probe without that def it quietly becomes `Nat.factorial`, and a true theorem comes back
REFUTED. It is not an "unknown identifier" ERROR. So the CLI scans the file first (`local_command_problems`) and
refuses, with ERROR:
* without `--import`, any non-theorem declaration in the file (def, abbrev, instance, structure, inductive, class,
  notation and its infix/prefix/postfix forms, macro, syntax, elab, opaque, axiom, attribute, export, alias,
  deriving...); pass `--import <Module>` of a BUILT module that contains them, and they are in scope as in the file;
* even with `--import`, any `local`/`scoped` command or attribute, any `private` non-theorem declaration, and any
  section `variable`. None of these carry over through an import.
`universe`, `set_option`, `open`, `namespace`, `section` and other theorems are allowed. A theorem named in a statement
and shadowed by a theorem of the file is not caught.

KNOWN LIMITATION. A dotted theorem name declared inside a namespace (`theorem RI.mem_add` under
`namespace ScaledInterval`) is not found by the judge's `decl_context`, so the CLI returns ERROR for it.
"""
from __future__ import annotations

import os
import re
import shutil
import signal
import subprocess
from dataclasses import dataclass
from pathlib import Path

from ..comparator import CLEAN_AXIOMS
from ..verify import _AXIOMS, _NO_AXIOMS

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
        "false": f"{head}{opts}theorem _tp_false{sig} : False := by\n  {FALSE_TACTIC}\n\n#print axioms _tp_false\n",
        "negation": f"{head}{opts}example : {prop} := by {PLAUSIBLE}\n",
    }
    if witness is not None:
        ex = f"∃ {_exists_binders(binders)}, True" if binders.strip() else "True"
        src["witness"] = f"{head}{opts}theorem _tp_witness : {ex} :=\n  {witness}\n\n#print axioms _tp_witness\n"
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
    return any(a in err for a in PURPOSE_ERRORS.get(key, ()) if a != COUNTEREXAMPLE)


def _unrelated(key: str, rc: int, output: str) -> str | None:
    """The first error in probe `key`'s output that is not one its purpose explains, or None."""
    errs = _errors(output)
    if rc != 0 and not errs:
        return f"{key} probe exited {rc} with no error message: {output.strip()[-300:]!r}"
    for e in errs:
        if not _purpose(key, e):
            if "autoImplicit" in e:
                return f"statement relies on autoImplicit; make binders explicit ({key} probe: {e[:500]})"
            return f"{key} probe: {e[:500]}"
    return None


def _timed_out(output: str) -> bool:
    return any(TIMEOUT_ERROR in e for e in _errors(output))


def _compiled(rc: int, output: str) -> bool:
    return rc == 0 and not _errors(output) and not _SORRY_RE.search(output)


def _axiom_problem(key: str, output: str) -> str | None:
    """Why compiled probe `key` does not count on axiom grounds (no `#print axioms` line for `_tp_<key>`, or an axiom
    outside CLEAN_AXIOMS), or None when it counts."""
    name = f"_tp_{key}"
    axioms: list[str] | None = None
    for m in _AXIOMS.finditer(output):
        if m.group(1) == name or m.group(1).endswith("." + name):
            axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in _NO_AXIOMS.finditer(output):
        if m.group(1) == name or m.group(1).endswith("." + name):
            axioms = []
    if axioms is None:
        return f"probe '{key}' compiled but printed no `#print axioms` line; not counted"
    bad = [a for a in axioms if a not in CLEAN_AXIOMS]
    return f"probe '{key}' used non-standard axioms {bad}; not counted" if bad else None


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
    notes = [f"probe '{key}' timed out at maxHeartbeats 200000 (inconclusive)" for key in timed_out]
    if "false" not in timed_out and _compiled(*outputs["false"]):
        bad = _axiom_problem("false", outputs["false"][1])
        if not bad:
            return ProbeResult("VACUOUS", "the hypotheses alone prove False (the `false` probe compiled, clean axioms)")
        notes.append(bad)
    neg = outputs["negation"][1]
    banners = [e for e in _errors(neg) if _banner(e)]
    if "negation" not in timed_out and banners:
        body = banners[0][_MSG_RE.match(banners[0]).end():]
        return ProbeResult("REFUTED", "plausible found a counterexample: "
                           + " ".join(body.strip().lstrip("=").split("-------------------")[0].split()))
    if "witness" in outputs and "witness" not in timed_out and _compiled(*outputs["witness"]):
        bad = _axiom_problem("witness", outputs["witness"][1])
        if not bad:
            return ProbeResult("WITNESSED", "the witness proves the hypotheses satisfiable (clean axioms); no "
                               "counterexample found")
        notes.append(bad)
    if NO_TESTABLE in neg:
        notes.append("negation probe did not run: no testable instance (e.g. ℝ), so no counterexample was searched for")
    return ProbeResult("PROBE_ONLY", "; ".join(notes + ["no contradiction in the hypotheses and no counterexample "
                                                        "found; one-sided, not evidence the claim is true"]))


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
                outputs[key] = _run([*prefix, "lake", "env", "lean", str(f.relative_to(project))], project, timeout)
            except (OSError, subprocess.TimeoutExpired) as exc:
                return ProbeResult("ERROR", f"{key} probe did not finish: {exc}")
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


def _blank_comments(text: str) -> str:
    """`text` with comments and string-literal contents replaced by spaces, newlines kept, so offsets and line
    numbers still match the source."""
    out, i, n = list(text), 0, len(text)

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
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
            blank(i, j)
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            blank(i + 1, min(j, n))
            i = j + 1
        else:
            i += 1
    return "".join(out)


# A command at the start of a line: optional `open ... in` / `set_option ... in` prefixes, attributes, modifiers, then
# the keyword.
_DECL_CMD_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:open|set_option)\b[^\n]*?\bin[ \t]+)*"
    r"(?P<attrs>(?:@\[[^\]]*\][ \t\n]*)*)"
    r"(?P<mods>(?:(?:noncomputable|private|protected|partial|unsafe|nonrec)[ \t]+)*)"
    r"(?P<kw>local|scoped|attribute|variable|def|abbrev|instance|structure|inductive|class|notation3|notation"
    r"|infixl|infixr|infix|prefix|postfix|macro_rules|macro|syntax|elab_rules|elab|opaque|axiom|export|alias"
    r"|irreducible_def|declare_syntax_cat|deriving|theorem|lemma)\b(?P<rest>[^\n]*)")
_LOCAL_RE = re.compile(r"\b(?:local|scoped)\b")
_ALWAYS = ("local/scoped/private declarations and section variables can change name resolution and do not carry over "
           "through --import; the probe cannot be trusted")
_WITHOUT_IMPORT = ("local declarations can change name resolution; pass --import <module> of a built module that "
                   "contains them, or the probe cannot be trusted")


def local_command_problems(module_text: str, imported: bool) -> str | None:
    """The first command in `module_text` that could make the probe read the statement differently from the file,
    named with its line, or None. See the module docstring: `local`/`scoped` commands and attributes, `private`
    non-theorem declarations and `variable`s always count; other non-theorem declarations count unless `imported`."""
    code = _blank_comments(module_text)
    for m in _DECL_CMD_RE.finditer(code):
        kw = m.group("kw")
        theorem = kw in ("theorem", "lemma")
        always = (bool(_LOCAL_RE.search(m.group("attrs"))) or kw in ("local", "scoped", "variable")
                  or (kw == "attribute" and bool(_LOCAL_RE.search(m.group("rest"))))
                  or ("private" in m.group("mods") and not theorem))
        if always or (not theorem and not imported):
            line = code.count("\n", 0, m.start()) + 1
            src = module_text.splitlines()[line - 1].strip()[:100]
            return f"`{src}` at line {line}: {_ALWAYS if always else _WITHOUT_IMPORT}"
    return None
