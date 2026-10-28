"""The "nanoda-direct" second-kernel route (step 0b Task 3, 2026-10-28).

Seven proved nodes have never had a second-kernel judge because no Comparator bundle can
consume them (a statement that declares a namespace or a `def`, a monolith lakefile that
cannot be path-required, or an island wired to no judge at all). The owner's decision: give
them a second kernel WITHOUT Comparator's statement-identity step --

  1. `lake build` the artifact module in its island (leanlock; done by the caller, not here);
  2. `lean4export <module> -- <theorem>` on the node's OWN registered theorem (resolved the
     way the grant gate resolves it: `guard_anchors.resolve_theorem(artifact_text,
     statement_text)` -- never a hand-typed guess, so a typo in the theorem name fails the
     export rather than silently exporting something else);
  3. `nanoda_bin` at the pinned `NANODA_REV`, with exactly the three standard axioms
     (`propext`, `Quot.sound`, `Classical.choice`) and `unpermitted_axiom_hard_error: true`.

Statement identity then rests on the gate's existing statement check (`statement_matches` /
`regen_diff`, run when the node was granted) plus the artifact's import-closure digest
(`provenance.closure_digest`), both already enforced elsewhere. This route is WEAKER than a
Comparator run -- there is no independent re-render of the challenge and no second party's
notion of "the registered statement" is checked here -- so every record it writes carries
`route = "nanoda-direct"`, and `provenance.render_provenance_report` labels it as such.

The verdict comes from the raw export/nanoda output, never from a flag: `classify` reads
the recorded exit codes and text exactly as `rejudge.parse_comparator_log` reads a
Comparator log. nanoda_lib's source (nanoda-37cb87b7, pinned by `NANODA_REV`):

  * the success line -- `main.rs:34`, `format!("Checked {} declarations with no errors", ...)`,
    printed only with `print_success_message: true` (its default is `false`,
    `util.rs:933-934`, so `nanoda_config` sets it);
  * an unpermitted axiom -- `parser.rs:837`,
    `format!("export file declares unpermitted axiom {:?}", name_string)`, returned as an
    `Err` that `main.rs`'s `Debug` impl prints as `Error: export file declares unpermitted
    axiom "<name>"` (confirmed against the step 0 negative-control log, which named
    `"propext"`; a `sorry`-bodied theorem exports the axiom `sorryAx`).

A run that checks ZERO declarations (e.g. an empty or mistargeted export) prints the SAME
success line with `n = 0` -- `Checked 0 declarations with no errors`, exit 0, no `Error:`
line -- so `classify` treats `n == 0` as FAIL, not PASS (Review Focus 3 / Global Constraint
"verdicts come from tool output, never from flags": a verdict that is merely "no errors
reported" is not the same claim as "something was checked and accepted").
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, List, Optional, Tuple

#: The three axioms every Comparator run (and this route) permits (judge.py / rejudge_queue.sh
#: `export_targets`): propext, Quot.sound, Classical.choice -- never sorryAx, never a
#: project-local axiom.
PERMITTED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")


class NanodaDirectError(Exception):
    """The node's export target (island, module, theorem) or import closure cannot be
    resolved; message says why. Mirrors `rejudge.RejudgeSetupError` for the routes
    Comparator CAN consume."""


def export_cmd(lean_dir, module: str, theorem: str, lean4export) -> List[str]:
    """`lake env <lean4export> <module> -- <theorem>`, run with cwd=*lean_dir* (lean4export's
    `dumpConstant` walks *theorem*'s own transitive dependencies -- propext, Classical.choice,
    etc. show up in the export as the axioms it actually used, with no need to list Comparator's
    separate builtin/primitive target list here: there is no statement-identity render to keep
    byte-identical to).

    *theorem* must be the node's OWN registered theorem (`guard_anchors.resolve_theorem`), so a
    typo here exports nothing reachable from it -- `lean4export` fails outright (Review Focus 2),
    never the WRONG constant's closure silently standing in for the right one.
    """
    return ["lake", "env", str(lean4export), module, "--", theorem]


def nanoda_config(export_path) -> dict:
    """The nanoda config: the export file on disk, exactly the three standard axioms, a HARD
    error on anything else, and both numeric extensions (nanoda's `Nat`/`String` kernel
    reductions, same as every Comparator run -- util.rs `nat_extension` / `string_extension`).

    `print_success_message` is true because nanoda's own default is false (util.rs:933-934);
    without it `use_config` returns `Ok(None)` on a clean run and `classify` would have nothing
    to read the declaration count from.
    """
    return {
        "export_file_path": str(export_path),
        "permitted_axioms": list(PERMITTED_AXIOMS),
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
    }


#: main.rs:34 -- the ONLY success-message shape this route accepts (print_success_message
#: true, permitted_axioms non-empty so `skipped_axioms` stays empty: unpermitted_axiom_hard_error
#: is always true here, so a run that skipped rather than erred on an axiom never happens).
_SUCCESS_RE = re.compile(r"^Checked (?P<n>\d+) declarations? with no errors$")


def _has_error_line(text: str) -> bool:
    return any(l.strip().lower().startswith(("error", "uncaught exception"))
               for l in text.splitlines())


def classify(export_rc: int, export_out: str, nanoda_rc: int, nanoda_out: str) -> str:
    """"pass" iff lean4export exited 0 and exported something, nanoda exited 0, no line in
    either output starts with "error"/"uncaught exception", and nanoda's own success line
    (main.rs:34) names a NON-ZERO declaration count.

    The last check is the zero-declarations case (Review Focus 3): an empty or mistargeted
    export still makes nanoda print "Checked 0 declarations with no errors" and exit 0 -- that
    reads like success but asserts nothing, so it is FAIL here, never PASS.
    """
    if export_rc != 0 or not export_out.strip() or _has_error_line(export_out):
        return "fail"
    if nanoda_rc != 0 or _has_error_line(nanoda_out):
        return "fail"
    n = None
    for line in nanoda_out.splitlines():
        m = _SUCCESS_RE.match(line.strip())
        if m:
            n = int(m.group("n"))
            break
    if not n:          # None (no success line at all) or 0 (zero declarations)
        return "fail"
    return "pass"


#: The delimiters `run_direct` writes around the raw export / nanoda output, in that order --
#: the nanoda-direct analogue of rejudge.py's `_PART_RE` for a Comparator log.
_SECTION_RE = re.compile(r"^=+\s*REJUDGE-(?P<which>EXPORT|NANODA)\s+exit=(?P<rc>-?\d+)\s*=+$")


def _parse_sections(text: str) -> Optional[Tuple[int, str, int, str]]:
    sections = {}
    cur = None
    body: List[str] = []
    for line in text.splitlines():
        m = _SECTION_RE.match(line.strip())
        if m:
            if cur is not None:
                sections[cur[0]] = (cur[1], "\n".join(body))
            cur = (m.group("which"), int(m.group("rc")))
            body = []
        elif cur is not None:
            body.append(line)
    if cur is not None:
        sections[cur[0]] = (cur[1], "\n".join(body))
    if "EXPORT" not in sections or "NANODA" not in sections:
        return None
    erc, eout = sections["EXPORT"]
    nrc, nout = sections["NANODA"]
    return erc, eout, nrc, nout


def verdict_of_log(text: str) -> str:
    """"pass"/"fail" of a whole nanoda-direct node log, as `run_direct` writes it: find the
    `REJUDGE-EXPORT exit=<rc>` and `REJUDGE-NANODA exit=<rc>` sections and `classify` their
    recorded output. A log missing either section (garbled, truncated, or not actually a
    nanoda-direct log) is "fail" -- there is nothing a pass could be about."""
    parsed = _parse_sections(text)
    if parsed is None:
        return "fail"
    return classify(*parsed)


@dataclass(frozen=True)
class Tools:
    """Paths `run_direct` needs, plus where it writes the node's export/config/log files.

    *telperion_root* is the repo root (campaign_root's grandparent in production:
    `<root>/missions/<campaign>`); it is a separate field, not derived, so a test can point it
    at a synthetic tree without a real `missions/` layout above *campaign_root*.
    """
    telperion_root: Path
    lean4export: Path
    nanoda: Path
    nanoda_rev: str
    out_dir: Path


#: `run(cmd, cwd=...) -> (returncode, combined stdout+stderr text)`, injected so tests never
#: invoke lake, lean4export or nanoda_bin. Production wiring (Task 4, not this task) supplies a
#: `run` that applies leanlock/ARDA_LEAN_SLOTS around a Lean invocation (`cmd[0] == "lake"`) and
#: calls nanoda_bin straight.
RunFn = Callable[..., Tuple[int, str]]


def run_direct(campaign_root, node, *, tools: Tools, run: RunFn) -> Path:
    """Export the node's OWN registered theorem and its closure, run nanoda on it, and write
    one node log: the `REJUDGE-HEADER` (artifact sha256 + closure sha256, exactly as
    `rejudge-record` computes them), `REJUDGE-ROUTE nanoda-direct`, informational lines, then
    the raw export and nanoda output under `REJUDGE-EXPORT`/`REJUDGE-NANODA` delimiters.
    Returns the log path. Raises `NanodaDirectError` (writes nothing) when the node's artifact,
    island, theorem or import closure cannot be resolved -- there is no verdict to log yet.
    """
    from . import judge
    from .provenance import ClosureError, closure_digest, closure_files, sha256_file
    from .rejudge import RejudgeSetupError, island_of_artifact
    from .schema import slug_of
    from .statements import statement_path

    slug = slug_of(node.name)
    if node.proof is None:
        raise NanodaDirectError(f"{slug}: no artifact linked")
    campaign_root = Path(campaign_root).resolve()
    artifact = (campaign_root / node.proof.artifact).resolve()
    if not artifact.is_file():
        raise NanodaDirectError(f"{slug}: artifact {node.proof.artifact!r} does not exist")
    stmt = statement_path(campaign_root, node)
    if not stmt.is_file():
        raise NanodaDirectError(f"{slug}: no statement file {stmt}")

    telperion_root = Path(tools.telperion_root).resolve()
    try:
        island = island_of_artifact(telperion_root, artifact)
    except RejudgeSetupError as exc:
        raise NanodaDirectError(f"{slug}: {exc}") from exc
    try:
        lean_dir = judge.island_dir(telperion_root, island)
    except judge.JudgeError as exc:
        raise NanodaDirectError(f"{slug}: {exc}") from exc
    module = judge.module_name_of(lean_dir, artifact)

    ga = judge._guard_anchors()
    try:
        theorem = ga.resolve_theorem(artifact.read_text(), stmt.read_text())
    except ga.RegistryError as exc:
        raise NanodaDirectError(f"{slug}: cannot resolve its registered theorem: {exc}") from exc

    try:
        cur_closure = closure_digest(campaign_root, node)
        cur_files = closure_files(campaign_root, node)
    except ClosureError as exc:
        raise NanodaDirectError(f"{slug}: cannot resolve its import closure: {exc}") from exc
    art_sha = sha256_file(artifact)

    out = Path(tools.out_dir) / slug
    out.mkdir(parents=True, exist_ok=True)
    export_path = out / "export.txt"
    cfg_path = out / "nanoda.json"

    export_rc, export_out = run(export_cmd(lean_dir, module, theorem, tools.lean4export),
                                cwd=lean_dir)
    export_path.write_text(export_out)
    cfg_path.write_text(json.dumps(nanoda_config(export_path)))
    nanoda_rc, nanoda_out = run([str(tools.nanoda), str(cfg_path)], cwd=out)

    lines = [
        f"REJUDGE-HEADER node={slug} artifact_sha256={art_sha} closure_sha256={cur_closure}",
        "REJUDGE-ROUTE nanoda-direct",
        f"REJUDGE-INFO artifact={artifact} theorem={theorem} module={module} island={island}",
        f"REJUDGE-INFO nanoda_rev={tools.nanoda_rev} nanoda_bin={tools.nanoda} "
        f"lean4export={tools.lean4export}",
        f"REJUDGE-INFO closure_files={len(cur_files)}",
        f"==================== REJUDGE-EXPORT exit={export_rc} ====================",
        export_out,
        f"==================== REJUDGE-NANODA exit={nanoda_rc} ====================",
        nanoda_out,
    ]
    log_path = out / "rejudge.log"
    log_path.write_text("\n".join(lines) + "\n")
    return log_path
