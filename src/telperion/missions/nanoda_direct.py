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

    `print_axioms` is false: its default is true (util.rs:938), and with no pretty-print
    destination configured nanoda appends "Unable to print axioms" (pretty_printer.rs:384) --
    AFTER `check_all_declars` already accepted the proof (main.rs:27-30), so it is output-only
    and does not affect trust, but it is not the `_SUCCESS_RE` shape `classify` accepts.
    """
    return {
        "export_file_path": str(export_path),
        "permitted_axioms": list(PERMITTED_AXIOMS),
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
        "print_axioms": False,
    }


#: main.rs:34 -- the ONLY success-message shape this route accepts (print_success_message
#: true, permitted_axioms non-empty so `skipped_axioms` stays empty: unpermitted_axiom_hard_error
#: is always true here, so a run that skipped rather than erred on an axiom never happens).
_SUCCESS_RE = re.compile(r"^Checked (?P<n>\d+) declarations? with no errors$")


def _has_error_line(text: str) -> bool:
    return any(l.strip().lower().startswith(("error", "uncaught exception"))
               for l in text.splitlines())


#: Review fix round 1 (2026-10-28), item 5: `LEAN_ABORT_ON_PANIC=1` (same as Comparator sets
#: for its own export) turns a Lean panic during the export into a hard abort instead of a
#: value that might otherwise still produce SOME export text. Lean's panic report starts the
#: line with "PANIC" (e.g. "PANIC at ... : unknown constant ..."); any such line fails.
def _has_panic_line(text: str) -> bool:
    return any(l.strip().startswith("PANIC") for l in text.splitlines())


def classify(export_rc: int, export_out: str, nanoda_rc: int, nanoda_out: str) -> str:
    """"pass" iff lean4export exited 0 and exported something, with no line starting
    "error"/"uncaught exception"/"PANIC"; nanoda exited 0 with no "error"/"uncaught
    exception" line; and nanoda's own success line (main.rs:34) names a declaration count --
    appearing EXACTLY ONCE, and that count is >= 1.

    Review fix round 1 (2026-10-28), item 4: before this, the FIRST matching success line won
    even when a second, contradictory one followed (e.g. "Checked 5" then "Checked 0") --
    that shape must fail, not silently read the first number. Item 5: a PANIC line in the
    export (Lean aborts hard under `LEAN_ABORT_ON_PANIC=1`, e.g. "PANIC ... Constant not
    found") fails even if lean4export's own exit code were somehow 0.

    The zero-declarations case (Review Focus 3, step 0b): an empty or mistargeted export
    still makes nanoda print "Checked 0 declarations with no errors" and exit 0 -- that reads
    like success but asserts nothing, so it is FAIL here, never PASS.
    """
    if (export_rc != 0 or not export_out.strip() or _has_error_line(export_out)
            or _has_panic_line(export_out)):
        return "fail"
    if nanoda_rc != 0 or _has_error_line(nanoda_out):
        return "fail"
    matches = [m for m in (_SUCCESS_RE.match(l.strip()) for l in nanoda_out.splitlines())
              if m is not None]
    if len(matches) != 1:
        return "fail"      # zero: no success line at all; two+: ambiguous/contradictory
    if int(matches[0].group("n")) < 1:
        return "fail"      # zero declarations checked
    return "pass"


#: The delimiters `run_direct` writes around the raw export / nanoda output, in that order --
#: the nanoda-direct analogue of rejudge.py's `_PART_RE` for a Comparator log.
_SECTION_RE = re.compile(r"^=+\s*REJUDGE-(?P<which>EXPORT|NANODA)\s+exit=(?P<rc>-?\d+)\s*=+$")

#: The exact line 2 this route's logs carry (`run_direct` writes it verbatim). Review fix
#: round 1 (2026-10-28), item 4: requiring the LITERAL line, not just "a line matching the
#: route pattern somewhere", is what makes a decoy `REJUDGE-ROUTE nanoda-direct` line buried
#: inside the export/nanoda tool output harmless -- it is never reached as "the" route line
#: unless it is actually on line 2.
_ROUTE_LINE = "REJUDGE-ROUTE nanoda-direct"


def _parse_sections(text: str) -> Optional[Tuple[int, str, int, str]]:
    """Strict structure (Review fix round 1, item 4): line 1 a REJUDGE-HEADER, line 2 exactly
    `REJUDGE-ROUTE nanoda-direct`, then zero or more blank/`REJUDGE-INFO` lines, then EXACTLY
    one EXPORT section immediately followed by EXACTLY one NANODA section (in that order) and
    nothing after it. Anything else -- a missing header, a route line that isn't on line 2 (a
    decoy deeper in the tool output included), a duplicate or out-of-order section, or stray
    content where only `REJUDGE-INFO`/blank lines belong -- returns None (fail)."""
    from . import rejudge as _rejudge
    lines = text.splitlines()
    if len(lines) < 2:
        return None
    if not _rejudge.is_rejudge_header_line(lines[0]):
        return None
    if lines[1].strip() != _ROUTE_LINE:
        return None
    i = 2
    while i < len(lines) and (not lines[i].strip() or lines[i].strip().startswith("REJUDGE-INFO")):
        i += 1
    if i >= len(lines):
        return None
    m = _SECTION_RE.match(lines[i].strip())
    if m is None or m.group("which") != "EXPORT":
        return None
    export_rc = int(m.group("rc"))
    i += 1
    export_body: List[str] = []
    while i < len(lines) and _SECTION_RE.match(lines[i].strip()) is None:
        export_body.append(lines[i])
        i += 1
    if i >= len(lines):
        return None
    m2 = _SECTION_RE.match(lines[i].strip())
    if m2.group("which") != "NANODA":
        return None            # a second EXPORT (or anything but NANODA) right after the first
    nanoda_rc = int(m2.group("rc"))
    i += 1
    nanoda_body: List[str] = []
    while i < len(lines):
        if _SECTION_RE.match(lines[i].strip()) is not None:
            return None        # a THIRD section delimiter -- a duplicate, not allowed
        nanoda_body.append(lines[i])
        i += 1
    return export_rc, "\n".join(export_body), nanoda_rc, "\n".join(nanoda_body)


def verdict_of_log(text: str) -> str:
    """"pass"/"fail" of a whole nanoda-direct node log, as `run_direct` writes it: find the
    `REJUDGE-EXPORT exit=<rc>` and `REJUDGE-NANODA exit=<rc>` sections (see `_parse_sections`
    for the exact structure required) and `classify` their recorded output. A log that does
    not match that structure -- including one with no header at all -- is "fail": there is
    nothing a pass could be about."""
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


#: `run(cmd, cwd=...) -> (returncode, stdout, stderr)`, injected so tests never invoke lake,
#: lean4export or nanoda_bin. Review fix round 1 (2026-10-28), item 5: stdout and stderr come
#: back SEPARATELY -- `run_direct` writes only stdout to `export.txt` (the file nanoda reads
#: as `export_file_path`; stderr mixed in would not be valid ndjson), while the node LOG gets
#: both, so a PANIC on stderr is still visible to a later re-parse. Production wiring (the
#: queue script, not this module) supplies a `run` that applies leanlock/ARDA_LEAN_SLOTS and
#: `LEAN_ABORT_ON_PANIC=1` around a Lean invocation (`cmd[0] == "lake"`) and calls nanoda_bin
#: straight.
RunFn = Callable[..., Tuple[int, str, str]]


def run_direct(campaign_root, node, *, tools: Tools, run: RunFn,
               pre_artifact_sha256: Optional[str] = None,
               pre_closure_sha256: Optional[str] = None) -> Path:
    """Export the node's OWN registered theorem and its closure, run nanoda on it, and write
    one node log: the `REJUDGE-HEADER` (artifact sha256 + closure sha256, exactly as
    `rejudge-record` computes them), `REJUDGE-ROUTE nanoda-direct`, informational lines, then
    the raw export and nanoda output under `REJUDGE-EXPORT`/`REJUDGE-NANODA` delimiters.
    Returns the log path. Raises `NanodaDirectError` (writes nothing) when the node's artifact,
    island, theorem or import closure cannot be resolved -- there is no verdict to log yet.

    Review fix round 2 (2026-10-28), gap 2 (soundness): *pre_artifact_sha256*/
    *pre_closure_sha256* are the digests the CALLER took before `lake build`-ing the artifact
    module (the queue script hashes before `timed_build`, not after) -- they are what the
    header binds to. After the whole run (export AND nanoda), the artifact and closure are
    re-hashed; if either no longer matches, the source changed mid-run, so the `.olean`
    lean4export read (and everything nanoda then checked) may not be what the pre-build hash
    promised. That is recorded as a failing line in the NANODA section (so `classify`'s own
    error-line check fails it, never a silent pass for the wrong source) rather than a
    separate out-of-band signal. Omitting either falls back to hashing at call time (every
    existing caller/test that does not pre-hash keeps its previous behaviour).
    """
    from . import judge
    from .provenance import (
        ClosureError, ProvenanceError, closure_digest, closure_files, lake_workspace,
        sha256_file,
    )
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

    # Controller Ruling 0b-7 (2026-10-28): `lean_dir` (the island root) is only used to
    # derive the MODULE name above -- the actual `lake`/`lean4export` invocation runs
    # from `lake_workspace`'s smaller directory when one declares the module (e.g.
    # zzl_aux under zeta_zero_localization, 23 libs vs. the island's 27,090; `lake env`
    # at the island root emits enough environment to exceed macOS ARG_MAX, so every
    # process lake spawns there fails outright). For every island without such a
    # sub-workspace, `lake_workspace` returns `lean_dir` unchanged.
    try:
        workspace = lake_workspace(campaign_root, node)
    except ProvenanceError as exc:
        raise NanodaDirectError(f"{slug}: cannot resolve its lake workspace: {exc}") from exc
    try:
        workspace_rel = workspace.relative_to(telperion_root)
    except ValueError:
        workspace_rel = workspace

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
    # The digests the header actually binds to: the pre-build ones when the caller took them
    # (the queue script does, right before `timed_build`), else what was just computed above.
    header_art_sha = pre_artifact_sha256 or art_sha
    header_closure = pre_closure_sha256 or cur_closure

    out = Path(tools.out_dir) / slug
    out.mkdir(parents=True, exist_ok=True)
    export_path = out / "export.txt"
    cfg_path = out / "nanoda.json"

    export_rc, export_stdout, export_stderr = run(
        export_cmd(workspace, module, theorem, tools.lean4export), cwd=workspace)
    # Review fix round 1 (2026-10-28), item 5: stdout ONLY into the file nanoda will read as
    # `export_file_path` -- stderr (where a Lean PANIC under LEAN_ABORT_ON_PANIC=1 lands)
    # must never be mixed into what is supposed to be a pure ndjson export.
    export_path.write_text(export_stdout)
    cfg_path.write_text(json.dumps(nanoda_config(export_path)))
    nanoda_rc, nanoda_stdout, nanoda_stderr = run([str(tools.nanoda), str(cfg_path)], cwd=out)

    # Review fix round 2 (2026-10-28), gap 2: re-hash AFTER the whole run and compare against
    # the pre-build digests the header just bound to. `closure_digest` raising ClosureError
    # here (e.g. an import removed mid-run) is itself a change, not a setup failure to raise
    # out of -- there is already a verdict to log by this point.
    post_art_sha = sha256_file(artifact) if artifact.is_file() else None
    try:
        post_closure = closure_digest(campaign_root, node)
    except ClosureError:
        post_closure = None
    sources_changed = post_art_sha != header_art_sha or post_closure != header_closure

    def _combined(stdout: str, stderr: str) -> str:
        return stdout if not stderr.strip() else stdout.rstrip("\n") + "\n--- stderr ---\n" + stderr

    nanoda_section = _combined(nanoda_stdout, nanoda_stderr)
    if sources_changed:
        nanoda_section = (nanoda_section.rstrip("\n") + "\nerror: sources changed during "
                          "the run (artifact/closure digest no longer matches the pre-build "
                          "digest the header is bound to)\n")

    lines = [
        f"REJUDGE-HEADER node={slug} artifact_sha256={header_art_sha} "
        f"closure_sha256={header_closure}",
        "REJUDGE-ROUTE nanoda-direct",
        f"REJUDGE-INFO artifact={artifact} theorem={theorem} module={module} island={island}",
        f"REJUDGE-INFO workspace={workspace_rel}",
        f"REJUDGE-INFO nanoda_rev={tools.nanoda_rev} nanoda_bin={tools.nanoda} "
        f"lean4export={tools.lean4export}",
        f"REJUDGE-INFO closure_files={len(cur_files)}",
        f"==================== REJUDGE-EXPORT exit={export_rc} ====================",
        _combined(export_stdout, export_stderr),
        f"==================== REJUDGE-NANODA exit={nanoda_rc} ====================",
        nanoda_section,
    ]
    log_path = out / "rejudge.log"
    log_path.write_text("\n".join(lines) + "\n")
    return log_path
