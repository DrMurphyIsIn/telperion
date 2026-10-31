"""The island registry (step 6): an island is an external Lean library Telperion has replayed itself (Comparator
with nanoda at the pinned NANODA_REV, plus the step-4 statement checks). Its pinned registration lives in
`<root>/islands/<name>/`, and library source never does:

    island.toml       the pin, the intended theorems and, once a replay passes, its [replay] record
    challenge.lean    a byte copy of the library's challenge file, its sha256 in island.toml
    comparator.json   OUR Comparator config: the three standard axioms, enable_nanoda, exactly the theorems
    replay/           the archived evidence of the passing replay (Ruling 6): comparator.log.xz (the Comparator log,
                      xz-compressed), probe-<sha256>.json (one `probe-negation --json` output per theorem) and
                      fingerprint.json (one `fingerprint --json` output for all of them); their sha256s are in
                      [replay] (log_sha256 is of the UNCOMPRESSED log)
    REPLAY.md         a generated human summary of the registration and of every replay; nothing reads it

Three commands write a registration (Task 2):

- `island add` clones the library at the pin (into `~/telperion-tools/islands/<name>/src`, outside the repo),
  copies the challenge file byte for byte, and writes island.toml without [replay], our comparator.json and
  REPLAY.md. It builds nothing.
- `island record-replay` ingests a replay run elsewhere (owner decision 2026-10-31: island replays run in a remote
  sandbox, never on the owner's machine): the Comparator log, the probe JSONs and the fingerprint JSON.
- `island replay` runs the same replay itself, through an injected `run`. It builds and executes the library's
  code, so it MUST RUN INSIDE A SANDBOX; we never run it locally.

Both replay commands judge their evidence with ONE function, `evaluate_replay`, and `island_problems` re-judges the
archived evidence with that same function on every check. On PASS the evidence is archived under replay/ and
[replay] is written; on FAIL nothing is written but a REPLAY.md section, and an earlier [replay] is dropped.

What `verified` means: island.toml is well formed and pinned, the challenge copy is intact, our comparator.json
is the standard one, and the archived evidence is present, matches its recorded sha256s and still parses to PASS
for this pin, this challenge and the pinned nanoda. It does NOT prove that a run happened: whoever ran the
sandbox could have written the log and the JSONs by hand. The anchor is the independent auditor's review of the
run itself; `verified` only says the evidence on file is complete and internally consistent.

`verified` is all or nothing: `island_problems` lists everything that keeps an island from it, including "not
replayed yet", and `status` is "verified" iff that list is empty, "self-reported" otherwise. In particular a
replay counts only for the pin and the challenge it ran on (the plan's Review Focus 1 and 2): moving `commit`,
editing challenge.lean, or bumping NANODA_REV drops the island to self-reported until it is re-replayed.

Every read fails closed: `islands/`, `islands/<name>/` and `islands/<name>/replay/` must be real directories, not
symlinks; every file goes through `guarded_read.read_guarded` (no symlink, a regular file, at most `MAX_BYTES`,
and the log at most `LOG_MAX_BYTES` once decompressed); a decode, TOML, JSON or xz error is a problem string, never
an exception. A name is checked against `[a-z0-9-]+` before any path is built from it, so nothing outside
`<root>/islands/<name>/` is ever read on a caller's say-so. Names reach git, lake and Lean only as list elements of
an argv (no shell).
"""
from __future__ import annotations

import datetime
import hashlib
import json
import lzma
import os
import re
import shlex
import shutil
import stat
import sys
import tempfile
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Optional, Sequence

from .guarded_read import read_guarded

ISLANDS_DIR = "islands"
ISLAND_TOML = "island.toml"
CHALLENGE_FILE = "challenge.lean"
COMPARATOR_FILE = "comparator.json"
REPLAY_FILE = "REPLAY.md"
REPLAY_DIR = "replay"
LOG_ARCHIVE = "comparator.log.xz"
FINGERPRINT_ARCHIVE = "fingerprint.json"

#: Upper bound on every registry file. A real one is a few kilobytes; refusing anything larger before decoding keeps
#: a hostile file from costing more than a stat.
MAX_BYTES = 1 << 20
#: Upper bound on a Comparator log, uncompressed (the real riemann-jensen log is 16 KB). Decompression stops here.
LOG_MAX_BYTES = 32 << 20

#: The negation-probe verdicts a verified island's theorems may carry (step 4).
PASSING_PROBES = ("PROBE_ONLY", "WITNESSED")

#: Where `island add` clones and `island replay` finds its tools, unless told otherwise.
DEFAULT_TOOLS = Path.home() / "telperion-tools"
DEFAULT_LEANLOCK = Path.home() / "hodge-engine" / "leanlock.sh"

_NAME_RE = re.compile(r"[a-z0-9-]+")
_HEX40 = re.compile(r"[0-9a-f]{40}")
_HEX64 = re.compile(r"[0-9a-f]{64}")
_TAG_RE = re.compile(r"v\d+\.\d+\.\d+(?:-rc\d+)?")
_TOOLCHAIN_PREFIX = "leanprover/lean4:"

_TOP_KEYS = ("name", "source", "commit", "toolchain", "licence", "challenge_module", "solution_module",
             "challenge_sha256", "theorems", "intended_use")
_REPLAY_KEYS = ("date", "commit", "challenge_sha256", "nanoda_rev", "comparator_tag", "log_sha256", "probe_sha256",
                "fingerprint_sha256", "verdict", "checks")
_CHECK_KEYS = ("probe", "fingerprint")
_COMPARATOR_KEYS = ("challenge_module", "solution_module", "theorem_names", "permitted_axioms", "enable_nanoda")


class IslandError(Exception):
    """An island that does not exist, cannot be read, or is not verified where that is required."""


@dataclass(frozen=True)
class TheoremCheck:
    probe: str
    fingerprint: str


@dataclass(frozen=True)
class Replay:
    date: str
    commit: str
    challenge_sha256: str
    nanoda_rev: str
    comparator_tag: str
    log_sha256: str
    verdict: str
    checks: tuple[tuple[str, TheoremCheck], ...]
    probe_sha256: tuple[tuple[str, str], ...] = ()
    fingerprint_sha256: str = ""


@dataclass(frozen=True)
class Island:
    name: str
    source: str
    commit: str
    toolchain: str
    licence: str
    challenge_module: str
    solution_module: str
    challenge_sha256: str
    theorems: tuple[str, ...]
    intended_use: str
    replay: Optional[Replay]


# --- paths and guarded reads ------------------------------------------------------------------------------------------

def _name_problem(name) -> Optional[str]:
    if not isinstance(name, str) or not _NAME_RE.fullmatch(name):
        return "not a valid island name (lowercase letters, digits and '-' only)"
    return None


def _root_problem(root: Path) -> Optional[str]:
    """Why `<root>/islands` cannot be trusted, or None (also None when it does not exist)."""
    try:
        st = (Path(root) / ISLANDS_DIR).lstat()
    except FileNotFoundError:
        return None
    except OSError as exc:
        return f"{ISLANDS_DIR}/ could not be read ({exc.strerror or exc})"
    if stat.S_ISLNK(st.st_mode):
        return f"{ISLANDS_DIR}/ is a symlink in the working tree; refusing to read the registry through it"
    if not stat.S_ISDIR(st.st_mode):
        return f"{ISLANDS_DIR} is not a directory; refusing to read the registry"
    return None


def _dir_problem(root: Path, name: str) -> Optional[str]:
    """Why `<root>/islands/<name>/` cannot be read as an island directory, or None. *name* is already valid."""
    problem = _root_problem(root)
    if problem:
        return problem
    try:
        st = (Path(root) / ISLANDS_DIR / name).lstat()
    except FileNotFoundError:
        return f"no such island (no directory {ISLANDS_DIR}/{name}/)"
    except OSError as exc:
        return f"{ISLANDS_DIR}/{name}/ could not be read ({exc.strerror or exc})"
    if stat.S_ISLNK(st.st_mode):
        return f"{ISLANDS_DIR}/{name}/ is a symlink in the working tree; refusing to read the island through it"
    if not stat.S_ISDIR(st.st_mode):
        return f"{ISLANDS_DIR}/{name} is not a directory"
    return None


def _read(root: Path, name: str, filename: str) -> tuple[Optional[bytes], Optional[str]]:
    """`(data, None)` or `(None, problem)`; a missing file is a problem too. Call only after `_dir_problem`."""
    data, problem = read_guarded(Path(root) / ISLANDS_DIR / name / filename, label=filename, max_bytes=MAX_BYTES)
    if data is None:
        return None, problem or f"{filename} is missing"
    return data, None


def _read_text(root: Path, name: str, filename: str) -> tuple[Optional[str], Optional[str]]:
    data, problem = _read(root, name, filename)
    if data is None:
        return None, problem
    try:
        return data.decode("utf-8"), None
    except UnicodeDecodeError:
        return None, f"{filename} is not valid UTF-8; refusing to trust it."


def _load_doc(root: Path, name: str) -> tuple[Optional[dict], Optional[str]]:
    """island.toml as a dict, or `(None, problem)`: a bad name, an untrusted directory, or an unreadable file."""
    problem = _name_problem(name) or _dir_problem(root, name)
    if problem:
        return None, problem
    text, problem = _read_text(root, name, ISLAND_TOML)
    if text is None:
        return None, problem
    try:
        return tomllib.loads(text), None
    except Exception as exc:  # TOMLDecodeError, or whatever else a hostile file provokes
        return None, f"{ISLAND_TOML} is not valid TOML ({exc})"


def island_names(root: Path) -> tuple[list[str], list[str]]:
    """`(names, problems)`: every entry of `<root>/islands/` that is a directory or a symlink (a symlinked island is
    listed so that checking it reports the refusal), sorted; plain files there (a README) are not islands. No
    `islands/` at all is an empty registry. A symlinked or unreadable `islands/` gives no names and a problem."""
    problem = _root_problem(root)
    if problem:
        return [], [problem]
    d = Path(root) / ISLANDS_DIR
    if not d.exists():
        return [], []
    names = []
    try:
        for entry in d.iterdir():
            st = entry.lstat()
            if stat.S_ISDIR(st.st_mode) or stat.S_ISLNK(st.st_mode):
                names.append(entry.name)
    except OSError as exc:
        return [], [f"{ISLANDS_DIR}/ could not be listed ({exc.strerror or exc})"]
    return sorted(names), []


def island_toolchain(root: Path, name: str) -> tuple[Optional[str], Optional[str]]:
    """`(toolchain, None)` or `(None, problem)`, for the kernel policy: island.toml's `toolchain`, read through the
    SAME guarded read and strict schema as `island check` (Ruling 6), so the two never disagree about whether a
    registration is well formed; any schema problem is the policy's problem too."""
    doc, problem = _load_doc(root, name)
    if doc is None:
        return None, problem
    isl, probs = _schema(doc, name)
    if isl is None:
        return None, f"island {name!r}: " + "; ".join(probs)
    return isl.toolchain, None


def pinned_nanoda_rev() -> tuple[Optional[str], Optional[str]]:
    """The engine's pinned nanoda rev (`<project>/NANODA_REV`), or `(None, problem)`."""
    from . import paths
    data, problem = read_guarded(paths.project_root() / "NANODA_REV", label="NANODA_REV", max_bytes=4096)
    if data is None:
        return None, problem or "NANODA_REV is missing"
    rev = data.decode("utf-8", errors="replace").strip()
    if not _HEX40.fullmatch(rev):
        return None, "NANODA_REV is not 40 lowercase hex digits"
    return rev, None


# --- the schema -------------------------------------------------------------------------------------------------------

def _hex_problem(where: str, value, pattern: re.Pattern, n: int) -> Optional[str]:
    if not isinstance(value, str) or not pattern.fullmatch(value):
        return f"{where} must be {n} lowercase hex digits"
    return None


def _lean_name_problem(where: str, value) -> Optional[str]:
    from .checks.negation_probe import name_components
    if not isinstance(value, str) or not value.isascii():
        return f"{where} {value!r} is not an ASCII dotted Lean identifier"
    try:
        name_components(value)
    except ValueError:
        return f"{where} {value!r} is not a plain dotted Lean identifier"
    return None


def _str_problem(where: str, value) -> Optional[str]:
    if not isinstance(value, str) or not value.strip():
        return f"{where} must be a non-empty string"
    return None


def _date_ok(date) -> bool:
    try:
        return isinstance(date, str) and len(date) == 10 and datetime.date.fromisoformat(date) is not None
    except ValueError:
        return False


def _unknown_keys(where: str, table: dict, allowed) -> list[str]:
    return [f"{where} has an unknown key {k!r}" for k in sorted(set(table) - set(allowed))]


def _replay_schema(rep) -> tuple[Optional[Replay], list[str]]:
    if not isinstance(rep, dict):
        return None, ["[replay] must be a table"]
    probs = _unknown_keys("[replay]", rep, _REPLAY_KEYS)
    probs += [f"[replay] is missing {k!r}" for k in _REPLAY_KEYS if k not in rep]
    if probs:
        return None, probs
    if not _date_ok(rep["date"]):
        probs.append("[replay] date must be an ISO date string (YYYY-MM-DD)")
    for key, pattern, n in (("commit", _HEX40, 40), ("nanoda_rev", _HEX40, 40), ("challenge_sha256", _HEX64, 64),
                            ("log_sha256", _HEX64, 64), ("fingerprint_sha256", _HEX64, 64)):
        p = _hex_problem(f"[replay] {key}", rep[key], pattern, n)
        if p:
            probs.append(p)
    if not isinstance(rep["comparator_tag"], str) or not _TAG_RE.fullmatch(rep["comparator_tag"]):
        probs.append("[replay] comparator_tag must look like vX.Y.Z or vX.Y.Z-rcN")
    if rep["verdict"] not in ("pass", "fail"):
        probs.append("[replay] verdict must be \"pass\" or \"fail\"")
    probe_sha: list[tuple[str, str]] = []
    if not isinstance(rep["probe_sha256"], dict):
        probs.append("[replay.probe_sha256] must be a table { <theorem> = <sha256 of its probe JSON> }")
    else:
        for thm, sha in rep["probe_sha256"].items():
            p = (_lean_name_problem("[replay.probe_sha256] key", thm)
                 or _hex_problem(f"[replay.probe_sha256] {thm!r}", sha, _HEX64, 64))
            if p:
                probs.append(p)
            else:
                probe_sha.append((thm, sha))
    from .checks.negation_probe import VERDICTS
    checks = rep["checks"]
    entries: list[tuple[str, TheoremCheck]] = []
    if not isinstance(checks, dict):
        probs.append("[replay.checks] must be a table")
    else:
        for thm, entry in checks.items():
            p = _lean_name_problem("[replay.checks] key", thm)
            if p:
                probs.append(p)
                continue
            if not isinstance(entry, dict):
                probs.append(f"[replay.checks] {thm!r} must be a table {{ probe, fingerprint }}")
                continue
            sub = _unknown_keys(f"[replay.checks] {thm!r}", entry, _CHECK_KEYS)
            sub += [f"[replay.checks] {thm!r} is missing {k!r}" for k in _CHECK_KEYS if k not in entry]
            if not sub:
                if entry["probe"] not in VERDICTS:
                    sub.append(f"[replay.checks] {thm!r} probe {entry['probe']!r} is not one of {', '.join(VERDICTS)}")
                p = _hex_problem(f"[replay.checks] {thm!r} fingerprint", entry["fingerprint"], _HEX64, 64)
                if p:
                    sub.append(p)
            probs += sub
            if not sub:
                entries.append((thm, TheoremCheck(entry["probe"], entry["fingerprint"])))
    if probs:
        return None, probs
    return Replay(date=rep["date"], commit=rep["commit"], challenge_sha256=rep["challenge_sha256"],
                  nanoda_rev=rep["nanoda_rev"], comparator_tag=rep["comparator_tag"], log_sha256=rep["log_sha256"],
                  verdict=rep["verdict"], checks=tuple(sorted(entries)), probe_sha256=tuple(sorted(probe_sha)),
                  fingerprint_sha256=rep["fingerprint_sha256"]), []


def _schema(doc: dict, name: str) -> tuple[Optional[Island], list[str]]:
    """`(island, [])` when *doc* has exactly island.toml's shape, else `(None, every problem found)`."""
    probs = _unknown_keys(ISLAND_TOML, doc, _TOP_KEYS + ("replay",))
    probs += [f"{ISLAND_TOML} is missing {k!r}" for k in _TOP_KEYS if k not in doc]
    g = doc.get
    if "name" in doc and g("name") != name:
        probs.append(f"name {g('name')!r} must equal the directory name {name!r}")
    if "source" in doc and _source_problem(g("source")):
        probs.append(_source_problem(g("source")))
    if "commit" in doc:
        probs += filter(None, [_hex_problem("commit", g("commit"), _HEX40, 40)])
    if "challenge_sha256" in doc:
        probs += filter(None, [_hex_problem("challenge_sha256", g("challenge_sha256"), _HEX64, 64)])
    if "toolchain" in doc:
        probs += filter(None, [_toolchain_problem(g("toolchain"))])
    for key in ("licence", "intended_use"):
        if key in doc:
            probs += filter(None, [_str_problem(key, g(key))])
    for key in ("challenge_module", "solution_module"):
        if key in doc:
            probs += filter(None, [_lean_name_problem(key, g(key))])
    theorems = g("theorems")
    if "theorems" in doc:
        if not isinstance(theorems, list) or not theorems:
            probs.append("theorems must be a non-empty array of theorem names")
        else:
            probs += filter(None, [_lean_name_problem("theorem", t) for t in theorems])
            dups = sorted({t for t in theorems if isinstance(t, str) and theorems.count(t) > 1})
            probs += [f"theorem {t!r} is listed more than once" for t in dups]
    replay = None
    if "replay" in doc:
        replay, rprobs = _replay_schema(doc["replay"])
        probs += rprobs
    if probs:
        return None, probs
    return Island(name=g("name"), source=g("source"), commit=g("commit"), toolchain=g("toolchain"),
                  licence=g("licence"), challenge_module=g("challenge_module"),
                  solution_module=g("solution_module"), challenge_sha256=g("challenge_sha256"),
                  theorems=tuple(theorems), intended_use=g("intended_use"), replay=replay), []


def _source_problem(source) -> Optional[str]:
    if not isinstance(source, str) or not source.startswith("https://") or any(ch.isspace() for ch in source):
        return "source must be an https:// URL"
    return None


def _toolchain_problem(tc) -> Optional[str]:
    if (not isinstance(tc, str) or not tc.startswith(_TOOLCHAIN_PREFIX)
            or not _TAG_RE.fullmatch(tc[len(_TOOLCHAIN_PREFIX):])):
        return f"toolchain {tc!r} must be {_TOOLCHAIN_PREFIX}vX.Y.Z or {_TOOLCHAIN_PREFIX}vX.Y.Z-rcN"
    return None


def load_island(root: Path, name: str) -> Island:
    """island.toml of `<root>/islands/<name>/`, schema-checked. `IslandError` for an invalid or unknown name, an
    untrusted directory, an unreadable file or any schema problem. Says nothing about whether it is verified."""
    doc, problem = _load_doc(root, name)
    if doc is None:
        raise IslandError(f"island {name!r}: {problem}")
    isl, probs = _schema(doc, name)
    if isl is None:
        raise IslandError(f"island {name!r}: " + "; ".join(probs))
    return isl


# --- the Comparator log -----------------------------------------------------------------------------------------------
#
# The format is the one the real riemann-jensen spec run wrote (standalone Comparator e3dcf308, v4.35.0; the
# auditor holds the log, md5 76bc5e06; a scrubbed copy is tests/fixtures/islands/rj_spec.out) and the one
# `replay_island` writes:
#
#   ISLAND-HEADER island=<name> commit=<40 hex> challenge_sha256=<64 hex>      the first line, written by the runner
#   COMPARATOR_NANODA <md5 of nanoda_bin> (nanoda_lib <40 hex>)                 which nanoda the runner gave Comparator
#   Exporting #[..., <every theorem>, ...] from <challenge module>             Comparator's own lines from here on
#   Exporting #[..., <every theorem>, ...] from <solution module>
#   nanoda kernel accepts the solution            (v4.32.0 / v4.33.0-rc2 print "Nanoda kernel ...")
#   Lean default kernel accepts the solution
#   Your solution is okay!
#   ISLAND-<label>-EXIT <Comparator's exit code>                                written by the runner

_HEADER_RE = re.compile(r"ISLAND-HEADER island=(?P<island>\S+) commit=(?P<commit>[0-9a-f]{40}) "
                        r"challenge_sha256=(?P<sha>[0-9a-f]{64})")
_EXIT_RE = re.compile(r"ISLAND-(?P<label>[A-Za-z0-9_.-]+?)-EXIT (?P<rc>-?\d+)")
_NANODA_RE = re.compile(r"COMPARATOR_NANODA [0-9a-f]{32} \(nanoda_lib (?P<rev>[0-9a-f]{40})\)")
_EXPORT_RE = re.compile(r"Exporting #\[(?P<names>[^\]]*)\] from (?P<module>\S+)")
#: The three accept lines, in the order Comparator prints them; each must be a whole line, exactly once.
ACCEPT_LINES = (("nanoda kernel accepts the solution", "Nanoda kernel accepts the solution"),
                ("Lean default kernel accepts the solution",),
                ("Your solution is okay!",))


@dataclass(frozen=True)
class ComparatorLog:
    """What `parse_comparator_log` read. `problems` are the format rules, independent of any island; the binding to
    an island (header, nanoda rev, exported theorems) is `comparator_log_problems`."""
    header: Optional[tuple[str, str, str]]          # (island, commit, challenge_sha256), from the first line
    nanoda_rev: Optional[str]                       # from the one COMPARATOR_NANODA line
    exit_code: Optional[int]                        # from the one ISLAND-<label>-EXIT line
    exports: tuple[tuple[str, tuple[str, ...]], ...]  # (module, exported names) per Exporting line
    problems: tuple[str, ...]


def parse_comparator_log(text: str) -> ComparatorLog:
    """Read one island Comparator log. A problem for: a first line that is not the ISLAND-HEADER, an ISLAND-HEADER
    anywhere else, an unknown `ISLAND-` line; not exactly one COMPARATOR_NANODA line; any accept line missing,
    repeated or out of order; any error line (starting "error" or "uncaught exception", as `rejudge` reads them)
    or any line reporting an unpermitted or illegal axiom; not exactly one exit line, a nonzero exit, or an exit line
    before "Your solution is okay!". Never raises."""
    from .missions.rejudge import _is_error_line
    lines = text.splitlines()
    probs: list[str] = []
    m = _HEADER_RE.fullmatch(lines[0].rstrip()) if lines else None
    header = (m["island"], m["commit"], m["sha"]) if m else None
    if m is None:
        probs.append("the first line is not an ISLAND-HEADER line (`ISLAND-HEADER island=<name> commit=<40 hex> "
                     "challenge_sha256=<64 hex>`, written by the runner before Comparator starts)")
    nanoda: list[str] = []
    exits: list[tuple[int, int]] = []
    accepts: list[list[int]] = [[] for _ in ACCEPT_LINES]
    exports: list[tuple[str, tuple[str, ...]]] = []
    for i, raw in enumerate(lines):
        s = raw.strip()
        if i == 0 and s.startswith("ISLAND-"):
            continue                       # the header, or a first line already reported as no header
        if s.startswith("ISLAND-"):
            e = _EXIT_RE.fullmatch(s)
            if s.startswith("ISLAND-HEADER"):
                probs.append("an ISLAND-HEADER line appears after the first line (two runs in one log?)")
            elif e:
                exits.append((i, int(e["rc"])))
            else:
                probs.append(f"an unrecognised ISLAND- line {s[:120]!r}")
            continue
        if s.startswith("COMPARATOR_NANODA"):
            n = _NANODA_RE.fullmatch(s)
            if n:
                nanoda.append(n["rev"])
            else:
                probs.append(f"a malformed COMPARATOR_NANODA line {s[:120]!r}")
        if _is_error_line(raw):
            probs.append(f"an error line: {s[:200]!r}")
        low = s.lower()
        if "unpermitted axiom" in low or "illegal axiom" in low:
            probs.append(f"an axiom outside the permitted three: {s[:200]!r}")
        for k, variants in enumerate(ACCEPT_LINES):
            if s in variants:
                accepts[k].append(i)
        x = _EXPORT_RE.fullmatch(s)
        if x:
            exports.append((x["module"], tuple(n.strip() for n in x["names"].split(","))))
    if not nanoda:
        probs.append("no COMPARATOR_NANODA line (`COMPARATOR_NANODA <md5> (nanoda_lib <40 hex>)`): the log does not "
                     "say which nanoda Comparator ran")
    elif len(nanoda) > 1:
        probs.append("more than one COMPARATOR_NANODA line")
    for k, variants in enumerate(ACCEPT_LINES):
        if not accepts[k]:
            alt = f" (or {variants[1]!r})" if len(variants) > 1 else ""
            probs.append(f"no line {variants[0]!r}{alt}: Comparator did not accept the solution")
        elif len(accepts[k]) > 1:
            probs.append(f"the line {variants[0]!r} appears more than once (two runs in one log?)")
    firsts = [a[0] for a in accepts if len(a) == 1]
    if len(firsts) == len(ACCEPT_LINES) and firsts != sorted(firsts):
        probs.append("the accept lines are out of order (nanoda, then the Lean kernel, then 'Your solution is okay!')")
    exit_code = None
    if not exits:
        probs.append("no exit line (`ISLAND-<label>-EXIT <code>`): Comparator's exit code is not recorded")
    elif len(exits) > 1:
        probs.append("more than one exit line (`ISLAND-<label>-EXIT`)")
    else:
        idx, exit_code = exits[0]
        if exit_code != 0:
            probs.append(f"the exit line says Comparator exited {exit_code}, not 0")
        if len(accepts[2]) == 1 and idx < accepts[2][0]:
            probs.append("the exit line comes before 'Your solution is okay!'")
    return ComparatorLog(header=header, nanoda_rev=nanoda[0] if len(nanoda) == 1 else None, exit_code=exit_code,
                         exports=tuple(exports), problems=tuple(probs))


def comparator_log_problems(text: str, isl: Island, nanoda_rev: Optional[str]) -> list[str]:
    """Everything that keeps *text* from being a passing Comparator log for *isl*: the format rules
    (`parse_comparator_log`), a header naming another island, commit or challenge sha256, a nanoda other than
    *nanoda_rev*, and an export from the challenge or the solution module (exactly one each, and from no other
    module) that leaves out one of the island's theorems. Empty iff it passes. Never raises."""
    log = parse_comparator_log(text)
    probs = list(log.problems)
    if log.header is not None:
        island, commit, sha = log.header
        if island != isl.name:
            probs.append(f"the ISLAND-HEADER names island {island!r}, not {isl.name!r}")
        if commit != isl.commit:
            probs.append(f"the ISLAND-HEADER commit {commit} is not the pin {isl.commit}")
        if sha != isl.challenge_sha256:
            probs.append(f"the ISLAND-HEADER challenge_sha256 {sha} is not the registered {isl.challenge_sha256}")
    if nanoda_rev is None:
        probs.append("cannot compare the log's nanoda with NANODA_REV: the pin could not be read")
    elif log.nanoda_rev is not None and log.nanoda_rev != nanoda_rev:
        probs.append(f"Comparator ran nanoda_lib {log.nanoda_rev}, not the pinned NANODA_REV {nanoda_rev}")
    for module in (isl.challenge_module, isl.solution_module):
        found = [names for mod, names in log.exports if mod == module]
        if not found:
            probs.append(f"no `Exporting #[...] from {module}` line: Comparator did not export {module}")
        elif len(found) > 1:
            probs.append(f"more than one `Exporting #[...] from {module}` line")
        else:
            missing = [t for t in isl.theorems if t not in found[0]]
            if missing:
                probs.append(f"the export from {module} does not include {', '.join(missing)}")
    for mod in sorted({mod for mod, _ in log.exports} - {isl.challenge_module, isl.solution_module}):
        probs.append(f"an export from {mod}, which is neither the challenge nor the solution module")
    return probs


# --- the probe and fingerprint JSONs ----------------------------------------------------------------------------------

def _short(value) -> str:
    """repr(value), cut to 80 characters: a hostile JSON value never floods a problem string."""
    r = repr(value)
    return r if len(r) <= 80 else r[:77] + "..."


def _common_json_problems(what: str, doc: dict, isl: Island) -> list[str]:
    """The fields `probe-negation --json` and `fingerprint --json` share: the challenge module, the challenge
    file's sha256 (both must be run with `--file <the challenge file>`), not stale, a replayed closure digest."""
    probs = []
    if doc.get("module") != isl.challenge_module:
        probs.append(f"{what} is of module {_short(doc.get('module'))}, not the challenge module "
                     f"{isl.challenge_module!r}")
    if doc.get("source_sha256") != isl.challenge_sha256:
        probs.append(f"{what} ran on source_sha256 {_short(doc.get('source_sha256'))}, not the registered challenge "
                     f"{isl.challenge_sha256} (run it with --file <the challenge file>)")
    if doc.get("stale"):
        probs.append(f"{what} says its --file was newer than the module's build (stale)")
    if not isinstance(doc.get("olean_sha256"), str) or not _HEX64.fullmatch(doc["olean_sha256"]):
        probs.append(f"{what} carries no olean_sha256 (the replayed closure it ran on)")
    return probs


def _probe_problems(doc, isl: Island) -> tuple[Optional[str], list[str]]:
    """`(theorem, problems)` for one `probe-negation --json` output; theorem is None when it names none of the
    island's theorems."""
    from .checks.negation_probe import VERDICTS
    if not isinstance(doc, dict):
        return None, ["a probe JSON is not a JSON object"]
    thm = doc.get("theorem")
    if not isinstance(thm, str) or thm not in isl.theorems:
        return None, [f"a probe JSON probed {_short(thm)}, which is not one of the island's theorems"]
    what = f"the probe JSON of {thm!r}"
    probs = []
    if doc.get("verdict") not in VERDICTS:
        probs.append(f"{what} has verdict {_short(doc.get('verdict'))}, not one of {', '.join(VERDICTS)}")
    return thm, probs + _common_json_problems(what, doc, isl)


def _fingerprint_problems(doc, isl: Island) -> list[str]:
    """Problems with the one `fingerprint --json` output, which must fingerprint exactly the island's theorems."""
    what = "the fingerprint JSON"
    if not isinstance(doc, dict):
        return [f"{what} is not a JSON object"]
    if "error" in doc:
        return [f"{what} reports an error ({str(doc['error'])[:200]!r}) and holds no fingerprints"]
    fps = doc.get("fingerprints")
    if not isinstance(fps, dict):
        return [f"{what} has no \"fingerprints\" object"]
    probs = [f"{what} has no fingerprint for theorem {t!r}" for t in isl.theorems if t not in fps]
    probs += [f"{what} fingerprints {_short(t)}, which is not one of the island's theorems"
              for t in sorted(set(fps) - set(isl.theorems), key=str)]
    probs += [f"{what}: the fingerprint of {t!r} is not 64 lowercase hex digits" for t in isl.theorems
              if t in fps and (not isinstance(fps[t], str) or not _HEX64.fullmatch(fps[t]))]
    if doc.get("mode") != "type":
        probs.append(f"{what} is a {_short(doc.get('mode'))}-mode fingerprint; a theorem's statement is "
                     "fingerprinted in type mode")
    return probs + _common_json_problems(what, doc, isl)


# --- the one verdict --------------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class ReplayVerdict:
    problems: tuple[str, ...]                 # empty iff the evidence passes
    checks: dict                              # theorem -> TheoremCheck, for each theorem fully evidenced


def evaluate_replay(isl: Island, *, log_text: str, probe_docs: Sequence, fingerprint_doc,
                    nanoda_rev: Optional[str], comparator_tag: str) -> ReplayVerdict:
    """THE verdict on one replay's evidence (Ruling 1), used by `island replay`, by `island record-replay` and, on
    the archived evidence, by every `island_problems`. PASS iff the problem list is empty:

    - the Comparator log passes for this island (`comparator_log_problems`): header = this pin and challenge, the
      three accept lines, nanoda at *nanoda_rev*, every theorem exported, exit 0;
    - *comparator_tag* is the island toolchain's version (the plan: tag = island toolchain);
    - exactly one probe JSON per theorem, each PROBE_ONLY or WITNESSED, of the challenge module and the challenge
      file; one fingerprint JSON covering exactly the theorems (type mode, same module and file);
    - every probe and the fingerprint ran on the same replayed closure (one `olean_sha256`).
    """
    probs = comparator_log_problems(log_text, isl, nanoda_rev)
    want_tag = isl.toolchain[len(_TOOLCHAIN_PREFIX):]
    if comparator_tag != want_tag:
        probs.append(f"comparator_tag {comparator_tag} differs from the island toolchain's {want_tag}")
    by_thm: dict[str, list[dict]] = {}
    if not probe_docs:
        probs.append("no negation-probe JSON given (one per theorem: `telperion probe-negation --json --module "
                     f"{isl.challenge_module} --theorem <name> --file <the challenge file>`)")
    for doc in probe_docs:
        thm, p = _probe_problems(doc, isl)
        probs += p
        if thm is not None:
            by_thm.setdefault(thm, []).append(doc)
    verdicts: dict[str, str] = {}
    for thm in isl.theorems:
        docs = by_thm.get(thm, [])
        if probe_docs and not docs:
            probs.append(f"theorem {thm!r} has no probe JSON")
        elif len(docs) > 1:
            probs.append(f"theorem {thm!r} has more than one probe JSON")
        elif docs:
            v = docs[0].get("verdict")
            verdicts[thm] = v
            if v not in PASSING_PROBES:
                probs.append(f"theorem {thm!r} probe is {v if isinstance(v, str) else _short(v)}, not one of "
                         f"{', '.join(PASSING_PROBES)}")
    fps: dict = {}
    if fingerprint_doc is None:
        probs.append("no fingerprint JSON given (`telperion fingerprint --json --import "
                     f"{isl.challenge_module} --target <each theorem> --file <the challenge file>`)")
    else:
        fprobs = _fingerprint_problems(fingerprint_doc, isl)
        probs += fprobs
        if isinstance(fingerprint_doc, dict) and isinstance(fingerprint_doc.get("fingerprints"), dict):
            fps = fingerprint_doc["fingerprints"]
        oleans = {d.get("olean_sha256") for docs in by_thm.values() for d in docs
                  if isinstance(d.get("olean_sha256"), str)}
        f_olean = fingerprint_doc.get("olean_sha256") if isinstance(fingerprint_doc, dict) else None
        for o in sorted(o for o in oleans if o != f_olean):
            probs.append(f"a probe ran on olean_sha256 {o[:12]}..., the fingerprint on {str(f_olean)[:12]}...; run "
                         "every check on one build")
    checks = {thm: TheoremCheck(verdicts[thm], fps[thm]) for thm in isl.theorems
              if thm in verdicts and isinstance(fps.get(thm), str) and _HEX64.fullmatch(fps[thm])}
    return ReplayVerdict(problems=tuple(probs), checks=checks)


# --- validation -------------------------------------------------------------------------------------------------------

def _comparator_problems(root: Path, isl: Island) -> list[str]:
    from .checks.kernel_policy import judge_config_problems
    text, problem = _read_text(root, isl.name, COMPARATOR_FILE)
    if text is None:
        return [problem]
    try:
        cfg = json.loads(text)
    except ValueError as exc:
        return [f"{COMPARATOR_FILE} is not valid JSON ({exc})"]
    if not isinstance(cfg, dict):
        return [f"{COMPARATOR_FILE} is not a JSON object"]
    probs = [f"{COMPARATOR_FILE}: {p}" for p in _unknown_keys("the config", cfg, _COMPARATOR_KEYS)]
    probs += [f"{COMPARATOR_FILE} is missing {k!r}" for k in _COMPARATOR_KEYS if k not in cfg]
    if probs:
        return probs
    for key in ("challenge_module", "solution_module"):
        if cfg[key] != getattr(isl, key):
            probs.append(f"{COMPARATOR_FILE} {key} {cfg[key]!r} differs from {ISLAND_TOML}'s {getattr(isl, key)!r}")
    names = cfg["theorem_names"]
    if (not isinstance(names, list) or len(names) != len(set(map(str, names)))
            or sorted(map(str, names)) != sorted(isl.theorems)):
        probs.append(f"{COMPARATOR_FILE} theorem_names must list exactly the island's theorems, once each")
    if cfg["enable_nanoda"] is not True:
        probs.append(f"{COMPARATOR_FILE} enable_nanoda must be true (an island is always judged with nanoda)")
    axioms = cfg["permitted_axioms"]
    if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms):
        probs.append(f"{COMPARATOR_FILE} permitted_axioms must be an array of names")
    else:
        # the axiom half of the judge's own rule; node_heavy=True only because the stricter nanoda rule is above
        probs += [f"{COMPARATOR_FILE}: {p}" for p in judge_config_problems(cfg, node_heavy=True)]
    return probs


def _xz_decode(raw: bytes, label: str) -> tuple[Optional[bytes], Optional[str]]:
    """One xz stream, at most `LOG_MAX_BYTES` once decompressed (decompression stops there), nothing after it."""
    dec = lzma.LZMADecompressor(format=lzma.FORMAT_XZ)
    try:
        data = dec.decompress(raw, max_length=LOG_MAX_BYTES + 1)
    except lzma.LZMAError as exc:
        return None, f"{label} is not a valid xz stream ({exc})"
    if len(data) > LOG_MAX_BYTES:
        return None, f"{label} is larger than {LOG_MAX_BYTES} bytes uncompressed; refusing to trust it."
    if not dec.eof:
        return None, f"{label} is a truncated xz stream"
    if dec.unused_data:
        return None, f"{label} has trailing data after its xz stream"
    return data, None


def _evidence_problems(root: Path, isl: Island, nanoda_rev: Optional[str]) -> list[str]:
    """Ruling 6: re-verify the archived evidence of `isl.replay` on every check. The files under replay/ must be
    exactly the recorded ones, each readable through the guarded reader with its recorded sha256; then the log and
    the JSONs are judged again by `evaluate_replay`, and the checks it derives must be [replay.checks]."""
    rep = isl.replay
    d = Path(root) / ISLANDS_DIR / isl.name / REPLAY_DIR
    try:
        st = d.lstat()
    except FileNotFoundError:
        return [f"no archived replay evidence: {REPLAY_DIR}/ is missing (a replay is recorded by "
                "`telperion island record-replay`, which archives its evidence)"]
    except OSError as exc:
        return [f"{REPLAY_DIR}/ could not be read ({exc.strerror or exc})"]
    if stat.S_ISLNK(st.st_mode):
        return [f"{REPLAY_DIR}/ is a symlink in the working tree; refusing to read the evidence through it"]
    if not stat.S_ISDIR(st.st_mode):
        return [f"{REPLAY_DIR} is not a directory"]
    probe_files = {f"probe-{sha}.json": (thm, sha) for thm, sha in rep.probe_sha256}
    try:
        present = set(os.listdir(d))
    except OSError as exc:
        return [f"{REPLAY_DIR}/ could not be listed ({exc.strerror or exc})"]
    probs = [f"{REPLAY_DIR}/{n} is an unexpected file in the archived evidence"
             for n in sorted(present - {LOG_ARCHIVE, FINGERPRINT_ARCHIVE, *probe_files})]

    def evidence(fname: str, max_bytes: int) -> Optional[bytes]:
        label = f"{REPLAY_DIR}/{fname}"
        data, problem = read_guarded(d / fname, label=label, max_bytes=max_bytes)
        if data is None:
            probs.append(problem or f"{label} is missing")
        return data

    def as_json(fname: str, raw: Optional[bytes], key: str, want: str) -> tuple[bool, object]:
        """`(True, the parsed JSON, whatever it is)` or `(False, None)` with the problem recorded."""
        if raw is None:
            return False, None
        if hashlib.sha256(raw).hexdigest() != want:
            probs.append(f"{REPLAY_DIR}/{fname} has sha256 {hashlib.sha256(raw).hexdigest()}, not the recorded "
                         f"{key} {want}")
            return False, None
        try:
            return True, json.loads(raw.decode("utf-8"))
        except ValueError as exc:   # UnicodeDecodeError is a ValueError
            probs.append(f"{REPLAY_DIR}/{fname} is not valid JSON ({exc})")
            return False, None

    log_text = None
    raw = evidence(LOG_ARCHIVE, MAX_BYTES)
    if raw is not None:
        data, problem = _xz_decode(raw, f"{REPLAY_DIR}/{LOG_ARCHIVE}")
        if data is None:
            probs.append(problem)
        elif hashlib.sha256(data).hexdigest() != rep.log_sha256:
            probs.append(f"{REPLAY_DIR}/{LOG_ARCHIVE} holds a log with sha256 {hashlib.sha256(data).hexdigest()}, "
                         f"not the recorded log_sha256 {rep.log_sha256}")
        else:
            try:
                log_text = data.decode("utf-8")
            except UnicodeDecodeError:
                probs.append(f"{REPLAY_DIR}/{LOG_ARCHIVE} holds a log that is not valid UTF-8")
    _, fp_doc = as_json(FINGERPRINT_ARCHIVE, evidence(FINGERPRINT_ARCHIVE, MAX_BYTES), "fingerprint_sha256",
                        rep.fingerprint_sha256)
    if fp_doc is None and not probs:
        probs.append(f"{REPLAY_DIR}/{FINGERPRINT_ARCHIVE} holds no fingerprint JSON object")
    probe_docs = []
    for fname, (thm, sha) in sorted(probe_files.items(), key=lambda kv: kv[1]):
        ok, doc = as_json(fname, evidence(fname, MAX_BYTES), f"probe_sha256 of {thm!r}", sha)
        if not ok:
            continue
        if not isinstance(doc, dict) or doc.get("theorem") != thm:
            got = doc.get("theorem") if isinstance(doc, dict) else doc
            probs.append(f"[replay.probe_sha256] {thm!r} names the probe JSON of {_short(got)}, not of {thm!r}")
            continue
        probe_docs.append(doc)
    if probs or log_text is None:
        return probs   # log_text is None only with a problem recorded; this keeps the invariant explicit
    v = evaluate_replay(isl, log_text=log_text, probe_docs=probe_docs, fingerprint_doc=fp_doc,
                        nanoda_rev=nanoda_rev, comparator_tag=rep.comparator_tag)
    probs += [f"archived evidence: {p}" for p in v.problems]
    recorded = dict(rep.checks)
    for thm in isl.theorems:
        got, want = v.checks.get(thm), recorded.get(thm)
        if got is None or want is None:
            continue
        if got.probe != want.probe:
            probs.append(f"[replay.checks] {thm!r} says probe {want.probe} but the archived probe JSON says "
                         f"{got.probe}")
        if got.fingerprint != want.fingerprint:
            probs.append(f"[replay.checks] {thm!r} fingerprint {want.fingerprint} differs from the archived "
                         f"fingerprint JSON's {got.fingerprint}")
    return probs


def _replay_problems(root: Path, isl: Island) -> list[str]:
    rep = isl.replay
    if rep is None:
        return ["not replayed: no [replay] record (self-reported until a replay passes and is recorded)"]
    probs = []
    if rep.verdict != "pass":
        probs.append(f"replay verdict is {rep.verdict!r}, not \"pass\"")
    if rep.commit != isl.commit:
        probs.append(f"replay ran at commit {rep.commit} but the pin is {isl.commit}; re-replay at the pin")
    if rep.challenge_sha256 != isl.challenge_sha256:
        probs.append(f"replay challenge_sha256 {rep.challenge_sha256} differs from the registered "
                     f"{isl.challenge_sha256}; re-replay")
    pinned, problem = pinned_nanoda_rev()
    if pinned is None:
        probs.append(f"cannot read the pinned nanoda rev: {problem}")
    elif rep.nanoda_rev != pinned:
        probs.append(f"replay ran nanoda {rep.nanoda_rev}, not the pinned NANODA_REV {pinned}; re-replay")
    want_tag = isl.toolchain[len(_TOOLCHAIN_PREFIX):]
    if rep.comparator_tag != want_tag:
        probs.append(f"replay comparator_tag {rep.comparator_tag} differs from the island toolchain's {want_tag}")
    checks = dict(rep.checks)
    for thm in isl.theorems:
        if thm not in checks:
            probs.append(f"theorem {thm!r} has no [replay.checks] entry (probe and fingerprint)")
        elif checks[thm].probe not in PASSING_PROBES:
            probs.append(f"theorem {thm!r} probe is {checks[thm].probe}, not one of {', '.join(PASSING_PROBES)}")
    probs += [f"[replay.checks] {thm!r} is not in theorems" for thm in sorted(set(checks) - set(isl.theorems))]
    probs += _evidence_problems(root, isl, pinned)
    return probs


def _registration_problems(root: Path, isl: Island) -> list[str]:
    """The challenge copy against its recorded sha256, and our comparator.json: what a replay needs to be about."""
    probs = []
    data, problem = _read(root, isl.name, CHALLENGE_FILE)
    if data is None:
        probs.append(problem)
    elif hashlib.sha256(data).hexdigest() != isl.challenge_sha256:
        probs.append(f"{CHALLENGE_FILE} sha256 {hashlib.sha256(data).hexdigest()} differs from the recorded "
                     f"challenge_sha256 {isl.challenge_sha256}; the registered copy was edited")
    return probs + _comparator_problems(root, isl)


def island_problems(root: Path, name: str) -> list[str]:
    """Everything that keeps `<root>/islands/<name>/` from `verified`; empty iff it is verified. Never raises."""
    doc, problem = _load_doc(root, name)
    if doc is None:
        return [problem]
    isl, probs = _schema(doc, name)
    if isl is None:
        data, problem = _read(root, name, CHALLENGE_FILE)
        return probs + ([problem] if data is None else [])
    return probs + _registration_problems(root, isl) + _replay_problems(root, isl)


def status(root: Path, name: str) -> str:
    """"verified" iff `island_problems` is empty, else "self-reported"."""
    return "self-reported" if island_problems(root, name) else "verified"


def require_verified(root: Path, name: str) -> Island:
    """The island, if it is verified; `IslandError("island <name>: ...")` otherwise, unknown names included."""
    probs = island_problems(root, name)
    if probs:
        raise IslandError(f"island {name!r}: " + "; ".join(probs))
    return load_island(root, name)


# --- writing a registration -------------------------------------------------------------------------------------------

def comparator_json_text(challenge_module: str, solution_module: str, theorems: Sequence[str]) -> str:
    """OUR comparator.json: the three standard axioms, nanoda on, exactly *theorems* in their order. Byte for byte the
    config the riemann-jensen spec run used (its log records md5 1c619f6c)."""
    from .comparator import CLEAN_AXIOMS
    q = json.dumps
    names = ",\n".join(f"    {q(t)}" for t in theorems)
    return ("{\n"
            f"  \"challenge_module\": {q(challenge_module)},\n"
            f"  \"solution_module\": {q(solution_module)},\n"
            f"  \"theorem_names\": [\n{names}\n  ],\n"
            f"  \"permitted_axioms\": [{', '.join(q(a) for a in CLEAN_AXIOMS)}],\n"
            "  \"enable_nanoda\": true\n"
            "}\n")


def _dumps_island(isl: Island, rep: Optional[Replay]) -> str:
    """island.toml for *isl* with [replay] *rep* (or none). A JSON string literal (ASCII, escaped) is a valid TOML
    basic string, so every value is written with json.dumps. The text is re-read through the strict schema before
    it is returned: a writer bug is an IslandError, never a registration `island check` would read differently."""
    q = json.dumps
    lines = [f"{k} = {q(getattr(isl, k))}" for k in _TOP_KEYS if k != "theorems"]
    lines.insert(_TOP_KEYS.index("theorems"), "theorems = [\n" + "".join(f"  {q(t)},\n" for t in isl.theorems) + "]")
    if rep is not None:
        lines += ["", "[replay]"]
        lines += [f"{k} = {q(getattr(rep, k))}" for k in ("date", "commit", "challenge_sha256", "nanoda_rev",
                                                          "comparator_tag", "verdict", "log_sha256",
                                                          "fingerprint_sha256")]
        probe_sha, checks = dict(rep.probe_sha256), dict(rep.checks)
        lines += ["", "[replay.probe_sha256]"] + [f"{q(t)} = {q(probe_sha[t])}" for t in isl.theorems if t in probe_sha]
        lines += ["", "[replay.checks]"] + [f"{q(t)} = {{ probe = {q(checks[t].probe)}, fingerprint = "
                                            f"{q(checks[t].fingerprint)} }}" for t in isl.theorems if t in checks]
    text = "\n".join(lines) + "\n"
    back, probs = _schema(tomllib.loads(text), isl.name)
    if back != Island(**{**isl.__dict__, "replay": rep}):
        raise IslandError(f"island {isl.name!r}: internal error writing {ISLAND_TOML} ({'; '.join(probs)})")
    return text


_REPLAY_MD_HEAD = ("This file is a generated human summary. `telperion island check` never reads it: whether the "
                   "island is verified is decided from island.toml's [replay] record and the evidence archived "
                   "under replay/, which is re-parsed on every check. Verified means that evidence is present and "
                   "internally consistent; it does not prove the run happened (whoever ran the sandbox could write "
                   "a log by hand). The independent auditor's review of the run is the anchor.")


def _replay_md_preamble(isl: Island, date: str, differences: Sequence[str]) -> str:
    lines = [f"# Replay record: {isl.name}", "", _REPLAY_MD_HEAD, "",
             f"- source: {isl.source}", f"- commit: {isl.commit}", f"- toolchain: {isl.toolchain}",
             f"- licence: {isl.licence}", f"- challenge: {isl.challenge_module} (challenge.lean, sha256 "
             f"{isl.challenge_sha256})", f"- intended use: {isl.intended_use}", "- theorems:"]
    lines += [f"  - `{t}`" for t in isl.theorems]
    lines += ["", f"## {date}: registered (`telperion island add`)", ""]
    if differences:
        lines.append("The library's own Comparator/comparator.json differs from ours; ours is used:")
        lines += [f"- {d}" for d in differences]
    else:
        lines.append("The library's own Comparator/comparator.json matches ours.")
    lines += ["", "Status: not yet replayed (self-reported)."]
    return "\n".join(lines) + "\n"


def _append_replay_md(root: Path, isl: Island, section: str) -> None:
    from .missions.schema import atomic_write_text
    text, _ = _read_text(root, isl.name, REPLAY_FILE)
    if text is None:   # missing or untrusted: start again (atomic_write_text replaces a symlink, never follows it)
        text = f"# Replay record: {isl.name}\n\n{_REPLAY_MD_HEAD}\n"
    atomic_write_text(Path(root) / ISLANDS_DIR / isl.name / REPLAY_FILE, text.rstrip("\n") + "\n\n" + section)


def _config_differences(upstream: dict, ours: dict) -> list[str]:
    """One line per key where the library's Comparator config and ours differ (ours wins; REPLAY.md says how)."""
    out = []
    for key in sorted(set(upstream) | set(ours)):
        if key not in ours:
            out.append(f"`{key}`: upstream sets {json.dumps(upstream[key])}; ours has no such key")
        elif key not in upstream or json.dumps(upstream[key]) != json.dumps(ours[key]):   # 1 is not true
            up = json.dumps(upstream[key]) if key in upstream else "(absent)"
            out.append(f"`{key}`: upstream {up}, ours {json.dumps(ours[key])}")
    return out


def _clone_read(src: Path, rel: str, max_bytes: int = MAX_BYTES) -> bytes:
    data, problem = read_guarded(src / rel, label=f"the clone's {rel}", max_bytes=max_bytes)
    if data is None:
        raise IslandError(problem or f"the clone has no {rel}")
    return data


def _module_path(module: str) -> str:
    """`Challenge.Basic` -> `Challenge/Basic.lean`; *module* is already a validated plain dotted identifier."""
    return "/".join(module.split(".")) + ".lean"


def _detect_licence(src: Path) -> Optional[str]:
    for fname in ("LICENSE", "LICENSE.md", "LICENSE.txt", "COPYING"):
        data, _ = read_guarded(src / fname, label=fname, max_bytes=MAX_BYTES)
        if data is None:
            continue
        text = data.decode("utf-8", errors="replace")
        if "Apache License" in text and "Version 2.0" in text:
            return "Apache-2.0"
        if "MIT License" in text or "Permission is hereby granted, free of charge" in text:
            return "MIT"
        return None
    return None


def add_island(root: Path, name: str, source: str, commit: str, intended_use: str, *,
               fetch: Callable[[str, str, Path], str], tools: Optional[Path] = None,
               licence: Optional[str] = None, date: Optional[str] = None) -> Island:
    """Register `<root>/islands/<name>/` from the library at *source* @ *commit*. `fetch(source, commit, dest)`
    clones it into `<tools>/islands/<name>/src` and returns the clone's HEAD, which must be *commit*. From the
    clone (guarded reads) come the toolchain (`lean-toolchain`), the theorem names and modules
    (`Comparator/comparator.json`), the challenge file and, unless *licence* is given, the licence (Apache-2.0 or MIT
    from LICENSE). Writes island.toml without [replay], a byte copy of the challenge, OUR comparator.json and
    REPLAY.md (which records how the library's config differs from ours). Nothing is built. Everything is checked
    before anything is written, and the island directory appears whole or not at all. `IslandError` otherwise."""
    from .missions.schema import atomic_write_text
    problem = (_name_problem(name) or _source_problem(source)
               or (None if isinstance(commit, str) and _HEX40.fullmatch(commit) else
                   "commit must be the full 40-hex commit (a branch or tag can move)")
               or _str_problem("intended_use", intended_use) or _root_problem(root))
    if problem:
        raise IslandError(f"island {name!r}: {problem}")
    dest = Path(root) / ISLANDS_DIR / name
    if dest.exists() or dest.is_symlink():
        raise IslandError(f"island {name!r}: already registered ({ISLANDS_DIR}/{name}/ exists)")
    src = Path(tools or DEFAULT_TOOLS) / ISLANDS_DIR / name / "src"
    head = fetch(source, commit, src)
    if head != commit:
        raise IslandError(f"island {name!r}: the clone's HEAD {str(head)[:40]!r} is not the pin {commit}; refusing to "
                          "register")
    try:
        toolchain = _clone_read(src, "lean-toolchain", 4096).decode("utf-8").strip()
        upstream = json.loads(_clone_read(src, "Comparator/comparator.json").decode("utf-8"))
    except (UnicodeDecodeError, ValueError) as exc:
        raise IslandError(f"island {name!r}: the clone's lean-toolchain or Comparator/comparator.json cannot be "
                          f"read ({exc})") from None
    except IslandError as exc:
        raise IslandError(f"island {name!r}: {exc}") from None
    if not isinstance(upstream, dict) or not isinstance(upstream.get("theorem_names"), list):
        raise IslandError(f"island {name!r}: the clone's Comparator/comparator.json has no theorem_names list")
    cm, sm = upstream.get("challenge_module"), upstream.get("solution_module")
    problem = _lean_name_problem("challenge_module", cm) or _lean_name_problem("solution_module", sm)
    if problem:
        raise IslandError(f"island {name!r}: the clone's Comparator/comparator.json: {problem}")
    try:
        challenge = _clone_read(src, _module_path(cm))
    except IslandError as exc:
        raise IslandError(f"island {name!r}: {exc}") from None
    if licence is None:
        licence = _detect_licence(src)
        if licence is None:
            raise IslandError(f"island {name!r}: cannot tell the licence from the clone's LICENSE; pass --licence "
                              "<SPDX id>")
    isl, probs = _schema({"name": name, "source": source, "commit": commit, "toolchain": toolchain,
                          "licence": licence, "challenge_module": cm, "solution_module": sm,
                          "challenge_sha256": hashlib.sha256(challenge).hexdigest(),
                          "theorems": list(upstream["theorem_names"]), "intended_use": intended_use}, name)
    if isl is None:
        raise IslandError(f"island {name!r}: " + "; ".join(probs))
    ours = comparator_json_text(cm, sm, isl.theorems)
    md = _replay_md_preamble(isl, date or datetime.date.today().isoformat(),
                             _config_differences(upstream, json.loads(ours)))
    (Path(root) / ISLANDS_DIR).mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(dir=Path(root) / ISLANDS_DIR, prefix=f".{name}.add-"))
    try:
        (stage / CHALLENGE_FILE).write_bytes(challenge)
        for fname, text in ((ISLAND_TOML, _dumps_island(isl, None)), (COMPARATOR_FILE, ours), (REPLAY_FILE, md)):
            atomic_write_text(stage / fname, text)
        os.chmod(stage / CHALLENGE_FILE, 0o644)
        os.chmod(stage, 0o755)
        os.rename(stage, dest)
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise
    return load_island(root, name)


# --- running commands (the real runner; tests inject fakes) -----------------------------------------------------------

@dataclass(frozen=True)
class RunResult:
    rc: int
    output: str                    # stdout and stderr together
    wall_s: float = 0.0
    peak_kb: Optional[int] = None  # the largest child RSS so far (getrusage RUSAGE_CHILDREN), in kB


#: The landrun pass-through shim, verbatim from Arda's missions/judge/rejudge_queue.sh setup (copied from
#: missions-comparator-heavy.yml). It does NOT sandbox anything: it drops landrun's flags and execs the command.
#: Install it as `<tools>/bin/landrun` only inside a sandbox that already isolates the whole replay (the cap-drop
#: container), or use a real landrun / a bwrap wrapper there instead.
LANDRUN_PASSTHROUGH_SHIM = """#!/usr/bin/env bash
set -euo pipefail
args=("$@"); i=0; n=${#args[@]}
while (( i < n )); do
  a="${args[$i]}"
  case "$a" in
    --ro|--rw|--rwx|--rox|--env|--log-level)
      v="${args[$((i+1))]:-}"
      [[ "$a" == "--env" && "$v" == *"="* ]] && export "$v"
      i=$((i+2)) ;;
    --env=*) export "${a#--env=}"; i=$((i+1)) ;;
    --*=*) i=$((i+1)) ;;
    -*) i=$((i+1)) ;;
    *) break ;;
  esac
done
exec "${args[@]:$i}"
"""


def _raise_stack_limit() -> None:  # pragma: no cover - runs in the child
    # Comparator and Lean need a large stack (rejudge_queue.sh: `ulimit -s 65520`); on macOS 65520 KB is the hard
    # limit and "unlimited" makes every exec'd binary die, so never ask for more than that.
    import resource
    try:
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        want = 65520 * 1024 if hard == resource.RLIM_INFINITY else min(hard, 65520 * 1024)
        if soft != resource.RLIM_INFINITY and soft < want:
            resource.setrlimit(resource.RLIMIT_STACK, (want, hard))
    except (ValueError, OSError):
        pass


def subprocess_run(argv: Sequence[str], *, cwd: Path, env: Optional[dict] = None, timeout: float) -> RunResult:
    """The real `run`: *argv* as a list (never a shell), *env* laid over the current environment, stdin closed,
    stdout and stderr together, the child in its own session so a timeout kills its whole process group.
    Never raises for a failing, missing or timed-out command: rc 124 is a timeout, 127 a command that cannot run."""
    import resource
    import signal
    import subprocess
    import time
    argv = [str(a) for a in argv]
    t0 = time.monotonic()
    try:
        p = subprocess.Popen(argv, cwd=str(cwd), env={**os.environ, **(env or {})}, stdin=subprocess.DEVNULL,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True,
                             preexec_fn=_raise_stack_limit)
    except OSError as exc:
        return RunResult(127, f"cannot run {argv[0]}: {exc.strerror or exc}\n", time.monotonic() - t0)
    try:
        out, _ = p.communicate(timeout=timeout)
        rc = p.returncode
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except OSError:
            pass
        out, _ = p.communicate()
        out = (out or b"") + f"\n{argv[0]}: timed out after {timeout} s; killed\n".encode()
        rc = 124
    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    return RunResult(rc, (out or b"").decode("utf-8", errors="replace"), time.monotonic() - t0,
                     peak // 1024 if sys.platform == "darwin" else peak)


def git_fetch(source: str, commit: str, dest: Path, *, timeout: float = 3600) -> str:
    """The real `fetch` for `island add`: a shallow fetch of exactly *commit* from *source* into a fresh *dest*,
    checked out detached; returns `git rev-parse HEAD`. An existing *dest* is never updated, only re-read (its HEAD
    is returned, and `add_island` refuses it unless it is the pin). Nothing in the clone is built or run."""
    dest = Path(dest)
    env = {"GIT_TERMINAL_PROMPT": "0"}

    def git(*args) -> str:
        r = subprocess_run(["git", *args], cwd=dest.parent, env=env, timeout=timeout)
        if r.rc != 0:
            raise IslandError(f"`{shlex.join(['git', *args])}` failed (exit {r.rc}): {r.output.strip()[-500:]}")
        return r.output

    if dest.is_symlink() or (dest.exists() and not dest.is_dir()):
        raise IslandError(f"{dest} exists and is not a directory; refusing to clone into it")
    if not dest.exists():
        dest.parent.mkdir(parents=True, exist_ok=True)
        git("init", "-q", str(dest))
        git("-C", str(dest), "remote", "add", "origin", source)
        git("-C", str(dest), "fetch", "-q", "--depth", "1", "origin", commit)
        git("-C", str(dest), "-c", "advice.detachedHead=false", "checkout", "-q", "--detach", commit)
    return git("-C", str(dest), "rev-parse", "HEAD").strip()


# --- recording a replay -----------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class ReplayResult:
    verdict: str                    # "pass" or "fail"
    problems: tuple[str, ...]
    log_sha256: str


def _registered(root: Path, name: str) -> Island:
    """The island, if its registration is sound enough to replay against; `IslandError` otherwise."""
    isl = load_island(root, name)
    probs = _registration_problems(root, isl)
    if probs:
        raise IslandError(f"island {name!r}: the registration is not valid ({'; '.join(probs)}); fix it before "
                          "recording a replay")
    return isl


def _remove_evidence(d: Path) -> None:
    """Delete `<island>/replay/` (ours: written only by `_archive_evidence`). A symlink there is unlinked, never
    followed; rmtree does not follow symlinks inside it either."""
    p = d / REPLAY_DIR
    if p.is_symlink() or p.is_file():
        p.unlink()
    elif p.exists():
        shutil.rmtree(p)


def _archive_evidence(d: Path, log_bytes: bytes, probes: Sequence[tuple[str, bytes]], fp_raw: bytes) -> dict:
    """Write replay/ whole (staged, then renamed into place) and return the sha256s for [replay]."""
    stage = Path(tempfile.mkdtemp(dir=d, prefix=".replay-new-"))
    try:
        (stage / LOG_ARCHIVE).write_bytes(lzma.compress(log_bytes, format=lzma.FORMAT_XZ))
        probe_sha = {}
        for thm, raw in probes:
            sha = hashlib.sha256(raw).hexdigest()
            probe_sha[thm] = sha
            (stage / f"probe-{sha}.json").write_bytes(raw)
        (stage / FINGERPRINT_ARCHIVE).write_bytes(fp_raw)
        for f in stage.iterdir():
            os.chmod(f, 0o644)
        os.chmod(stage, 0o755)
        _remove_evidence(d)
        os.rename(stage, d / REPLAY_DIR)
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise
    return {"log_sha256": hashlib.sha256(log_bytes).hexdigest(), "probe_sha256": probe_sha,
            "fingerprint_sha256": hashlib.sha256(fp_raw).hexdigest()}


def _conclude(root: Path, isl: Island, problems: Sequence[str], checks: dict, *, how: str, date: str, tag: str,
              nanoda_rev: str, log_bytes: bytes, probes: Sequence[tuple[str, bytes]], fp_raw: Optional[bytes],
              commands: Sequence[tuple[str, RunResult]] = ()) -> ReplayResult:
    """Write the outcome, shared by both replay commands. PASS: archive the evidence, then write [replay] (in that
    order, so a crash between leaves an old [replay] whose evidence no longer matches: self-reported, never a false
    verified). FAIL: write no [replay]; an earlier one is dropped with its evidence. Either way REPLAY.md gets a
    dated section."""
    from .missions.schema import atomic_write_text
    d = Path(root) / ISLANDS_DIR / isl.name
    log_sha = hashlib.sha256(log_bytes).hexdigest()
    passed = not problems
    prior = isl.replay
    if passed:
        shas = _archive_evidence(d, log_bytes, probes, fp_raw)
        rep = Replay(date=date, commit=isl.commit, challenge_sha256=isl.challenge_sha256, nanoda_rev=nanoda_rev,
                     comparator_tag=tag, log_sha256=log_sha, verdict="pass",
                     checks=tuple(sorted(checks.items())), probe_sha256=tuple(sorted(shas["probe_sha256"].items())),
                     fingerprint_sha256=shas["fingerprint_sha256"])
        atomic_write_text(d / ISLAND_TOML, _dumps_island(isl, rep))
    else:
        if prior is not None:
            atomic_write_text(d / ISLAND_TOML, _dumps_island(isl, None))
        _remove_evidence(d)
    lines = [f"## {date}: {'PASS' if passed else 'FAIL'} (`telperion {how}`)", "",
             f"- commit {isl.commit}, challenge_sha256 {isl.challenge_sha256}",
             f"- nanoda_lib {nanoda_rev} (NANODA_REV), Comparator {tag}",
             f"- Comparator log sha256 {log_sha} ({len(log_bytes)} bytes)"
             + (f"; archived as {REPLAY_DIR}/{LOG_ARCHIVE}" if passed else "")]
    for thm in isl.theorems:
        if thm in checks:
            lines.append(f"- `{thm}`: probe {checks[thm].probe}, fingerprint {checks[thm].fingerprint}")
    if commands:
        lines += ["", "Commands (in the clone; wall time, and the largest child RSS so far):"]
        lines += [f"- `{cmd}`: exit {r.rc}, wall {r.wall_s:.1f} s, peak {r.peak_kb} kB" for cmd, r in commands]
    if not passed:
        lines += ["", "Problems:"] + [f"- {p}" for p in problems]
        lines += ["", "No [replay] was recorded."]
        if prior is not None:
            lines.append(f"The earlier [replay] ({prior.date}, log sha256 {prior.log_sha256}) was dropped with its "
                         "evidence: the island is self-reported until a replay passes again.")
    _append_replay_md(root, isl, "\n".join(lines) + "\n")
    return ReplayResult("pass" if passed else "fail", tuple(problems), log_sha)


def _input(name: str, path, label: str, max_bytes: int) -> bytes:
    data, problem = read_guarded(Path(path), label=f"{label} {path}", max_bytes=max_bytes)
    if data is None:
        raise IslandError(f"island {name!r}: {problem or f'{label} {path} is missing'}")
    return data


def _input_json(name: str, path, label: str):
    raw = _input(name, path, label, MAX_BYTES)
    try:
        return raw, json.loads(raw.decode("utf-8"))
    except ValueError as exc:
        raise IslandError(f"island {name!r}: {label} {path} is not valid JSON ({exc})") from None


def _check_date(name: str, date) -> None:
    if not _date_ok(date):
        raise IslandError(f"island {name!r}: --date must be an ISO date (YYYY-MM-DD), not {date!r}")


def _check_date_tag(name: str, date, tag) -> None:
    _check_date(name, date)
    if not isinstance(tag, str) or not _TAG_RE.fullmatch(tag):
        raise IslandError(f"island {name!r}: --comparator-tag must look like vX.Y.Z or vX.Y.Z-rcN, not {tag!r}")


def record_replay(root: Path, name: str, *, log, probe_jsons: Sequence = (), fingerprint_json=None, date: str,
                  comparator_tag: str) -> ReplayResult:
    """Ingest a replay run elsewhere (Ruling 1): the Comparator log *log* (its first line the ISLAND-HEADER), one
    `probe-negation --json` output per theorem and one `fingerprint --json` output, all produced in the sandbox.
    Judged by `evaluate_replay`, exactly as `replay_island` judges its own run; on PASS the files are archived
    under replay/ and [replay] is written. Every input goes through the guarded reader; an unreadable, non-UTF-8,
    oversized or non-JSON input, a bad date or tag, or an invalid registration is an `IslandError` and nothing is
    written. A FAIL is recorded in REPLAY.md only."""
    isl = _registered(root, name)
    _check_date_tag(name, date, comparator_tag)
    log_bytes = _input(name, log, "the Comparator log", LOG_MAX_BYTES)
    try:
        log_text = log_bytes.decode("utf-8")
    except UnicodeDecodeError:
        raise IslandError(f"island {name!r}: the Comparator log {log} is not valid UTF-8") from None
    probes = [_input_json(name, p, "the probe JSON") for p in probe_jsons]
    fp = _input_json(name, fingerprint_json, "the fingerprint JSON") if fingerprint_json is not None else None
    pinned, problem = pinned_nanoda_rev()
    if pinned is None:
        raise IslandError(f"island {name!r}: cannot read the pinned nanoda rev: {problem}")
    v = evaluate_replay(isl, log_text=log_text, probe_docs=[doc for _, doc in probes],
                        fingerprint_doc=None if fp is None else fp[1], nanoda_rev=pinned, comparator_tag=comparator_tag)
    return _conclude(root, isl, v.problems, v.checks, how="island record-replay", date=date, tag=comparator_tag,
                     nanoda_rev=pinned, log_bytes=log_bytes, fp_raw=None if fp is None else fp[0],
                     probes=[(doc.get("theorem"), raw) for raw, doc in probes if isinstance(doc, dict)])


def _md5_file(path: Path) -> str:
    h = hashlib.md5()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _json_output(text: str) -> tuple[Optional[dict], bytes]:
    """`(doc, raw)`: the JSON object a check printed as its last stdout line and that line's bytes (what is archived),
    or `(None, b"")`."""
    lines = text.strip().splitlines()
    try:
        doc = json.loads(lines[-1]) if lines else None
    except ValueError:
        doc = None
    return (doc, (lines[-1] + "\n").encode("utf-8")) if isinstance(doc, dict) else (None, b"")


def replay_island(root: Path, name: str, *, run: Callable[..., RunResult], tools: Optional[Path] = None,
                  date: Optional[str] = None, leanlock: Optional[Path] = DEFAULT_LEANLOCK,
                  python: Optional[str] = None, timeout: float = 6 * 3600,
                  check_timeout: float = 3600) -> ReplayResult:
    """Replay the island in `<tools>/islands/<name>/src` through *run* (`subprocess_run`, or a fake in tests). It
    builds and runs the library's code: it MUST RUN INSIDE A SANDBOX, and we never run it locally (owner decision
    2026-10-31; replays are ingested with `record_replay` instead).

    Refuses (`IslandError`, nothing run but `git rev-parse`) unless: the registration is valid; the clone's HEAD is
    the pin; its challenge file has the registered sha256 and its lean-toolchain is the island's; the Comparator tag
    for the toolchain is known; Comparator, lean4export, nanoda_bin (at NANODA_REV) and the landrun shim are all in
    *tools*. Then, through leanlock unless *leanlock* is None: `lake exe cache get`, `lake build`, `lake env
    comparator <our comparator.json>` (PATH and COMPARATOR_* as rejudge_queue.sh sets them), `probe-negation` per
    theorem and `fingerprint` for all of them, on the challenge. The log `<tools>/islands/<name>/comparator.log`
    starts with the ISLAND-HEADER and the COMPARATOR_NANODA line and ends with the exit line. The verdict is
    `evaluate_replay`'s, plus a failed build; `_conclude` writes it."""
    from .missions import judge
    isl = _registered(root, name)
    date = date or datetime.date.today().isoformat()
    _check_date(name, date)
    tools = Path(tools or DEFAULT_TOOLS)
    src = tools / ISLANDS_DIR / name / "src"
    if src.is_symlink() or not src.is_dir():
        raise IslandError(f"island {name!r}: no clone at {src} (`telperion island add` makes it)")
    head = run(["git", "-C", str(src), "rev-parse", "HEAD"], cwd=src, timeout=120)
    if head.rc != 0 or head.output.strip() != isl.commit:
        raise IslandError(f"island {name!r}: the clone's HEAD {head.output.strip()[:40]!r} is not the pin "
                          f"{isl.commit}; refusing to replay")
    rel = _module_path(isl.challenge_module)
    try:
        challenge = _clone_read(src, rel)
        toolchain = _clone_read(src, "lean-toolchain", 4096).decode("utf-8", errors="replace").strip()
    except IslandError as exc:
        raise IslandError(f"island {name!r}: {exc}") from None
    if hashlib.sha256(challenge).hexdigest() != isl.challenge_sha256:
        raise IslandError(f"island {name!r}: the clone's {rel} sha256 {hashlib.sha256(challenge).hexdigest()} is not "
                          f"the registered challenge_sha256 {isl.challenge_sha256}; refusing to replay")
    if toolchain != isl.toolchain:
        raise IslandError(f"island {name!r}: the clone's lean-toolchain {toolchain!r} is not the island toolchain "
                          f"{isl.toolchain!r}; refusing to replay")
    try:
        tag = judge.comparator_tag(isl.toolchain)
    except judge.JudgeError as exc:
        raise IslandError(f"island {name!r}: {exc}") from None
    pinned, problem = pinned_nanoda_rev()
    if pinned is None:
        raise IslandError(f"island {name!r}: cannot read the pinned nanoda rev: {problem}")
    cmpdir = tools / f"comparator-{tag}"
    l4x = next(iter(sorted(p for p in (cmpdir / ".lake").rglob("lean4export") if p.parent.name == "bin")), None) \
        if (cmpdir / ".lake").is_dir() else None
    nanoda_dir = tools / f"nanoda-{pinned[:8]}"
    nanoda_bin = nanoda_dir / "target" / "release" / "nanoda_bin"
    landrun = tools / "bin" / "landrun"
    comparator_bin = cmpdir / ".lake" / "build" / "bin" / "comparator"
    for what, path in (("Comparator", comparator_bin), ("lean4export", l4x), ("nanoda_bin", nanoda_bin),
                       ("the landrun shim", landrun), ("leanlock", leanlock)):
        if what == "leanlock" and path is None:
            continue
        if path is None or not Path(path).is_file():
            raise IslandError(f"island {name!r}: {what} not found at {path}; build or install it first")
    nrev = run(["git", "-C", str(nanoda_dir), "rev-parse", "HEAD"], cwd=nanoda_dir, timeout=120)
    if nrev.rc != 0 or nrev.output.strip() != pinned:
        raise IslandError(f"island {name!r}: the nanoda checkout {nanoda_dir} is at {nrev.output.strip()[:40]!r}, "
                          f"not the pinned NANODA_REV {pinned}; refusing to replay")

    lock = [str(leanlock)] if leanlock is not None else []
    lock_env = {"ARDA_LEAN_SLOTS": "1", "OPENBLAS_NUM_THREADS": "1"}
    cfg = (Path(root) / ISLANDS_DIR / name / COMPARATOR_FILE).resolve()
    py = [python or sys.executable, "-m", "telperion.cli"]
    # what the log and REPLAY.md show: no machine paths (both end up in a public repo); the argv itself is unchanged
    shown = [(str(cfg), f"{ISLANDS_DIR}/{name}/{COMPARATOR_FILE}"), (str(src), "<clone>"), (str(tools), "<tools>"),
             (py[0], "python"), *([(lock[0], "leanlock.sh")] if lock else [])]

    def show(argv) -> str:
        out = []
        for a in map(str, argv):
            for full, short in shown:
                a = a.replace(full, short)
            out.append(a)
        return shlex.join(out)

    log = [f"ISLAND-HEADER island={name} commit={isl.commit} challenge_sha256={isl.challenge_sha256}",
           f"== telperion island replay {name} {date} (Comparator {tag}; this command must run inside a sandbox)",
           f"COMPARATOR_NANODA {_md5_file(nanoda_bin)} (nanoda_lib {pinned})",
           f"COMPARATOR_LEAN4EXPORT {_md5_file(l4x)} {show([l4x])}",
           f"COMPARATOR_LANDRUN {show([landrun])} {_md5_file(landrun)}",
           f"comparator {show([comparator_bin])} {_md5_file(comparator_bin)} (tag {tag})"]
    commands: list[tuple[str, RunResult]] = []
    run_probs: list[str] = []

    def step(argv: list[str], env: dict, limit: float) -> RunResult:
        r = run(argv, cwd=src, env=env, timeout=limit)
        commands.append((show(argv), r))
        return r

    for argv in ([*lock, "lake", "exe", "cache", "get"], [*lock, "lake", "build"]):
        r = step(argv, lock_env, timeout)
        log += [f"== {show(argv)}", *r.output.rstrip("\n").splitlines(), f"== exit {r.rc}"]
        if r.rc != 0:
            run_probs.append(f"`{shlex.join(argv[len(lock):])}` failed (exit {r.rc})")
            break
    probes: list[tuple[str, bytes]] = []
    probe_docs: list = []
    fp_raw = fp_doc = None
    if not run_probs:
        env = {**lock_env, "PATH": os.pathsep.join([str(tools / "bin"), str(cmpdir / ".lake" / "build" / "bin"),
                                                    os.environ.get("PATH", "")]),
               "COMPARATOR_LANDRUN": str(landrun), "COMPARATOR_LEAN4EXPORT": str(l4x),
               "COMPARATOR_NANODA": str(nanoda_bin)}
        argv = [*lock, "lake", "env", "comparator", str(cfg)]
        r = step(argv, env, timeout)
        log += ["== comparator", *r.output.rstrip("\n").splitlines(), f"ISLAND-replay-EXIT {r.rc}"]
        for thm in isl.theorems:
            r = step([*lock, *py, "probe-negation", "--project", str(src), "--module", isl.challenge_module,
                      "--theorem", thm, "--file", str(src / rel), "--json"], lock_env, check_timeout)
            doc, raw = _json_output(r.output)
            if doc is None:
                run_probs.append(f"probe-negation of {thm!r} printed no JSON object (exit {r.rc})")
            else:
                probe_docs.append(doc)
                probes.append((doc.get("theorem"), raw))
        targets = [x for t in isl.theorems for x in ("--target", t)]
        r = step([*lock, *py, "fingerprint", "--project", str(src), "--import", isl.challenge_module, *targets,
                  "--file", str(src / rel), "--json"], lock_env, check_timeout)
        fp_doc, fp_raw = _json_output(r.output)
        if fp_doc is None:
            run_probs.append(f"fingerprint printed no JSON object (exit {r.rc})")
    log_bytes = ("\n".join(log) + "\n").encode("utf-8")
    from .missions.schema import atomic_write_text
    atomic_write_text(tools / ISLANDS_DIR / name / "comparator.log", log_bytes.decode("utf-8"))
    v = evaluate_replay(isl, log_text=log_bytes.decode("utf-8"), probe_docs=probe_docs, fingerprint_doc=fp_doc,
                        nanoda_rev=pinned, comparator_tag=tag)
    problems = run_probs + list(v.problems)
    return _conclude(root, isl, problems, v.checks, how="island replay", date=date, tag=tag, nanoda_rev=pinned,
                     log_bytes=log_bytes, probes=probes, fp_raw=fp_raw, commands=commands)
