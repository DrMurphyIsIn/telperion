"""The island registry (step 6): an island is an external Lean library Telperion has replayed itself (Comparator
with nanoda at the pinned NANODA_REV, plus the step-4 statement checks). Its pinned registration lives in
`<root>/islands/<name>/`, and library source never does:

    island.toml       the pin, the intended theorems and, once a replay passes, its [replay] record
    challenge.lean    a byte copy of the library's challenge file, its sha256 in island.toml
    comparator.json   OUR Comparator config: the three standard axioms, enable_nanoda, exactly the theorems
    REPLAY.md         the human record of the replay, naming the pin and the Comparator log's sha256

This module only reads and validates the registry. Replays run in a remote sandbox and are ingested by
`telperion island record-replay` (Task 2), never built here.

`verified` is all or nothing: `island_problems` lists everything that keeps an island from it, including "not
replayed yet", and `status` is "verified" iff that list is empty, "self-reported" otherwise. In particular a
replay counts only for the pin and the challenge it ran on (the plan's Review Focus 1 and 2): moving `commit`,
editing challenge.lean, or bumping NANODA_REV drops the island to self-reported until it is re-replayed.

Every read fails closed: `islands/` and `islands/<name>/` must be real directories, not symlinks; every file goes
through `guarded_read.read_guarded` (no symlink, a regular file, at most `MAX_BYTES`); a decode, TOML or JSON error
is a problem string, never an exception. A name is checked against `[a-z0-9-]+` before any path is built from it,
so nothing outside `<root>/islands/<name>/` is ever read on a caller's say-so.
"""
from __future__ import annotations

import datetime
import hashlib
import json
import re
import stat
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .guarded_read import read_guarded

ISLANDS_DIR = "islands"
ISLAND_TOML = "island.toml"
CHALLENGE_FILE = "challenge.lean"
COMPARATOR_FILE = "comparator.json"
REPLAY_FILE = "REPLAY.md"

#: Upper bound on every registry file. A real one is a few kilobytes; refusing anything larger before decoding keeps
#: a hostile file from costing more than a stat.
MAX_BYTES = 1 << 20

#: The negation-probe verdicts a verified island's theorems may carry (step 4).
PASSING_PROBES = ("PROBE_ONLY", "WITNESSED")

_NAME_RE = re.compile(r"[a-z0-9-]+")
_HEX40 = re.compile(r"[0-9a-f]{40}")
_HEX64 = re.compile(r"[0-9a-f]{64}")
_TAG_RE = re.compile(r"v\d+\.\d+\.\d+(?:-rc\d+)?")
_TOOLCHAIN_PREFIX = "leanprover/lean4:"

_TOP_KEYS = ("name", "source", "commit", "toolchain", "licence", "challenge_module", "solution_module",
             "challenge_sha256", "theorems", "intended_use")
_REPLAY_KEYS = ("date", "commit", "challenge_sha256", "nanoda_rev", "comparator_tag", "log_sha256", "verdict",
                "checks")
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


# --- paths and guarded reads ---------------------------------------------------------------------------------------

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
    """`(toolchain, None)` or `(None, problem)`, for the kernel policy: just island.toml's `toolchain` string,
    through the same guarded read. Its format is the policy's to judge (`parse_toolchain`); the rest of the schema
    is `island check`'s."""
    doc, problem = _load_doc(root, name)
    if doc is None:
        return None, problem
    tc = doc.get("toolchain")
    if not isinstance(tc, str):
        return None, f"{ISLAND_TOML} has no string `toolchain`"
    return tc, None


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


# --- the schema ----------------------------------------------------------------------------------------------------

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


def _unknown_keys(where: str, table: dict, allowed) -> list[str]:
    return [f"{where} has an unknown key {k!r}" for k in sorted(set(table) - set(allowed))]


def _replay_schema(rep) -> tuple[Optional[Replay], list[str]]:
    if not isinstance(rep, dict):
        return None, ["[replay] must be a table"]
    probs = _unknown_keys("[replay]", rep, _REPLAY_KEYS)
    probs += [f"[replay] is missing {k!r}" for k in _REPLAY_KEYS if k not in rep]
    if probs:
        return None, probs
    date = rep["date"]
    try:
        ok = isinstance(date, str) and len(date) == 10 and datetime.date.fromisoformat(date) is not None
    except ValueError:
        ok = False
    if not ok:
        probs.append("[replay] date must be an ISO date string (YYYY-MM-DD)")
    for key, pattern, n in (("commit", _HEX40, 40), ("nanoda_rev", _HEX40, 40), ("challenge_sha256", _HEX64, 64),
                            ("log_sha256", _HEX64, 64)):
        p = _hex_problem(f"[replay] {key}", rep[key], pattern, n)
        if p:
            probs.append(p)
    if not isinstance(rep["comparator_tag"], str) or not _TAG_RE.fullmatch(rep["comparator_tag"]):
        probs.append("[replay] comparator_tag must look like vX.Y.Z or vX.Y.Z-rcN")
    if rep["verdict"] not in ("pass", "fail"):
        probs.append("[replay] verdict must be \"pass\" or \"fail\"")
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
                  verdict=rep["verdict"], checks=tuple(sorted(entries))), []


def _schema(doc: dict, name: str) -> tuple[Optional[Island], list[str]]:
    """`(island, [])` when *doc* has exactly island.toml's shape, else `(None, every problem found)`."""
    probs = _unknown_keys(ISLAND_TOML, doc, _TOP_KEYS + ("replay",))
    probs += [f"{ISLAND_TOML} is missing {k!r}" for k in _TOP_KEYS if k not in doc]
    g = doc.get
    if "name" in doc and g("name") != name:
        probs.append(f"name {g('name')!r} must equal the directory name {name!r}")
    if "source" in doc and (not isinstance(g("source"), str) or not g("source").startswith("https://")
                            or any(ch.isspace() for ch in g("source"))):
        probs.append("source must be an https:// URL")
    if "commit" in doc:
        probs += filter(None, [_hex_problem("commit", g("commit"), _HEX40, 40)])
    if "challenge_sha256" in doc:
        probs += filter(None, [_hex_problem("challenge_sha256", g("challenge_sha256"), _HEX64, 64)])
    if "toolchain" in doc:
        tc = g("toolchain")
        if (not isinstance(tc, str) or not tc.startswith(_TOOLCHAIN_PREFIX)
                or not _TAG_RE.fullmatch(tc[len(_TOOLCHAIN_PREFIX):])):
            probs.append(f"toolchain {tc!r} must be {_TOOLCHAIN_PREFIX}vX.Y.Z or {_TOOLCHAIN_PREFIX}vX.Y.Z-rcN")
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


# --- validation ----------------------------------------------------------------------------------------------------

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
    text, problem = _read_text(root, isl.name, REPLAY_FILE)
    if text is None:
        probs.append(problem)
    else:
        for what, value in (("pin", rep.commit), ("Comparator log sha256", rep.log_sha256)):
            if value not in text:
                probs.append(f"{REPLAY_FILE} does not record the replay's {what} ({value})")
    return probs


def island_problems(root: Path, name: str) -> list[str]:
    """Everything that keeps `<root>/islands/<name>/` from `verified`; empty iff it is verified. Never raises."""
    doc, problem = _load_doc(root, name)
    if doc is None:
        return [problem]
    isl, probs = _schema(doc, name)
    data, problem = _read(root, name, CHALLENGE_FILE)
    if data is None:
        probs.append(problem)
    elif isl is not None and hashlib.sha256(data).hexdigest() != isl.challenge_sha256:
        probs.append(f"{CHALLENGE_FILE} sha256 {hashlib.sha256(data).hexdigest()} differs from the recorded "
                     f"challenge_sha256 {isl.challenge_sha256}; the registered copy was edited")
    if isl is None:
        return probs
    probs += _comparator_problems(root, isl)
    probs += _replay_problems(root, isl)
    return probs


def status(root: Path, name: str) -> str:
    """"verified" iff `island_problems` is empty, else "self-reported"."""
    return "self-reported" if island_problems(root, name) else "verified"


def require_verified(root: Path, name: str) -> Island:
    """The island, if it is verified; `IslandError("island <name>: ...")` otherwise, unknown names included."""
    probs = island_problems(root, name)
    if probs:
        raise IslandError(f"island {name!r}: " + "; ".join(probs))
    return load_island(root, name)
