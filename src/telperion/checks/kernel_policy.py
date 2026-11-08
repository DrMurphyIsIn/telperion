"""Kernel policy (spec 5.1): a Lean toolchain floor with a shrink-only exception list, and judge configs that
never turn the second kernel (nanoda) off except for re-judged heavy nodes.

Lean v4.33.1 fixed kernel soundness bugs (#14806 order-dependent defeq cache, #14807 is_prop on a stuck type,
#14808 recursor checks, #14582 non-uniform inductives, #14849 numeral size). v4.34.1 is the first line we pin
that carries them; older projects are allowed only by name, on a list meant to shrink.

A project is the directory of a tracked `lean-toolchain`, or an island (step 6): `islands/<name>`, whose toolchain
is its island.toml's. An island's toolchain is held to the same floor, so registering a library cannot bypass it.
"""
from __future__ import annotations

import re
import subprocess
import tomllib
from pathlib import Path

FLOOR = "leanprover/lean4:v4.34.1"
_TC = re.compile(r"^leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?$")


def parse_toolchain(s: str) -> tuple[int, int, int, int, int]:
    m = _TC.match(s.strip())
    if not m:
        raise ValueError(f"cannot parse Lean toolchain {s.strip()!r}")
    maj, mi, pa, rc = m.groups()
    return (int(maj), int(mi), int(pa), 0 if rc else 1, int(rc or 0))


def below_floor(toolchain: str) -> bool:
    return parse_toolchain(toolchain) < parse_toolchain(FLOOR)


def _tracked_paths(root: Path) -> list[str]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True).stdout.decode()
    return [x for x in out.split("\0") if x]


def _tracked_toolchain_paths(tracked: list[str]) -> list[str]:
    """Tracked `lean-toolchain` paths (relative to root) outside any `.lake/`, sorted. Nothing is
    read here, so a toolchain tracked in git but deleted on disk cannot crash this."""
    return sorted(p for p in tracked if Path(p).parts[-1] == "lean-toolchain" and ".lake" not in Path(p).parts)


def _island_projects(root: Path, tracked: list[str]) -> tuple[dict[str, str], set[str], list[str]]:
    """Step 6: `(toolchains, known, problems)` for the islands, as projects named `islands/<name>` whose toolchain
    is island.toml's `toolchain`. An island is every directory (or symlink) under `islands/` on disk, plus every
    `islands/<name>/` with a tracked file, so neither an uncommitted island nor a committed one deleted on disk is
    missed. One whose island.toml is missing, refused (a symlink anywhere on the way, oversized, not UTF-8),
    garbled, or fails the registry's strict schema (`islands.island_toolchain`, the parser `island check` uses) is a
    problem, never skipped: its toolchain could be anything. The toolchain is taken exactly as written."""
    from telperion import islands

    names, problems = islands.island_names(root)
    names = set(names) | {Path(p).parts[1] for p in tracked
                          if len(Path(p).parts) >= 3 and Path(p).parts[0] == islands.ISLANDS_DIR}
    toolchains: dict[str, str] = {}
    known: set[str] = set()
    for name in sorted(names):
        proj = f"{islands.ISLANDS_DIR}/{name}"
        known.add(proj)
        tc, problem = islands.island_toolchain(root, name)
        if tc is None:
            problems.append(f"{proj}: {problem}")
        else:
            toolchains[proj] = tc
    return toolchains, known, problems


def _projects(root: Path) -> tuple[dict[str, str], set[str], list[str]]:
    """`(toolchains, known, problems)` over every project: each tracked `lean-toolchain`'s directory, then each
    island. Shared by find_projects and policy_problems."""
    tracked = _tracked_paths(root)
    problems: list[str] = []
    known: set[str] = set()
    projects: dict[str, str] = {}
    for p in _tracked_toolchain_paths(tracked):
        proj = str(Path(p).parent)
        known.add(proj)
        fp = root / p
        if not fp.exists():
            problems.append(f"{proj}: lean-toolchain is tracked but missing on disk")
            continue
        projects[proj] = fp.read_text().strip()
    itc, iknown, iproblems = _island_projects(root, tracked)
    problems += iproblems
    for proj in sorted(iknown & known):
        # an island's toolchain is island.toml's; a lean-toolchain beside it would be a second, competing pin
        problems.append(f"{proj}: has a lean-toolchain file; an island's toolchain is the one in island.toml "
                        "(library source never lives in islands/)")
        projects.pop(proj, None)
    for proj, tc in itc.items():
        if proj not in known:
            projects[proj] = tc
    return projects, known | iknown, problems


def find_projects(root: Path) -> list[tuple[str, str]]:
    projects, _known, _problems = _projects(root)
    return list(projects.items())


def _parse_exceptions_text(text: str, source: str) -> dict[str, dict]:
    """Shared by load_exceptions and shrink_problems: parse exceptions TOML *text*
    (not yet read from a path — a base-ref blob has no path of its own), reporting
    problems against *source* (a path, or a ref-qualified label for a base blob)."""
    try:
        doc = tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        raise ValueError(f"exceptions file {source}: not valid TOML: {e}") from e
    result: dict[str, dict] = {}
    for i, e in enumerate(doc.get("exception", [])):
        for key in ("project", "toolchain", "reason"):
            if key not in e:
                raise ValueError(f"exceptions file {source}: entry {i} is missing '{key}'")
        name = e["project"]
        if name in result:
            raise ValueError(f"exceptions file {source}: duplicate project '{name}'")
        result[name] = {"toolchain": e["toolchain"], "reason": e["reason"]}
    return result


def load_exceptions(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    return _parse_exceptions_text(path.read_text(), str(path))


def shrink_problems(base_text: str | None, current: dict) -> list[str]:
    """What is wrong if `current`'s exception list is not a shrink of the one at the
    base ref (spec 5.1: the list is shrink-only). *base_text* is the TOML text of the
    exceptions file at the base ref, or None if the file did not exist there — a brand
    new exceptions file has no base to shrink from, so every entry in `current` is
    correctly reported as added.

    Removing an entry, or raising its toolchain (e.g. bumping a project past the
    floor), is always fine and never reported."""
    base = _parse_exceptions_text(base_text, "<base ref>") if base_text is not None else {}
    problems: list[str] = []
    for proj in sorted(set(current) - set(base)):
        problems.append(f"exception added: {proj} (the list is shrink-only)")
    for proj in sorted(set(current) & set(base)):
        if parse_toolchain(current[proj]["toolchain"]) < parse_toolchain(base[proj]["toolchain"]):
            problems.append(f"exception toolchain lowered: {proj}")
    return problems


def policy_problems(root: Path, exceptions: dict) -> list[str]:
    projects, known_projects, problems = _projects(root)
    for proj, tc in projects.items():
        try:
            low = below_floor(tc)
        except ValueError as e:
            problems.append(f"{proj}: {e}")
            continue
        ex = exceptions.get(proj)
        if low and ex is None:
            problems.append(f"{proj}: {tc} is below the floor {FLOOR} and is not on the exception list")
        elif ex is not None and not low:
            problems.append(f"{proj}: stale exception: {tc} meets the floor; remove it from the list")
        elif ex is not None and ex["toolchain"].strip() != tc:
            problems.append(f"{proj}: toolchain mismatch: list says {ex['toolchain']}, project has {tc}")
    for proj in sorted(set(exceptions) - known_projects):
        problems.append(f"{proj}: stale exception: no such project")
    return problems


def judge_config_problems(config: dict, *, node_heavy: bool) -> list[str]:
    """What is wrong with one rendered Comparator config: the axiom whitelist must be exactly
    CLEAN_AXIOMS, and nanoda may be off only for a heavy node (spec 5.1)."""
    from telperion.missions.judge import CLEAN_AXIOMS
    problems = []
    got, want = list(config.get("permitted_axioms", [])), list(CLEAN_AXIOMS)
    if sorted(got) != sorted(want):
        extra, missing = sorted(set(got) - set(want)), sorted(set(want) - set(got))
        problems.append(f"permitted_axioms must be exactly {want}; extra {extra}, missing {missing}")
    if not config.get("enable_nanoda", False) and not node_heavy:
        problems.append("enable_nanoda is off for a non-heavy node (neither heavy_certificates nor "
                        "judge_via = \"heavy\"; spec 5.1: nanoda required)")
    return problems
