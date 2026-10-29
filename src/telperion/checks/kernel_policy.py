"""Kernel policy (spec 5.1): a Lean toolchain floor with a shrink-only exception list, and judge configs that
never turn the second kernel (nanoda) off except for re-judged heavy nodes.

Lean v4.33.1 fixed kernel soundness bugs (#14806 order-dependent defeq cache, #14807 is_prop on a stuck type,
#14808 recursor checks, #14582 non-uniform inductives, #14849 numeral size). v4.34.1 is the first line we pin
that carries them; older projects are allowed only by name, on a list meant to shrink.
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


def _tracked_toolchain_paths(root: Path) -> list[str]:
    """Tracked `lean-toolchain` paths (relative to root) outside any `.lake/`, sorted.

    Shared by find_projects and policy_problems so both see the same tracked set; neither
    reads the file here, so a toolchain tracked in git but deleted on disk cannot crash this."""
    out = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True).stdout.decode()
    return sorted(
        p for p in (x for x in out.split("\0") if x)
        if Path(p).parts[-1] == "lean-toolchain" and ".lake" not in Path(p).parts
    )


def find_projects(root: Path) -> list[tuple[str, str]]:
    found = []
    for p in _tracked_toolchain_paths(root):
        fp = root / p
        if not fp.exists():
            continue
        found.append((str(Path(p).parent), fp.read_text().strip()))
    return found


def load_exceptions(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    try:
        doc = tomllib.loads(path.read_text())
    except tomllib.TOMLDecodeError as e:
        raise ValueError(f"exceptions file {path}: not valid TOML: {e}") from e
    result: dict[str, dict] = {}
    for i, e in enumerate(doc.get("exception", [])):
        for key in ("project", "toolchain", "reason"):
            if key not in e:
                raise ValueError(f"exceptions file {path}: entry {i} is missing '{key}'")
        name = e["project"]
        if name in result:
            raise ValueError(f"exceptions file {path}: duplicate project '{name}'")
        result[name] = {"toolchain": e["toolchain"], "reason": e["reason"]}
    return result


def policy_problems(root: Path, exceptions: dict) -> list[str]:
    problems: list[str] = []
    known_projects: set[str] = set()
    projects: dict[str, str] = {}
    for p in _tracked_toolchain_paths(root):
        proj = str(Path(p).parent)
        known_projects.add(proj)
        fp = root / p
        if not fp.exists():
            problems.append(f"{proj}: lean-toolchain is tracked but missing on disk")
            continue
        projects[proj] = fp.read_text().strip()
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
