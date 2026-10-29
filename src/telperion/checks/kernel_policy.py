"""Kernel policy (spec 5.1): a Lean toolchain floor with a shrink-only exception list, and judge configs that
never turn the second kernel (nanoda) off except for re-judged heavy nodes.

Lean v4.33.1 fixed kernel soundness bugs (#14806 order-dependent defeq cache, #14807 is_prop on a stuck type,
#14808 recursor checks, #14582 non-uniform inductives, #14849 numeral size). v4.34.1 is the first line we pin
that carries them; older projects are allowed only by name, and only with nanoda as a second kernel.
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


def find_projects(root: Path) -> list[tuple[str, str]]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True).stdout.decode()
    found = []
    for p in sorted(x for x in out.split("\0") if x):
        parts = Path(p).parts
        if parts[-1] != "lean-toolchain" or ".lake" in parts:
            continue
        found.append((str(Path(p).parent), (root / p).read_text().strip()))
    return found


def load_exceptions(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    doc = tomllib.loads(path.read_text())
    return {e["project"]: {"toolchain": e["toolchain"], "reason": e["reason"]} for e in doc.get("exception", [])}


def policy_problems(root: Path, exceptions: dict) -> list[str]:
    problems: list[str] = []
    projects = dict(find_projects(root))
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
    for proj in sorted(set(exceptions) - set(projects)):
        problems.append(f"{proj}: stale exception: no such project")
    return problems
