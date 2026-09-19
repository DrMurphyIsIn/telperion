"""Build coverage: does CI actually compile the Lean an artifact lives in?

THE HOLE THIS CLOSES (audit 2026-09-18/19). `grant_status` checks that a node's artifact
file *exists* and *contains* the node's statement, and (since the 2026-09-18 hardening) that
it carries no `sorry`. It never asked the one question that makes any of that mean something:
**is this file compiled by anything?**

It is not a hypothetical. Twice in two days:

  * `ZeroFreePolylog.lean` / `ZeroFreeElementary.lean` -- artifacts of two `proved` rh nodes,
    imported by nothing, absent from `defaultTargets`, outside every axiom guard's closure.
    Three independently built worktrees had no `.olean` for either. CI compiled them for the
    first time on 2026-09-18, when they were finally wired in.
  * The whole `zeta_reflection` island -- home of all six `proved` anduril node artifacts,
    granted 2026-09-18, and referenced by **no workflow at all**.

Sorry-free is not verified. Containing the statement is not proving it. Only a kernel run is
evidence, and a kernel run that no job performs is not evidence either.

WHAT IS CHECKED HERE, AND WHAT IS NOT. This module answers a deliberately narrow, decidable
question: *does some CI job run `lake build` inside the island directory this artifact lives
in?* It does NOT check that the build succeeds (that is CI's job, reported on the commit), nor
that the specific module is inside `defaultTargets` (Lake target closures are not statically
decidable from the manifest alone, and the islands express coverage through guard libs whose
import closure is the real target set). So this is a floor, not a ceiling: it makes "granted
against Lean nothing compiles" impossible, and leaves "granted against Lean that compiles but
is not in the guarded closure" to the island's own axiom guard.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, List, Optional, Set

__all__ = [
    "island_of",
    "ci_built_islands",
    "islands_with_lean",
    "artifact_coverage_error",
]

#: `telperion/examples/<island>/...`
_ISLAND_RE = re.compile(r"(?:^|/)examples/([A-Za-z0-9_]+)(?:/|$)")

#: a `cd` into an island inside a `run:` block
_CD_RE = re.compile(r"cd\s+\S*?examples/([A-Za-z0-9_]+)/lean")

#: the command that constitutes actual verification
_BUILD_RE = re.compile(r"\blake\s+build\b")


def island_of(path: Path | str) -> Optional[str]:
    """The example-island name an artifact path lives in, or None if it is not in one."""
    m = _ISLAND_RE.search(str(path).replace("\\", "/"))
    return m.group(1) if m else None


def _workflow_docs(repo_root: Path) -> List[dict]:
    try:
        import yaml
    except ImportError:  # pragma: no cover - PyYAML is a CI/dev dependency
        return []
    docs = []
    wf_dir = repo_root / ".github" / "workflows"
    for p in sorted(wf_dir.glob("*.y*ml")):
        try:
            doc = yaml.safe_load(p.read_text())
        except Exception:
            continue
        if isinstance(doc, dict):
            docs.append(doc)
    return docs


def ci_built_islands(repo_root: Path) -> Set[str]:
    """Islands in which some workflow step runs `lake build`.

    A step's effective directory is its own `working-directory`, else the job's
    `defaults.run.working-directory`. A `cd .../examples/<x>/lean` inside the step's `run`
    counts too -- three jobs in this repo address their island that way rather than through
    `working-directory`, and missing them would produce false orphans.
    """
    built: Set[str] = set()
    for doc in _workflow_docs(repo_root):
        jobs = doc.get("jobs") or {}
        if not isinstance(jobs, dict):
            continue
        for job in jobs.values():
            if not isinstance(job, dict):
                continue
            job_dir = (((job.get("defaults") or {}).get("run") or {}).get("working-directory"))
            for step in (job.get("steps") or []):
                if not isinstance(step, dict):
                    continue
                run = str(step.get("run") or "")
                if not _BUILD_RE.search(run):
                    continue
                where = step.get("working-directory") or job_dir
                if where:
                    name = island_of(str(where))
                    if name:
                        built.add(name)
                built.update(_CD_RE.findall(run))
    return built


def islands_with_lean(repo_root: Path) -> Set[str]:
    """Every example island that has at least one `.lean` source of its own."""
    out: Set[str] = set()
    examples = repo_root / "telperion" / "examples"
    if not examples.is_dir():
        return out
    for d in examples.iterdir():
        lean = d / "lean"
        if lean.is_dir() and any(lean.rglob("*.lean")):
            out.add(d.name)
    return out


def artifact_coverage_error(
    artifact_path: Path,
    repo_root: Path,
    built: Optional[Set[str]] = None,
) -> Optional[str]:
    """Return an error string if this artifact is in an island CI never builds, else None.

    An artifact outside `telperion/examples/**` is not judged here: campaign-local Lean is
    covered by the campaign's own build, and a non-Lean artifact has nothing to compile.
    """
    if artifact_path.suffix != ".lean":
        return None
    name = island_of(artifact_path)
    if name is None:
        return None
    if built is None:
        built = ci_built_islands(repo_root)
    if name in built:
        return None
    return (
        f"artifact lives in example island {name!r}, which no CI workflow builds "
        f"(no step runs `lake build` in telperion/examples/{name}/lean). A node may not be "
        f"`proved` against Lean that nothing compiles -- wire the island into "
        f".github/workflows/ or move the artifact to one that is wired."
    )
