"""Comparator-challenge ingest — formalization repos that ship
``ComparatorChallenges/*.json`` (the ``leanprover/comparator`` +
``nanoda``/``landrun`` toolchain, the SAME stack as Telperion's own
``comparator.py`` challenge output and the zeta-23-lean port) publish their
top-level statements in a machine-readable, independently-checkable form.

This module INGESTS those challenge configs as ``LEAD_FORMALIZED`` leads for
the source-mining pipeline (the theorems are already Lean-verified upstream —
the lead is a PORT/distillation opportunity, exactly like a GitHub-adapter
commit), and can OPTIONALLY run the comparator check itself when the local
toolchain is present (gracefully skipped otherwise — the honest no-op gating
of the Zulip adapter).

Origin: the OpenAI NavierStokesAndEuler mining campaign (2026-09) — its
``ComparatorChallenges/{NavierStokes,Euler}.json`` carry the Clay-alternative
breakdown statements; ``anthropics/zeta-23-lean`` ships the same shape.

Usage::

    from telperion.source_mining_challenges import challenge_source
    from telperion.source_mining import mine_source
    src = challenge_source("/path/to/clone", "openai/NavierStokesAndEuler")
    cands = mine_source(src, src.fetch())
"""
from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

from .source_mining import LEAD_FORMALIZED, Source

#: The conventional directory (openai/NavierStokesAndEuler, zeta-23-lean, and
#: Telperion's own emitted challenges all use it).
CHALLENGES_DIR = "ComparatorChallenges"


def parse_challenge_config(cfg: dict, repo: str, fname: str) -> dict | None:
    """Normalize one challenge-config dict into a classify_entry-compatible
    entry, or None if it lacks the identifying ``challenge_module`` key."""
    module = cfg.get("challenge_module")
    if not module:
        return None
    names = list(cfg.get("theorem_names", []))
    axioms = list(cfg.get("permitted_axioms", []))
    return {
        "id": f"{repo}#challenge:{Path(fname).stem}",
        "title": f"Comparator challenge {module}: " + ", ".join(names[:4]),
        "abstract": (
            f"Independently-checkable comparator challenge from {repo} "
            f"({fname}). Challenge module {module}, solution module "
            f"{cfg.get('solution_module', '?')}; theorems: {', '.join(names)}; "
            f"permitted axioms: {', '.join(axioms)}."
        ),
        "source": {"repo": repo, "file": fname, "kind": "comparator-challenge",
                   "theorem_names": names},
    }


def find_challenge_configs(repo_path: str | Path) -> list[Path]:
    """Locate challenge configs: ``ComparatorChallenges/*.json`` plus any other
    ``*.json`` in the tree carrying a ``challenge_module`` key (shallow scan,
    skipping build/VCS dirs)."""
    root = Path(repo_path)
    out: list[Path] = sorted((root / CHALLENGES_DIR).glob("*.json")) \
        if (root / CHALLENGES_DIR).is_dir() else []
    seen = set(out)
    for p in sorted(root.glob("*/*.json")):
        if p in seen or any(part.startswith(".") or part == ".lake"
                            for part in p.parts):
            continue
        try:
            if "challenge_module" in json.loads(p.read_text()):
                out.append(p)
        except (json.JSONDecodeError, OSError):
            continue
    return out


def ingest_challenges(repo_path: str | Path, repo: str) -> list[dict]:
    """Parse every challenge config under ``repo_path`` into lead entries.
    Malformed configs are skipped (a broken file never crashes the poll)."""
    entries: list[dict] = []
    root = Path(repo_path)
    for p in find_challenge_configs(root):
        try:
            cfg = json.loads(p.read_text())
        except (json.JSONDecodeError, OSError):
            continue
        e = parse_challenge_config(cfg, repo, str(p.relative_to(root)))
        if e is not None:
            entries.append(e)
    return entries


def challenge_source(repo_path: str | Path, repo: str) -> Source:
    """The ``challenges`` adapter: comparator-challenge configs in a local
    formalization-repo clone → direct-port (formalized) leads."""
    return Source(name="challenges", lead_type=LEAD_FORMALIZED,
                  fetch=lambda: ingest_challenges(repo_path, repo))


def run_comparator_check(repo_path: str | Path, config_path: str | Path,
                         timeout: int = 3600) -> dict:
    """OPTIONALLY run ``lake exe comparator <config>`` in the repo, returning
    ``{status: verified|failed|skipped, ...}``.

    Honest gating: requires ``lake`` on PATH and a lakefile in the repo —
    otherwise returns ``status: skipped`` with the reason (mirrors the Zulip
    adapter's credential no-op).  A verified run means the repo's own
    comparator toolchain (lean4export + nanoda + landrun) re-checked the
    statement — independent of this process's trust in the repo's CI.
    """
    root = Path(repo_path)
    if shutil.which("lake") is None:
        return {"status": "skipped", "reason": "lake not on PATH"}
    if not ((root / "lakefile.toml").exists() or (root / "lakefile.lean").exists()):
        return {"status": "skipped", "reason": f"no lakefile in {root}"}
    try:
        proc = subprocess.run(
            ["lake", "exe", "comparator", str(config_path)],
            cwd=root, capture_output=True, text=True, timeout=timeout)
    except (subprocess.TimeoutExpired, OSError) as e:
        return {"status": "failed", "reason": f"{type(e).__name__}: {e}"}
    return {
        "status": "verified" if proc.returncode == 0 else "failed",
        "returncode": proc.returncode,
        "stdout_tail": proc.stdout[-2000:],
        "stderr_tail": proc.stderr[-2000:],
    }
