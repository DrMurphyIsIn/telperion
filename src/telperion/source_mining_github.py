"""GitHub-repos source adapter — watch already-formalized Lean math repos.

The commits of the big Lean-verified math libraries (Mathlib, DeepMind's
formal-conjectures, PrimeNumberTheoremAnd, Compfiles) are a stream of *proven*
results.  A commit whose message names a certificate shape Telperion emits is a
``LEAD_FORMALIZED`` lead: the theorem already exists in Lean, so the lead is a
*direct port* (wire an emitter that reproduces / reuses it), not a
formalize-first candidate.

`parse_github_commits` is the pure normalizer (commit JSON → entry dict) so the
classifier can be exercised offline; `fetch_github_repos` is the thin,
unauthenticated urllib GET that the `github_source()` adapter injects into the
Source framework.
"""
from __future__ import annotations

from typing import Iterable

from .source_mining import LEAD_FORMALIZED, Source

# Already-formalized (Lean-verified) math repos — commits are proven results.
GITHUB_REPOS: tuple[str, ...] = (
    "leanprover-community/mathlib4",
    "google-deepmind/formal-conjectures",
    "AlexKontorovich/PrimeNumberTheoremAnd",
    "dwrensha/compfiles",              # Catalog Of Math Problems Formalized In Lean
    # Frontier formalization drops mined by the 2026-09 campaigns — commits are
    # Lean-verified port leads (NS/Euler blowup: 25 emitter kinds distilled;
    # zeta-23: hermitian-moment emitters; ZetaZeros: curvature/enclosure emitters).
    "openai/NavierStokesAndEuler",
    "anthropics/zeta-23-lean",
    "AxiomMath/ZetaZeros",
)

GITHUB_API = "https://api.github.com"


def parse_github_commits(commits: list[dict], repo: str) -> list[dict]:
    """Normalize a repo's GitHub commit JSON into classify_entry-compatible
    entries.  Pure (offline-testable).

    Each commit → ``{id: "{repo}@{sha[:12]}", title: <first message line>,
    abstract: <full message>, source: {repo, url}}``.  Merge commits (message
    starts with ``"Merge "``) are skipped — they carry no theorem signal.
    """
    out: list[dict] = []
    for c in commits:
        sha = str(c.get("sha", ""))
        commit = c.get("commit") or {}
        message = (commit.get("message") or "").strip()
        if not sha or not message:
            continue
        if message.startswith("Merge "):
            continue
        title = message.splitlines()[0].strip()
        out.append({
            "id": f"{repo}@{sha[:12]}",
            "title": title,
            "abstract": message,
            "source": {"repo": repo, "url": c.get("html_url", "")},
        })
    return out


def fetch_github_repos(repos: Iterable[str] = GITHUB_REPOS, per_repo: int = 30,
                       timeout: float = 30.0) -> list[dict]:
    """Fetch recent commits across `repos` and normalize them into entries.

    Unauthenticated (60 req/hr shared rate limit).  Any per-repo failure — an
    HTTP 403 rate-limit, a network error, a bad payload — is swallowed so one
    dead repo can never crash the poll; that repo is simply skipped.
    """
    import json
    import urllib.error
    import urllib.request

    headers = {
        "User-Agent": "telperion-source-mining/0.1",
        "Accept": "application/vnd.github+json",
    }
    out: list[dict] = []
    for repo in repos:
        url = f"{GITHUB_API}/repos/{repo}/commits?per_page={per_repo}"
        req = urllib.request.Request(url, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310
                commits = json.loads(resp.read().decode("utf-8"))
            if isinstance(commits, list):
                out.extend(parse_github_commits(commits, repo))
        except (urllib.error.URLError, TimeoutError, ValueError, OSError):
            # rate-limited (403), network hiccup, or malformed payload — skip repo.
            continue
    return out


def github_source(repos: Iterable[str] = GITHUB_REPOS, per_repo: int = 30) -> Source:
    """The `github` adapter: Lean-verified repos → direct-port (formalized) leads."""
    return Source(name="github", lead_type=LEAD_FORMALIZED,
                  fetch=lambda: fetch_github_repos(repos, per_repo),
                  default_topics=("rh", "bg", "pvsnp"))
