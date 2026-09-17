"""Claims: TTL management, advisory claim/release, and claim-over semantics.

A claim reserves a node for a session for up to `ttl_hours` hours. If another
session attempts to claim while a fresh claim is active, ClaimError is raised.
If the existing claim is stale (age >= ttl_hours), it is claimed-over: a new
claim is created with `superseded` recording the old session's ID.

Time injection via `_now` (a datetime; default None -> datetime.now(timezone.utc))
allows tests to avoid sleeps. All times are UTC. Started times in claim files
are ISO strings (may be naive or +00:00 — parsed via fromisoformat and treated
as UTC if naive).
"""
from __future__ import annotations

from datetime import datetime, timedelta, timezone
from pathlib import Path

from .registry import load_campaign
from .schema import Claim, ClaimError, load_claim, save_claim, slug_of


def is_stale(claim: Claim, _now: datetime | None = None) -> bool:
    """Return True if the claim's age is >= ttl_hours (i.e., expired).

    Age is calculated as (_now - started). If a claim's age equals its ttl_hours,
    it is considered stale. Claims with age < ttl_hours are fresh.

    Args:
        claim: the Claim to check.
        _now: current UTC time (default: datetime.now(timezone.utc)).

    Returns:
        True if age >= ttl_hours, False otherwise.
    """
    if _now is None:
        _now = datetime.now(timezone.utc)

    # Parse started as ISO string; treat naive as UTC
    started_dt = datetime.fromisoformat(claim.started)
    if started_dt.tzinfo is None:
        started_dt = started_dt.replace(tzinfo=timezone.utc)

    age = _now - started_dt
    ttl_delta = timedelta(hours=claim.ttl_hours)
    return age >= ttl_delta


def load_claims(root: Path) -> dict[str, Claim]:
    """Load all claims from <root>/claims/ directory.

    Returns a dict keyed by node slug, containing all Claim objects found in
    claims/*.toml, regardless of staleness. Use load_fresh_claims() to filter
    out expired claims.

    Args:
        root: campaign root directory.

    Returns:
        dict[str, Claim] mapping node slug to Claim object.
    """
    root = Path(root)
    claims_dir = root / "claims"
    result: dict[str, Claim] = {}

    if not claims_dir.is_dir():
        return result

    for toml_file in sorted(claims_dir.glob("*.toml")):
        claim_obj = load_claim(toml_file)
        slug = slug_of(claim_obj.node)
        result[slug] = claim_obj

    return result


def load_fresh_claims(root: Path, _now: datetime | None = None) -> dict[str, Claim]:
    """Load all fresh (non-stale) claims from <root>/claims/ directory.

    A claim is fresh if its age < ttl_hours (i.e., is_stale() returns False).
    Stale claims are filtered out and not included in the returned dict.

    Args:
        root: campaign root directory.
        _now: current UTC time for staleness check (default: datetime.now(timezone.utc)).

    Returns:
        dict[str, Claim] mapping node slug to fresh Claim objects only.
    """
    all_claims = load_claims(root)
    fresh = {slug: claim for slug, claim in all_claims.items()
             if not is_stale(claim, _now=_now)}
    return fresh


def claim(root: Path, slug: str, session: str, ttl_hours: int = 24, note: str = "",
          _now: datetime | None = None) -> Claim:
    """Claim a node for a session, returning the new Claim.

    A claim reserves the node for the session for up to ttl_hours hours.

    Raises ClaimError if:
    - The node is not open (status != "open").
    - Another session holds a fresh claim on the node.

    If an existing claim is stale (age >= ttl_hours), it is claimed-over:
    a new claim is created with superseded recording the old session ID.

    Args:
        root: campaign root directory.
        slug: node slug (e.g., "Demo_lemma_a").
        session: session ID claiming the node.
        ttl_hours: TTL in hours (default: 24).
        note: optional note on the claim (default: "").
        _now: current UTC time (default: datetime.now(timezone.utc)).

    Returns:
        The new Claim object (written to <root>/claims/<slug>.toml).

    Raises:
        ClaimError: if node is not open or another session holds a fresh claim.
    """
    if _now is None:
        _now = datetime.now(timezone.utc)

    root = Path(root)

    # Load the campaign to check if the node exists and is open
    campaign = load_campaign(root)
    if slug not in campaign.nodes:
        raise ClaimError(f"Node {slug!r} not found in campaign.")

    node = campaign.nodes[slug]
    if node.status != "open":
        raise ClaimError(f"Node {slug!r} is not open (status: {node.status!r}).")

    # Check for existing claims
    all_claims = load_claims(root)
    if slug in all_claims:
        existing = all_claims[slug]
        if is_stale(existing, _now=_now):
            # Claim-over: create new claim with superseded set
            new_claim = Claim(
                node=node.name,
                session=session,
                started=_now.isoformat(),
                ttl_hours=ttl_hours,
                note=note,
                superseded=existing.session,
            )
        else:
            # Fresh claim by another session -> error
            if existing.session != session:
                raise ClaimError(
                    f"Node {slug!r} is already claimed by session {existing.session!r}."
                )
            # Same session re-claiming (shouldn't happen, but allow it to update)
            new_claim = Claim(
                node=node.name,
                session=session,
                started=_now.isoformat(),
                ttl_hours=ttl_hours,
                note=note,
                superseded="",
            )
    else:
        # No existing claim, create a fresh one
        new_claim = Claim(
            node=node.name,
            session=session,
            started=_now.isoformat(),
            ttl_hours=ttl_hours,
            note=note,
            superseded="",
        )

    # Write the claim to disk
    claims_dir = root / "claims"
    claims_dir.mkdir(exist_ok=True)
    claim_file = claims_dir / f"{slug}.toml"
    save_claim(new_claim, claim_file)

    return new_claim


def release(root: Path, slug: str, session: str) -> None:
    """Release a claim, removing its file.

    Only the current claim holder may release. After a claim-over, the
    displaced session has no further authority over the claim.

    Args:
        root: campaign root directory.
        slug: node slug.
        session: session ID releasing the claim.

    Raises:
        ClaimError: if the claim is not held by this session, or if no claim
                    file exists.
    """
    root = Path(root)
    claims_dir = root / "claims"
    claim_file = claims_dir / f"{slug}.toml"

    if not claim_file.exists():
        raise ClaimError(f"No claim file for node {slug!r}.")

    existing = load_claim(claim_file)

    # Only the current holder may release
    if session != existing.session:
        raise ClaimError(
            f"Session {session!r} cannot release a claim held by {existing.session!r}."
        )

    claim_file.unlink()
