"""Lean-Zulip source adapter (raw math) — mine the formalization chatter.

The Lean community's Zulip (`https://leanprover.zulipchat.com`) is where new
Mathlib results, open formalization requests ("Is there code for X?"), and
frontier discussions surface *before* anything is in a repo.  This adapter polls
selected streams via the Zulip REST API and normalizes each message topic into a
`classify_entry`-compatible entry.

Because Zulip discussion is UNFORMALIZED, this is a ``LEAD_RAW`` source: a matched
shape is a *formalize-first* candidate, never a ready certificate.

The network path needs a Zulip bot email + API key (a read-only bot subscribed to
the streams below).  Supply them via `fetch_zulip(email=, api_key=)` or the env
vars ``ZULIP_EMAIL`` / ``ZULIP_API_KEY`` (and optionally ``ZULIP_SITE``).  With no
credentials the fetch is a graceful no-op (logs a note, returns ``[]``) so the
scheduler and the offline core stay healthy without a provisioned bot.  The
message parser (`parse_zulip_messages`) is pure and offline-testable.
"""
from __future__ import annotations

import base64
import html
import json
import os
import re
import sys
import urllib.parse
import urllib.request
from typing import Iterable

from .source_mining import LEAD_RAW, Source

ZULIP_SITE = "https://leanprover.zulipchat.com"
# Streams richest in certificate-relevant, formalization-ready chatter: the
# number-theory / RH corner (Palomar), core Mathlib development, and the
# standing "does a formalization already exist?" request channel.
ZULIP_STREAMS = ("Palomar", "mathlib4", "Is there code for X?")

_TAG_RE = re.compile(r"<[^>]+>")


def _strip_html(content: str) -> str:
    """Reduce Zulip message HTML to plain text: drop tags, unescape entities,
    collapse whitespace.  Minimal by design (Zulip content is well-formed HTML
    but we only need the text signal for the classifier)."""
    text = _TAG_RE.sub(" ", content or "")
    text = html.unescape(text)
    return " ".join(text.split())


def parse_zulip_messages(payload: dict, stream: str = "") -> list[dict]:
    """Parse a Zulip ``GET /api/v1/messages`` response into
    classify_entry-compatible entries.  Pure (offline-testable).

    Per message: ``id = "zulip-<msg id>"``; ``title`` = the topic
    (``subject``); ``abstract`` = the message ``content`` with HTML stripped and
    entities unescaped; the near-message permalink in ``source.url``.  The stream
    name (when known) is carried in ``classification.zulip`` alongside the sender.
    """
    out: list[dict] = []
    for message in payload.get("messages", []) or []:
        mid = message.get("id")
        entry_id = f"zulip-{mid}"
        title = message.get("subject", "") or ""
        abstract = _strip_html(message.get("content", "") or "")
        stream_slug = urllib.parse.quote(stream, safe="") if stream else "unknown"
        out.append({
            "id": entry_id,
            "title": title,
            "abstract": abstract,
            "classification": {
                "zulip": {
                    "stream": stream,
                    "sender": message.get("sender_full_name", ""),
                    "timestamp": message.get("timestamp"),
                },
            },
            "source": {
                "url": f"{ZULIP_SITE}/#narrow/stream/{stream_slug}/near/{mid}",
            },
        })
    return out


def _fetch_one_stream(site: str, stream: str, num_before: int, auth_header: str,
                      timeout: float) -> list[dict]:
    """GET one stream's most recent messages.  Raises on network/HTTP error
    (the caller wraps per-stream so one bad stream never sinks the poll)."""
    narrow = json.dumps([{"operator": "channel", "operand": stream}])
    params = urllib.parse.urlencode({
        "anchor": "newest",
        "num_before": str(num_before),
        "num_after": "0",
        "narrow": narrow,
    })
    req = urllib.request.Request(
        f"{site}/api/v1/messages?{params}",
        headers={
            "Authorization": f"Basic {auth_header}",
            "User-Agent": "telperion-source-mining/0.1",
        },
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310
        payload = json.loads(resp.read().decode("utf-8"))
    return parse_zulip_messages(payload, stream=stream)


def fetch_zulip(site: str = ZULIP_SITE, streams: Iterable[str] = ZULIP_STREAMS,
                num_before: int = 100, email: str | None = None,
                api_key: str | None = None, timeout: float = 30.0) -> list[dict]:
    """Fetch the most recent messages across `streams`, newest first.

    Credentials come from the args or, failing that, the env vars
    ``ZULIP_EMAIL`` / ``ZULIP_API_KEY`` (site from ``ZULIP_SITE``).  With no
    credentials this is a graceful no-op: it logs a note to stderr and returns
    ``[]`` (never raises), so an unprovisioned Zulip bot degrades to "no leads"
    rather than breaking the scheduler.  Per-stream network errors are caught and
    skipped."""
    site = os.environ.get("ZULIP_SITE", site)
    email = email if email is not None else os.environ.get("ZULIP_EMAIL")
    api_key = api_key if api_key is not None else os.environ.get("ZULIP_API_KEY")

    if not email or not api_key:
        print("[zulip] no credentials (ZULIP_EMAIL / ZULIP_API_KEY unset) — "
              "skipping Zulip fetch; returning no leads.", file=sys.stderr)
        return []

    auth_header = base64.b64encode(f"{email}:{api_key}".encode("utf-8")).decode("ascii")
    out: list[dict] = []
    for stream in streams:
        try:
            out.extend(_fetch_one_stream(site, stream, num_before, auth_header, timeout))
        except Exception as exc:  # noqa: BLE001 — one bad stream must not sink the poll
            print(f"[zulip] stream {stream!r} fetch failed: {exc!r} — skipping.",
                  file=sys.stderr)
    return out


def zulip_source(site: str = ZULIP_SITE, streams: Iterable[str] = ZULIP_STREAMS,
                 num_before: int = 100) -> Source:
    """The Lean-Zulip source adapter: raw-math (formalize-first) leads."""
    return Source(name="zulip", lead_type=LEAD_RAW,
                  fetch=lambda: fetch_zulip(site=site, streams=streams,
                                            num_before=num_before),
                  default_topics=("rh", "bg", "pvsnp"))
