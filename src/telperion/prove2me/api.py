"""HTTP client for prove2.me.  stdlib urllib only — no new dependencies.

Safety properties of an AUTONOMOUS agent live here, not in callers:
  * version gate  — server `version` != SKILL_VERSION => ProtocolDrift
  * throttle      — >= min_interval_s between any two requests
  * backoff       — 429/5xx retried with exponential backoff (3 retries)
  * breaker       — breaker_threshold consecutive 5xx halts ALL further calls
"""
from __future__ import annotations

import json
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path

# Update whenever docs/vendor/prove2me_skill.md is re-vendored (spec §api.py).
# Value comes from that file's metadata.version.
SKILL_VERSION = "0.10.1"

DEFAULT_BASE_URL = "https://prove2.me/api/v1"  # confirm against vendored skill.md
_RETRIES = 3


class Prove2MeError(Exception):
    """Base class for all bridge errors."""


class AuthError(Prove2MeError):
    """401/403, or auth chain not established."""


class ProtocolDrift(Prove2MeError):
    """Server skill version != ours: refetch https://prove2.me/skill.md."""


class RateLimited(Prove2MeError):
    """429 persisted through backoff."""


class PlatformDown(Prove2MeError):
    """5xx (single) or circuit breaker open (repeated)."""


@dataclass(frozen=True)
class HttpResponse:
    status: int
    body: str

    def json(self) -> dict:
        return json.loads(self.body) if self.body else {}


def _urllib_transport(method: str, url: str, headers: dict, body: bytes | None) -> HttpResponse:
    req = urllib.request.Request(url, data=body, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            return HttpResponse(resp.status, resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        return HttpResponse(e.code, e.read().decode("utf-8", errors="replace"))


class Prove2MeClient:
    def __init__(
        self,
        workspace: Path,
        base_url: str = DEFAULT_BASE_URL,
        transport=None,
        min_interval_s: float = 1.0,
        breaker_threshold: int = 5,
        _sleep=time.sleep,
        _now=time.monotonic,
    ):
        self.workspace = Path(workspace)
        self.base_url = base_url.rstrip("/")
        self._transport = transport or _urllib_transport
        self._min_interval = min_interval_s
        self._breaker_threshold = breaker_threshold
        self._consecutive_5xx = 0
        self._last_request_at: float | None = None
        self._sleep = _sleep
        self._now = _now
        self.access_token: str | None = None

    # -- core ---------------------------------------------------------------

    def request(self, method: str, path: str, json_body: dict | None = None, auth: bool = True) -> dict:
        if self._consecutive_5xx >= self._breaker_threshold:
            raise PlatformDown(
                f"circuit breaker open after {self._consecutive_5xx} consecutive "
                f"server errors; halt the loop and investigate before resetting"
            )
        headers = {"Content-Type": "application/json", "User-Agent": "telperion-p2m"}
        if auth:
            if not self.access_token:
                raise AuthError("no access token: run the auth chain first")
            headers["Authorization"] = f"Bearer {self.access_token}"
        body = json.dumps(json_body).encode() if json_body is not None else None

        resp: HttpResponse | None = None
        for attempt in range(_RETRIES + 1):
            self._throttle()
            resp = self._transport(method, self.base_url + path, headers, body)
            if resp.status not in (429,) and resp.status < 500:
                break
            if attempt < _RETRIES:
                self._sleep(2.0 * 2 ** attempt)
        assert resp is not None

        if resp.status == 429:
            raise RateLimited(f"{method} {path}: still 429 after {_RETRIES} retries")
        if resp.status >= 500:
            self._consecutive_5xx += 1
            raise PlatformDown(f"{method} {path}: HTTP {resp.status}")
        self._consecutive_5xx = 0
        if resp.status in (401, 403):
            raise AuthError(f"{method} {path}: HTTP {resp.status}: {resp.body[:200]}")
        if resp.status >= 400:
            raise Prove2MeError(f"{method} {path}: HTTP {resp.status}: {resp.body[:500]}")
        return resp.json()

    def _throttle(self) -> None:
        now = self._now()
        if self._last_request_at is not None:
            wait = self._min_interval - (now - self._last_request_at)
            if wait > 0:
                self._sleep(wait)
        self._last_request_at = self._now()

    def _check_version(self, payload: dict) -> None:
        v = payload.get("version")
        if v is not None and v != SKILL_VERSION:
            raise ProtocolDrift(
                f"platform skill version {v!r} != ours {SKILL_VERSION!r}: "
                f"re-vendor https://prove2.me/skill.md and update SKILL_VERSION"
            )
