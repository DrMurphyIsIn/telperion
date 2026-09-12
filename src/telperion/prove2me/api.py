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
from datetime import datetime, timezone
from pathlib import Path

# Update whenever docs/vendor/prove2me_skill.md is re-vendored (spec §api.py).
# Value comes from that file's metadata.version.
SKILL_VERSION = "0.10.1"

DEFAULT_BASE_URL = "https://prove2.me/api/v1"
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
        if not self.body:
            return {}
        try:
            return json.loads(self.body)
        except json.JSONDecodeError as e:
            raise Prove2MeError(f"malformed JSON in response: {e}") from e


def _encode_multipart(fields: dict, file_content: bytes,
                      file_field: str = "file",
                      filename: str = "solution.lean") -> tuple[bytes, str]:
    """RFC 2388 multipart/form-data body for POST /verify (stdlib only).

    Boundary is derived from the payload hash — deterministic (no
    Date.now/random in cert-adjacent paths) and collision-checked against
    the content.
    """
    import hashlib as _hashlib
    seed = _hashlib.sha256(file_content + repr(sorted(fields.items())).encode())
    boundary = "telperion-p2m-" + seed.hexdigest()[:24]
    while boundary.encode() in file_content:
        boundary += "x"
    parts: list[bytes] = []
    for name, value in fields.items():
        parts.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"'
            f"\r\n\r\n{value}\r\n".encode()
        )
    parts.append(
        f'--{boundary}\r\nContent-Disposition: form-data; name="{file_field}"; '
        f'filename="{filename}"\r\nContent-Type: text/plain; charset=utf-8'
        f"\r\n\r\n".encode() + file_content + b"\r\n"
    )
    parts.append(f"--{boundary}--\r\n".encode())
    return b"".join(parts), f"multipart/form-data; boundary={boundary}"


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

    def request(self, method: str, path: str, json_body: dict | None = None, auth: bool = True,
                multipart: tuple[bytes, str] | None = None) -> dict:
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
        if multipart is not None:
            body, content_type = multipart
            headers["Content-Type"] = content_type
        else:
            body = json.dumps(json_body).encode() if json_body is not None else None

        resp: HttpResponse | None = None
        for attempt in range(_RETRIES + 1):
            self._throttle()
            try:
                resp = self._transport(method, self.base_url + path, headers, body)
            except urllib.error.URLError as e:
                if attempt < _RETRIES:
                    self._sleep(2.0 * 2 ** attempt)
                    continue
                self._consecutive_5xx += 1
                raise PlatformDown(f"connection failed: {e}") from e
            if resp.status not in (429,) and resp.status < 500:
                break
            if attempt < _RETRIES:
                self._sleep(2.0 * 2 ** attempt)
        if resp is None:
            raise Prove2MeError("internal: no response from transport")

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

    # -- auth chain (credentials -> 30-day key -> hourly token) -------------

    @property
    def _tokens_path(self) -> Path:
        return self.workspace / "telperion_tokens.json"

    def _load_tokens(self) -> dict:
        if self._tokens_path.exists():
            return json.loads(self._tokens_path.read_text())
        return {}

    def _save_tokens(self, updates: dict) -> None:
        doc = self._load_tokens()
        doc.update(updates)
        self.workspace.mkdir(parents=True, exist_ok=True)
        self._tokens_path.write_text(json.dumps(doc, indent=1) + "\n")

    def login(self, email: str, password: str) -> None:
        out = self.request("POST", "/login",
                           {"email": email, "password": password}, auth=False)
        self._check_version(out)
        self._session_token = out.get("session_token") or out.get("token")

    def mint_api_key(self) -> str:
        headers_token = getattr(self, "_session_token", None)
        if not headers_token:
            raise AuthError("login first: mint_api_key needs a session token")
        old = self.access_token
        self.access_token = headers_token          # session token authorizes minting
        try:
            out = self.request("POST", "/agent/api-key", {})
        finally:
            self.access_token = old
        self._check_version(out)
        self._session_token = None
        self._save_tokens({"api_key": out["api_key"],
                           "api_key_expires": out.get("expires_at", "")})
        return out["api_key"]

    def refresh(self) -> None:
        key = self._load_tokens().get("api_key")
        if not key:
            raise AuthError("no api key: run login + mint_api_key (or paste one "
                            "from account settings into telperion_tokens.json)")
        out = self.request("POST", "/agent/refresh", {"api_key": key}, auth=False)
        self._check_version(out)
        self.access_token = out["access_token"]
        self._save_tokens({"access_token": self.access_token,
                           "access_expires": out.get("expires_at", "")})

    def ensure_auth(self) -> None:
        if self.access_token:
            return
        saved = self._load_tokens()
        expires_str = saved.get("access_expires")
        if not self._is_token_valid(expires_str):
            self.refresh()
            return
        self.access_token = saved.get("access_token")

    def _is_token_valid(self, expires_at: str | int | float | None) -> bool:
        """Check if a token expiry timestamp is still valid (in the future).

        The live platform returns epoch seconds (int); older fixtures and the
        vendored docs show ISO 8601 strings. Accept both; anything
        unparseable is invalid (forces a refresh).
        """
        if not expires_at:
            return False
        try:
            if isinstance(expires_at, (int, float)):
                expiry = datetime.fromtimestamp(expires_at, timezone.utc)
            else:
                expiry = datetime.fromisoformat(expires_at.replace("Z", "+00:00"))
            return expiry > datetime.now(timezone.utc)
        except (ValueError, TypeError, OSError):
            return False

    # -- endpoints ----------------------------------------------------------

    def missions(self) -> list:
        """All missions, paginated (live API defaults to 20/page; limit+offset
        confirmed 2026-09-11)."""
        all_missions: list = []
        offset = 0
        while True:
            out = self.request("GET", f"/missions?limit=100&offset={offset}")
            batch = out if isinstance(out, list) else out.get("missions", [])
            all_missions.extend(batch)
            if len(batch) < 100:
                return all_missions
            offset += 100

    def milestones(self, mission_id: str) -> list:
        out = self.request("GET", f"/missions/{mission_id}/milestones")
        return out if isinstance(out, list) else out.get("milestones", [])

    def theorem(self, theorem_id: str) -> dict:
        return self.request("GET", f"/theorems/{theorem_id}")

    def theorem_graph(self, theorem_id: str) -> dict:
        return self.request("GET", f"/theorems/{theorem_id}/graph")

    def theorem_submissions(self, theorem_id: str) -> list:
        out = self.request("GET", f"/theorems/{theorem_id}/submissions")
        return out if isinstance(out, list) else out.get("submissions", [])

    def milestone_history(self, milestone_id: str) -> list:
        out = self.request("GET", f"/milestones/{milestone_id}/history")
        return out if isinstance(out, list) else out.get("history", [])

    def verify(self, lean_source: str, target_id: str, explanation: str = "",
               proof_type: str = "") -> str:
        """Submit solution.lean for a theorem. LIVE contract (references/prove.md):
        multipart/form-data with theorem_id + file (+ optional explanation,
        proof_type=disprove). Visibility inherits from the target."""
        fields = {"theorem_id": target_id}
        if proof_type:
            fields["proof_type"] = proof_type
        if explanation:
            fields["explanation"] = explanation
        out = self.request("POST", "/verify",
                           multipart=_encode_multipart(fields, lean_source.encode()))
        return out["submission_id"]

    def verdict(self, submission_id: str) -> dict:
        return self.request("GET", f"/verify?submission_id={submission_id}")

    def annotate(self, submission_id: str, explanation: str) -> None:
        self.request("PATCH", f"/submissions/{submission_id}",
                     {"explanation": explanation})

    def comment(self, mission_id: str, text: str) -> None:
        self.request("POST", f"/missions/{mission_id}/comments", {"text": text})

    def rate(self, target_id: str, payload: dict) -> None:
        self.request("POST", "/rate", {"target_id": target_id, **payload})

    def submit_problem(self, payload: dict) -> dict:
        return self.request("POST", "/submit-problem", payload)

    def submit_definition(self, payload: dict) -> dict:
        return self.request("POST", "/submit-definition", payload)

    def publish_jobs(self) -> list:
        out = self.request("GET", "/publish-jobs")
        return out if isinstance(out, list) else out.get("jobs", [])
