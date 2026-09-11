"""Prove2MeClient core: transport injection, auth gate, throttle, breaker."""
import json
import sys
import urllib.error
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.api import (  # noqa: E402
    SKILL_VERSION,
    AuthError,
    HttpResponse,
    PlatformDown,
    ProtocolDrift,
    Prove2MeClient,
    Prove2MeError,
    RateLimited,
)


def make_client(tmp_path, responses, **kw):
    """Client with a scripted transport; records every request it makes."""
    calls = []

    def transport(method, url, headers, body):
        calls.append((method, url, headers, body))
        r = responses.pop(0)
        return r if isinstance(r, HttpResponse) else HttpResponse(*r)

    slept = []
    c = Prove2MeClient(
        workspace=tmp_path,
        transport=transport,
        _sleep=slept.append,
        _now=lambda: 0.0,
        **kw,
    )
    return c, calls, slept


def ok(payload):
    return HttpResponse(200, json.dumps(payload))


def test_request_returns_parsed_json(tmp_path):
    c, calls, _ = make_client(tmp_path, [ok({"hello": "world"})])
    out = c.request("GET", "/missions", auth=False)
    assert out == {"hello": "world"}
    assert calls[0][0] == "GET" and calls[0][1].endswith("/missions")


def test_version_gate_raises_protocol_drift(tmp_path):
    bad = ok({"version": SKILL_VERSION + "-newer", "access_token": "t"})
    c, _, _ = make_client(tmp_path, [bad])
    with pytest.raises(ProtocolDrift):
        c._check_version(bad.json())


def test_401_raises_auth_error(tmp_path):
    c, _, _ = make_client(tmp_path, [HttpResponse(401, "{}")])
    with pytest.raises(AuthError):
        c.request("GET", "/missions", auth=False)


def test_429_raises_rate_limited_after_retries(tmp_path):
    c, calls, slept = make_client(
        tmp_path, [HttpResponse(429, "{}")] * 4
    )
    with pytest.raises(RateLimited):
        c.request("GET", "/missions", auth=False)
    assert len(calls) == 4          # initial + 3 backoff retries
    assert len(slept) >= 3          # backoff sleeps happened


def test_breaker_halts_after_5_consecutive_5xx(tmp_path):
    c, _, _ = make_client(tmp_path, [HttpResponse(500, "{}")] * 40)
    for _ in range(5):
        with pytest.raises(PlatformDown):
            c.request("GET", "/missions", auth=False)
    with pytest.raises(PlatformDown, match="circuit breaker"):
        c.request("GET", "/missions", auth=False)


def test_breaker_resets_on_success(tmp_path):
    seq = [HttpResponse(500, "{}")] * 16 + [ok({})] + [HttpResponse(500, "{}")] * 4
    c, _, _ = make_client(tmp_path, list(seq))
    for _ in range(4):
        with pytest.raises(PlatformDown):
            c.request("GET", "/missions", auth=False)
    c.request("GET", "/missions", auth=False)   # success resets counter
    with pytest.raises(PlatformDown):
        c.request("GET", "/missions", auth=False)  # count restarts at 1, no halt


def test_urlerror_raises_platform_down_and_trips_breaker(tmp_path):
    """URLError (connection failure, timeout, DNS) is typed, retried, and counted by breaker."""
    calls = []

    def transport_with_urlerror(method, url, headers, body):
        calls.append((method, url))
        raise urllib.error.URLError("connection refused")

    c = Prove2MeClient(
        workspace=tmp_path,
        transport=transport_with_urlerror,
        _sleep=lambda x: None,
        _now=lambda: 0.0,
    )
    with pytest.raises(PlatformDown, match="connection failed"):
        c.request("GET", "/missions", auth=False)
    # Initial + 3 retries = 4 transport calls
    assert len(calls) == 4, f"Expected 4 calls (initial + 3 retries), got {len(calls)}"
    assert c._consecutive_5xx == 1  # URLError counts as a server error


def test_malformed_json_raises_typed_error(tmp_path):
    """Non-JSON error body (e.g., HTML 502) raises Prove2MeError, not raw JSONDecodeError."""
    resp = HttpResponse(502, "<html>Gateway Error</html>")
    with pytest.raises(Prove2MeError, match="malformed JSON"):
        resp.json()


def test_malformed_json_in_request_response(tmp_path):
    """Malformed JSON in a 200 response is caught and wrapped."""
    c, _, _ = make_client(tmp_path, [HttpResponse(200, "not json")])
    with pytest.raises(Prove2MeError, match="malformed JSON"):
        c.request("GET", "/missions", auth=False)


def test_auth_chain_persists_key_and_token(tmp_path):
    responses = [
        ok({"version": SKILL_VERSION, "session_token": "sess"}),          # /login
        ok({"api_key": "KEY30", "expires_at": "2026-10-11T00:00:00Z"}),   # /agent/api-key
        ok({"version": SKILL_VERSION, "access_token": "HOURLY",
            "expires_at": "2026-09-11T13:00:00Z"}),                        # /agent/refresh
    ]
    c, calls, _ = make_client(tmp_path, responses)
    c.login("me@example.com", "pw")
    c.mint_api_key()
    c.refresh()
    assert c.access_token == "HOURLY"
    saved = json.loads((tmp_path / "telperion_tokens.json").read_text())
    assert saved["api_key"] == "KEY30"
    # every auth response was version-gated: drift in any would have raised


def test_login_version_drift_refuses(tmp_path):
    c, _, _ = make_client(
        tmp_path, [ok({"version": "other", "session_token": "s"})]
    )
    with pytest.raises(ProtocolDrift):
        c.login("me@example.com", "pw")


def test_verify_returns_submission_id_and_verdict_polls(tmp_path):
    c, calls, _ = make_client(
        tmp_path,
        [ok({"submission_id": "sub1"}), ok({"status": "Proved"})],
    )
    c.access_token = "t"
    sid = c.verify("theorem solution : 1 = 1 := rfl", target_id="thm9")
    assert sid == "sub1"
    assert c.verdict("sub1")["status"] == "Proved"
    assert calls[0][0] == "POST" and "/verify" in calls[0][1]
    assert calls[1][0] == "GET" and "submission_id=sub1" in calls[1][1]


def test_ensure_auth_uses_persisted_key(tmp_path):
    (tmp_path / "telperion_tokens.json").write_text(json.dumps(
        {"api_key": "KEY30", "api_key_expires": "2099-01-01T00:00:00Z"}
    ))
    c, calls, _ = make_client(
        tmp_path,
        [ok({"version": SKILL_VERSION, "access_token": "T2",
             "expires_at": "2099-01-01T01:00:00Z"})],
    )
    c.ensure_auth()
    assert c.access_token == "T2"
