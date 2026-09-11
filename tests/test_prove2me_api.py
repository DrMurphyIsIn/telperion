"""Prove2MeClient core: transport injection, auth gate, throttle, breaker."""
import json
import sys
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
