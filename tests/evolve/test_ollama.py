from __future__ import annotations

import json
from telperion.evolve.ollama import OllamaClient


class _FakeResp:
    def __init__(self, payload):
        self._p = json.dumps(payload).encode()

    def read(self):
        return self._p

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


def test_chat_parses_content(monkeypatch):
    c = OllamaClient()
    payload = {"choices": [{"message": {"content": '{"ratio_src":"s+1","s0":5,"lift_max":4}'}}]}
    monkeypatch.setattr("telperion.evolve.ollama.urllib.request.urlopen",
                        lambda *a, **k: _FakeResp(payload))
    out = c.chat("sys", "user", temperature=0.5, seed=1)
    assert '"ratio_src"' in out


def test_chat_returns_none_on_transport_error(monkeypatch):
    c = OllamaClient()
    def boom(*a, **k):
        raise OSError("connection refused")
    monkeypatch.setattr("telperion.evolve.ollama.urllib.request.urlopen", boom)
    assert c.chat("sys", "user", temperature=0.5, seed=1) is None
