from __future__ import annotations

import json
import urllib.error
import urllib.request


class OllamaClient:
    def __init__(self, host: str = "http://localhost:11434", model: str = "qwen2.5-coder:7b"):
        self.host = host.rstrip("/")
        self.model = model

    def available(self) -> bool:
        try:
            with urllib.request.urlopen(self.host + "/api/tags", timeout=2.0):
                return True
        except Exception:  # noqa: BLE001
            return False

    def chat(self, system: str, user: str, temperature: float, seed: int, timeout: float = 60.0) -> str | None:
        body = json.dumps({
            "model": self.model,
            "messages": [{"role": "system", "content": system},
                         {"role": "user", "content": user}],
            "temperature": float(temperature),
            "seed": int(seed),
            "stream": False,
        }).encode()
        req = urllib.request.Request(
            self.host + "/v1/chat/completions", data=body,
            headers={"Content-Type": "application/json"},
        )
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                data = json.loads(resp.read())
            return data["choices"][0]["message"]["content"]
        except Exception:  # noqa: BLE001 - unreachable/malformed => structured fallback
            return None
