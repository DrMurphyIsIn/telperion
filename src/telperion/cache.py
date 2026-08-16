"""The persistent certification cache — justified by measurement.

The 972-cell production family spent most of a 25-minute run on redundant
work: fork workers rebuild cold caches, and the provenance-hash pass re-derives
everything serially.  This cache makes re-certification a read.

Trust note: the cache is a PERFORMANCE layer, not a soundness layer.  A stale
or corrupted entry produces wrong emitted text, which the drift net catches
and the Lean kernel would refuse — same guarantee as everything else the
generator does.  Entries are keyed by content hash (expression srepr + knobs +
tool version), so editing a family busts its entries automatically.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import sympy as sp


class DiskCache:
    def __init__(self, directory: Path | str):
        self.dir = Path(directory)
        self.dir.mkdir(parents=True, exist_ok=True)
        self.hits = 0
        self.misses = 0

    def _path(self, key: str) -> Path:
        return self.dir / f"{key}.json"

    def get(self, key: str):
        p = self._path(key)
        if not p.exists():
            self.misses += 1
            return None
        self.hits += 1
        return json.loads(p.read_text())

    def put(self, key: str, value: dict) -> None:
        self._path(key).write_text(json.dumps(value))


def cert_key(expr: sp.Expr, lift_max: int) -> str:
    from . import __version__

    payload = f"{__version__}|{lift_max}|{sp.srepr(expr)}"
    return hashlib.sha256(payload.encode()).hexdigest()[:32]


def memoize(cache: DiskCache, key_fn):
    """Decorator for expensive family internals (comparator searches, closed
    forms): results must be JSON-able.  Family authors opt in explicitly —
    the tool never caches user code behind their back."""

    def wrap(fn):
        def inner(*args):
            key = "user_" + hashlib.sha256(
                repr(key_fn(*args)).encode()
            ).hexdigest()[:32]
            got = cache.get(key)
            if got is not None:
                return got["value"]
            value = fn(*args)
            cache.put(key, {"value": value})
            return value

        return inner

    return wrap
