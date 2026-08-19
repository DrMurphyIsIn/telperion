from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Cell:
    certifies: bool
    complexity_bin: int


class MapElites:
    def __init__(self):
        self._cells = {}  # Cell -> (score, payload)

    def insert(self, key: Cell, score: float, payload) -> bool:
        cur = self._cells.get(key)
        if cur is None or score > cur[0]:
            self._cells[key] = (score, payload)
            return True
        return False

    def best(self):
        if not self._cells:
            return None
        score, payload = max(self._cells.values(), key=lambda t: t[0])
        return score, payload

    def cells(self) -> dict:
        return dict(self._cells)
