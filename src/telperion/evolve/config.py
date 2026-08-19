from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

try:
    import tomllib  # py3.11+
except ModuleNotFoundError:  # py3.9
    tomllib = None

_REPO = Path(__file__).resolve().parents[3]
_DEFAULT_LEAN = str(_REPO / "examples" / "g1_floors" / "lean")


@dataclass(frozen=True)
class EvolveConfig:
    model_tag: str = "qwen2.5-coder:7b"
    model_digest: str = ""            # pin like the Mathlib rev; empty = unpinned
    islands: int = 4
    gens: int = 20
    temperatures: tuple = (0.2, 0.6, 1.0, 1.2)
    max_llm_calls: int = 200
    max_kernel_checks: int = 20
    lean_project: str = _DEFAULT_LEAN
    use_llm: bool = True

    @classmethod
    def default(cls) -> "EvolveConfig":
        return cls()

    @classmethod
    def from_toml(cls, path: str) -> "EvolveConfig":
        text = Path(path).read_text()
        table = _read_evolve_table(text)
        base = cls.default().__dict__
        merged = {**base, **table}
        if "temperatures" in merged:
            merged["temperatures"] = tuple(merged["temperatures"])
        return cls(**{k: merged[k] for k in base})


def _read_evolve_table(text: str) -> dict:
    if tomllib is not None:
        data = tomllib.loads(text)
        return data.get("evolve", {})
    # minimal 3.9 fallback: parse the [evolve] table's simple key = value lines
    out, in_tbl = {}, False
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("[") and s.endswith("]"):
            in_tbl = s == "[evolve]"
            continue
        if not in_tbl or "=" not in s or s.startswith("#"):
            continue
        k, v = (x.strip() for x in s.split("=", 1))
        out[k] = _coerce(v)
    return out


def _coerce(v: str):
    v = v.strip()
    # Remove inline comments (# starts a comment)
    if "#" in v:
        v = v.split("#")[0].strip()
    if v.startswith("[") and v.endswith("]"):
        inner = v[1:-1].strip()
        return [_coerce(x) for x in inner.split(",")] if inner else []
    if v.startswith('"') and v.endswith('"'):
        return v[1:-1]
    if v in ("true", "false"):
        return v == "true"
    try:
        return int(v)
    except ValueError:
        try:
            return float(v)
        except ValueError:
            return v
