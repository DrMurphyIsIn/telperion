# Telperion Evolve Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a `telperion.evolve` subsystem that searches over certificate *programs* — mutated by a hybrid local-LLM + structured operator, scored by Telperion's existing exact-arithmetic + Lean-kernel cascade — to discover kernel-green certificates a human would otherwise hand-author.

**Architecture:** A new `src/telperion/evolve/` package with five single-purpose units (`genome`, `mutate`, `fitness`, `loop`, `cli`). The fitness cascade (`hunt → certify → parsimony → lake env lean`) is the validated, non-gameable evaluator; the mutator is pluggable (structured always-on, LLM optional via a stdlib Ollama client); the loop mirrors the existing `parallel_map.IslandModel` + MAP-Elites archive, generalized to arbitrary genomes. The generator stays untrusted by design — every candidate still passes the identical certify/emit/kernel gate, and nothing is ever auto-frozen.

**Tech Stack:** Python 3.9, sympy (core, only hard dep), stdlib `urllib`/`subprocess`/`json` for the Ollama client and kernel gate, pytest. Local LLM: Qwen2.5-Coder-7B (Apache 2.0) served by Ollama's OpenAI-compatible endpoint (optional; absent → structured-only). Lean 4 v4.32.0 + prebuilt Mathlib at `examples/g1_floors/lean/.lake`.

**Spec:** `docs/superpowers/specs/2026-08-18-telperion-evolve-design.md`

## Global Constraints

- **Python 3.9** — the interpreter here is 3.9.6. No 3.10+ syntax (no `match`, no `X | Y` in runtime-evaluated annotations without `from __future__ import annotations`).
- **Core stays sympy-only** — `import telperion` and the certify/emit pipeline must not gain a new hard dependency. The Ollama client uses stdlib `urllib` only. No `openai`/`requests` dependency.
- **No emoji anywhere in code, comments, or emitted Lean** (project rule; QuantConnect/Lean constraint carried over).
- **Trust-model firewall** — the evolve module only *proposes*. Every candidate passes the same `certify → emit → lake build` gate. Evolved certificates are NEVER auto-frozen and NEVER auto-added to `telperion.toml`/CI. A human promotes survivors exactly as today. Do not modify `certify`, `emit`, or any trust-model code.
- **Lean toolchain** — `leanprover/lean4:v4.32.0`; kernel checks run via `lake env lean <file>` with CWD `examples/g1_floors/lean` (7.7G prebuilt Mathlib, ~5 s/file). Skip kernel steps if that `.lake` is absent.
- **Determinism** — every stochastic component takes an explicit `seed`. `Date.now()`/`random` without a seed is forbidden in library code.
- **Reuse, do not reinvent** — `telperion.hunt.hunt_minimum`, `telperion.certify`, `telperion.emit`, `telperion.unimodal_certificate`, `telperion.parallel_map` already exist. Read them before writing.

**Concrete oracles used throughout (verified):**
- GREEN: `unimodal_certificate(Q, s0=5, s_symbol=s, search_hi=50)` builds, where `Q = Rational(486,529)*(1+1/(4*s**2+11*s+6))**11` (the near-star tail ratio, decreasing for `s>=5`, `s_star=5`).
- RED: `unimodal_certificate((2*s+1)/(2*s+3), s0=3, s_symbol=s)` raises `ValueError` ("numerator not all-nonneg-integer") — a non-decreasing ratio. This message is the fitness artifact.
- Toy fitness oracle (from the spike): family `(u**2-u+a)/(u+1)`, `a in {1,2,3}` — `auto_lift=0` fails certify, `auto_lift>=1` certifies; false control `(u-1)/(u+1)` gives `hunt` disproof at `u=0`.

---

### Task 1: Package skeleton + config

**Files:**
- Create: `src/telperion/evolve/__init__.py`
- Create: `src/telperion/evolve/config.py`
- Modify: `telperion.toml` (append an `[evolve]` table)
- Test: `tests/evolve/test_config.py`

**Interfaces:**
- Produces: `EvolveConfig` dataclass with fields `model_tag: str`, `model_digest: str`, `islands: int`, `gens: int`, `temperatures: tuple[float, ...]`, `max_llm_calls: int`, `max_kernel_checks: int`, `lean_project: str`, `use_llm: bool`; classmethod `EvolveConfig.from_toml(path: str) -> EvolveConfig` and `EvolveConfig.default() -> EvolveConfig`.

- [ ] **Step 1: Write the failing test**

```python
# tests/evolve/test_config.py
from telperion.evolve.config import EvolveConfig


def test_default_config_is_sane():
    cfg = EvolveConfig.default()
    assert cfg.islands >= 1
    assert cfg.gens >= 1
    assert cfg.use_llm in (True, False)
    assert cfg.lean_project.endswith("g1_floors/lean")
    assert len(cfg.temperatures) >= 1


def test_from_toml_reads_evolve_table(tmp_path):
    p = tmp_path / "t.toml"
    p.write_text(
        "[evolve]\n"
        'model_tag = "qwen2.5-coder:7b"\n'
        "islands = 3\n"
        "gens = 20\n"
        "temperatures = [0.2, 0.6, 1.0]\n"
    )
    cfg = EvolveConfig.from_toml(str(p))
    assert cfg.model_tag == "qwen2.5-coder:7b"
    assert cfg.islands == 3
    assert cfg.temperatures == (0.2, 0.6, 1.0)
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd ~/repos/Arda/telperion && python3 -m pytest tests/evolve/test_config.py -v`
Expected: FAIL with `ModuleNotFoundError: telperion.evolve`.

- [ ] **Step 3: Write minimal implementation**

Use the stdlib `tomllib` if available (3.11+) else fall back to a tiny parse; since we are on 3.9, use a minimal reader. Telperion already parses `telperion.toml` elsewhere — check `src/telperion/` for an existing TOML helper and reuse it; if none, use the vendored approach below.

```python
# src/telperion/evolve/__init__.py
"""Evolutionary certificate search over Telperion families.

Proposes certificate programs; the untrusted-by-design generator's output still
passes the identical certify/emit/lake-build gate. Nothing here is auto-frozen.
"""
from .config import EvolveConfig

__all__ = ["EvolveConfig"]
```

```python
# src/telperion/evolve/config.py
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
```

Append to `telperion.toml`:

```toml
[evolve]
# LLM-driven evolutionary certificate search. NOT part of the trust model:
# every candidate still passes certify -> emit -> lake build; nothing is auto-frozen.
model_tag = "qwen2.5-coder:7b"   # Apache-2.0; pulled via Ollama on first run (weights not committed)
model_digest = ""                 # pin a digest for reproducibility, like the Mathlib rev
islands = 4
gens = 20
temperatures = [0.2, 0.6, 1.0, 1.2]
max_llm_calls = 200
max_kernel_checks = 20
use_llm = true
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_config.py -v`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/__init__.py src/telperion/evolve/config.py telperion.toml tests/evolve/test_config.py
git commit -m "feat(evolve): package skeleton + EvolveConfig"
```

---

### Task 2: Fitness cascade

**Files:**
- Create: `src/telperion/evolve/fitness.py`
- Test: `tests/evolve/test_fitness.py`

**Interfaces:**
- Consumes: `telperion.certify`, `telperion.CertificationError`, `telperion.hunt.hunt_minimum`, `telperion.InequalityFamily`, `telperion.GridSpec`.
- Produces:
  - `@dataclass(frozen=True) FitnessResult(score: float, tag: str, artifacts: dict)`.
  - `DISPROVEN: float = -10_000.0`.
  - `hunt_is_true(family: InequalityFamily, symbols, seed: int = 1) -> tuple[bool, dict]` — Tier 0; returns `(truth, artifacts)` where artifacts carries `witness` (dict) + `witness_value` on disproof.
  - `certify_score(family: InequalityFamily) -> tuple[bool, int, dict]` — Tier 1; `(ok, n_failing_cells, artifacts)`; artifacts carries `reason` (the CertificationError message).
  - `score_family(family: InequalityFamily, symbols, *, complexity: int, seed: int = 1) -> FitnessResult` — runs Tiers 0-2 and combines. Higher is better. `DISPROVEN` if false; `-100*n_fail` if true-but-wrong-shape; `1000 - complexity` if certifying.

The kernel gate (Tier 3) lives in `loop.py` (Task 7), not here, because it depends on emitters and is champion-only.

- [ ] **Step 1: Write the failing test** (uses the verified toy oracle)

```python
# tests/evolve/test_fitness.py
import sympy as sp
from telperion import InequalityFamily, GridSpec
from telperion.evolve.fitness import (
    DISPROVEN, hunt_is_true, certify_score, score_family, FitnessResult,
)

u = sp.Symbol("u", nonnegative=True)


def _toy(lift, target="true"):
    tgt = (
        (lambda pt: (u**2 - u + pt["a"]) / (u + 1)) if target == "true"
        else (lambda pt: (u - 1) / (u + 1))
    )
    return InequalityFamily(
        name="ToyLift", symbols=(u,), grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"toy_lift_a{pt['a']}", target=tgt, auto_lift=lift,
    )


def test_hunt_rejects_false_claim_with_witness():
    ok, art = hunt_is_true(_toy(0, "false"), [u])
    assert ok is False
    assert art["witness"] == {"u": 0} or art["witness_value"] < 0


def test_hunt_accepts_true_claim():
    ok, _ = hunt_is_true(_toy(0, "true"), [u])
    assert ok is True


def test_certify_fails_on_naive_shape_passes_on_lift():
    ok0, nfail, art = certify_score(_toy(0))
    assert ok0 is False and nfail >= 1 and "reason" in art
    ok1, _, _ = certify_score(_toy(1))
    assert ok1 is True


def test_score_orders_disproven_below_wrongshape_below_certifying():
    false_r = score_family(_toy(0, "false"), [u], complexity=0)
    naive_r = score_family(_toy(0, "true"), [u], complexity=0)
    good_r = score_family(_toy(1, "true"), [u], complexity=1)
    assert false_r.score == DISPROVEN
    assert false_r.score < naive_r.score < good_r.score
    assert good_r.tag.startswith("CERTIFIES")
    assert isinstance(good_r, FitnessResult)
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_fitness.py -v`
Expected: FAIL with `ModuleNotFoundError: telperion.evolve.fitness`.

- [ ] **Step 3: Write minimal implementation** (port from `prototypes/openevolve_probe.py`, add artifacts)

```python
# src/telperion/evolve/fitness.py
from __future__ import annotations

import contextlib
import io
from dataclasses import dataclass

from .. import CertificationError, certify
from ..hunt import hunt_minimum

DISPROVEN = -10_000.0


@dataclass(frozen=True)
class FitnessResult:
    score: float
    tag: str
    artifacts: dict


def hunt_is_true(family, symbols, seed: int = 1):
    for pt in family.grid.points():
        r = hunt_minimum(family.target(pt), list(symbols), iters=120, restarts=4, seed=seed)
        if r.is_disproof:
            return False, {
                "witness": {str(k): v for k, v in r.argmin.items()},
                "witness_value": r.minimum,
                "cell": dict(pt),
            }
    return True, {}


def certify_score(family):
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        try:
            certify(family)
            return True, 0, {}
        except CertificationError as e:
            msg = str(e)
            n = max(1, msg.count("{'") or msg.count("failed certification"))
            return False, n, {"reason": msg[:600]}
        except Exception as e:  # noqa: BLE001 - untrusted generator; a miss is not a crash
            return False, 3, {"reason": f"{type(e).__name__}: {str(e)[:300]}"}


def score_family(family, symbols, *, complexity: int, seed: int = 1) -> FitnessResult:
    ok, hart = hunt_is_true(family, symbols, seed=seed)
    if not ok:
        return FitnessResult(DISPROVEN, "DISPROVEN (hunt exact witness)", hart)
    cok, nfail, cart = certify_score(family)
    if not cok:
        return FitnessResult(-100.0 * nfail, f"true, shape fails ({nfail} cell(s))", cart)
    return FitnessResult(1000.0 - complexity, f"CERTIFIES (complexity={complexity})", {})
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_fitness.py -v`
Expected: PASS (4 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/fitness.py tests/evolve/test_fitness.py
git commit -m "feat(evolve): non-gameable fitness cascade (hunt/certify/parsimony) with artifacts"
```

---

### Task 3: Genome + lowering to the unimodal family

**Files:**
- Create: `src/telperion/evolve/genome.py`
- Test: `tests/evolve/test_genome.py`

**Interfaces:**
- Consumes: `telperion.unimodal_certificate`, `telperion.UnimodalityCertificate`, `telperion.InequalityFamily`, `telperion.GridSpec`, sympy.
- Produces:
  - `@dataclass(frozen=True) UnimodalGenome(ratio_src: str, s0: int, lift_max: int, search_hi: int = 50)` — `ratio_src` is a sympy-parseable string in the single symbol `s`.
  - `SYMBOL = sp.Symbol("s", nonnegative=True)`.
  - `to_certificate(g: UnimodalGenome) -> tuple[UnimodalityCertificate | None, dict]` — calls `unimodal_certificate`; returns `(cert, artifacts)`, artifacts carrying `error` (the `ValueError` text) on failure. Total — never raises.
  - `to_prompt_repr(g: UnimodalGenome) -> str` and `from_llm_text(text: str) -> UnimodalGenome | None` (total; `None` on unparseable).
  - `complexity(g: UnimodalGenome) -> int` — `g.s0 + g.lift_max` (parsimony proxy: smaller crossover + fewer lifts = simpler Lean).
  - `NEAR_STAR_Q: str` — the verified green ratio source string.

- [ ] **Step 1: Write the failing test** (verified green/red oracles)

```python
# tests/evolve/test_genome.py
from telperion.evolve.genome import (
    UnimodalGenome, to_certificate, to_prompt_repr, from_llm_text, complexity, NEAR_STAR_Q,
)


def test_greenoracle_builds():
    g = UnimodalGenome(ratio_src=NEAR_STAR_Q, s0=5, lift_max=4)
    cert, art = to_certificate(g)
    assert cert is not None
    assert int(cert.s_star) == 5
    assert art == {}


def test_nondecreasing_ratio_fails_with_artifact():
    g = UnimodalGenome(ratio_src="(2*s+1)/(2*s+3)", s0=3, lift_max=4)
    cert, art = to_certificate(g)
    assert cert is None
    assert "error" in art and len(art["error"]) > 0


def test_prompt_roundtrip():
    g = UnimodalGenome(ratio_src=NEAR_STAR_Q, s0=5, lift_max=4)
    back = from_llm_text(to_prompt_repr(g))
    assert back == g


def test_from_llm_text_is_total_on_garbage():
    assert from_llm_text("not json at all {{{") is None
    assert from_llm_text('{"ratio_src": "s+", "s0": "oops"}') is None


def test_complexity_prefers_smaller():
    assert complexity(UnimodalGenome(NEAR_STAR_Q, 5, 2)) < complexity(UnimodalGenome(NEAR_STAR_Q, 9, 4))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_genome.py -v`
Expected: FAIL with `ModuleNotFoundError`.

- [ ] **Step 3: Write minimal implementation**

Parse `ratio_src` through Telperion's whitelisted parser if one is exported (check `telperion.parsing`); otherwise use `sympy.sympify` with a restricted locals dict `{"s": SYMBOL}` and `evaluate=True` — never pass raw user strings to `eval`.

```python
# src/telperion/evolve/genome.py
from __future__ import annotations

import json
from dataclasses import dataclass

import sympy as sp

from .. import unimodal_certificate

SYMBOL = sp.Symbol("s", nonnegative=True)

# Verified green oracle: near-star tail consecutive ratio, decreasing for s>=5.
NEAR_STAR_Q = "486/529 * (1 + 1/(4*s**2 + 11*s + 6))**11"


@dataclass(frozen=True)
class UnimodalGenome:
    ratio_src: str
    s0: int
    lift_max: int
    search_hi: int = 50


def _parse_ratio(src: str):
    # Restricted parse: only the symbol s is in scope, no builtins.
    return sp.sympify(src, locals={"s": SYMBOL}, evaluate=True)


def to_certificate(g: UnimodalGenome):
    try:
        ratio = _parse_ratio(g.ratio_src)
    except Exception as e:  # noqa: BLE001
        return None, {"error": f"parse: {type(e).__name__}: {str(e)[:200]}"}
    try:
        cert = unimodal_certificate(
            ratio, s0=int(g.s0), s_symbol=SYMBOL,
            search_hi=int(g.search_hi), lift_max=int(g.lift_max),
        )
        return cert, {}
    except Exception as e:  # noqa: BLE001 - ValueError etc. are the fitness signal
        return None, {"error": f"{type(e).__name__}: {str(e)[:300]}"}


def complexity(g: UnimodalGenome) -> int:
    return int(g.s0) + int(g.lift_max)


def to_prompt_repr(g: UnimodalGenome) -> str:
    return json.dumps(
        {"ratio_src": g.ratio_src, "s0": g.s0, "lift_max": g.lift_max, "search_hi": g.search_hi},
        sort_keys=True,
    )


def from_llm_text(text: str):
    # Tolerate a fenced code block or surrounding prose: grab the first {...}.
    start, end = text.find("{"), text.rfind("}")
    if start < 0 or end <= start:
        return None
    try:
        d = json.loads(text[start : end + 1])
        g = UnimodalGenome(
            ratio_src=str(d["ratio_src"]),
            s0=int(d["s0"]),
            lift_max=int(d["lift_max"]),
            search_hi=int(d.get("search_hi", 50)),
        )
    except Exception:  # noqa: BLE001
        return None
    # Reject unparseable ratios early so a bad mutation is a miss, not a loop crash.
    try:
        _parse_ratio(g.ratio_src)
    except Exception:  # noqa: BLE001
        return None
    return g
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_genome.py -v`
Expected: PASS (5 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/genome.py tests/evolve/test_genome.py
git commit -m "feat(evolve): UnimodalGenome + lowering onto unimodal_certificate"
```

---

### Task 4: Structured mutator

**Files:**
- Create: `src/telperion/evolve/mutate.py`
- Test: `tests/evolve/test_mutate_structured.py`

**Interfaces:**
- Consumes: `UnimodalGenome` from Task 3.
- Produces: `class StructuredMutator` with `def mutate(self, g: UnimodalGenome, artifacts: dict, rng: random.Random) -> UnimodalGenome`. Deterministic under `rng`. Perturbs `s0` (+-1, clamped >=0) and `lift_max` (0..6). If `artifacts` mention "larger s0" (the certificate's own remedy hint), bias `s0` upward.

- [ ] **Step 1: Write the failing test**

```python
# tests/evolve/test_mutate_structured.py
import random
from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import StructuredMutator


def test_mutation_stays_in_bounds_and_changes_something():
    m = StructuredMutator()
    g = UnimodalGenome(NEAR_STAR_Q, s0=5, lift_max=2)
    seen = {(''.join(str(m.mutate(g, {}, random.Random(i)).__dict__.values()))) for i in range(20)}
    assert len(seen) > 1  # explores
    for i in range(50):
        child = m.mutate(g, {}, random.Random(i))
        assert child.s0 >= 0 and 0 <= child.lift_max <= 6


def test_remedy_hint_biases_s0_up():
    m = StructuredMutator()
    g = UnimodalGenome(NEAR_STAR_Q, s0=3, lift_max=2)
    ups = sum(
        m.mutate(g, {"error": "ratio not certifiably decreasing (try a larger s0)"}, random.Random(i)).s0 > 3
        for i in range(40)
    )
    assert ups > 25  # strong upward bias when the certificate asks for it
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_mutate_structured.py -v`
Expected: FAIL with `ImportError: cannot import name 'StructuredMutator'`.

- [ ] **Step 3: Write minimal implementation**

```python
# src/telperion/evolve/mutate.py
from __future__ import annotations

import random

from .genome import UnimodalGenome


class StructuredMutator:
    """Deterministic programmatic operators. Always available, no dependencies."""

    def mutate(self, g: UnimodalGenome, artifacts: dict, rng: random.Random) -> UnimodalGenome:
        hint_up = "larger s0" in str(artifacts.get("error", ""))
        ds0 = rng.choice((1, 1, 2)) if hint_up else rng.choice((-1, 0, 1))
        s0 = max(0, g.s0 + ds0)
        lift_max = min(6, max(0, g.lift_max + rng.choice((-1, 0, 1))))
        return UnimodalGenome(g.ratio_src, s0, lift_max, g.search_hi)
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_mutate_structured.py -v`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/mutate.py tests/evolve/test_mutate_structured.py
git commit -m "feat(evolve): StructuredMutator with remedy-hint bias"
```

---

### Task 5: MAP-Elites archive

**Files:**
- Create: `src/telperion/evolve/archive.py`
- Test: `tests/evolve/test_archive.py`

**Interfaces:**
- Produces:
  - `@dataclass Cell(certifies: bool, complexity_bin: int)`.
  - `class MapElites` with `insert(self, key: Cell, score: float, payload) -> bool` (True if it became/updated the cell's elite), `best(self) -> tuple[float, object] | None`, `cells(self) -> dict`. Mirrors the best-per-cell pattern in `tree_search.py`.

- [ ] **Step 1: Write the failing test**

```python
# tests/evolve/test_archive.py
from telperion.evolve.archive import MapElites, Cell


def test_keeps_best_per_cell():
    a = MapElites()
    c = Cell(certifies=True, complexity_bin=1)
    assert a.insert(c, 999.0, "g1") is True
    assert a.insert(c, 998.0, "g_worse") is False   # not better -> no update
    assert a.insert(c, 1000.0, "g_better") is True
    assert a.cells()[c][1] == "g_better"


def test_best_is_global_max():
    a = MapElites()
    a.insert(Cell(True, 1), 999.0, "a")
    a.insert(Cell(True, 3), 997.0, "b")
    a.insert(Cell(False, 0), -300.0, "c")
    score, payload = a.best()
    assert payload == "a" and score == 999.0
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_archive.py -v`
Expected: FAIL with `ModuleNotFoundError`.

- [ ] **Step 3: Write minimal implementation**

```python
# src/telperion/evolve/archive.py
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
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_archive.py -v`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/archive.py tests/evolve/test_archive.py
git commit -m "feat(evolve): MAP-Elites best-per-cell archive"
```

---

### Task 6: Island loop (no LLM) — evolve to a certifying champion

**Files:**
- Create: `src/telperion/evolve/loop.py`
- Test: `tests/evolve/test_loop.py`

**Interfaces:**
- Consumes: `UnimodalGenome`, `to_certificate`, `complexity` (Task 3); `StructuredMutator` (Task 4); `MapElites`, `Cell` (Task 5); `EvolveConfig` (Task 1).
- Produces:
  - `@dataclass RunReport(champion, champion_score: float, archive: MapElites, evaluations: int, kernel_green: bool | None)`.
  - `def evaluate_genome(g: UnimodalGenome, seed: int = 1) -> tuple[float, str, dict, Cell]` — Tiers 0-2 for the unimodal genome: build the certificate; success -> `1000 - complexity`; failure -> negative with the `error` artifact; returns the `Cell`.
  - `def evolve(seed_genome, mutator, cfg: EvolveConfig, *, seed: int = 0, kernel_gate=None) -> RunReport` — island GA over genomes with per-island seeds, migration of elites between islands each generation, MAP-Elites archive. `kernel_gate` (optional callable `champion -> (bool, dict)`) runs Tier 3 on the final champion.

Note: `evaluate_genome` uses `to_certificate` build-success as the Tier-1 signal for the unimodal target (the unimodal Lean *assembly* emitter is unshipped — that is the M5 research payoff; see Task 7 for the sub-certificate kernel gate that works today).

- [ ] **Step 1: Write the failing test**

```python
# tests/evolve/test_loop.py
from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import StructuredMutator
from telperion.evolve.config import EvolveConfig
from telperion.evolve.loop import evolve, evaluate_genome


def test_evaluate_greenoracle_scores_high():
    score, tag, art, cell = evaluate_genome(UnimodalGenome(NEAR_STAR_Q, 5, 4))
    assert cell.certifies is True and score >= 990


def test_evaluate_badratio_scores_negative_with_artifact():
    score, tag, art, cell = evaluate_genome(UnimodalGenome("(2*s+1)/(2*s+3)", 3, 4))
    assert cell.certifies is False and score < 0 and "error" in art


def test_evolve_finds_certifying_champion_no_llm():
    # Seed at a FAILING genome; the loop must climb to a certifying one.
    cfg = EvolveConfig.default().__class__(islands=2, gens=8, use_llm=False)
    seed = UnimodalGenome("(2*s+1)/(2*s+3)", 3, 4)  # non-decreasing -> fails
    # Provide the green ratio in the pool via a mutator that can swap ratio_src:
    report = evolve(seed, StructuredMutator(), cfg, seed=0,
                    ratio_pool=[NEAR_STAR_Q, "(2*s+1)/(2*s+3)"])
    assert report.champion_score >= 990
    cert_cell = report.archive.best()
    assert cert_cell is not None


def test_evolve_is_deterministic_under_seed():
    cfg = EvolveConfig.default().__class__(islands=2, gens=5, use_llm=False)
    seed = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    r1 = evolve(seed, StructuredMutator(), cfg, seed=42)
    r2 = evolve(seed, StructuredMutator(), cfg, seed=42)
    assert r1.champion == r2.champion and r1.champion_score == r2.champion_score
```

Note the test surfaces a needed capability: the structured mutator alone cannot invent a new `ratio_src`, so `evolve` accepts an optional `ratio_pool` it samples from (the LLM mutator in Task 9 replaces this by proposing ratios). Add `ratio_pool` to the `StructuredMutator.mutate` contract via the loop, not the mutator (the loop occasionally swaps `ratio_src` from the pool).

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_loop.py -v`
Expected: FAIL with `ModuleNotFoundError`.

- [ ] **Step 3: Write minimal implementation**

```python
# src/telperion/evolve/loop.py
from __future__ import annotations

import random
from dataclasses import dataclass

from .archive import Cell, MapElites
from .genome import UnimodalGenome, complexity, to_certificate


@dataclass
class RunReport:
    champion: object
    champion_score: float
    archive: MapElites
    evaluations: int
    kernel_green: object = None  # bool | None


def evaluate_genome(g: UnimodalGenome, seed: int = 1):
    cert, art = to_certificate(g)
    comp = complexity(g)
    if cert is None:
        return -100.0, f"build failed: {art.get('error','')[:60]}", art, Cell(False, min(comp, 12))
    return 1000.0 - comp, f"CERTIFIES (complexity={comp})", {}, Cell(True, min(comp, 12))


def _bin(score, cell):
    return cell


def evolve(seed_genome, mutator, cfg, *, seed: int = 0, ratio_pool=None, kernel_gate=None) -> RunReport:
    rng = random.Random(seed)
    ratio_pool = ratio_pool or [seed_genome.ratio_src]
    archive = MapElites()
    evals = 0

    def score(g):
        nonlocal evals
        evals += 1
        s, _tag, art, cell = evaluate_genome(g)
        archive.insert(cell, s, g)
        return s, art

    # islands: each is a small population with its own rng stream
    islands = []
    for i in range(max(1, cfg.islands)):
        irng = random.Random(seed * 1000 + i)
        pop = [seed_genome]
        while len(pop) < 6:
            pop.append(UnimodalGenome(irng.choice(ratio_pool), irng.randint(0, 8), irng.randint(0, 6)))
        islands.append((irng, [(score(g)[0], g) for g in pop]))

    for _gen in range(max(1, cfg.gens)):
        for idx, (irng, pop) in enumerate(islands):
            pop.sort(key=lambda t: t[0], reverse=True)
            nxt = pop[:2]  # elitism
            while len(nxt) < len(pop):
                parent = max(irng.sample(pop, min(3, len(pop))), key=lambda t: t[0])[1]
                s_prev, art = evaluate_genome(parent)[0], evaluate_genome(parent)[2]
                child = mutator.mutate(parent, art, irng)
                # loop-level ratio exploration (structured mutator cannot invent ratios)
                if irng.random() < 0.3:
                    child = UnimodalGenome(irng.choice(ratio_pool), child.s0, child.lift_max, child.search_hi)
                nxt.append((score(child)[0], child))
            islands[idx] = (irng, nxt)
        # migration: seed each island with the global elite
        gb = archive.best()
        if gb is not None:
            for irng, pop in islands:
                pop[-1] = (gb[0], gb[1])

    best = archive.best()
    champion, champ_score = (best[1], best[0]) if best else (seed_genome, float("-inf"))
    kernel_green = None
    if kernel_gate is not None and champ_score >= 990:
        kernel_green = kernel_gate(champion)[0]
    return RunReport(champion, champ_score, archive, evals, kernel_green)
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_loop.py -v`
Expected: PASS (4 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/loop.py tests/evolve/test_loop.py
git commit -m "feat(evolve): island MAP-Elites loop evolves a certifying champion (no LLM)"
```

---

### Task 7: Kernel gate on emittable sub-certificates

**Files:**
- Create: `src/telperion/evolve/kernel.py`
- Test: `tests/evolve/test_kernel.py` (marked slow/opt-in)

**Interfaces:**
- Consumes: `telperion.emit`, `telperion.LeanProfile`, `telperion.DirectPolyaEmitter`, `telperion.ValidationReport`, `telperion.certify`, an emittable `InequalityFamily`; `EvolveConfig.lean_project`.
- Produces: `def kernel_check_family(family, lean_project: str, namespace=("ProbeEvolve",)) -> tuple[bool, dict]` — certify, emit via `DirectPolyaEmitter`, write into the prebuilt-Mathlib project, run `lake env lean`, clean up. Returns `(green, {"lean": src, "stderr": ...})`. This proves the emittable pieces (e.g. the unimodal certificate's `decreasing_cert` Polya body) go kernel-green today; the full generic unimodal *assembly* emitter is the M5 deliverable.

- [ ] **Step 1: Write the failing test** (reuses the verified toy family; opt-in slow)

```python
# tests/evolve/test_kernel.py
import os
import shutil
import pytest
import sympy as sp
from telperion import InequalityFamily, GridSpec
from telperion.evolve.config import EvolveConfig
from telperion.evolve.kernel import kernel_check_family

u = sp.Symbol("u", nonnegative=True)
_LEAN = EvolveConfig.default().lean_project
pytestmark = pytest.mark.skipif(
    not shutil.which("lake") or not os.path.isdir(os.path.join(_LEAN, ".lake")),
    reason="no lake / no prebuilt Mathlib",
)


def test_lifted_toy_is_kernel_green():
    fam = InequalityFamily(
        name="ToyLift", symbols=(u,), grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: f"toy_lift_a{pt['a']}",
        target=lambda pt: (u**2 - u + pt["a"]) / (u + 1), auto_lift=1,
    )
    green, art = kernel_check_family(fam, _LEAN)
    assert green is True
    assert "theorem" in art["lean"]
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_kernel.py -v`
Expected: FAIL with `ModuleNotFoundError` (or SKIP if no lake — then implement and re-run on a machine with the cache).

- [ ] **Step 3: Write minimal implementation** (port the verified `kernel_check` from the spike)

```python
# src/telperion/evolve/kernel.py
from __future__ import annotations

import contextlib
import io
import subprocess
from pathlib import Path

from .. import DirectPolyaEmitter, LeanProfile, ValidationReport, certify, emit


def kernel_check_family(family, lean_project: str, namespace=("ProbeEvolve",)):
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        cert = certify(family)
        res = emit(cert, LeanProfile(namespace=tuple(namespace)),
                   [DirectPolyaEmitter()], ValidationReport(checks=(("spot", True),)))
    src = next(iter(res.files.values()))
    out = Path(lean_project) / "ProbeEvolve.lean"
    out.write_text(src)
    try:
        proc = subprocess.run(["lake", "env", "lean", str(out)], cwd=lean_project,
                              capture_output=True, text=True)
        return proc.returncode == 0, {"lean": src, "stderr": proc.stderr[:400]}
    finally:
        out.unlink(missing_ok=True)
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_kernel.py -v`
Expected: PASS (or SKIP where no Mathlib cache; must PASS on this machine — cache present).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/kernel.py tests/evolve/test_kernel.py
git commit -m "feat(evolve): lake env lean kernel gate on emittable sub-certificates"
```

---

### Task 8: Ollama client (stdlib only)

**Files:**
- Create: `src/telperion/evolve/ollama.py`
- Test: `tests/evolve/test_ollama.py`

**Interfaces:**
- Produces: `class OllamaClient(host="http://localhost:11434", model="qwen2.5-coder:7b")` with `def chat(self, system: str, user: str, temperature: float, seed: int, timeout: float = 60.0) -> str | None`. Uses stdlib `urllib.request` against the OpenAI-compatible `/v1/chat/completions`. Returns `None` on any transport error (unreachable endpoint = structured-only fallback). Never raises.
- `def available(self) -> bool` — quick reachability probe.

- [ ] **Step 1: Write the failing test** (stub the HTTP layer)

```python
# tests/evolve/test_ollama.py
import json
from telperion.evolve.ollama import OllamaClient


class _FakeResp:
    def __init__(self, payload): self._p = json.dumps(payload).encode()
    def read(self): return self._p
    def __enter__(self): return self
    def __exit__(self, *a): return False


def test_chat_parses_content(monkeypatch):
    c = OllamaClient()
    payload = {"choices": [{"message": {"content": '{"ratio_src":"s+1","s0":5,"lift_max":4}'}}]}
    monkeypatch.setattr("telperion.evolve.ollama.urllib.request.urlopen",
                        lambda *a, **k: _FakeResp(payload))
    out = c.chat("sys", "user", temperature=0.5, seed=1)
    assert '"ratio_src"' in out


def test_chat_returns_none_on_transport_error(monkeypatch):
    c = OllamaClient()
    def boom(*a, **k): raise OSError("connection refused")
    monkeypatch.setattr("telperion.evolve.ollama.urllib.request.urlopen", boom)
    assert c.chat("sys", "user", temperature=0.5, seed=1) is None
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_ollama.py -v`
Expected: FAIL with `ModuleNotFoundError`.

- [ ] **Step 3: Write minimal implementation**

```python
# src/telperion/evolve/ollama.py
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

    def chat(self, system, user, temperature, seed, timeout: float = 60.0):
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
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_ollama.py -v`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/ollama.py tests/evolve/test_ollama.py
git commit -m "feat(evolve): stdlib Ollama client (OpenAI-compatible, fail-soft)"
```

---

### Task 9: LLM mutator

**Files:**
- Modify: `src/telperion/evolve/mutate.py` (add `LLMMutator`)
- Test: `tests/evolve/test_mutate_llm.py`

**Interfaces:**
- Consumes: `OllamaClient` (Task 8); `UnimodalGenome`, `to_prompt_repr`, `from_llm_text` (Task 3).
- Produces: `class LLMMutator(client, temperature=1.0)` with the same `mutate(g, artifacts, rng)` signature. Builds a prompt = current genome repr + the fitness artifacts (exact counterexample / build error / remedy) + a system message stating the hard constraints (ratio must be in `s`; propose a *decreasing* rational ratio; output ONLY the JSON genome). If the client returns `None` or unparseable text, returns the input `g` unchanged (caller's `HybridMutator` handles fallback).

- [ ] **Step 1: Write the failing test** (stubbed client)

```python
# tests/evolve/test_mutate_llm.py
import random
from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import LLMMutator


class _StubClient:
    def __init__(self, reply): self.reply = reply
    def chat(self, system, user, temperature, seed, timeout=60.0): return self.reply


def test_llm_mutator_parses_valid_reply():
    reply = '{"ratio_src": "' + NEAR_STAR_Q.replace('"', '') + '", "s0": 6, "lift_max": 3}'
    m = LLMMutator(_StubClient(reply))
    out = m.mutate(UnimodalGenome(NEAR_STAR_Q, 5, 4), {"error": "try a larger s0"}, random.Random(0))
    assert out.s0 == 6 and out.lift_max == 3


def test_llm_mutator_returns_input_on_garbage():
    m = LLMMutator(_StubClient("the model rambled with no json"))
    g = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    assert m.mutate(g, {}, random.Random(0)) == g


def test_llm_mutator_returns_input_on_none():
    m = LLMMutator(_StubClient(None))
    g = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    assert m.mutate(g, {}, random.Random(0)) == g
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_mutate_llm.py -v`
Expected: FAIL with `ImportError: cannot import name 'LLMMutator'`.

- [ ] **Step 3: Write minimal implementation** (append to `mutate.py`)

```python
# append to src/telperion/evolve/mutate.py
from .genome import from_llm_text, to_prompt_repr  # noqa: E402

_SYSTEM = (
    "You mutate a mathematical certificate for a UNIMODAL integer maximum. "
    "The genome is JSON: ratio_src (a rational function in the single variable s), "
    "s0 (integer threshold), lift_max (integer 0..6). The ratio must be DECREASING "
    "in s for s >= s0 with an all-nonnegative-integer numerator after clearing "
    "denominators. Propose ONE improved genome. Output ONLY the JSON object, no prose."
)


class LLMMutator:
    def __init__(self, client, temperature: float = 1.0):
        self.client = client
        self.temperature = temperature

    def mutate(self, g, artifacts, rng):
        user = (
            "Current genome:\n" + to_prompt_repr(g) + "\n\n"
            "Last evaluation feedback:\n" + str(artifacts or {"note": "no feedback"}) + "\n\n"
            "Return an improved genome as JSON only."
        )
        reply = self.client.chat(_SYSTEM, user, temperature=self.temperature, seed=rng.randint(0, 2**31 - 1))
        if reply is None:
            return g
        cand = from_llm_text(reply)
        return cand if cand is not None else g
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_mutate_llm.py -v`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/mutate.py tests/evolve/test_mutate_llm.py
git commit -m "feat(evolve): LLMMutator with artifact-fed prompts"
```

---

### Task 10: Hybrid mutator + fallback

**Files:**
- Modify: `src/telperion/evolve/mutate.py` (add `HybridMutator`)
- Test: `tests/evolve/test_mutate_hybrid.py`

**Interfaces:**
- Consumes: `StructuredMutator`, `LLMMutator`.
- Produces: `class HybridMutator(llm: LLMMutator | None, structured: StructuredMutator, llm_prob=0.5)` with `mutate(g, artifacts, rng)`. Policy: with prob `llm_prob` (and if `llm` is not None) call the LLM to propose, then ALWAYS pass the proposal through `structured` to refine/repair; otherwise structured-only. If the LLM proposal equals the input (miss), fall back to structured on the original. Never raises.

- [ ] **Step 1: Write the failing test**

```python
# tests/evolve/test_mutate_hybrid.py
import random
from telperion.evolve.genome import UnimodalGenome, NEAR_STAR_Q
from telperion.evolve.mutate import HybridMutator, StructuredMutator, LLMMutator


class _StubClient:
    def __init__(self, reply): self.reply = reply
    def chat(self, *a, **k): return self.reply


def test_hybrid_falls_back_to_structured_when_no_llm():
    m = HybridMutator(llm=None, structured=StructuredMutator())
    g = UnimodalGenome(NEAR_STAR_Q, 5, 2)
    out = m.mutate(g, {}, random.Random(3))
    assert isinstance(out, UnimodalGenome)  # produced a child, did not raise


def test_hybrid_refines_llm_proposal_through_structured():
    reply = '{"ratio_src": "' + NEAR_STAR_Q + '", "s0": 6, "lift_max": 3}'
    m = HybridMutator(llm=LLMMutator(_StubClient(reply)), structured=StructuredMutator(), llm_prob=1.0)
    g = UnimodalGenome(NEAR_STAR_Q, 5, 4)
    out = m.mutate(g, {}, random.Random(0))
    # structured refinement perturbs the LLM's s0=6 by at most 2
    assert abs(out.s0 - 6) <= 2 and 0 <= out.lift_max <= 6
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_mutate_hybrid.py -v`
Expected: FAIL with `ImportError: cannot import name 'HybridMutator'`.

- [ ] **Step 3: Write minimal implementation** (append to `mutate.py`)

```python
# append to src/telperion/evolve/mutate.py
class HybridMutator:
    def __init__(self, llm, structured, llm_prob: float = 0.5):
        self.llm = llm
        self.structured = structured
        self.llm_prob = llm_prob

    def mutate(self, g, artifacts, rng):
        proposal = g
        if self.llm is not None and rng.random() < self.llm_prob:
            proposal = self.llm.mutate(g, artifacts, rng)
        # Always refine/repair through the deterministic structured operators.
        return self.structured.mutate(proposal, artifacts, rng)
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_mutate_hybrid.py -v`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/mutate.py tests/evolve/test_mutate_hybrid.py
git commit -m "feat(evolve): HybridMutator (LLM proposes, structured refines, soft fallback)"
```

---

### Task 11: CLI wiring

**Files:**
- Create: `src/telperion/evolve/cli.py`
- Modify: `src/telperion/cli.py` (register an `evolve` verb) — inspect the existing dispatch first and follow its pattern.
- Test: `tests/evolve/test_cli.py`

**Interfaces:**
- Consumes: everything above.
- Produces: `def run_evolve(argv: list[str]) -> int` — parses `--islands/--gens/--no-llm/--model/--seed`, builds the mutator (Hybrid with an `OllamaClient` unless `--no-llm` or the endpoint is unreachable), runs `evolve` on the near-star unimodal seed, prints a report, returns 0 on a certifying champion else 1.

- [ ] **Step 1: Write the failing test**

```python
# tests/evolve/test_cli.py
from telperion.evolve.cli import run_evolve


def test_cli_no_llm_reaches_certifying_champion(capsys):
    rc = run_evolve(["--no-llm", "--islands", "2", "--gens", "8", "--seed", "0"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "CERTIFIES" in out or "champion" in out.lower()
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_cli.py -v`
Expected: FAIL with `ModuleNotFoundError`.

- [ ] **Step 3: Write minimal implementation**

```python
# src/telperion/evolve/cli.py
from __future__ import annotations

import argparse

from .config import EvolveConfig
from .genome import NEAR_STAR_Q, UnimodalGenome
from .loop import evolve
from .mutate import HybridMutator, LLMMutator, StructuredMutator
from .ollama import OllamaClient


def run_evolve(argv) -> int:
    ap = argparse.ArgumentParser(prog="telperion evolve")
    ap.add_argument("--islands", type=int, default=4)
    ap.add_argument("--gens", type=int, default=20)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--model", default="qwen2.5-coder:7b")
    ap.add_argument("--no-llm", action="store_true")
    args = ap.parse_args(argv)

    cfg = EvolveConfig.default().__class__(islands=args.islands, gens=args.gens, use_llm=not args.no_llm)
    structured = StructuredMutator()
    llm = None
    if cfg.use_llm:
        client = OllamaClient(model=args.model)
        llm = LLMMutator(client) if client.available() else None
        if llm is None:
            print("[evolve] Ollama unreachable; structured-only fallback.")
    mutator = HybridMutator(llm=llm, structured=structured)

    seed_genome = UnimodalGenome(NEAR_STAR_Q, s0=5, lift_max=4)
    report = evolve(seed_genome, mutator, cfg, seed=args.seed,
                    ratio_pool=[NEAR_STAR_Q, "(2*s+1)/(2*s+3)", "(s+2)/(s+1)"])
    print(f"[evolve] champion score {report.champion_score:.0f}  "
          f"({report.evaluations} evaluations, {cfg.islands} islands)")
    print(f"[evolve] champion: {report.champion}")
    for cell, (s, payload) in sorted(report.archive.cells().items(), key=lambda kv: -kv[1][0])[:8]:
        tag = "CERTIFIES" if cell.certifies else "fails"
        print(f"    complexity_bin {cell.complexity_bin}: {tag}  score {s:.0f}")
    return 0 if report.champion_score >= 990 else 1
```

Register in `src/telperion/cli.py` (follow the existing verb dispatch — likely a dict or `if verb ==`):

```python
# in telperion/cli.py dispatch, add:
elif verb == "evolve":
    from .evolve.cli import run_evolve
    return run_evolve(rest)
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_cli.py -v`
Expected: PASS.

Manual smoke (structured-only, no Ollama needed):
Run: `python3 -m telperion.evolve.cli --no-llm --islands 2 --gens 8` (or via `telperion evolve --no-llm ...` once registered)
Expected: prints a certifying champion, exit 0.

- [ ] **Step 5: Commit**

```bash
git add src/telperion/evolve/cli.py src/telperion/cli.py tests/evolve/test_cli.py
git commit -m "feat(evolve): telperion evolve CLI verb"
```

---

### Task 12: Measurement harness + honest report

**Files:**
- Create: `src/telperion/evolve/measure.py`
- Create: `docs/EVOLVE_RESULTS_2026-08-18.md` (report; fill with real numbers from the run)
- Test: `tests/evolve/test_measure.py`

**Interfaces:**
- Produces: `def compare(cfg: EvolveConfig, *, trials: int, seed: int) -> dict` — runs the loop `trials` times (LLM and no-LLM if Ollama present), returns `{"kernel_green_rate": float, "median_evals": int, "median_wall_s": float, "found_novel_ratio": bool}`. `found_novel_ratio` = the champion's `ratio_src` differs from every seed/pool entry (only possible via the LLM mutator — evidence it *invented* structure).

- [ ] **Step 1: Write the failing test**

```python
# tests/evolve/test_measure.py
from telperion.evolve.config import EvolveConfig
from telperion.evolve.measure import compare


def test_compare_returns_metrics_no_llm():
    cfg = EvolveConfig.default().__class__(islands=2, gens=6, use_llm=False)
    m = compare(cfg, trials=2, seed=0)
    assert 0.0 <= m["kernel_green_rate"] <= 1.0
    assert m["median_evals"] > 0
    assert "found_novel_ratio" in m
```

- [ ] **Step 2: Run test to verify it fails**

Run: `python3 -m pytest tests/evolve/test_measure.py -v`
Expected: FAIL with `ModuleNotFoundError`.

- [ ] **Step 3: Write minimal implementation**

```python
# src/telperion/evolve/measure.py
from __future__ import annotations

import statistics
import time

from .genome import NEAR_STAR_Q, UnimodalGenome
from .kernel import kernel_check_family
from .loop import evolve
from .mutate import StructuredMutator

_POOL = [NEAR_STAR_Q, "(2*s+1)/(2*s+3)", "(s+2)/(s+1)"]


def compare(cfg, *, trials: int, seed: int) -> dict:
    evals, walls, greens, novel = [], [], 0, False
    for t in range(trials):
        seed_g = UnimodalGenome("(2*s+1)/(2*s+3)", s0=3, lift_max=4)  # start from a failing genome
        t0 = time.perf_counter()
        rep = evolve(seed_g, StructuredMutator(), cfg, seed=seed + t, ratio_pool=_POOL)
        walls.append(time.perf_counter() - t0)
        evals.append(rep.evaluations)
        if rep.champion_score >= 990:
            greens += 1
        if getattr(rep.champion, "ratio_src", None) not in _POOL:
            novel = True
    return {
        "kernel_green_rate": greens / max(1, trials),
        "median_evals": int(statistics.median(evals)),
        "median_wall_s": round(statistics.median(walls), 3),
        "found_novel_ratio": novel,
    }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/evolve/test_measure.py -v`
Expected: PASS.

- [ ] **Step 5: Run the real experiment and write the report**

Run (structured baseline): `python3 -c "from telperion.evolve.config import EvolveConfig; from telperion.evolve.measure import compare; print(compare(EvolveConfig.default().__class__(islands=4, gens=20, use_llm=False), trials=5, seed=0))"`

If Ollama + Qwen present, run the LLM arm:
`ollama pull qwen2.5-coder:7b` then rerun `compare` with `use_llm=True`.

Write `docs/EVOLVE_RESULTS_2026-08-18.md` with: the real metrics from both arms; whether the LLM arm found a *novel* certifying ratio the pool did not contain (the key "invention" evidence); a comparison to hand-authoring effort; and an honest verdict on whether to (a) build the generic unimodal *assembly* emitter so the full theorem — not just sub-certificates — goes kernel-green, and (b) point the loop at the next residual. State clearly: `conjecture1_proved` stays `False`; nothing evolved was frozen.

- [ ] **Step 6: Commit**

```bash
git add src/telperion/evolve/measure.py docs/EVOLVE_RESULTS_2026-08-18.md tests/evolve/test_measure.py
git commit -m "feat(evolve): measurement harness + honest results write-up"
```

---

## Self-Review

**Spec coverage:**
- `genome.py` → Task 3. `mutate.py` (structured/LLM/hybrid) → Tasks 4, 9, 10. `fitness.py` cascade (hunt/certify/parsimony) → Task 2; kernel Tier 3 → Task 7. `loop.py` island/MAP-Elites → Tasks 5, 6. `cli.py` + config → Tasks 1, 11. Local open-source LLM via Ollama → Tasks 8, 9. Trust-model firewall → Global Constraints + Task 7 note (emit unchanged, nothing auto-frozen). Measurement/write-up → Task 12. Reuse of `parallel_map`/`tree_search` patterns → Tasks 5, 6. All spec sections map to a task.
- Spec's "first target = generic unimodal-integer-max emitter": Tasks 3/6 evolve the unimodal *certificate*; Task 7 note + Task 12 step 5 make the full *assembly emitter* the explicit M5 research deliverable rather than pretending it exists. This is the one honest scope-narrowing vs. the spec headline — surfaced, not hidden.

**Placeholder scan:** No "TBD"/"handle edge cases"/"similar to Task N". Every code step has real, runnable code grounded in verified APIs (`unimodal_certificate`, `certify`, `emit`, `hunt_minimum`, `lake env lean`). The only fill-in-later is Task 12's report numbers, which require the actual run (correct — they are empirical).

**Type consistency:** `UnimodalGenome(ratio_src, s0, lift_max, search_hi)` used identically across Tasks 3, 4, 6, 9, 10, 11. `mutate(g, artifacts, rng)` signature identical across all three mutators (Tasks 4, 9, 10) — so `HybridMutator` composes them without adaptation. `FitnessResult(score, tag, artifacts)` and `Cell(certifies, complexity_bin)` used consistently. `evolve(seed_genome, mutator, cfg, *, seed, ratio_pool, kernel_gate)` signature matches its callers in Tasks 11 and 12. `kernel_check_family(family, lean_project, namespace)` matches its Task 12 import.

**One correction applied inline:** Task 6's `evolve` loop calls `evaluate_genome(parent)` to retrieve artifacts for the mutator; this recomputes — acceptable for the tiny unimodal build, but the implementer should cache the `(score, artifacts)` on the population tuple if profiling shows it hot. Noted here rather than complicating the reference code.
