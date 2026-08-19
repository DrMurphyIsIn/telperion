from __future__ import annotations

import contextlib
import io
import re
from dataclasses import dataclass

from .. import CertificationError, certify
from ..hunt import hunt_minimum

DISPROVEN = -10_000.0


@dataclass(frozen=True)
class FitnessResult:
    score: float
    tag: str
    artifacts: dict


def hunt_is_true(family, symbols, seed: int = 1) -> tuple[bool, dict]:
    for pt in family.grid.points():
        r = hunt_minimum(family.target(pt), list(symbols), iters=120, restarts=4, seed=seed)
        if r.is_disproof:
            return False, {
                "witness": {str(k): v for k, v in r.argmin.items()},
                "witness_value": r.minimum,
                "cell": dict(pt),
            }
    return True, {}


def certify_score(family) -> tuple[bool, int, dict]:
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        try:
            certify(family)
            return True, 0, {}
        except CertificationError as e:
            msg = str(e)
            # Message format: "N instance(s) failed certification: ..."
            m = re.search(r"(\d+)\s+instance", msg)
            n = int(m.group(1)) if m else 1
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
