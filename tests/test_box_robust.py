"""Box-robust kernel-emitter tests (#2).

`box_min_lower_bound` computes a rigorous rational LOWER bound of a separable
-quadratic target over a rational box, monomial-wise (sign-aware endpoint /
corner-product extremes).  `certify_box_robust_point` refuses (ValueError) a box
whose margin is < 0.  The emitter produces one forall-box `0 <= target` theorem
per instance, discharged by nlinarith.
"""
import sys
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import certify  # noqa: E402
from telperion.emit_box_robust import (  # noqa: E402
    BoxRobustEmitter,
    box_min_lower_bound,
    box_robust_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


def _grid_one() -> GridSpec:
    return GridSpec([("i", [0])])


def _profile() -> LeanProfile:
    return LeanProfile(namespace=("BoxDemo",))


def test_box_min_positive_turan_shape():
    c0, c1, c2 = sp.symbols("c0 c1 c2")
    target = c1**2 - 4 * c0 * c2
    box = [(F(1, 2), F(1, 2)), (F(1), F(1)), (F(0), F(0))]  # c1^2 - 0 = 1 > 0
    m = box_min_lower_bound(box, target, (c0, c1, c2))
    assert m > 0


def test_box_min_refuses_negative():
    c0, c1, c2 = sp.symbols("c0 c1 c2")
    target = c1**2 - 4 * c0 * c2
    box = [(F(1), F(1)), (F(1), F(1)), (F(1), F(1))]  # 1 - 4 = -3 < 0
    m = box_min_lower_bound(box, target, (c0, c1, c2))
    assert m < 0


def test_emit_produces_forall_theorem():
    c0, c1, c2 = sp.symbols("c0 c1 c2")
    fam = box_robust_family(
        "BoxDemo", (), _grid_one(),
        lambda pt: "box_demo_0",
        lambda pt: ([(F(1, 2), F(1, 2)), (F(1), F(1)), (F(0), F(0))],
                    c1**2 - 4 * c0 * c2, (c0, c1, c2)),
    )
    cf = certify(fam)
    text, n = BoxRobustEmitter().emit_body(cf, _profile())
    assert n == 1 and "≤" in text and "∀" in text
