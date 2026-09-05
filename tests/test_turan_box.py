"""Turan-box emitter tests (#5): log-concavity a1^2 >= a0*a2 over a rational box.

`turan_box_family` is a thin convenience layer over `box_robust` (#2): it
translates three interval-enclosed sequence values (a0_box, a1_box, a2_box) into
the box_robust target `a1**2 - a0*a2` and delegates certification/emission
entirely to the #2 machinery.

A log-concave triple (a1^2 - a0*a2 > 0 over the box) emits a theorem containing
`a1^2 - a0*a2` (or the Lean-rendered equivalent) and `0 <=`.  A NON-log-concave
triple (margin < 0) is REFUSED via certify() raising CertificationError.
"""
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import certify  # noqa: E402
from telperion.certify import CertificationError  # noqa: E402
from telperion.emit_box_robust import BoxRobustEmitter  # noqa: E402
from telperion.emit_turan_box import turan_box_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


def _grid_one() -> GridSpec:
    return GridSpec([("i", [0])])


def _profile() -> LeanProfile:
    return LeanProfile(namespace=("TuranDemo",))


# ---------------------------------------------------------------------------
# Log-concave triple: a0=1, a1=2, a2=1  ->  a1^2 - a0*a2 = 4 - 1 = 3 > 0
# ---------------------------------------------------------------------------

def test_log_concave_emits_theorem():
    """A log-concave triple emits a theorem with `0 <=` and the target expression."""
    fam = turan_box_family(
        "TuranDemo", (), _grid_one(),
        lambda pt: "turan_logconcave_0",
        # a0=1, a1=2, a2=1 (exact point boxes): a1^2 - a0*a2 = 4-1 = 3
        lambda pt: ((F(1), F(1)), (F(2), F(2)), (F(1), F(1))),
    )
    cf = certify(fam)
    text, n = BoxRobustEmitter().emit_body(cf, _profile())
    assert n == 1, f"expected 1 theorem, got {n}"
    # box_robust renders the conclusion as `(0:ℝ) ≤ <target>`
    assert "(0:ℝ) ≤" in text, (
        f"expected nonneg conclusion '(0:ℝ) <=...' in emitted text, got:\n{text}"
    )
    # The target rendered as Lean should contain the key subexpression tokens.
    # box_robust renders a1^2 - a0*a2; check the target expression appears.
    assert "a1" in text, "expected variable a1 in emitted theorem"


def test_log_concave_count_one():
    """Exactly one theorem is emitted for a single-point grid."""
    fam = turan_box_family(
        "TuranDemo", (), _grid_one(),
        lambda pt: "turan_logconcave_ct",
        lambda pt: ((F(1), F(1)), (F(2), F(2)), (F(1), F(1))),
    )
    cf = certify(fam)
    _, n = BoxRobustEmitter().emit_body(cf, _profile())
    assert n == 1


# ---------------------------------------------------------------------------
# NON-log-concave triple: a0=1, a1=1, a2=2  ->  a1^2 - a0*a2 = 1-2 = -1 < 0
# ---------------------------------------------------------------------------

def test_non_log_concave_refuses():
    """A non-log-concave triple must raise CertificationError (margin < 0)."""
    fam = turan_box_family(
        "TuranDemo", (), _grid_one(),
        lambda pt: "turan_refuse",
        # a0=1, a1=1, a2=2: 1 - 2 = -1 < 0
        lambda pt: ((F(1), F(1)), (F(1), F(1)), (F(2), F(2))),
    )
    with pytest.raises(CertificationError):
        certify(fam)
