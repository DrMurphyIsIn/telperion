"""Route ledger + executable status + review brief tests."""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import GridSpec, InequalityFamily  # noqa: E402
from telperion.ledger import RouteLedger, fingerprint_text  # noqa: E402
from telperion.status import review_brief  # noqa: E402

u = sp.Symbol("u", nonnegative=True)


def test_ledger_records_and_dedupes(tmp_path):
    p = tmp_path / "ROUTES.json"
    led = RouteLedger(p)
    fp = fingerprint_text("target-x")
    assert led.record("target-x", fp, "polya_lift", "NON_CONVERGENT", "tie at u=1")
    assert not led.record("target-x", fp, "polya_lift", "NON_CONVERGENT", "tie at u=1")
    assert led.record("target-x", fp, "sos", "REFUSED", "outside v1 class")
    led.save()
    led2 = RouteLedger(p)
    assert len(led2.entries) == 2
    md = led2.render_md()
    assert "polya_lift → NON_CONVERGENT" in md
    assert fp in md


def test_ledger_fingerprint_distinguishes_targets(tmp_path):
    led = RouteLedger(tmp_path / "R.json")
    led.record("a", fingerprint_text("a"), "hunt", "DISPROOF", "min -1")
    led.record("b", fingerprint_text("b"), "hunt", "DISPROOF", "min -1")
    assert len(led.entries) == 2


def test_review_brief_flags_missing_declarations():
    fam = InequalityFamily(
        name="B",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"B_a{pt['a']}",
        target=lambda pt: 1 + u,
    )
    text = review_brief(fam, "b.py:family", "c" * 64)
    assert "NO ties declared" in text
    assert "none declared" in text          # anchors
    assert "relax --axis a" in text
    assert "cccccccccccccccc" in text


def test_review_brief_acknowledges_declarations():
    fam = InequalityFamily(
        name="B2",
        symbols=(u,),
        grid=GridSpec([("a", [1])]),
        lean_name=lambda pt: "B2_a1",
        target=lambda pt: u / (1 + u),
        ties=lambda pt: [{u: sp.Integer(0)}],
        anchors=lambda pt: [({u: sp.Integer(1)}, sp.Rational(1, 2))],
    )
    text = review_brief(fam, "b.py:family", "d" * 64)
    assert "declared ties exist" in text
    assert "re-evaluate each anchor" in text
    assert "no multi-valued integer axes" in text
