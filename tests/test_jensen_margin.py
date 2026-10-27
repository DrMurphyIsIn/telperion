# telperion/tests/test_jensen_margin.py
from fractions import Fraction as F
import pytest


def test_engine_disc2_margin_positive_box():
    from telperion.jensen_margin import disc2_margin
    # c0=1, c1=3, c2=1  ->  D = 9 - 4 = 5
    assert disc2_margin([(F(1), F(1)), (F(3), F(3)), (F(1), F(1))]) == F(5)


def test_engine_disc2_margin_straddling_c1_uses_zero():
    from telperion.jensen_margin import disc2_margin
    assert disc2_margin([(F(1), F(1)), (F(-1), F(1)), (F(1), F(1))]) == F(-4)


def test_engine_disc2_margin_rejects_wrong_length():
    from telperion.jensen_margin import disc2_margin
    with pytest.raises(ValueError):
        disc2_margin([(F(1), F(1))])


def test_emitter_does_not_import_rh_jensen():
    import ast
    from pathlib import Path
    p = Path(__file__).resolve().parents[1] / "src/telperion/emit_jensen_polynomial_hyperbolicity.py"
    assert "rh_jensen" not in {(n.module or "") for n in ast.walk(ast.parse(p.read_text()))
                                if isinstance(n, ast.ImportFrom)}
