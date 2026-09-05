"""emit_order_residue emits a well-typed re-export of residue_logDeriv at a fixed order."""
import pytest

from telperion.emit_order_residue import emit_order_residue_cert


def test_pole_specialization():
    cert = emit_order_residue_cert("residue_logDeriv_pole", -1)
    assert "theorem residue_logDeriv_pole {f : ℂ → ℂ} {z₀ : ℂ}" in cert
    assert "(hf : MeromorphicAt f z₀)" in cert
    assert "meromorphicOrderAt f z₀ = (((-1) : ℤ) : WithTop ℤ)" in cert
    assert "nhds ((((-1) : ℤ)) : ℂ)" in cert
    assert cert.rstrip().endswith(":=\n  residue_logDeriv hf hord".rstrip()) or \
        "residue_logDeriv hf hord" in cert
    assert "simple pole" in cert          # auto-doc label


def test_double_zero_specialization():
    cert = emit_order_residue_cert("residue_logDeriv_dz", 2)
    assert "= ((2 : ℤ) : WithTop ℤ)" in cert
    assert "nhds (((2 : ℤ)) : ℂ)" in cert
    assert "double zero" in cert


def test_custom_lemma_name_and_doc():
    cert = emit_order_residue_cert("r", 1, residue_lemma="ZFB.residue_logDeriv",
                                   doc="custom")
    assert "ZFB.residue_logDeriv hf hord" in cert
    assert cert.rstrip().endswith("ZFB.residue_logDeriv hf hord")
    assert "/-- custom -/" in cert


def test_rejects_non_int_order():
    with pytest.raises(TypeError, match="must be an int"):
        emit_order_residue_cert("bad", 1.5)
