"""reexport_cert factors the wrapper-emitter pattern and reproduces the two existing wrappers."""
import pytest

from telperion.emit_reexport import reexport_cert
from telperion.emit_order_residue import emit_order_residue_cert
from telperion.emit_borel_caratheodory import emit_borel_caratheodory_cert


def _body(cert: str) -> str:
    """Drop the leading docstring line(s) and normalize whitespace; compare the `theorem … := …`
    body structurally (the helper may line-break differently from the hand-written emitters)."""
    lines = cert.splitlines()
    i = 0
    while i < len(lines) and lines[i].lstrip().startswith("/--"):
        i += 1
    return " ".join(" ".join(lines[i:]).split())


def test_reproduces_order_residue():
    hand = emit_order_residue_cert("residue_logDeriv_pole", -1)
    viahelper = reexport_cert(
        "residue_logDeriv_pole", "residue_logDeriv",
        binders="{f : ℂ → ℂ} {z₀ : ℂ}",
        hyps=("(hf : MeromorphicAt f z₀) "
              "(hord : meromorphicOrderAt f z₀ = (((-1) : ℤ) : WithTop ℤ))"),
        conclusion=("Filter.Tendsto (fun z => (z - z₀) * logDeriv f z) (nhdsWithin z₀ {z₀}ᶜ)\n"
                    "      (nhds ((((-1) : ℤ)) : ℂ))"),
        args="hf hord",
    )
    assert _body(viahelper) == _body(hand)


def test_reproduces_borel_caratheodory():
    hand = emit_borel_caratheodory_cert("bc_g")
    viahelper = reexport_cert(
        "bc_g", "Complex.borelCaratheodory",
        binders="{f : ℂ → ℂ} {M R : ℝ} {z : ℂ}",
        hyps=("(hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))\n"
              "    (hf₁ : Set.MapsTo f (Metric.ball 0 R) {z | z.re ≤ M})\n"
              "    (hR : 0 < R) (hz : z ∈ Metric.ball 0 R)"),
        conclusion="‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)",
        args="hM hf hf₁ hR hz",
    )
    assert _body(viahelper) == _body(hand)


def test_no_args_reexport():
    cert = reexport_cert("myThm", "Mathlib.someLemma", conclusion="P", args="")
    assert cert.rstrip().endswith(":=\n  Mathlib.someLemma")
    assert "theorem myThm :" in cert


def test_rejects_missing_pieces():
    with pytest.raises(ValueError, match="required"):
        reexport_cert("", "L", conclusion="P")
    with pytest.raises(ValueError, match="required"):
        reexport_cert("t", "L", conclusion="")
