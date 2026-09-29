"""monotone_tail PIECEWISE-LINEAR NODE-CONDITION face.

Layer 1: exact self-check refusals (node condition, node ordering, U_0 = 0,
U_i <= 0, log-tangent slope).  A brute-force sanity check of the certified
claim on a grid, for the concrete U = min(0, segment lines) and the log L.
Layer 2 (Lean-gated): the registered MonotoneRatioTailEmitter adapter forges
M = 0 (false at m = 1, y = 1) and the kernel rejects it, while the true twin
M = 1 compiles.

conjecture1_proved = False.
"""
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

import telperion.negctrl_adapters  # noqa: E402,F401  (registers adapters)
from lean_env import lean_env_ready  # noqa: E402
from telperion import GridSpec, LeanProfile, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_monotone_tail import (  # noqa: E402
    MonotoneRatioTailEmitter,
    PLNodeTailPayload,
    monotone_tail_family,
    pl_node_tail_certificate,
)
from telperion.emitter_sensitivity import NEG_CONTROL_ADAPTER, REGISTRY  # noqa: E402
from telperion.lean_lint import check_lean_text  # noqa: E402
from telperion.negative_control_harness import (  # noqa: E402
    generic_negative_control,
    registered_adapters,
)

R = sp.Rational
_ENV = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"
NODES = [(R(1, 4), 0), (R(1, 2), R(-1, 20)), (R(3, 4), R(-1, 8)), (1, R(-1, 5))]


def _umin(pl: PLNodeTailPayload, y: float) -> float:
    return min([0.0] + [float(pl.ubar(i, 0)) + float(pl.slopes[i]) * y
                        for i in range(len(pl.slopes))])


def test_certificate_and_slopes():
    pl = pl_node_tail_certificate(M=1, nodes=NODES, y_dag=R(1, 2), s=R(2, 3), L="log_tangent")
    assert pl.slopes == (R(-1, 5), R(-3, 10), R(-3, 10))
    assert pl.ubar(2, 1) == R(-1, 5)


def test_certified_claim_holds_on_a_grid():
    """Independent float check of the concrete corollary (min-PL U, log L)."""
    pl = pl_node_tail_certificate(M=1, nodes=NODES, y_dag=R(1, 2), s=R(2, 3), L="log_tangent")
    for m in range(pl.M + 1, 60):
        for k in range(1, 401):
            y = k / 400
            assert m * _umin(pl, y) + math.log(1 + y) - math.log(1.5) <= 1e-12


def test_forged_threshold_is_genuinely_false():
    pl = pl_node_tail_certificate(M=1, nodes=NODES, y_dag=R(1, 2), s=R(2, 3), L="log_tangent")
    # m = 1 (M = 0) at y = 1: -1/5 + log(4/3) > 0
    assert 1 * _umin(pl, 1.0) + math.log(2) - math.log(1.5) > 0.08


def test_refuses_node_condition():
    with pytest.raises(ValueError, match="node condition fails"):
        pl_node_tail_certificate(M=0, nodes=NODES, y_dag=R(1, 2), s=R(2, 3))
    # the y = 1 node binds at M + 1 = 15 in the second dogfood instance
    nodes = [(R(1, 3), 0), (R(2, 3), R(-1, 40)), (1, R(-1, 30))]
    pl_node_tail_certificate(M=14, nodes=nodes, y_dag=R(1, 3), s=R(3, 4))
    with pytest.raises(ValueError, match="node condition fails"):
        pl_node_tail_certificate(M=13, nodes=nodes, y_dag=R(1, 3), s=R(3, 4))


def test_region_zero_needs_y0_le_ydag():
    # y0 = 1/2 > y_dag = 1/4 with s > 0: U = 0 on (1/4, 1/2] cannot absorb s*(y - y_dag)
    with pytest.raises(ValueError, match="node condition fails at y = 1/2"):
        pl_node_tail_certificate(M=100, nodes=[(R(1, 2), 0), (1, -1)], y_dag=R(1, 4), s=1)


@pytest.mark.parametrize("nodes,match", [
    ([(0, 0), (1, -1)], "0 < y_0"),
    ([(R(1, 2), 0), (R(3, 4), -1)], "y_K = 1"),
    ([(R(1, 2), 0), (R(1, 2), -1), (1, -1)], "0 < y_0"),
    ([(R(1, 2), R(-1, 10)), (1, -1)], "U_0 must be 0"),
    ([(R(1, 2), 0), (1, R(1, 10))], "<= 0"),
    ([(1, 0)], "two nodes"),
])
def test_refuses_malformed_nodes(nodes, match):
    with pytest.raises(ValueError, match=match):
        pl_node_tail_certificate(M=5, nodes=nodes, y_dag=R(1, 2), s=0)


def test_refuses_log_slope_below_tangent():
    with pytest.raises(ValueError, match="s >= 1/"):
        pl_node_tail_certificate(M=5, nodes=NODES, y_dag=R(1, 2), s=R(1, 2), L="log_tangent")


def test_ratio_face_unchanged_and_family_emits():
    spec = {"M": 1, "nodes": NODES, "y_dag": R(1, 2), "s": R(2, 3), "L": "log_tangent"}
    fam = monotone_tail_family("PLT", (), GridSpec([("k", [0])]), lambda pt: "plt",
                               spec=lambda pt: spec)
    res = emit(certify(fam), LeanProfile(namespace=("PLT",)), [MonotoneRatioTailEmitter()],
               ValidationReport(checks=(("x", True),)))
    text = res.files["PLT.lean"]
    for thm in ("plt ", "plt_L_nonpos", "plt_L_tangent", "plt_concrete"):
        assert f"theorem {thm}" in text
    assert res.n_theorems == 4
    assert "sorry" not in text and "native_decide" not in text
    check_lean_text(text)


def test_dogfood_generate_check():
    import importlib.util
    p = Path(__file__).resolve().parents[1] / "examples" / "pl_node_tail" / "generate.py"
    spec = importlib.util.spec_from_file_location("plt_gen", p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    assert mod.main(check=True) == 0


# --- negative control -------------------------------------------------------

def _adapter():
    ad = registered_adapters().get("MonotoneRatioTailEmitter")
    assert ad is not None
    return ad


def test_registry_declares_wired_adapter():
    assert REGISTRY["MonotoneRatioTailEmitter"].neg_control.kind == NEG_CONTROL_ADAPTER


def test_adapter_twins_match_layer_one():
    f, t = _adapter().make_false_cert(), _adapter().make_true_cert()
    kw = dict(nodes=t.nodes, y_dag=t.y_dag, s=t.s, L=t.L)
    assert pl_node_tail_certificate(M=t.M, **kw) == t
    with pytest.raises(ValueError, match="node condition fails"):
        pl_node_tail_certificate(M=f.M, **kw)


@pytest.mark.skipif(not lean_env_ready(_ENV), reason="Lean env not built")
def test_kernel_negative_control():
    res = generic_negative_control(_adapter(), env_dir=str(_ENV))
    assert res.kernel_rejects is True, res.detail
    assert res.true_compiles is True, res.detail
    assert res.okay
