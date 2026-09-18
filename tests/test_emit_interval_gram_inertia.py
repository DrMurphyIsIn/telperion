"""interval_gram_inertia emitter: certificate, refusals, rendering, registry wiring, dogfood.

The emitted claim -- "every real symmetric matrix in this rational box has signature exactly
(p, q)" -- is decided by the Lean KERNEL (CI `lake build` of the gram_inertia island, plus the
two-sided negative control in test_certificate_sensitivity).  These are the pre-CI self-checks: the
exact congruence, the honest refusals (the anti-phantom face), byte-stable rendering, and full
registry/dispatch wiring.  conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    GridSpec,
    IntervalGramInertiaCert,
    IntervalGramInertiaEmitter,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    interval_gram_inertia_certificate,
    interval_gram_inertia_family,
    interval_gram_inertia_prelude_lean,
)
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_interval_gram_inertia import _congruence_diagonalize  # noqa: E402

_R = sp.Rational


def _box(mid, w):
    n = len(mid)
    lo = [[_R(mid[i][j]) - w for j in range(n)] for i in range(n)]
    hi = [[_R(mid[i][j]) + w for j in range(n)] for i in range(n)]
    return lo, hi


# --- registry wiring --------------------------------------------------------

def test_kind_is_interval_gram_inertia():
    fam = interval_gram_inertia_family(
        "T", GridSpec([("case", [0])]), lambda pt: "t", spec=lambda pt: None)
    assert fam.kind == "interval_gram_inertia"


def test_emitter_for_round_trips():
    assert emitter_for("interval_gram_inertia").kind == "interval_gram_inertia"


def test_kind_is_a_special_kind():
    from telperion.certify import _SPECIAL_DISPATCH, _SPECIAL_KINDS
    assert "interval_gram_inertia" in _SPECIAL_KINDS
    assert "interval_gram_inertia" in _SPECIAL_DISPATCH


def test_emitter_is_classified_and_has_adapter():
    from telperion.emitter_sensitivity import CERTIFICATE_SENSITIVE, REGISTRY
    from telperion.negative_control_harness import ADAPTERS
    assert REGISTRY["IntervalGramInertiaEmitter"].stance == CERTIFICATE_SENSITIVE
    assert "IntervalGramInertiaEmitter" in ADAPTERS


def test_emitter_declares_its_prelude_dependencies():
    em = IntervalGramInertiaEmitter()
    assert "RHInertia.compress_posDef_of_interval" in em.requires_prelude
    assert "RHInertia.inertia_eq_of_witnesses" in em.requires_prelude


# --- the exact congruence ---------------------------------------------------

def test_congruence_diagonalizes_exactly():
    M = sp.Matrix([[2, 1, 0], [1, 2, 0], [0, 0, -3]])
    B, D = _congruence_diagonalize(M)
    assert D == (B.T * M * B).applyfunc(sp.nsimplify)
    assert all(D[i, j] == 0 for i in range(3) for j in range(3) if i != j)


def test_congruence_handles_a_zero_diagonal():
    """`[[0, 1], [1, 0]]` is nonsingular and indefinite but has NO nonzero diagonal entry: the
    congruence must rotate (e_k -> e_k + e_j) rather than give up."""
    M = sp.Matrix([[0, 1], [1, 0]])
    B, D = _congruence_diagonalize(M)
    assert D == (B.T * M * B).applyfunc(sp.nsimplify)
    assert sorted([sp.sign(D[0, 0]), sp.sign(D[1, 1])]) == [-1, 1]


# --- the certificate --------------------------------------------------------

@pytest.mark.parametrize("mid,w,sig", [
    ([[1, 0], [0, -2]], _R(1, 10), (1, 1)),
    ([[2, 1, 0], [1, 2, 0], [0, 0, -3]], _R(1, 20), (2, 1)),
    ([[3, 1, 0, 0], [1, 3, 0, 0], [0, 0, -2, 1], [0, 0, 1, -2]], _R(1, 60), (2, 2)),
    ([[_R(1, 2), _R(3, 4)], [_R(3, 4), _R(-1, 3)]], _R(1, 50), (1, 1)),
])
def test_signature_and_margins(mid, w, sig):
    lo, hi = _box(mid, w)
    cert = interval_gram_inertia_certificate(lo, hi, sig)
    assert (cert.p, cert.q) == sig
    assert cert.p + cert.q == cert.n
    assert cert.margin_x > 0 and cert.margin_y > 0
    assert cert.w == w
    # the Cauchy-Schwarz constants are the column counts (unit absolute-sum columns)
    assert cert.s_x == cert.p and cert.s_y == cert.q


def test_compressed_forms_are_the_claimed_diagonals():
    lo, hi = _box([[2, 1, 0], [1, 2, 0], [0, 0, -3]], _R(1, 20))
    cert = interval_gram_inertia_certificate(lo, hi)
    M = sp.Matrix([[sp.Rational(v) for v in row] for row in cert.mid])
    X = sp.Matrix([[sp.Rational(v) for v in row] for row in cert.x_basis])
    Y = sp.Matrix([[sp.Rational(v) for v in row] for row in cert.y_basis])
    assert (X.T * M * X).applyfunc(sp.nsimplify) == sp.diag(*cert.cx)
    assert (Y.T * (-M) * Y).applyfunc(sp.nsimplify) == sp.diag(*cert.cy)
    for k in range(cert.p):
        assert sum(abs(sp.Rational(v)) for v in X[:, k]) == 1
    for k in range(cert.q):
        assert sum(abs(sp.Rational(v)) for v in Y[:, k]) == 1


def test_midpoint_is_the_exact_box_centre():
    lo, hi = _box([[1, 0], [0, -2]], _R(1, 10))
    cert = interval_gram_inertia_certificate(lo, hi)
    for i in range(2):
        for j in range(2):
            assert 2 * sp.Rational(cert.mid[i][j]) == (
                sp.Rational(cert.lo[i][j]) + sp.Rational(cert.hi[i][j]))


# --- the refusals (the anti-phantom face) -----------------------------------

def test_refuses_asymmetric_box():
    with pytest.raises(ValueError, match="SYMMETRIC"):
        interval_gram_inertia_certificate([[1, 0], [1, -1]], [[1, 0], [1, -1]])


def test_refuses_empty_box():
    with pytest.raises(ValueError, match="empty box"):
        interval_gram_inertia_certificate([[1, 0], [0, -1]], [[0, 0], [0, -1]])


def test_refuses_singular_midpoint():
    with pytest.raises(ValueError, match="SINGULAR"):
        interval_gram_inertia_certificate([[1, 0], [0, 0]], [[1, 0], [0, 0]])


def test_refuses_definite_box():
    with pytest.raises(ValueError, match="definite box"):
        lo, hi = _box([[1, 0], [0, 1]], _R(1, 100))
        interval_gram_inertia_certificate(lo, hi)


def test_refuses_box_wider_than_the_pivot_margin():
    """The headline refusal: a box straddling an eigenvalue sign.  `diag(1, -1)` widened by 3/2
    contains matrices with a NEGATIVE (0,0) entry, so the signature is not constant."""
    lo, hi = _box([[1, 0], [0, -1]], _R(3, 2))
    with pytest.raises(ValueError, match="WIDER than"):
        interval_gram_inertia_certificate(lo, hi)


def test_refuses_a_wrong_claimed_signature():
    lo, hi = _box([[1, 0], [0, -2]], _R(1, 10))
    with pytest.raises(ValueError, match="claimed signature"):
        interval_gram_inertia_certificate(lo, hi, (2, 0))


def test_refuses_non_square_bounds():
    with pytest.raises(ValueError, match="square"):
        interval_gram_inertia_certificate([[1, 0]], [[1, 0]])


# --- rendering --------------------------------------------------------------

def _one_instance_lean(mid, w, name="t"):
    lo, hi = _box(mid, w)
    cert = interval_gram_inertia_certificate(lo, hi)
    return cert, IntervalGramInertiaEmitter()._emit_inertia(cert, name)


def test_emitted_theorem_shape():
    cert, lean = _one_instance_lean([[2, 1, 0], [1, 2, 0], [0, 0, -3]], _R(1, 20), "demo")
    assert "theorem demo (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsHermitian)" in lean
    assert f"RHLinalg.posIndex hG = {cert.p} ∧ RHInertia.defect hG = {cert.q}" in lean
    assert "RHInertia.compress_posDef_of_interval" in lean
    assert "RHInertia.inertia_eq_of_witnesses hG" in lean
    assert "conjecture1_proved = False" in lean
    assert "sorry" not in lean


def test_emitted_theorem_states_both_box_bounds():
    cert, lean = _one_instance_lean([[1, 0], [0, -2]], _R(1, 10), "demo")
    assert "hlo : ∀ i j," in lean and "hhi : ∀ i j," in lean
    # every box corner appears as a Lean literal
    assert "(9 / 10)" in lean and "(11 / 10)" in lean


def test_rendering_is_byte_stable():
    _, a = _one_instance_lean([[1, 0], [0, -2]], _R(1, 10), "demo")
    _, b = _one_instance_lean([[1, 0], [0, -2]], _R(1, 10), "demo")
    assert a == b


def test_margin_route_is_the_certificate_arithmetic():
    """The private pure-real route the negative control forges: the compressed pivots must
    strictly dominate the interval slack."""
    cert, _ = _one_instance_lean([[1, 0], [0, -2]], _R(1, 10))
    lean = IntervalGramInertiaEmitter()._emit_compress_margin(cert, "core")
    assert "theorem core (v0 : ℝ) (hv :" in lean
    assert "nlinarith" in lean
    assert "conjecture1_proved = False" in lean


def test_prelude_declares_the_bridge_lemmas():
    pre = interval_gram_inertia_prelude_lean()
    for decl in ("posIndex_add_posIndex_neg_le", "card_le_posIndex_of_compress_posDef",
                 "compress_posDef_of_interval", "inertia_eq_of_witnesses", "def defect"):
        assert decl in pre, decl
    assert "import RHLinalg" in pre
    assert "sorry" not in pre
    assert "conjecture1_proved = False" in pre


# --- the pipeline (certify -> emit) -----------------------------------------

def test_pipeline_emits_one_theorem_per_box():
    specs = {
        0: ([[1, 0], [0, -2]], _R(1, 10)),
        1: ([[2, 1, 0], [1, 2, 0], [0, 0, -3]], _R(1, 20)),
    }
    fam = interval_gram_inertia_family(
        "T", GridSpec([("case", [0, 1])]),
        lambda pt: f"t{pt['case']}",
        spec=lambda pt: _box(*specs[pt["case"]]),
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("T",), imports=("RHInertia",), prelude="open Matrix"),
        [IntervalGramInertiaEmitter()],
        ValidationReport(checks=(("interval_gram_inertia", True),)),
    )
    text = next(iter(report.files.values()))
    assert "import RHInertia" in text
    assert "theorem t0" in text and "theorem t1" in text
    assert "sorry" not in text


def test_pipeline_refuses_a_straddling_box():
    fam = interval_gram_inertia_family(
        "T", GridSpec([("case", [0])]), lambda pt: "t",
        spec=lambda pt: _box([[1, 0], [0, -1]], _R(3, 2)),
    )
    with pytest.raises(Exception, match="WIDER than"):
        certify(fam)


# --- the dogfood example ----------------------------------------------------

def test_example_generate_check_is_clean():
    """The shipped gram_inertia example regenerates byte-for-byte (the drift gate CI runs)."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "examples" / "gram_inertia"))
    import importlib
    gen = importlib.import_module("generate")
    assert gen.main(check=True) == 0


def test_example_lean_is_axiom_guarded_and_sorry_free():
    lean_dir = Path(__file__).resolve().parents[1] / "examples" / "gram_inertia" / "lean"
    for f in ("RHInertia.lean", "GramInertia.lean"):
        text = (lean_dir / f).read_text(encoding="utf-8")
        assert "sorry" not in text, f
        assert "conjecture1_proved = False" in text, f
