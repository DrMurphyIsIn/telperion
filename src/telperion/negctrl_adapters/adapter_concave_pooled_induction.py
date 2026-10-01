"""Negative-control adapter for ConcavePooledInductionEmitter (concave pooled-mean induction).

The instance is the dogfood's bounded-degree case `path_density`: the matching message
`y = 1 / (1 + R)`, `y_leaf = 1`, profit `g = -1/(1+R)`, `l_leaf = -1`, child count at most 1
(paths), witness `U` = interpolant of (0, 0), (1/2, -1/8), (1, -3/10).  The emitted main
theorem is

    theorem nm (b : PTree) (hb : b.AllDeg (fun m => m ≤ 1)) :
        0 ≤ msg ∧ msg ≤ 1 ∧ ell + alpha * size ≤ U msg

and on a path of `n` vertices `-ell = sum_u y_u` has density `-> 1/phi = 0.6180...`.

FALSE forgery: `alpha = 13/20 = 0.65 > 1/phi`.  The statement is then FALSE, not merely
unproved: on a long path `ell + (13/20) n` grows like `(0.65 - 0.618) n`, while `U <= 0`.
Layer 1 (`concave_pooled_certificate`) refuses it (a cell obligation is false at `m = 1`,
`R = 1/2`); the adapter mints it with ``check=False``, which computes the same certificate
algebra (cells, Bernstein coefficients) with every sign check skipped, so the forged file is
algebraically self-consistent and ONLY the inequalities are wrong.  The kernel is the
arbiter: some cell's `linarith` from the Bernstein product facts cannot reach a polynomial
with a negative coefficient, and the main theorem does not elaborate.

TRUE twin: the honest certificate at `alpha = 3/5`, byte-for-byte the dogfood block.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_concave_pooled_induction import (
    PATH_DENSITY_SPEC,
    ConcavePooledCert,
    ConcavePooledInductionEmitter,
    concave_pooled_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

#: the forged deficit, above the sharp path constant 1/phi = 0.6180...
FORGED_ALPHA = sp.Rational(13, 20)


def make_true_cert() -> ConcavePooledCert:
    """The honest bounded-degree dogfood certificate (alpha = 3/5)."""
    return concave_pooled_certificate(**PATH_DENSITY_SPEC)


def make_false_cert() -> ConcavePooledCert:
    """Hand-forged FALSE cert: the same witness and recursion at alpha = 13/20, built with
    every Layer-1 sign check skipped."""
    return concave_pooled_certificate(**dict(PATH_DENSITY_SPEC, alpha=FORGED_ALPHA),
                                      check=False)


def _emit(cert: ConcavePooledCert, name: str) -> str:
    return emit_via_single_instance_family(
        ConcavePooledInductionEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="ConcavePooledInductionEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged path-density bound sum_u y_u >= (13/20) n for the matching message on "
            "paths (false: the path density tends to 1/phi = 0.618...): a cell's Bernstein "
            "linarith cannot reach a polynomial with a negative coefficient and the kernel "
            "rejects it; the true twin at alpha = 3/5 compiles"
        ),
        imports_line="import Mathlib",
    )
)


# ---------------------------------------------------------------------------
# Extension controls (2026-10-01).  NOT registered (the registry holds one adapter per
# emitter, the path-density control above); the kernel runs are in
# tests/test_negctrl_concave_pooled_ext.py against examples/concave_pooled_induction/lean.
# ---------------------------------------------------------------------------

from dataclasses import replace as _replace  # noqa: E402
from fractions import Fraction as _Fraction  # noqa: E402

from telperion import emit_concave_pooled_induction as _cpi  # noqa: E402

#: the leaf-exempt flat witness 1/12 lowered by 1/1000
EXEMPT_FORGED_DROP = sp.Rational(1, 1000)


def make_exempt_true_cert() -> ConcavePooledCert:
    """The honest flat leaf-exempt certificate: `ell + |T|/4 <= 1/12` on every non-leaf tree
    of child count <= 2 (tight at the root with two leaf children)."""
    return concave_pooled_certificate(**_cpi.LEAF_EXEMPT_FLAT_SPEC)


def make_exempt_false_cert() -> ConcavePooledCert:
    """FALSE by 1/1000: the flat witness lowered to `1/12 - 1/1000`.  The root with two leaf
    children has `ell + 3/4 = -2/3 + 3/4 = 1/12 > 1/12 - 1/1000`, so the claim fails on that
    tree; built with every Layer-1 check skipped (same cell layout as the true twin)."""
    nodes = [(x, v - EXEMPT_FORGED_DROP) for x, v in _cpi.LEAF_EXEMPT_FLAT_SPEC["nodes"]]
    return concave_pooled_certificate(**dict(_cpi.LEAF_EXEMPT_FLAT_SPEC, nodes=nodes),
                                      check=False)


EXEMPT_ADAPTER = NegativeControlAdapter(
    emitter_name="ConcavePooledInductionEmitter",
    make_false_cert=make_exempt_false_cert,
    make_true_cert=make_exempt_true_cert,
    emit_call=_emit,
    prelude="",
    allow_axioms=(),
    label=(
        "leaf-exempt: forged sum_u (1 - y_u) >= |T|/4 - (1/12 - 1/1000) on non-leaf trees of "
        "child count <= 2 (false at the root with two leaf children by exactly 1/1000): the "
        "all-leaves step's norm_num fails and the kernel rejects it; the true twin compiles"
    ),
    imports_line="import Mathlib",
)

#: the log enclosure `log u <= H` forged to `H - 1/1000` (then below log u)
LOG_FORGED_DROP = _Fraction(1, 1000)


def make_log_true_cert() -> ConcavePooledCert:
    """The honest log-profit certificate (`g = -1/(1+R) + (1/5) log(1 + R/2)`, alpha = 1/2)."""
    return concave_pooled_certificate(**_cpi.LOG_PROFIT_SPEC)


def make_log_false_cert() -> ConcavePooledCert:
    """FALSE by 1/1000: every log enclosure `log u <= H` replaced by `log u <= H - 1/1000`
    (false: H exceeds log u by less than 1e-6), the cells REBUILT on the true twin's layout
    with the forged constants (so the algebra is self-consistent and only the log facts are
    wrong).  The Taylor-box `linarith` of the enclosure lemma fails and the kernel rejects."""
    true = make_log_true_cert()
    orig = _cpi._log_upper

    def forged(u):
        bd = orig(u)
        return _replace(bd, H=bd.H - LOG_FORGED_DROP)

    _cpi._log_upper = forged
    try:
        ctx = _cpi._ctx_of(true)
        cells = tuple(_cpi._build_cell(ctx, c.m, c.s, c.t, c.j, c.mode, check=False, p=c.p,
                                       k=c.k) for c in true.cells)
    finally:
        _cpi._log_upper = orig
    return _replace(true, cells=cells, checked=False)


LOG_ADAPTER = NegativeControlAdapter(
    emitter_name="ConcavePooledInductionEmitter",
    make_false_cert=make_log_false_cert,
    make_true_cert=make_log_true_cert,
    emit_call=_emit,
    prelude="",
    allow_axioms=(),
    label=(
        "log term in g: the tangent constants log u <= H forged to H - 1/1000 (false), cells "
        "rebuilt consistently: the enclosure lemma's Taylor-box linarith fails and the kernel "
        "rejects it; the true twin compiles"
    ),
    imports_line="import Mathlib",
)
