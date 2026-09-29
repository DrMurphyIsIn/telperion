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
