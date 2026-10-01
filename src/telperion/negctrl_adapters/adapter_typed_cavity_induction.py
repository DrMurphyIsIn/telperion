"""Negative-control adapter for TypedCavityInductionEmitter (a type table as an inductive
invariant over all trees).

The instance is the maximum-degree-3 Balister-Bollobas-Gerke half-tree recursion
(J. Graph Theory 56 (2007) 270-286, recursion (2) at alpha = gamma = 1): half-tree messages
`y = 1/d`, values `c_T = R_{-1}(T) - beta n(T)`, `g(m, R) = R/(m + 1) - beta`, types by root
degree d = 1, 2, 3, the table `c_d` of their (4)-(5).  The emitted main theorem is

    theorem nm (b : PTree) (hb : b.AllDeg (fun k => k ≤ 2)) :
        Inv nm_B nm_ylo nm_yhi (b.typ nm_tp nm_h 1) (b.ell nm_g nm_h (-beta) 1) (b.msg nm_h 1)

FALSE forgery: `beta` lowered from the published `beta_3 = 7/27` to `7/27 - 1/1000`, with the
table `c_d` recomputed at the lowered beta by (4)-(5).  The claim is then FALSE, not merely
unproved: start from `T_0 = [3, 2, 1]` (BBG's notation; `c_{T_0} = c_3 = 4/3 - 5 beta`) and
join two copies of `T_j` at a new root, `T_{j+1}`.  By (2), `c_{T_{j+1}} - x* = 2 (c_{T_j} - x*)`
with `x* = beta - 2/9`, and `c_3 - x* = 14/9 - 6 beta > 0` exactly when `beta < 7/27`, so `c_T`
doubles its excess at every level and passes `c_3`.  Layer 1
(`typed_cavity_certificate`) refuses it (the degree-3 step with two degree-3 children,
`2 (c_3 + 1/9) - beta <= c_3`, is false by 3/500).  The adapter mints it with ``check=False``:
the certificate algebra (types, count vectors, point cells) is the honest one at the lowered
beta, and ONLY the inequalities are wrong.  The kernel is the arbiter: that cell's `norm_num`
cannot prove a false rational inequality, so the main theorem does not elaborate.

TRUE twin: the honest certificate at beta_3 = 7/27, byte-for-byte the dogfood instance.

conjecture1_proved = False.
"""
from __future__ import annotations

from telperion.emit_typed_cavity_induction import (
    BBG3_LOWERED_SPEC,
    BBG3_SPEC,
    TypedCavityCert,
    TypedCavityInductionEmitter,
    typed_cavity_certificate,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_true_cert() -> TypedCavityCert:
    """The honest maximum-degree-3 certificate at the published beta_3 = 7/27."""
    return typed_cavity_certificate(**BBG3_SPEC)


def make_false_cert() -> TypedCavityCert:
    """Hand-forged FALSE cert: beta_3 lowered by 1/1000 (table recomputed), built with every
    Layer-1 sign check skipped."""
    return typed_cavity_certificate(**BBG3_LOWERED_SPEC, check=False)


def _emit(cert: TypedCavityCert, name: str) -> str:
    return emit_via_single_instance_family(
        TypedCavityInductionEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="TypedCavityInductionEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged BBG maximum-degree-3 table at beta = 7/27 - 1/1000 (false: below the "
            "published beta_3 the degree-3 step 2 (c_3 + 1/9) - beta <= c_3 fails by 3/500 and "
            "c_T is unbounded on complete binary half-trees): the point cell's norm_num cannot "
            "prove the false rational inequality and the kernel rejects it; the true twin at "
            "beta_3 = 7/27 compiles"
        ),
        imports_line="import Mathlib",
    )
)
