"""Negative-control adapter for GridModulusNonvanishingEmitter (the Face-7 pilot box).

The load-bearing content of a grid-modulus certificate is the chain

    half_width^2 + half_height^2 <= delta^2        (the grid really is a delta-net)
    bound_M * delta < bound_L                      (the gap condition)

emitted as `norm_num` goals over ℚ and conjoined by the capstone `theorem <name>`.  Each of
`delta`, `bound_M`, `bound_L` is a SUPPLIED number that appears in the emitted statement, so
corrupting one makes the emitted theorem FALSE and the trusted kernel must reject it.  Layer 1
(`grid_modulus_nonvanishing_certificate`) already refuses such a certificate; this adapter mints
the frozen dataclass BY HAND to bypass that guard and let the kernel be the arbiter.

FALSE forgery: the honest Face-7 cell has half-extents `(1/16, 1/4)`, so the exact cell
half-diagonal squared is `1/256 + 1/16 = 17/256 = 0.06640625`.  The forgery understates the
covering radius as `delta = 1/5`, whose square is `1/25 = 0.04` -- far BELOW the half-diagonal.
The grid then does not cover the box at all (points near a cell corner sit `0.2577` away, not
`0.2`), and `norm_num` refutes `cover_radius_ok`, hence the capstone.  Note the forgery is
deliberately SUBTLE in the other direction: shrinking `delta` makes the gap condition
`3/10 * 1/5 = 3/50 < 1/10` *easier*, so a checker that only looked at the gap would wave it
through.  Exactly one goal fails, and it is the right one.

TRUE twin: the shipped Face-7 certificate, `delta = 13/50` -- `(13/50)^2 = 0.0676 >= 0.06640625`,
the gap `3/10 * 13/50 = 39/500 < 1/10` holds, and the column span and row tiling close.  A genuine
certificate; compiles clean.

The emitted Lean is pure ℚ arithmetic over plain Mathlib, so the control needs no prelude and no
island lemma.

SCOPE: the instance this control exercises is the `deriv riemannZeta` box `[1/4, 3/8] x [6, 10]`.
That is NOT the Speiser wall and NOT a step toward RH.  conjecture1_proved = False.
"""
from __future__ import annotations

from telperion.emit_grid_modulus_nonvanishing import (
    GridModulusNonvanishingCertificate,
    GridModulusNonvanishingEmitter,
)
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# The shipped Face-7 geometry, shared by both twins so that ONLY `delta` differs.
_COMMON = dict(
    re0="1/4", re1="3/8", im0="6", im1="10",
    grid_re="5/16",
    grid_im=("25/4", "27/4", "29/4", "31/4", "33/4", "35/4", "37/4", "39/4"),
    half_width="1/16", half_height="1/4",
    bound_M="3/10", bound_L="1/10",
    backend="riemannZeta", prec=30, sweep_nre=8, sweep_nim=40,
    observed_sup_second="0.2871904959", observed_min_first="0.2019822134",
)


def make_false_cert() -> GridModulusNonvanishingCertificate:
    """Hand-forged FALSE cert: delta = 1/5, so delta^2 = 1/25 = 0.04 UNDERSTATES the exact cell
    half-diagonal squared 17/256 = 0.06640625 -- the grid does not cover the box and the emitted
    covering-radius goal is false (Layer 1 would refuse this cert)."""
    return GridModulusNonvanishingCertificate(delta="1/5", **_COMMON)


def make_true_cert() -> GridModulusNonvanishingCertificate:
    """Paired TRUE twin: the shipped delta = 13/50 -- (13/50)^2 = 169/2500 = 0.0676 dominates
    17/256 = 0.06640625, and the gap 3/10 * 13/50 = 39/500 < 1/10 holds."""
    return GridModulusNonvanishingCertificate(delta="13/50", **_COMMON)


def _emit(cert: GridModulusNonvanishingCertificate, name: str) -> str:
    return emit_via_single_instance_family(
        GridModulusNonvanishingEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="GridModulusNonvanishingEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged grid-modulus certificate with delta = 1/5 on a cell of half-extents "
            "(1/16, 1/4): delta^2 = 1/25 understates the exact half-diagonal squared 17/256, "
            "so the grid does not net the box and the kernel rejects the norm_num "
            "covering-radius goal (the gap condition alone would have waved it through); "
            "true twin (same geometry, delta = 13/50) compiles"
        ),
        imports_line="import Mathlib",
    )
)
