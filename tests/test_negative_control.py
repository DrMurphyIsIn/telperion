"""Kernel-gated negative control — the AXLE ``disprove`` lesson.

Telperion's negative control is TWO layers:

* Layer 1 (untrusted): the ``*_certificate()`` self-check raises ``ValueError`` on
  a false instance.
* Layer 2 (TRUSTED): even if Layer 1 were bypassed, the emitted proof of a false
  statement FAILS to compile — the Lean kernel rejects it.

These tests pin BOTH layers on a genuinely FALSE monotone instance
``log(3) − 4·FSTAR ≤ 0`` (false: ``3^11 ≈ 177147 > (621/64)^4 ≈ 8863``, fold ≈ 20),
and confirm the ``assert_kernel_rejects`` primitive does NOT false-positive on a
TRUE instance ``log(7/4) ≤ 4·FSTAR``.

The Layer-2 verifies elaborate against the pre-built env at
``examples/log_combination/lean`` (~5-9s each); kept to two verifies to stay fast.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402
from lean_env import lean_env_ready  # noqa: E402

from telperion.negative_control import (  # noqa: E402
    FSTAR_PRELUDE,
    NegativeControlResult,
    assert_kernel_rejects,
    log_combination_negative_control,
)
from telperion.emit_log_combination import (  # noqa: E402
    LogCombinationCertificate,
    LogCombinationEmitter,
)
from lean_env import lean_env_ready  # noqa: E402

_ENV = Path(__file__).resolve().parents[1] / "examples" / "log_combination" / "lean"
# Layer-2 (kernel) controls need a usable Lean env — lake on PATH AND a built
# Mathlib cache; skip cleanly on the no-toolchain unit job. The Layer-1 offline
# self-check test below stays unguarded so it always runs.
requires_env = pytest.mark.skipif(
    not lean_env_ready(_ENV), reason="needs a built Lean env (lake + Mathlib)")


def test_false_monotone_layer1_refuses():
    """Layer 1: the untrusted self-check refuses the false monotone instance
    (offline, no kernel needed)."""
    from telperion.emit_log_combination import log_combination_certificate

    with pytest.raises(ValueError):
        log_combination_certificate(
            terms=[(1, "3"), (-4, "621/64")], q="0", route="monotone",
        )


@requires_env
def test_false_monotone_negative_control_both_layers():
    """The full two-layer control on the FALSE instance ``log(3) − 4·FSTAR ≤ 0``.

    Layer 1 fires (self-check refuses) AND Layer 2 fires (the forged proof's
    ``norm_num`` fact ``3^11 ≤ (621/64)^4`` is false, so it will not compile)."""
    if not lean_env_ready(_ENV):
        pytest.skip("log_combination Mathlib env not built (Layer-2 needs the Lean kernel)")
    res = log_combination_negative_control(
        terms=[(1, "3"), (-4, "621/64")], q="0", route="monotone",
        env_dir=str(_ENV),
    )
    assert isinstance(res, NegativeControlResult)
    assert res.selfcheck_refused is True          # Layer 1
    assert res.kernel_rejects is True             # Layer 2 (the load-bearing claim)
    assert res.okay is True, res.detail


@requires_env
def test_assert_kernel_rejects_no_false_positive_on_true_theorem():
    """``assert_kernel_rejects`` must NOT flag a VALID proof of a TRUE statement.

    Emit the (true) monotone proof of ``log(7/4) ≤ 4·FSTAR`` directly and confirm
    the kernel accepts it, so ``assert_kernel_rejects`` returns ``False`` — i.e.
    this is NOT a negative-control case."""
    if not lean_env_ready(_ENV):
        pytest.skip("log_combination Mathlib env not built (needs the Lean kernel)")
    B = sp.Rational(621, 64)
    N = sp.Integer(11)
    fold = sp.nsimplify(sp.Rational(7, 4) ** (1 * N) / B ** 4)   # ≈ 0.053 ≤ 1
    cert = LogCombinationCertificate(
        coeff=sp.Integer(1), rat=sp.Rational(7, 4), fstar_coeff=sp.Integer(4),
        fstar_base=B, fstar_den=N, q=sp.Integer(0), route="monotone",
        fold_value=fold,
    )
    name = "true_monotone_74"
    proof = LogCombinationEmitter()._emit_monotone(cert, name)
    content = f"import Mathlib\n{proof}\n"

    rejected = assert_kernel_rejects(
        content, name, env_dir=str(_ENV), prelude=FSTAR_PRELUDE,
    )
    # TRUE statement, valid proof -> kernel accepts -> NOT rejected.
    assert rejected is False
