"""Negative-control adapter for TwoFreqOfflineEmitter (MIRRORMERE ladder rung T2).

The emitted theorem REFUTES real-rootedness of a two-frequency section, and its whole
load-bearing content is the EXACT inequality `|c1|^2 != |c2|^2`: the proof rewrites with
the island iff, turns the resulting `||c1|| = ||c2||` into a normSq equality, evaluates
both sides to rational literals, and closes by `norm_num` deriving False from them.  If
the two moduli are EQUAL that last step has nothing to work with -- and, worse, the
theorem is then genuinely FALSE (equal modulus IS real-rootedness).  The kernel is the
arbiter.

FALSE forgery: the selfinversive_rigidity TRUE instance, `c1 = 3/5 + 4/5 i`, `c2 = 1`,
frequencies 1 and 2 -- equal moduli `|c1|^2 = |c2|^2 = 1`.  Layer 1
(`twofreq_offline_certificate`) refuses it outright; the adapter mints the frozen
dataclass BY HAND to bypass that guard, so the forged proof reaches `h2 : (1 : R) = 1`
and must derive False from it.  `norm_num` cannot, and the theorem is rejected.

TRUE twin: the Euler factor at p = 2, `1 - 2^(-s)` on `s = 1/2 + i x`, i.e.
`twoFreq 1 (-(1/sqrt 2)) 0 (-(log 2))`, whose moduli are 1 and 1/2 -- a genuine off-line
section, compiles clean and axiom-clean.

BRIDGE-HYPOTHESIS MODE.  The harness elaborates twins against plain `import Mathlib`, so
both carry `twoFreq` VERBATIM from TwoFreqRigidity.lean:40-42 in the prelude and take the
island iff `twoFreq_realRooted_iff` as an EXPLICIT hypothesis `hiff`.  This is the same
discipline as `adapter_bragg_floor`: the control tests the EMITTER's own arithmetic, and
nothing else.  The hypothesis-free island theorem (which discharges `hiff` from the real
lemma) is compiled by the `twofreq-offline-compiles` CI job inside the quasicrystal
island.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_twofreq_offline import (
    TWOFREQ_PRELUDE,
    TwoFreqOfflineCert,
    TwoFreqOfflineEmitter,
)
from telperion.negative_control_harness import NegativeControlAdapter, register


def make_false_cert() -> TwoFreqOfflineCert:
    """Hand-forged FALSE cert: EQUAL moduli (|c1|^2 = |c2|^2 = 1), which makes the sum
    genuinely real-rooted, so the emitted negation is false.  twofreq_offline_certificate
    refuses exactly this."""
    return TwoFreqOfflineCert(
        c1=("gauss", sp.Rational(3, 5), sp.Rational(4, 5)),
        c2=("gauss", sp.Integer(1), sp.Integer(0)),
        lam1=("rat", sp.Integer(1)),
        lam2=("rat", sp.Integer(2)),
        normsq1=sp.Integer(1), normsq2=sp.Integer(1),
        p=None, displacement=None, mode="offline",
    )


def make_true_cert() -> TwoFreqOfflineCert:
    """Paired TRUE twin: the p = 2 Euler-factor section, moduli 1 and 1/2."""
    return TwoFreqOfflineCert(
        c1=("gauss", sp.Integer(1), sp.Integer(0)),
        c2=("inv_sqrt", -1, sp.Integer(2)),
        lam1=("rat", sp.Integer(0)),
        lam2=("neglog", 2),
        normsq1=sp.Integer(1), normsq2=sp.Rational(1, 2),
        p=2, displacement=sp.Rational(1, 2), mode="offline",
    )


def _emit(cert: TwoFreqOfflineCert, name: str) -> str:
    # Private route: the emitter's per-instance renderer, in bridge-hypothesis mode.
    return TwoFreqOfflineEmitter().emit_theorem(cert, name, bridge=True)


register(
    NegativeControlAdapter(
        emitter_name="TwoFreqOfflineEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude=TWOFREQ_PRELUDE,
        allow_axioms=(),
        label=(
            "forged two-frequency section with EQUAL moduli (c1 = 3/5 + 4/5 i, c2 = 1, "
            "|c1|^2 = |c2|^2 = 1): equal modulus IS real-rootedness, so the emitted "
            "negation is false and the closing norm_num cannot derive False from 1 = 1; "
            "kernel rejects.  True twin (the p = 2 Euler factor, moduli 1 vs 1/2) compiles"
        ),
        imports_line="import Mathlib",
    )
)
