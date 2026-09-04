"""Kernel-gated NEGATIVE CONTROL — the ``disprove`` lesson.

Telperion emitters refuse a FALSE instance via a ``ValueError`` in their
``*_certificate()`` generation-time self-check.  That refusal is **Layer 1**: an
UNTRUSTED Python guard (sympy arithmetic in *our* code).  A skeptic can rightly
ask "what if the self-check has a bug, or is bypassed?"  The honest answer is the
**Layer 2** control, which is TRUSTED: even if Layer 1 were bypassed and the
emitter forged a proof of a false statement, that emitted Lean **fails to
compile** — the Lean KERNEL, not our Python, is the arbiter.

This module demonstrates Layer 2 directly.  It CONSTRUCTS a certificate dataclass
by hand (bypassing the self-check), emits the theorem Lean via the same emitter
methods used for true instances, and confirms via :func:`telperion.verify.verify_lean`
that the kernel REJECTS it (a compile error, or a dirty / ``sorry`` axiom set).

The control "holds" (``okay``) when EITHER layer catches the false instance:

    okay = selfcheck_refused (Layer 1)  OR  kernel_rejects (Layer 2).

For a genuinely false instance both fire; the interesting, load-bearing claim is
Layer 2 — the generator *cannot forge a compiling proof of a false claim*.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

try:  # normal package import
    from . import emit_log_combination
    from .emit_log_combination import (
        LogCombinationCertificate,
        LogCombinationEmitter,
        log_combination_certificate,
    )
    from .verify import verify_lean
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion import emit_log_combination
    from telperion.emit_log_combination import (
        LogCombinationCertificate,
        LogCombinationEmitter,
        log_combination_certificate,
    )
    from telperion.verify import verify_lean


# The FSTAR prelude the emitted routes' `rw [FSTAR]` step needs (the BG default).
FSTAR_PRELUDE = "noncomputable def FSTAR : ℝ := Real.log (621 / 64) / 11"


@dataclass
class NegativeControlResult:
    """Two-layer negative-control outcome for one (false) instance.

    * ``selfcheck_refused`` — Layer 1: the untrusted ``*_certificate()`` self-check
      raised ``ValueError`` (refused to build the cert).
    * ``kernel_rejects``    — Layer 2: the hand-constructed cert was emitted and the
      Lean KERNEL rejected the proof (``True``); ``False`` if it verified clean;
      ``None`` if Layer 2 was not exercised.
    * ``okay``              — the control holds: Layer 1 refused OR Layer 2 rejected.
    * ``detail``            — human-readable summary.
    """

    selfcheck_refused: bool          # Layer 1 (untrusted)
    kernel_rejects: object           # Layer 2 (trusted): bool | None
    okay: bool                       # control holds = refused OR kernel_rejects
    detail: str = ""


def _splice_prelude(content: str, prelude: str) -> str:
    """Insert ``prelude`` after any leading ``import`` lines of ``content``.

    Lean requires ``import`` commands at the very top of the file, so a prelude
    (which may itself reference Mathlib, e.g. ``Real.log``) must be placed AFTER
    them.  If ``content`` has no leading imports, the prelude goes on top.
    """
    if not prelude:
        return content
    lines = content.splitlines()
    i = 0
    while i < len(lines) and (
        lines[i].lstrip().startswith("import") or not lines[i].strip()
    ):
        i += 1
    head = lines[:i]
    tail = lines[i:]
    return "\n".join([*head, prelude, *tail]) + ("\n" if content.endswith("\n") else "")


def assert_kernel_rejects(
    content, name, *, env_dir, prelude="", allow_axioms=()
) -> bool:
    """Confirm the Lean KERNEL rejects a proof attempt of theorem ``name``.

    ``content`` is Lean source claiming ``theorem name : … := by <proof>`` — a
    proof ATTEMPT, not a ``sorry`` stub.  This is the GENERAL Layer-2 primitive: it
    elaborates ``content`` (with ``prelude`` prepended) against the built env at
    ``env_dir`` and returns ``True`` iff the kernel does NOT accept it clean —
    i.e. there is a compile error, OR the checked declaration carries a dirty /
    ``sorry`` axiom set.

    Returns ``True``  when the kernel correctly REJECTS (the point for a FALSE claim).
    Returns ``False`` when the proof verifies clean (a VALID proof of a TRUE
    statement lands here — so this primitive never false-positives on truth).

    ``prelude`` (e.g. the ``FSTAR`` def) is spliced in AFTER any leading ``import``
    lines — Lean requires ``import`` at the very top of the file, so the prelude
    (which itself may reference Mathlib) must follow the imports, not precede them.
    """
    body = _splice_prelude(content, prelude)
    r = verify_lean(body, env_dir=env_dir, decls=[name], allow_axioms=allow_axioms)
    verified_clean = bool(r.okay and r.axioms_clean)
    return not verified_clean


def log_combination_negative_control(
    *, terms, q, route, env_dir,
    fstar_base="621/64", fstar_den=11,
) -> NegativeControlResult:
    """Two-layer negative control for a log-combination instance ``Σ c·log(r) ≤ q``.

    Layer 1: call :func:`emit_log_combination.log_combination_certificate`; if it
    raises ``ValueError`` the self-check refused (``selfcheck_refused=True``).

    Layer 2 (run regardless of Layer 1): CONSTRUCT the
    :class:`LogCombinationCertificate` by hand — computing ``fold_value`` (and
    ``tangent_bound`` for the tangent route) in sympy WITHOUT the ``≤`` guards —
    then emit the theorem Lean via ``LogCombinationEmitter()._emit_<route>`` and
    feed it to :func:`assert_kernel_rejects`.  For a FALSE instance the emitted
    ``norm_num`` fact (e.g. ``3^11 ≤ (621/64)^4``) is false, so the proof does not
    compile and Layer 2 fires.

    ``okay = selfcheck_refused or kernel_rejects``.
    """
    # ---- Layer 1: untrusted self-check ------------------------------------
    selfcheck_refused = False
    l1_detail = "self-check ACCEPTED (no ValueError)"
    try:
        log_combination_certificate(
            terms=terms, q=q, route=route,
            fstar_base=fstar_base, fstar_den=fstar_den,
        )
    except ValueError as e:
        selfcheck_refused = True
        l1_detail = f"self-check REFUSED: {str(e)[:80]}"

    # ---- Layer 2: forge the cert by hand, emit, confirm kernel rejects ----
    (coeff, rat), (fneg, fbase) = terms
    coeff = sp.Integer(coeff)
    rat = sp.Rational(rat)
    fneg = sp.Integer(fneg)
    q = sp.Rational(q)
    B = sp.Rational(fstar_base)
    N = sp.Integer(fstar_den)
    k = -fneg  # multiplier of FSTAR in the − k·FSTAR encoding

    name = "negctrl_forged"
    emitter = LogCombinationEmitter()

    if route == "monotone":
        # fold F = r^{cN} / B^{k}; emitted norm_num fact is r^{cN} ≤ B^{k}.
        fold = sp.nsimplify(rat ** (coeff * N) / B ** k)
        cert = LogCombinationCertificate(
            coeff=coeff, rat=rat, fstar_coeff=k, fstar_base=B, fstar_den=N,
            q=q, route="monotone", fold_value=fold,
        )
        forged = emitter._emit_monotone(cert, name)
    elif route == "tangent":
        # fold F = r^{cN} · B^{−k}; emitted norm_num fact is F − 1 ≤ N·q.
        fold = sp.nsimplify(rat ** (coeff * N) * B ** (-k))
        tb = sp.nsimplify(fold - 1)
        cert = LogCombinationCertificate(
            coeff=coeff, rat=rat, fstar_coeff=k, fstar_base=B, fstar_den=N,
            q=q, route="tangent", fold_value=fold, tangent_bound=tb,
        )
        forged = emitter._emit_tangent(cert, name)
    elif route == "tight":
        fold = sp.nsimplify(rat ** (coeff * N) * B ** (-k))
        cert = LogCombinationCertificate(
            coeff=coeff, rat=rat, fstar_coeff=k, fstar_base=B, fstar_den=N,
            q=q, route="tight", fold_value=fold, tangent_bound=None,
        )
        forged = emitter._emit_tight(cert, name)
    else:
        raise ValueError(f"unknown route {route!r} (expected monotone|tangent|tight)")

    content = f"import Mathlib\n{forged}\n"
    kernel_rejects = assert_kernel_rejects(
        content, name, env_dir=env_dir, prelude=FSTAR_PRELUDE,
    )

    okay = selfcheck_refused or bool(kernel_rejects)
    l2_detail = (
        "kernel REJECTED the forged proof" if kernel_rejects
        else "kernel ACCEPTED the forged proof (control BREACH)"
    )
    detail = f"Layer1[{l1_detail}] | Layer2[{l2_detail}]"
    return NegativeControlResult(
        selfcheck_refused=selfcheck_refused,
        kernel_rejects=kernel_rejects,
        okay=okay,
        detail=detail,
    )
