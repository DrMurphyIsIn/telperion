"""Negative-control adapter for FwdTelescopeEmitter.

The FwdTelescope certificate is a single polynomial fact: the contiguous
telescoping identity  A(q) - (P - q - j) + N(j) = 0  (the "telescoping mate").
Telperion's certify_fwd_telescope_point verifies it exactly in sympy and
REFUSES any conjectured pnum factor N whose residual is nonzero.

FALSE forgery: corrupt the numerator factor N from the true knapsack value
n/2 - u to n/2 - 2*u.  Residual becomes -j != 0, so the sympy self-check
would refuse it; the harness mints the family without going through certify().
The emitted Lean is well-formed but the load-bearing `field_simp; ring` in
{name}_fwdDiff_iter can no longer close (pnum step no longer telescopes
against pden), so the kernel rejects.

TRUE twin: the genuine knapsack instance (A,P,N) = (n/2 - q, n, n/2 - u),
whose `field_simp; ring` closes exactly.  Minimal difference: coefficient of u.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_fwd_telescope import FwdTelescopeEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)

# Shared symbols: A may use (n, q); P only n; N only (n, u) -- per the emitter's
# symbol guard in certify_fwd_telescope_point.
_n, _q, _u = sp.symbols("n q u")


def _make_false_cert():
    # payload = (A, P, N).  N corrupted from n/2 - u to n/2 - 2*u.
    # Contiguous residual A - (P - q - j) + N(j) = -j != 0  ->  a FALSE claim.
    A = _n / 2 - _q
    P = sp.sympify("n")
    N = _n / 2 - 2 * _u
    return (A, P, N)


def _make_true_cert():
    # The genuine knapsack instance; residual = 0, so `field_simp; ring` closes.
    A = _n / 2 - _q
    P = sp.sympify("n")
    N = _n / 2 - _u
    return (A, P, N)


def _emit_call(cert, name: str) -> str:
    # emit_body unpacks `A, P, N = inst.payload`, so hand the 3-tuple in as payload.
    # It also reads `n = tuple(fam.family.symbols)[0]` to render the closed form,
    # so declare n (else IndexError on an empty symbols tuple).
    body = emit_via_single_instance_family(
        FwdTelescopeEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
        family_kwargs={"symbols": (_n,)},
    )
    # The emitter renders SIX prefixed declarations; the load-bearing one (the
    # telescoping closed form whose final `field_simp; ring` the corrupt N breaks)
    # is `{name}_fwdDiff_iter`.  The generic engine axiom-checks the decl named
    # exactly `name` (verify_lean(..., decls=[name])), so rename that single
    # theorem's own identifier `{name}_fwdDiff_iter` -> `name`.  The helper
    # declarations ({name}_f, _pnum, _pden, _pden_pos, _pden_shift) keep their
    # names and their references are untouched (none contains "_fwdDiff_iter"),
    # so the proof is unchanged; only the checked identifier now matches.
    return body.replace(f"{name}_fwdDiff_iter", name)


register(
    NegativeControlAdapter(
        emitter_name="FwdTelescopeEmitter",
        make_false_cert=_make_false_cert,
        make_true_cert=_make_true_cert,
        emit_call=_emit_call,
        prelude="",
        allow_axioms=(),
        label=(
            "Forged FwdTelescope: corrupted pnum factor N = n/2 - 2*u (true is "
            "n/2 - u). The contiguous identity A(q)-(P-q-j)+N(j)=0 fails with "
            "residual -j, so the telescoping closed form is FALSE and the final "
            "field_simp; ring in _fwdDiff_iter cannot close -> kernel rejects."
        ),
        imports_line="import Mathlib",
    )
)
