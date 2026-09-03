"""Integrality-gate emitter — a finite exceptional table + a uniform p-adic
valuation certificate (the BG "23-gate" strictness).

Shape.  A "strictness gate": a property ``P(n)`` holds STRICTLY for every ``n``
EXCEPT a finite exceptional set, and the exceptions occur exactly when a prime
``p ∣ n`` — the arithmetic obstruction.  Two composable parts, both decidable:

  * the P-ADIC part — a valuation fact ``v_p(N) = k`` pinning the tie exactly
    at ``p ∣ n``, in the frozen decidable-divisibility form
    ``(p^k ∣ N) ∧ ¬ (p^(k+1) ∣ N)`` (composed straight from
    ``padic.ValuationFact.lean(tactic='norm_num')`` — the ``emit_padic``
    primitive), and

  * the FINITE-EXCEPTIONAL-TABLE part — the finite set of ``p ∣ n`` cases, each
    a concrete ℤ strict inequality ``lhs < rhs`` (or ``lhs ≤ rhs``) closed by
    ``norm_num`` per row, PLUS a single guarded ``∀ i ∈ table, P i := by decide``
    over the same rows (the ``emit_finite_decide`` primitive: an all-ℤ/ℕ
    ``decide`` claim, no ℚ so the kernel reduces).

The BG motivating case is the 23-gate: ``621/64 = 27·23`` and
``64·243·23 = 621·576`` — the tie sits exactly on the 23-column, so the strict
inequality is an arithmetic (integrality) fact, not a smooth one.  Here it is
certified as ``v_23(621) = 1`` (``23 ∣ 621``, ``23² ∤ 621``) together with the
finite table of exceptional rows.

Certificate content (all exact, all sympy-self-checked before ANY Lean is
written):

  * the prime ``p`` and the valuation fact ``v_p(N) = k`` — checked by
    ``padic.padic_val`` (RAISES ``ValueError`` on a wrong valuation: the
    anti-phantom negative control);
  * the finite exceptional table — a list of concrete integer strict/weak
    inequalities, each re-checked exactly in Python (RAISES if any row is
    false); the guarded ∀-fact is the SAME rows, so table and ∀ can never
    diverge.

EMITTED LEAN (per instance):

    -- p-adic tie pin (emit_padic shape):
    theorem <name>_valuation : (p^k ∣ N) ∧ ¬ (p^(k+1) ∣ N) := by norm_num
    -- finite exceptional table, one ℤ inequality per row:
    theorem <name>_row_0 : (a₀ : ℤ) < b₀ := by norm_num
    ...
    -- the same rows, one guarded ∀-fact (emit_finite_decide shape):
    theorem <name>_table : ∀ x ∈ <name>_exc, x.1 < x.2 := by decide

Only ``norm_num`` (concrete ℤ arithmetic) and ``decide`` (the finite table over
ℤ/ℕ) are used — the two lowest-risk kernel-reducible tactics.

HONEST SCOPE: this certifies ONLY the finite exceptional table and the single
p-adic valuation fact pinning the tie at ``p ∣ n``.  It does NOT prove the
strict inequality for the (infinite) non-exceptional set, nor does it close any
downstream Brualdi-Goldwasser obligation.  conjecture1_proved=False.

Composes: ``emit_padic`` (``PadicValuationEmitter`` / ``ValuationFact``) for the
p-adic part; ``emit_finite_decide`` (``FiniteDecideEmitter``) for the finite
guarded-∀ table; the ℤ-``norm_num`` discipline from ``emit_finite_argmax``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .padic import ValuationFact, padic_val
    from .workflow import Emitter
except ImportError:  # run directly: `python src/telperion/emit_integrality_gate.py`
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.padic import ValuationFact, padic_val
    from telperion.workflow import Emitter


_OPS = {"lt": lambda a, b: a < b, "le": lambda a, b: a <= b}
_LEAN_OPS = {"lt": "<", "le": "≤"}


# ---------------------------------------------------------------------------
# Certificate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class IntegralityGateCertificate:
    """A verified integrality-gate certificate.

    Two composable, exact parts:

      * ``valuation`` — a ``ValuationFact`` ``v_p(N) = k`` (the arithmetic
        obstruction: the tie is pinned exactly where ``p ∣ n``), re-derived by
        ``padic.padic_val``;
      * ``rows`` — the finite exceptional table, a tuple of
        ``(a, b, op)`` with ``op ∈ {'lt','le'}`` and ``a op b`` TRUE over ℤ
        (each row re-checked exactly).  The emitted guarded ∀-fact is exactly
        these rows, so the per-row theorems and the ∀-fact never diverge.

    ``op`` is the ambient comparison for the guarded ∀-fact (all rows share it,
    so ``∀ x ∈ table, x.1 <op> x.2`` type-checks); per-row theorems use each
    row's own op.
    """

    p: int                                    # the obstruction prime
    valuation: ValuationFact                  # v_p(N) = k
    rows: tuple                               # ((a, b, op), ...): a op b over ℤ
    table_op: str                             # ambient op for the guarded ∀-fact


def integrality_gate_certificate(
    *,
    prime: int,
    valuation_n: int,
    valuation_k: int,
    rows: Sequence,
    valuation_name: str = "val",
) -> IntegralityGateCertificate:
    """Build and EXACTLY self-check an integrality-gate certificate.

    Parameters
    ----------
    prime
        The obstruction prime ``p`` (the tie sits on the ``p``-column).
    valuation_n, valuation_k
        Pin the tie via ``v_p(valuation_n) = valuation_k``; certified as
        ``p^k ∣ N ∧ ¬ p^(k+1) ∣ N``.  RAISES ``ValueError`` if the claimed
        valuation is wrong (the negative control).
    rows
        The finite exceptional table.  Each row is ``(a, b)`` (defaults to a
        strict ``a < b``) or ``(a, b, op)`` with ``op ∈ {'lt','le'}``.  Every
        row is re-checked exactly over ℤ; RAISES if any is false.  The table
        must be non-empty and all rows must share the same ``op`` (so the
        guarded ∀-fact type-checks).
    """
    p = int(prime)
    if p < 2 or sp.Integer(p).is_prime is False:
        raise ValueError(f"REFUSED: {p} is not a prime (obstruction prime)")

    # --- p-adic part: pin the tie via the valuation fact (emit_padic shape) ---
    n, k = int(valuation_n), int(valuation_k)
    if n == 0:
        raise ValueError("REFUSED: v_p(0) is undefined (valuation_n = 0)")
    actual = padic_val(n, p)
    if actual != k:
        raise ValueError(
            f"REFUSED: valuation fact wrong — claimed v_{p}({n}) = {k}, "
            f"engine says {actual}"
        )
    vfact = ValuationFact(name=valuation_name, n=n, p=p, k=k)
    if not vfact.check():  # defensive: exact dual of the Lean check
        raise ValueError(
            f"REFUSED: ValuationFact self-check failed for v_{p}({n}) = {k}"
        )

    # --- finite exceptional table: exact per-row check (emit_finite_decide) ---
    norm_rows = []
    for i, row in enumerate(rows):
        if len(row) == 2:
            a, b, op = row[0], row[1], "lt"
        elif len(row) == 3:
            a, b, op = row[0], row[1], row[2]
        else:
            raise ValueError(f"REFUSED: row {i} malformed (want (a,b) or (a,b,op)): {row!r}")
        if op not in _OPS:
            raise ValueError(f"REFUSED: row {i} op {op!r} not in {{'lt','le'}}")
        a_i, b_i = sp.Integer(a), sp.Integer(b)
        if not _OPS[op](a_i, b_i):
            raise ValueError(
                f"REFUSED: exceptional-table row {i} is FALSE: "
                f"{a_i} {_LEAN_OPS[op]} {b_i} does not hold"
            )
        norm_rows.append((int(a_i), int(b_i), op))

    if not norm_rows:
        raise ValueError("REFUSED: exceptional table is empty; nothing to certify")
    ops = {op for _, _, op in norm_rows}
    if len(ops) != 1:
        raise ValueError(
            f"REFUSED: mixed ops {ops} in the table; the guarded ∀-fact needs "
            "one uniform comparison (split into separate instances)"
        )
    table_op = norm_rows[0][2]

    return IntegralityGateCertificate(
        p=p,
        valuation=vfact,
        rows=tuple(norm_rows),
        table_op=table_op,
    )


def certify_integrality_gate_point(family, pt, name):
    """Certify one integrality-gate instance from ``family.special[1](pt) -> spec``.

    ``spec`` is a dict ``{"prime": p, "valuation_n": N, "valuation_k": k,
    "rows": [...]}`` (optional ``"valuation_name"``).  Returns
    ``(CertifiedInstance, n_checks)`` where ``n_checks`` = 1 (valuation) + one
    per exceptional row + 1 (the guarded ∀-fact)."""
    spec = family.special[1](pt)
    cert = integrality_gate_certificate(
        prime=spec["prime"],
        valuation_n=spec["valuation_n"],
        valuation_k=spec["valuation_k"],
        rows=spec["rows"],
        valuation_name=spec.get("valuation_name", f"{name}_val"),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    n_checks = 1 + len(cert.rows) + 1
    return inst, n_checks


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

@dataclass
class IntegralityGateEmitter(Emitter):
    """Emit the p-adic tie pin + the finite exceptional table.

    Per instance:

      * ``theorem <name>_valuation : (p^k ∣ N) ∧ ¬ (p^(k+1) ∣ N) := by norm_num``
        — composed verbatim from ``ValuationFact.lean(tactic='norm_num')``
        (the ``emit_padic`` shape);
      * one ``theorem <name>_row_i : (a : ℤ) <op> b := by norm_num`` per row;
      * a single ``def <name>_exc : List (ℤ × ℤ) := [...]`` + guarded ∀-fact
        ``theorem <name>_table : ∀ x ∈ <name>_exc, x.1 <op> x.2 := by decide``
        (the ``emit_finite_decide`` shape, all-ℤ so the kernel reduces).

    Only ``norm_num`` / ``decide`` — the two lowest-risk kernel tactics."""

    def __post_init__(self):
        self.kind = "integrality_gate"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: IntegralityGateCertificate = inst.payload  # type: ignore[assignment]
            base = inst.lean_name
            vf = cert.valuation
            pk = cert.p ** vf.k
            pk1 = cert.p ** (vf.k + 1)
            op = _LEAN_OPS[cert.table_op]

            lines.append(
                f"-- Integrality gate (p = {cert.p}): the strict inequality is an "
                f"arithmetic\n"
                f"-- fact — the tie sits exactly on the {cert.p}-column.  Two decidable "
                f"parts:\n"
                f"-- (1) the p-adic tie pin v_{cert.p}({vf.n}) = {vf.k}, and\n"
                f"-- (2) the finite exceptional table ({len(cert.rows)} rows, the "
                f"{cert.p} ∣ n cases).\n"
            )
            # (1) p-adic tie pin — composed from emit_padic's ValuationFact.lean.
            lines.append(
                f"theorem {base}_valuation : "
                f"({pk} ∣ {vf.n}) ∧ ¬ ({pk1} ∣ {vf.n}) := by norm_num\n"
            )
            nthm += 1
            # (2a) one ℤ inequality per exceptional row (norm_num discipline).
            for i, (a, b, rop) in enumerate(cert.rows):
                lines.append(
                    f"theorem {base}_row_{i} : ({a} : ℤ) {_LEAN_OPS[rop]} {b} := by norm_num\n"
                )
                nthm += 1
            # (2b) the same rows as one guarded ∀-fact (emit_finite_decide shape).
            body = ", ".join(
                f"({a}, {b if b >= 0 else f'(-{-b})'})" for a, b, _ in cert.rows
            )
            lines.append(
                f"def {base}_exc : List (ℤ × ℤ) := [{body}]\n"
                f"theorem {base}_table : ∀ x ∈ {base}_exc, x.1 {op} x.2 := by decide\n"
            )
            nthm += 1
        return "".join(lines), nthm


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def integrality_gate_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an integrality-gate family (kind='integrality_gate').

    ``spec``: a callable ``pt -> {"prime": p, "valuation_n": N,
    "valuation_k": k, "rows": [(a, b) | (a, b, op), ...]}`` (optional
    ``"valuation_name"``).  Refuses (at certification) a non-prime ``p``, a
    wrong valuation, an empty/mixed-op table, or any false exceptional row."""
    n = sp.symbols("n")
    return InequalityFamily(
        name=name,
        symbols=(n,),
        grid=grid,
        lean_name=lean_name,
        special=("integrality_gate", spec),
        constants=dict(constants or {}),
    )


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== positive: the BG 23-gate  v_23(621) = 1  +  finite exceptional table ===")
    # 621/64 = 27·23, and 64·243·23 = 621·576 (the tie sits on the 23-column).
    # p-adic part: v_23(621) = 1  (23 | 621, 23^2 = 529 ∤ 621).
    # exceptional table: the concrete integer inequalities witnessing the gate,
    #   e.g. 64·243·23 = 357696 = 621·576 pinned strictly around by neighbours,
    #   and the 27·23 = 621 identity's strict flanks.
    cert = integrality_gate_certificate(
        prime=23,
        valuation_n=621,
        valuation_k=1,
        rows=[
            (64 * 243 * 23, 621 * 576 + 1),   # 357696 < 357697  (tie +1, strict)
            (621 * 576 - 1, 64 * 243 * 23),   # 357695 < 357696  (tie -1, strict)
            (27 * 23, 622),                   # 621   < 622   (27·23 strictly below next)
            (64 * 243, 15553),                # 15552 < 15553 (the 64·243 flank)
        ],
    )
    print(f"  cert OK: p={cert.p}, v_{cert.p}({cert.valuation.n})={cert.valuation.k}, "
          f"{len(cert.rows)} exceptional rows, table_op={cert.table_op}")

    print("\n=== positive: a small p=5 gate  v_5(50) = 2  +  table ===")
    cert2 = integrality_gate_certificate(
        prime=5,
        valuation_n=50,
        valuation_k=2,               # 50 = 2·5^2, v_5(50)=2
        rows=[(1, 2), (7, 10), (49, 50)],
    )
    print(f"  cert OK: p={cert2.p}, v_{cert2.p}({cert2.valuation.n})={cert2.valuation.k}, "
          f"{len(cert2.rows)} rows")

    print("\n=== NEGATIVE CONTROL: wrong valuation v_23(621) = 2 (expect ValueError) ===")
    try:
        integrality_gate_certificate(
            prime=23, valuation_n=621, valuation_k=2, rows=[(1, 2)]
        )
        raise SystemExit("FAIL: wrong valuation was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: a false exceptional row  10 < 3 (expect ValueError) ===")
    try:
        integrality_gate_certificate(
            prime=23, valuation_n=621, valuation_k=1, rows=[(10, 3)]
        )
        raise SystemExit("FAIL: false row was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== NEGATIVE CONTROL: non-prime obstruction p = 21 (expect ValueError) ===")
    try:
        integrality_gate_certificate(
            prime=21, valuation_n=42, valuation_k=1, rows=[(1, 2)]
        )
        raise SystemExit("FAIL: non-prime was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {e}")

    print("\n=== emitted Lean (two instances) ===")
    insts = [
        CertifiedInstance(point={"case": 0}, lean_name="ig_bg_23gate",
                          corners=(), payload=cert),
        CertifiedInstance(point={"case": 1}, lean_name="ig_p5_gate",
                          corners=(), payload=cert2),
    ]

    class _View:
        instances = insts

    body, nthm = IntegralityGateEmitter().emit_body(
        _View(), LeanProfile(namespace=("IntegralityGate",))
    )
    print(f"\n-- {nthm} theorems --\n")
    print(body)
