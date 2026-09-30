"""Monotone-ratio family-tail emitter — the ``b(s) <= B for all s >= s0`` shape.

A first-class emitter for the monotone-ratio tail bound (the source is
``bg/near_star_tail.py``'s ``NearStarTailCertificate``): given a POSITIVE
sequence ``b(s)`` defined by an exact rational cavity form, prove

    b(s) <= B    for every integer s >= s0

via three ingredients that between them cover the whole tail:

  (1) the consecutive RATIO ``r(s) = b(s+1)/b(s)`` — a rational function of ``s``
      even when ``b`` itself is not (the transcendental amplitude factors cancel
      in the quotient; this is the near-star's ``(486/529)(1+1/(4s^2+11s+6))^11``);
  (2) the NONINCREASING TAIL: ``r(s) <= 1`` for all ``s >= s0``, i.e. ``b`` is
      nonincreasing on the tail.  Since ``b(s) > 0`` this is equivalent to
      ``1 - r(s) >= 0``; that rational claim is Polya-certified on the tail region
      ``s = s0 + t, t >= 0`` (an all-nonneg-coefficient numerator over an
      all-positive denominator, the ``polya_certify`` shape);
  (3) the BASE value ``b(s0) <= B`` — an exact rational fact (``norm_num``).

Then ``b(s) <= b(s0) <= B`` for every ``s >= s0``: descend from any ``s`` to
``s0`` one nonincreasing step at a time (ingredient 2), landing on the base
(ingredient 3).  That descent is a single clean ``Nat`` induction.

HONEST SCOPE
------------
* The NONINCREASING-STEP certificate (``0 <= 1 - r(s0+t)`` over ``t >= 0``, a
  num/den Polya form closed by ``positivity``) and the BASE fact
  (``b(s0) <= B`` by ``norm_num`` on an exact rational) are STANDARD, robust
  Lean — the same two tactics ``emit_cone`` / ``emit_lattice_box`` rely on.  The
  step numerator is rendered so ``positivity`` closes it as written.
* The step is stated as ``1 - r(s0+t) >= 0`` (equivalently ``r(s0+t) <= 1``).
  This is EXACTLY the ``b`` nonincreasing fact for a positive ``b``, and it is
  what the induction consumes; it is proven rigorously and independently of any
  Lean encoding of ``b`` itself.
* The assembled ``forall s >= s0, b s <= B`` theorem is emitted over an ABSTRACT
  ``b : ℕ → ℝ`` fed the two proven ingredients as hypotheses (``hstep`` : the
  per-step nonincrease, ``hbase`` : ``b s0 <= B``).  That assembly lemma is a
  genuine, ``sorry``-free ``Nat.le_induction`` — it is the mechanical part.  What
  it does NOT do is pin ``b`` to a concrete Lean closed form: encoding an
  arbitrary transcendental cavity ``b`` as a Lean function and re-deriving its
  ratio in-kernel is the remaining piece, and it is documented as such (no
  ``sorry``, no stub) rather than faked.  For the near-star the concrete
  ``r``-step and the concrete rational base ARE emitted and kernel-checkable; the
  outstanding link is instantiating the abstract assembly at the concrete ``b``.

NEGATIVE CONTROL
----------------
``certify_monotone_tail_point`` refuses (ValueError, no Lean) when the tail is
NOT certifiably nonincreasing (``1 - r(s0+t)`` has no nonneg-num / positive-den
Polya form) or when the base is violated (``b(s0) > B``).

PIECEWISE-LINEAR NODE-CONDITION face (``PLNodeTailPayload``)
------------------------------------------------------------
Closes a two-parameter family in one step:

    for all integers m >= M+1 and all y in (0, 1]:   m*U(y) + L(y) <= 0,

where ``U <= 0`` lies below a piecewise-linear function with rational nodes
``(y_i, U_i)`` (``0 < y_0 < ... < y_K = 1``, ``U_0 = 0``, ``U = 0`` on ``(0, y_0]``),
and ``L(y) <= 0`` for ``y <= y_dag``, ``L(y) <= s*(y - y_dag)`` for ``y > y_dag``.
Certificate: ``(M+1)*|U_i| >= s*(y_i - y_dag)`` at every node with
``y_i > y_dag``.  It is the same monotone-plus-base shape as the ratio tail, with the
roles moved: ``m*U(y)`` is nonincreasing in ``m`` because ``U <= 0``, and the node
condition is the base case ``m = M+1`` for every ``y`` at once.  For ``y > y_dag``,
``h(y) = m*U(y) + s*(y - y_dag)`` is linear on each segment and ``<= 0`` at both
ends of the part of the segment beyond ``y_dag`` (at ``y_dag``, and at the nodes), hence everywhere.  The kernel
checks each segment through the exact convex-combination identity
``(b - a)*h(y) = (b - y)*h(a) + (y - a)*h(b)`` (``ring``) with ``h(a), h(b) <= 0``
from the node literals (``linarith``).

The core theorem takes ``U`` and ``L`` abstractly, with the piecewise-linear
majorant and the two ``L`` conditions as HYPOTHESES (the honest seam). With
``L = "log_tangent"``, it also discharges the ``L`` hypotheses for
``L(y) = log(1+y) - log(1+y_dag)`` (monotone below ``y_dag``; tangent
``log x <= x - 1`` above, which needs ``s >= 1/(1+y_dag)``). It then states a
hypothesis-free corollary for the concrete ``U = min(0, l_0, ..., l_{K-1})``, where ``l_i`` is the
line through nodes ``i`` and ``i+1``: the minimum lies below every segment line, so it
satisfies every ``U`` hypothesis.

The node-condition pattern is distilled from a draft communicated by
Prof. John L. Goldwasser (28 Sep 2026); only the generic shape is used.
conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance, PolyaCertificate, polya_certify
from .expr import expr_lean, expr_lean_from_parts, rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


# ---------------------------------------------------------------------------
# Payload
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MonotoneTailPayload:
    """The certified pieces of one ``b(s) <= B for s >= s0`` instance."""

    b_expr: sp.Expr          # b(s), a (possibly transcendental) exact expr in s
    s_symbol: sp.Symbol      # the integer variable s
    s0: int                  # tail start
    bound: sp.Rational       # B
    ratio: sp.Expr           # r(s) = b(s+1)/b(s), a RATIONAL function of s
    step_cert: PolyaCertificate   # Polya cert for 0 <= 1 - r(s0 + t), t >= 0
    t_symbol: sp.Symbol      # the tail variable t (s = s0 + t)
    base_value: sp.Rational  # b(s0) as an exact rational


@dataclass(frozen=True)
class PLNodeTailPayload:
    """The piecewise-linear node-condition tail (see the module docstring).

    ``nodes`` are ``((y_i, U_i), ...)``, ``slopes[i]`` the slope of segment
    ``[y_i, y_{i+1}]``, ``L`` is ``None`` (abstract) or ``"log_tangent"``."""

    M: int
    nodes: tuple
    slopes: tuple
    y_dag: sp.Rational
    s: sp.Rational
    L: str | None = None

    def ubar(self, i: int, y) -> sp.Rational:
        """The piecewise-linear majorant on segment ``i``, evaluated at ``y``."""
        yi, ui = self.nodes[i]
        return ui + self.slopes[i] * (y - yi)


def pl_node_tail_certificate(*, M, nodes, y_dag, s, L=None) -> PLNodeTailPayload:
    """Build and EXACTLY self-check a piecewise-linear node-condition tail.

    REFUSED (``ValueError``) unless: ``M >= 0``; at least two nodes with
    ``0 < y_0 < ... < y_K = 1``; ``U_0 = 0`` and every ``U_i <= 0``; and the node
    condition ``(M+1)*U_i + s*(y_i - y_dag) <= 0`` at every node with
    ``y_i > y_dag`` (exact over ℚ, the negative control).  For
    ``L = "log_tangent"`` also ``y_dag > -1`` and ``s >= 1/(1+y_dag)``."""
    M = int(M)
    if M < 0:
        raise ValueError(f"pl_node_tail REFUSED: M must be >= 0, got {M}")
    nodes = tuple((sp.Rational(y), sp.Rational(u)) for y, u in nodes)
    y_dag, s = sp.Rational(y_dag), sp.Rational(s)
    if len(nodes) < 2:
        raise ValueError("pl_node_tail REFUSED: need at least two nodes")
    ys = [y for y, _ in nodes]
    if not (ys[0] > 0 and all(a < b for a, b in zip(ys, ys[1:])) and ys[-1] == 1):
        raise ValueError(f"pl_node_tail REFUSED: nodes must satisfy 0 < y_0 < ... < y_K = 1, got {ys}")
    if nodes[0][1] != 0:
        raise ValueError(f"pl_node_tail REFUSED: U_0 must be 0 (U = 0 on (0, y_0]), got {nodes[0][1]}")
    if any(u > 0 for _, u in nodes):
        raise ValueError("pl_node_tail REFUSED: every node value U_i must be <= 0")
    if L not in (None, "log_tangent"):
        raise ValueError(f"pl_node_tail REFUSED: unknown L mode {L!r}")
    if L == "log_tangent":
        if not y_dag > -1:
            raise ValueError(f"pl_node_tail REFUSED: log_tangent needs y_dag > -1, got {y_dag}")
        if not s >= 1 / (1 + y_dag):
            raise ValueError(
                f"pl_node_tail REFUSED: log_tangent needs s >= 1/(1+y_dag) = {1 / (1 + y_dag)}, got {s}")
    for y, u in nodes:
        if y > y_dag and (M + 1) * u + s * (y - y_dag) > 0:
            raise ValueError(
                f"pl_node_tail REFUSED: node condition fails at y = {y}: (M+1)*|U| = "
                f"{(M + 1) * -u} < s*(y - y_dag) = {s * (y - y_dag)} (negative control)")
    slopes = tuple((u1 - u0) / (y1 - y0) for (y0, u0), (y1, u1) in zip(nodes, nodes[1:]))
    return PLNodeTailPayload(M=M, nodes=nodes, slopes=slopes, y_dag=y_dag, s=s, L=L)


# ---------------------------------------------------------------------------
# Certification
# ---------------------------------------------------------------------------

def certify_monotone_tail_point(family, pt, name):
    """Certify one monotone-tail instance: (CertifiedInstance, n_checks).

    Reads ``(b_expr, s0, bound, s_symbol) = family.special[1](pt)``, derives the
    exact consecutive ratio ``r(s) = b(s+1)/b(s)``, Polya-certifies the
    nonincreasing tail ``0 <= 1 - r(s0 + t)`` over the nonnegative tail variable
    ``t``, and checks the base ``b(s0) <= B`` exactly.  Raises ValueError (a
    refusal, no Lean) when the tail is not certifiably nonincreasing or the base
    is violated.
    """
    spec = family.special[1](pt)
    if isinstance(spec, dict):  # piecewise-linear node-condition face
        pl = pl_node_tail_certificate(
            M=spec["M"], nodes=spec["nodes"], y_dag=spec["y_dag"], s=spec["s"],
            L=spec.get("L"))
        inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=pl)
        return inst, len(pl.nodes)
    b_expr, s0, bound, s = spec
    b_expr = sp.sympify(b_expr)
    bound = sp.Rational(bound)
    s0 = int(s0)

    checks = 0

    # (1) exact consecutive ratio r(s) = b(s+1)/b(s) — must be a rational fn of s.
    ratio = sp.simplify(b_expr.subs(s, s + 1) / b_expr)
    ratio = sp.together(ratio)
    r_num, r_den = sp.fraction(ratio)
    if not (sp.Poly(sp.expand(r_num), s) and sp.Poly(sp.expand(r_den), s)):
        raise ValueError(
            f"monotone-tail instance '{name}' REFUSED: ratio b(s+1)/b(s) is not "
            "a rational function of s"
        )
    checks += 1

    # (2) nonincreasing tail: 0 <= 1 - r(s0 + t) over t >= 0 (Polya).
    t = sp.Symbol("t", nonnegative=True)
    step_expr = sp.together(1 - ratio.subs(s, s0 + t))
    try:
        step_cert = polya_certify(step_expr, (t,))
    except ValueError as e:
        raise ValueError(
            f"monotone-tail instance '{name}' REFUSED: tail is not certifiably "
            f"nonincreasing (1 - r(s0+t) has no Polya form): {e}"
        )
    checks += 1

    # (3) base: b(s0) <= B exactly.
    base_value = sp.nsimplify(b_expr.subs(s, s0))
    base_value = sp.Rational(base_value)
    if base_value > bound:
        raise ValueError(
            f"monotone-tail instance '{name}' REFUSED: base b({s0}) = "
            f"{base_value} > B = {bound}"
        )
    checks += 1

    payload = MonotoneTailPayload(
        b_expr=b_expr,
        s_symbol=s,
        s0=s0,
        bound=bound,
        ratio=ratio,
        step_cert=step_cert,
        t_symbol=t,
        base_value=base_value,
    )
    inst = CertifiedInstance(
        point=dict(pt),
        lean_name=name,
        corners=(),
        payload=payload,
    )
    return inst, checks


# ---------------------------------------------------------------------------
# Emitter
# ---------------------------------------------------------------------------

def _rl(q) -> str:
    """A rational as a real Lean literal ``(p/q : ℝ)``."""
    q = sp.Rational(q)
    return f"({q.p} : ℝ)" if q.q == 1 else f"({q.p}/{q.q} : ℝ)"


def _pl_line(pl: PLNodeTailPayload, i: int, y: str) -> str:
    yi, ui = pl.nodes[i]
    return f"({_rl(ui)} + {_rl(pl.slopes[i])} * ({y} - {_rl(yi)}))"


def _pl_segment(pl: PLNodeTailPayload, i: int, hlo: str, hhi: str, ind: str) -> list[str]:
    """Proof lines for ``y`` in segment ``i`` (``hlo : y_i < y``, ``hhi : y ≤ y_{i+1}``)."""
    yd, s_ = pl.y_dag, pl.s
    Ub = _pl_line(pl, i, "y")
    out = [
        f"{ind}have hu := hU{i + 1} y (le_of_lt {hlo}) {hhi}",
        f"{ind}have hmu : (m : ℝ) * U y ≤ (m : ℝ) * {Ub} := mul_le_mul_of_nonneg_left hu hm0",
        f"{ind}rcases le_or_gt y {_rl(yd)} with hd | hd",
        f"{ind}· have hL := hL1 y hy0 hd",
        f"{ind}  have hub : {Ub} ≤ 0 := by linarith",
        f"{ind}  have hmub := mul_le_mul_of_nonneg_left hub hm0",
        f"{ind}  linarith",
        f"{ind}· have hL := hL2 y hd hy1",
    ]
    b = pl.nodes[i + 1][0]
    if yd >= b:  # no part of this segment lies beyond y_dag
        out.append(f"{ind}  linarith")
        return out
    a = max(pl.nodes[i][0], yd)
    ua, ub = pl.ubar(i, a), pl.ubar(i, b)
    ha = f"((m : ℝ) * {_rl(ua)} + {_rl(s_)} * ({_rl(a)} - {_rl(yd)}))"
    hb = f"((m : ℝ) * {_rl(ub)} + {_rl(s_)} * ({_rl(b)} - {_rl(yd)}))"
    out += [
        f"{ind}  have hA : {ha} ≤ 0 := by linarith",
        f"{ind}  have hB : {hb} ≤ 0 := by linarith",
        f"{ind}  have hid : ({_rl(b)} - {_rl(a)}) * ((m : ℝ) * {Ub} + {_rl(s_)} * (y - {_rl(yd)}))",
        f"{ind}      = ({_rl(b)} - y) * {ha} + (y - {_rl(a)}) * {hb} := by ring",
        f"{ind}  have p1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ {_rl(b)} - y)",
        f"{ind}  have p2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ y - {_rl(a)})",
        f"{ind}  have hseg : ({_rl(b)} - {_rl(a)}) * ((m : ℝ) * {Ub} + {_rl(s_)} * (y - {_rl(yd)})) ≤ 0 := by",
        f"{ind}    rw [hid]; linarith",
        f"{ind}  linarith",
    ]
    return out


def _emit_pl_node_tail(pl: PLNodeTailPayload, name: str) -> str:
    K = len(pl.nodes) - 1
    yd, s_ = _rl(pl.y_dag), _rl(pl.s)
    y0 = _rl(pl.nodes[0][0])
    hyps = [f"    (hU0 : ∀ y : ℝ, 0 < y → y ≤ {y0} → U y ≤ 0)"]
    for i in range(K):
        hyps.append(
            f"    (hU{i + 1} : ∀ y : ℝ, {_rl(pl.nodes[i][0])} ≤ y → y ≤ {_rl(pl.nodes[i + 1][0])} → "
            f"U y ≤ {_pl_line(pl, i, 'y')})")
    hyps.append(f"    (hL1 : ∀ y : ℝ, 0 < y → y ≤ {yd} → L y ≤ 0)")
    hyps.append(f"    (hL2 : ∀ y : ℝ, {yd} < y → y ≤ 1 → L y ≤ {s_} * (y - {yd}))")
    concl = f"∀ m : ℕ, {pl.M + 1} ≤ m → ∀ y : ℝ, 0 < y → y ≤ 1 → (m : ℝ) * U y + L y ≤ 0"
    body = [
        "  intro m hm y hy0 hy1",
        f"  have hmR : ({pl.M + 1} : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm",
        "  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity",
        f"  rcases le_or_gt y {y0} with h0 | h0",
        "  · have hu := hU0 y hy0 h0",
        "    have hmu := mul_le_mul_of_nonneg_left hu hm0",
        f"    rcases le_or_gt y {yd} with hd | hd",
        "    · have hL := hL1 y hy0 hd",
        "      linarith",
        "    · have hL := hL2 y hd hy1",
        "      linarith",
    ]
    ind = "  "
    for i in range(K):
        if i < K - 1:
            body.append(f"{ind}· rcases le_or_gt y {_rl(pl.nodes[i + 1][0])} with h{i + 1} | h{i + 1}")
            ind += "  "
            body.append(f"{ind}· " + _pl_segment(pl, i, f"h{i}", f"h{i + 1}", ind + "  ")[0].lstrip())
            body += _pl_segment(pl, i, f"h{i}", f"h{i + 1}", ind + "  ")[1:]
        else:
            body.append(f"{ind}· " + _pl_segment(pl, i, f"h{i}", "hy1", ind + "  ")[0].lstrip())
            body += _pl_segment(pl, i, f"h{i}", "hy1", ind + "  ")[1:]
    nodes_txt = ", ".join(f"({y}, {u})" for y, u in pl.nodes)
    out = (
        f"-- {name}: piecewise-linear node-condition tail.  For all m ≥ {pl.M + 1} and y ∈ (0, 1],\n"
        f"-- m·U(y) + L(y) ≤ 0, with U below the PL function on nodes {nodes_txt}\n"
        f"-- and L ≤ 0 below y† = {pl.y_dag}, L ≤ {pl.s}·(y − y†) above.  Certificate: the node\n"
        f"-- condition (M+1)·|U_i| ≥ s·(y_i − y†) at every node beyond y†; per segment the\n"
        f"-- convex-combination identity (ring).  U, L and their conditions are HYPOTHESES.\n"
        f"theorem {name} (U L : ℝ → ℝ)\n" + "\n".join(hyps) + " :\n"
        f"    {concl} := by\n" + "\n".join(body) + "\n\n"
    )
    if pl.L != "log_tangent":
        return out
    Lf = f"Real.log (1 + y) - Real.log (1 + {yd})"
    inv = _rl(1 / (1 + pl.y_dag))
    lines_ = [_pl_line(pl, i, "y") for i in range(K)]
    Umin = "0" if K == 0 else lines_[-1]
    for ln in reversed(lines_[:-1]):
        Umin = f"min {ln} ({Umin})"
    Umin = f"min 0 ({Umin})"
    u_proofs = ["fun _ _ _ => min_le_left _ _"]
    for i in range(K):
        e = "le_refl _" if i == K - 1 else "min_le_left _ _"
        for _ in range(i):
            e = f"le_trans (min_le_right _ _) ({e})"
        u_proofs.append(f"fun _ _ _ => le_trans (min_le_right _ _) ({e})")
    out += (
        f"-- {name}_L_nonpos / {name}_L_tangent: L(y) = log(1+y) − log(1+y†) meets hL1 (log\n"
        f"-- monotone) and hL2 (log x ≤ x − 1 at x = (1+y)/(1+y†), then s ≥ 1/(1+y†)).\n"
        f"theorem {name}_L_nonpos : ∀ y : ℝ, 0 < y → y ≤ {yd} → {Lf} ≤ 0 := by\n"
        f"  intro y hy h\n"
        f"  have := Real.log_le_log (by linarith) (by linarith : 1 + y ≤ 1 + {yd})\n"
        f"  linarith\n\n"
        f"theorem {name}_L_tangent :\n"
        f"    ∀ y : ℝ, {yd} < y → y ≤ 1 → {Lf} ≤ {s_} * (y - {yd}) := by\n"
        f"  intro y hy h\n"
        f"  have hpos : (0 : ℝ) < (1 + y) / (1 + {yd}) := div_pos (by linarith) (by norm_num)\n"
        f"  have h1 := Real.log_le_sub_one_of_pos hpos\n"
        f"  have h2 : Real.log ((1 + y) / (1 + {yd})) = Real.log (1 + y) - Real.log (1 + {yd}) :=\n"
        f"    Real.log_div (by linarith) (by norm_num)\n"
        f"  have h3 : (1 + y) / (1 + {yd}) - 1 = {inv} * (y - {yd}) := by ring\n"
        f"  linarith\n\n"
        f"-- {name}_concrete: hypothesis-free instance, U = min(0, segment lines) (below every\n"
        f"-- segment line, so it meets every U hypothesis) and L = log(1+y) − log(1+y†).\n"
        f"theorem {name}_concrete :\n"
        f"    ∀ m : ℕ, {pl.M + 1} ≤ m → ∀ y : ℝ, 0 < y → y ≤ 1 →\n"
        f"      (m : ℝ) * {Umin} + ({Lf}) ≤ 0 :=\n"
        f"  {name} (fun y => {Umin}) (fun y => {Lf})\n"
        + "".join(f"    ({p})\n" for p in u_proofs)
        + f"    {name}_L_nonpos {name}_L_tangent\n\n"
    )
    return out


@dataclass
class MonotoneRatioTailEmitter(Emitter):
    """Emit ``b(s) <= B for all s >= s0`` as three kernel-checkable pieces.

    Per instance:

      * ``<name>_step`` — the nonincreasing-step certificate
        ``0 <= 1 - r(s0 + t)`` for ``t >= 0`` (equivalently ``r(s0+t) <= 1``),
        a num/den Polya form discharged by ``positivity`` (robust, the
        ``DirectPolya`` idiom).
      * ``<name>_base`` — the base fact ``b(s0) <= B`` on an exact rational,
        by ``norm_num`` (robust).
      * ``<name>_tail`` — the assembled ``forall s, s0 <= s -> b s <= B`` over an
        ABSTRACT ``b : ℕ → ℝ``, via ``Nat.le_induction``, fed the two ingredients
        as hypotheses ``hstep`` (per-step nonincrease) and ``hbase``.  This is a
        genuine ``sorry``-free assembly; instantiating ``b`` at the concrete
        cavity form is documented as the remaining link (see module docstring).

    Deterministic ordering: grid order.
    """

    def __post_init__(self):
        self.kind = "monotone_tail"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n = 0
        for inst in fam.instances:
            pl: MonotoneTailPayload = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            if isinstance(pl, PLNodeTailPayload):
                lines.append(_emit_pl_node_tail(pl, name))
                n += 4 if pl.L == "log_tangent" else 1
                continue
            t = pl.t_symbol

            # --- (a) nonincreasing-step certificate: 0 <= 1 - r(s0 + t) --------
            cert = pl.step_cert
            step_body = expr_lean_from_parts(cert.numerator, cert.denominator, (t,))
            trivial_den = sp.simplify(cert.denominator - 1) == 0
            if trivial_den:
                step_thm = (
                    f"theorem {name}_step ({t} : ℝ) (h{t} : 0 ≤ {t}) :\n"
                    f"    0 ≤ {step_body} := by\n"
                    f"  positivity\n"
                )
            else:
                step_thm = (
                    f"theorem {name}_step ({t} : ℝ) (h{t} : 0 ≤ {t}) :\n"
                    f"    0 ≤ {step_body} := by\n"
                    f"  positivity\n"
                )
            lines.append(step_thm)
            n += 1

            # --- (b) base fact: b(s0) <= B on an exact rational ----------------
            base_s = rat_lean(pl.base_value)
            bound_s = rat_lean(pl.bound)
            lines.append(
                f"theorem {name}_base : ({base_s} : ℝ) ≤ {bound_s} := by norm_num\n"
            )
            n += 1

            # --- (c) assembled monotone-tail theorem (abstract b) --------------
            # Nat.le_induction from the anchor s0: b s0 <= B is the base; the
            # inductive step uses hstep (b (m+1) <= b m for m >= s0) to keep the
            # bound.  A genuine sorry-free assembly over an abstract positive
            # nonincreasing b; instantiating b at the concrete cavity form (whose
            # step is <name>_step and whose base is <name>_base) is the remaining
            # link — documented, not faked.
            lines.append(
                f"-- {name}: assembled monotone-tail bound over an abstract\n"
                f"-- b : ℕ → ℝ.  The two ingredients above ({name}_step : the\n"
                f"-- nonincreasing step r(s0+t) ≤ 1, and {name}_base : b(s0) ≤ B)\n"
                f"-- feed hstep and hbase.  Instantiating b at the concrete cavity\n"
                f"-- form is the remaining link (see module docstring).\n"
                f"theorem {name}_tail (b : ℕ → ℝ) (B : ℝ)\n"
                f"    (hstep : ∀ m, {pl.s0} ≤ m → b (m + 1) ≤ b m)\n"
                f"    (hbase : b {pl.s0} ≤ B) :\n"
                f"    ∀ s, {pl.s0} ≤ s → b s ≤ B := by\n"
                f"  intro s hs\n"
                f"  induction s, hs using Nat.le_induction with\n"
                f"  | base => exact hbase\n"
                f"  | succ m hm ih => exact le_trans (hstep m hm) ih\n"
            )
            n += 1
        return "".join(lines), n


# ---------------------------------------------------------------------------
# Convenience constructor
# ---------------------------------------------------------------------------

def monotone_tail_family(
    name: str,
    symbols: Sequence[sp.Symbol],
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a monotone-ratio tail family (kind='monotone_tail'), mirroring
    ``cone_family`` / ``lattice_box_family``.

    Parameters
    ----------
    name, grid, lean_name
        As for every family: name, the finite parameter grid, and a
        ``pt -> str`` Lean theorem-name map.
    symbols
        The free variables (typically empty for a pure integer-tail family; the
        tail variable ``s`` is supplied inside ``spec``, not here).
    spec
        A callable ``pt -> (b_expr, s0, bound, s_symbol)`` (or, for the
        piecewise-linear node-condition face, ``pt -> {"M", "nodes", "y_dag",
        "s", "L"}``, see ``pl_node_tail_certificate``) where ``b_expr`` is a
        sympy expression for the positive sequence ``b(s)`` in the integer symbol
        ``s_symbol``, ``s0`` the integer tail start, and ``bound`` the rational
        ``B``.  ``certify_monotone_tail_point`` derives ``r(s) = b(s+1)/b(s)``,
        Polya-certifies the nonincreasing tail ``0 <= 1 - r(s0 + t)``, checks
        ``b(s0) <= B`` exactly, and refuses (no Lean) otherwise.
    """
    return InequalityFamily(
        name=name,
        symbols=tuple(symbols),
        grid=grid,
        lean_name=lean_name,
        special=("monotone_tail", spec),
        constants=dict(constants or {}),
    )
