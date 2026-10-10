"""ScaledIntervalEval emitter (kind ``scaled_interval_eval``) -- kernel-computable
fixed-point interval evaluation of an expression DAG.

Shape (Part C, C1; prior art: OpenAI's ``openai/math`` Lean library, Apache-2.0,
``lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean``).  A real interval is
an integer pair ``(lo, hi)`` at a fixed scale ``S``: it encloses ``x`` when
``lo <= S*x <= hi``.  Every operation (add, neg, sub, mul, divNat, widen, square, a
Taylor sum, exp with argument reduction) is computable integer arithmetic with floor
division and a one-ulp outward round, and each has a ``mem_*`` soundness lemma proved
ONCE in the ``ScaledInterval`` prelude (:func:`scaled_interval_prelude_lean`).

Per instance the generator emits, for every DAG node ``k``:

* ``<n>_b<k> : RI := ⟨lo, hi⟩``  -- the literal box;
* ``<n>_v<k> : ℝ``                -- the node's real value (a noncomputable def);
* ``<n>_b<k>_calc : RI.subset (op <child boxes>) <n>_b<k> = true := by decide +kernel``
  -- the kernel re-runs the integer operation and checks containment;
* ``<n>_b<k>_mem : RI.Mem S <n>_b<k> (<n>_v<k> ..) := RI.mem_of_subset (RI.mem_op ..) _calc``;

and a final theorem stated over ℝ: ``lo <= f x /\\ f x <= hi`` (quantified over the
declared variables and their rational ranges), closed by ``RI.le_of_mem`` /
``RI.ge_of_mem`` against two more ``decide +kernel`` facts.

The Python fold mirrors the Lean integer semantics bit for bit (Lean's ``Int`` ``/`` is
Euclidean, which is floor division for the positive divisors used here), so the literal
boxes are exactly what the kernel computes; the checks are SUBSET checks anyway, so a
mismatch could only make a check fail, never make a false box pass.

Trust: the kernel recomputes every box, so nothing numeric is trusted from Python.  No
``native_decide``, no ``sorry``, no ``axiom``; no heartbeat overrides.

``conjecture1_proved = False``.  These are enclosures of explicit elementary
expressions at rational points or over rational boxes; nothing here is about RH.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from math import factorial
from typing import Callable, Mapping

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

#: Default scale: 40 decimal digits.
DEFAULT_SCALE = 10 ** 40
#: Argument-reduction cap: exp arguments with |x| > 2**MAX_EXP_K are refused.
MAX_EXP_K = 64
#: Taylor-order cap.
MAX_EXP_N = 400
#: Node cap for one instance (one file; sharding is future work).
MAX_NODES = 2000

# --------------------------------------------------------------------------------------
# The integer semantics -- an exact mirror of the Lean definitions in the prelude.
# A box is a pair (lo, hi) of Python ints.
# --------------------------------------------------------------------------------------


def sie_of_range(S: int, p1: int, q1: int, p2: int, q2: int) -> tuple[int, int]:
    """``RI.ofRange S p1 q1 p2 q2 = ⟨S*p1 / q1, S*p2 / q2 + 1⟩`` (floor division)."""
    return (S * p1 // q1, S * p2 // q2 + 1)


def sie_of_frac(S: int, p: int, q: int) -> tuple[int, int]:
    """``RI.ofFrac S p q = RI.ofRange S p q p q``."""
    return sie_of_range(S, p, q, p, q)


def sie_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sie_neg(a):
    return (-a[1], -a[0])


def sie_sub(a, b):
    return sie_add(a, sie_neg(b))


def sie_mul(S: int, a, b):
    """``RI.mul``: the four corner products, floor-divided by ``S``, plus one ulp above."""
    pr = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(pr) // S, max(pr) // S + 1)


def sie_divnat(a, n: int):
    return (a[0] // n, a[1] // n + 1)


def sie_widen(a, r: int):
    return (a[0] - r, a[1] + r)


def sie_square(S: int, a, k: int):
    """``RI.square S a k`` (``square a (k+1) = square (mul a a) k``)."""
    for _ in range(k):
        a = sie_mul(S, a, a)
    return a


def sie_taylor(S: int, a, n: int):
    """``RI.taylor S a n``: the boxes of ``x^n/n!`` and ``sum_{j<=n} x^j/j!``."""
    term, total = (S, S), (S, S)
    for i in range(n):
        term = sie_divnat(sie_mul(S, term, a), i + 1)
        total = sie_add(total, term)
    return term, total


def sie_exp_r(S: int, a, k: int, n: int, r: int):
    """``RI.expR S a k n r``."""
    red = sie_divnat(a, 2 ** k)
    return sie_square(S, sie_widen(sie_taylor(S, red, n)[1], r), k)


def sie_exp_small_ok(S: int, a, k: int) -> bool:
    red = sie_divnat(a, 2 ** k)
    return -S <= red[0] and red[1] <= S


def sie_exp_rem_ok(S: int, n: int, r: int) -> bool:
    return S * (n + 2) <= r * (factorial(n + 1) * (n + 1))


def sie_exp(S: int, a):
    """Choose ``(k, n, r)`` and return ``(box, (k, n, r))``.

    ``k`` is the least reduction with the reduced box inside ``[-S, S]``; ``n`` the least
    order whose ``Real.exp_bound`` remainder ``(n+2)/((n+1)!(n+1))`` is at most ``1/S``;
    ``r = 1``.  Raises ``ValueError`` (REFUSED) past the caps."""
    k = 0
    while not sie_exp_small_ok(S, a, k):
        k += 1
        if k > MAX_EXP_K:
            raise ValueError(
                f"scaled_interval_eval REFUSED: exp argument box {a} at scale {S} needs "
                f"more than {MAX_EXP_K} halvings")
    n, r = 1, 1
    while not sie_exp_rem_ok(S, n, r):
        n += 1
        if n > MAX_EXP_N:
            raise ValueError(
                f"scaled_interval_eval REFUSED: Taylor order above {MAX_EXP_N} at scale {S}")
    return sie_exp_r(S, a, k, n, r), (k, n, r)


# --------------------------------------------------------------------------------------
# The certificate.
# --------------------------------------------------------------------------------------

_OPS = ("const", "var", "add", "sub", "neg", "mul", "exp")
_IDENT = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")


@dataclass(frozen=True)
class SIENode:
    """One DAG node.  ``args`` are child indices; ``data`` is op-specific:
    const ``(p, q)``; var ``(name, p1, q1, p2, q2)``; exp ``(k, n, r)``; else ``()``.
    ``vars`` is the ordered tuple of variable names the subtree depends on."""

    op: str
    args: tuple[int, ...]
    data: tuple
    box: tuple[int, int]
    vars: tuple[str, ...]


@dataclass(frozen=True)
class ScaledIntervalEvalCert:
    scale: int
    var_ranges: tuple[tuple[str, sp.Rational, sp.Rational], ...]
    nodes: tuple[SIENode, ...]
    root: int
    claim_lo: sp.Rational
    claim_hi: sp.Rational


def _rat(v, what: str) -> sp.Rational:
    if isinstance(v, float) or isinstance(v, sp.Float):
        raise ValueError(f"scaled_interval_eval REFUSED: {what} is a float ({v!r}); "
                         "give an exact rational")
    try:
        q = sp.Rational(v)
    except (TypeError, ValueError):
        raise ValueError(f"scaled_interval_eval REFUSED: {what} {v!r} is not rational")
    if not isinstance(q, sp.Rational):
        raise ValueError(f"scaled_interval_eval REFUSED: {what} {v!r} is not rational")
    return q


class _Builder:
    def __init__(self, S: int, ranges: dict[str, tuple[sp.Rational, sp.Rational]],
                 order: list[str]):
        self.S = S
        self.ranges = ranges
        self.order = order
        self.nodes: list[SIENode] = []
        self.index: dict[tuple, int] = {}

    def _add(self, op, args, data, box) -> int:
        key = (op, args, data)
        if key in self.index:
            return self.index[key]
        used = set()
        for a in args:
            used.update(self.nodes[a].vars)
        if op == "var":
            used.add(data[0])
        vs = tuple(v for v in self.order if v in used)
        self.nodes.append(SIENode(op, args, data, box, vs))
        if len(self.nodes) > MAX_NODES:
            raise ValueError(f"scaled_interval_eval REFUSED: more than {MAX_NODES} nodes")
        self.index[key] = len(self.nodes) - 1
        return self.index[key]

    def box(self, i):
        return self.nodes[i].box

    def const(self, q: sp.Rational) -> int:
        p, d = int(q.p), int(q.q)
        return self._add("const", (), (p, d), sie_of_frac(self.S, p, d))

    def var(self, name: str) -> int:
        lo, hi = self.ranges[name]
        data = (name, int(lo.p), int(lo.q), int(hi.p), int(hi.q))
        return self._add("var", (), data, sie_of_range(self.S, *data[1:]))

    def binop(self, op, a, b) -> int:
        A, B = self.box(a), self.box(b)
        box = {"add": lambda: sie_add(A, B), "sub": lambda: sie_sub(A, B),
               "mul": lambda: sie_mul(self.S, A, B)}[op]()
        return self._add(op, (a, b), (), box)

    def neg(self, a) -> int:
        return self._add("neg", (a,), (), sie_neg(self.box(a)))

    def exp(self, a) -> int:
        box, (k, n, r) = sie_exp(self.S, self.box(a))
        return self._add("exp", (a,), (k, n, r), box)

    def build(self, e) -> int:
        if isinstance(e, sp.Float):
            raise ValueError(f"scaled_interval_eval REFUSED: float literal {e!r}")
        if e is sp.E:
            return self.exp(self.const(sp.Integer(1)))
        if isinstance(e, sp.Rational):
            return self.const(e)
        if isinstance(e, sp.Symbol):
            if e.name not in self.ranges:
                raise ValueError(f"scaled_interval_eval REFUSED: symbol {e.name!r} has no "
                                 "declared rational range")
            return self.var(e.name)
        if isinstance(e, sp.exp):
            return self.exp(self.build(e.args[0]))
        if isinstance(e, sp.Add):
            terms = list(e.args)
            acc = self.build(terms[0])
            for t in terms[1:]:
                c, _rest = t.as_coeff_Mul()
                if c < 0:
                    acc = self.binop("sub", acc, self.build(-t))
                else:
                    acc = self.binop("add", acc, self.build(t))
            return acc
        if isinstance(e, sp.Mul):
            c, rest = e.as_coeff_Mul()
            if c == -1:
                return self.neg(self.build(rest))
            factors = list(e.args)
            acc = self.build(factors[0])
            for f in factors[1:]:
                acc = self.binop("mul", acc, self.build(f))
            return acc
        if isinstance(e, sp.Pow):
            base, ex = e.args
            if base is sp.E:
                return self.exp(self.build(ex))
            if not (ex.is_Integer and int(ex) >= 1):
                raise ValueError(f"scaled_interval_eval REFUSED: power {e} needs a positive "
                                 "integer exponent")
            b = self.build(base)
            acc = b
            for _ in range(int(ex) - 1):
                acc = self.binop("mul", acc, b)
            return acc
        raise ValueError(f"scaled_interval_eval REFUSED: unsupported expression {e} "
                         f"({type(e).__name__}); supported: rationals, declared symbols, "
                         "+, -, *, positive integer powers, exp")


def scaled_interval_eval_certificate(expr, *, vars: Mapping | None = None,
                                     scale: int = DEFAULT_SCALE, lo=None, hi=None
                                     ) -> ScaledIntervalEvalCert:
    """Build the DAG of ``expr`` (a sympy expression), fold it at ``scale`` with the exact
    Lean integer semantics, and check the claimed enclosure.

    ``vars`` maps each symbol name to a rational range ``(lo, hi)``.  ``lo``/``hi`` are the
    claimed rational endpoints; when omitted, the claim is the root box over ``scale``.

    REFUSES: ``scale < 2``; a non-rational or inverted range; a declared variable that does
    not occur; an unsupported node; an exp argument past the reduction cap; an inverted
    claim; and a claim that does not contain the computed box (for example one ulp too
    tight) -- the same integer checks the kernel will decide."""
    S = int(scale)
    if S < 2:
        raise ValueError(f"scaled_interval_eval REFUSED: scale must be >= 2, got {scale}")
    ranges: dict[str, tuple[sp.Rational, sp.Rational]] = {}
    order: list[str] = []
    for name, (a, b) in (vars or {}).items():
        if not _IDENT.match(name) or name.startswith("h_"):
            raise ValueError(f"scaled_interval_eval REFUSED: bad variable name {name!r}")
        qa, qb = _rat(a, f"range lo of {name}"), _rat(b, f"range hi of {name}")
        if qa > qb:
            raise ValueError(f"scaled_interval_eval REFUSED: inverted range for {name}: "
                             f"[{qa}, {qb}]")
        ranges[name] = (qa, qb)
        order.append(name)
    e = sp.sympify(expr)
    builder = _Builder(S, ranges, order)
    root = builder.build(e)
    used = set(builder.nodes[root].vars)
    unused = [v for v in order if v not in used]
    if unused:
        raise ValueError(f"scaled_interval_eval REFUSED: declared variable(s) {unused} do not "
                         "occur in the expression (vacuous binder)")
    rlo, rhi = builder.nodes[root].box
    claim_lo = sp.Rational(rlo, S) if lo is None else _rat(lo, "claimed lo")
    claim_hi = sp.Rational(rhi, S) if hi is None else _rat(hi, "claimed hi")
    if claim_lo > claim_hi:
        raise ValueError(f"scaled_interval_eval REFUSED: inverted claim [{claim_lo}, {claim_hi}]")
    if not (S * claim_lo.p <= rlo * claim_lo.q):
        raise ValueError(
            f"scaled_interval_eval REFUSED: claimed lo {claim_lo} is above the computed box "
            f"lower end {rlo}/{S} -- the kernel's lowerOK check would fail")
    if not (rhi * claim_hi.q <= S * claim_hi.p):
        raise ValueError(
            f"scaled_interval_eval REFUSED: claimed hi {claim_hi} is below the computed box "
            f"upper end {rhi}/{S} -- the kernel's upperOK check would fail")
    return ScaledIntervalEvalCert(
        scale=S,
        var_ranges=tuple((n, ranges[n][0], ranges[n][1]) for n in order),
        nodes=tuple(builder.nodes), root=root, claim_lo=claim_lo, claim_hi=claim_hi)


def certify_scaled_interval_eval_point(family, pt, name):
    """``spec = family.special[1](pt)`` is a dict with ``expr`` and optional ``vars``,
    ``scale``, ``lo``, ``hi``.  Returns ``(CertifiedInstance, n_checks)`` where
    ``n_checks`` is the number of kernel-decided facts (one per node, two per exp node,
    plus the two claim checks)."""
    spec = dict(family.special[1](pt))
    expr = spec.pop("expr")
    cert = scaled_interval_eval_certificate(expr, **spec)
    n_checks = sum(3 if nd.op == "exp" else 1 for nd in cert.nodes) + 2
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, n_checks


# --------------------------------------------------------------------------------------
# Lean rendering.
# --------------------------------------------------------------------------------------

def _int(v: int) -> str:
    return str(v) if v >= 0 else f"({v})"


def _real_rat(q: sp.Rational) -> str:
    """A rational as a real literal: ``(2 : ℝ)``, ``((1 : ℝ) / 3)``, ``((-1 : ℝ) / 3)``."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"({q.p} : ℝ)"
    return f"(({q.p} : ℝ) / {q.q})"


def _tree_text(cert: ScaledIntervalEvalCert, k: int) -> str:
    nd = cert.nodes[k]
    a = [_tree_text(cert, i) for i in nd.args]
    if nd.op == "const":
        return _real_rat(sp.Rational(nd.data[0], nd.data[1]))
    if nd.op == "var":
        return nd.data[0]
    if nd.op == "add":
        return f"({a[0]} + {a[1]})"
    if nd.op == "sub":
        return f"({a[0]} - {a[1]})"
    if nd.op == "mul":
        return f"({a[0]} * {a[1]})"
    if nd.op == "neg":
        return f"(-{a[0]})"
    if nd.op == "exp":
        return f"(Real.exp {a[0]})"
    raise ValueError(nd.op)


def _statement(cert: ScaledIntervalEvalCert) -> str:
    """The final theorem's type, single-sourced for the statement gate."""
    body = _tree_text(cert, cert.root)
    concl = f"{_real_rat(cert.claim_lo)} ≤ {body} ∧ {body} ≤ {_real_rat(cert.claim_hi)}"
    binders = "".join(
        f"∀ {n} : ℝ, {_real_rat(lo)} ≤ {n} → {n} ≤ {_real_rat(hi)} → "
        for n, lo, hi in cert.var_ranges)
    return binders + concl


def _render_instance(cert: ScaledIntervalEvalCert, p: str) -> tuple[list[str], int]:
    S = f"{p}_S"
    hS = f"{p}_hS"
    L: list[str] = []
    n_thm = 0
    ranges = {n: (lo, hi) for n, lo, hi in cert.var_ranges}

    def app(k: int, kind: str) -> str:
        nd = cert.nodes[k]
        if kind == "v":
            args = "".join(f" {v}" for v in nd.vars)
            return f"({p}_v{k}{args})" if nd.vars else f"{p}_v{k}"
        args = "".join(f" {v} h_{v}_lo h_{v}_hi" for v in nd.vars)
        return f"({p}_b{k}_mem{args})" if nd.vars else f"{p}_b{k}_mem"

    L.append(f"-- {p}: scaled_interval_eval at scale S = {cert.scale} "
             f"({len(cert.nodes)} nodes).  Every box is recomputed by the kernel "
             "(decide +kernel); the mem_* lemmas lift it to ℝ.  conjecture1_proved = False.")
    L.append(f"def {S} : ℤ := {cert.scale}")
    L.append(f"theorem {hS} : (0 : ℤ) < {S} := by decide +kernel")
    n_thm += 1
    for k, nd in enumerate(cert.nodes):
        b = f"{p}_b{k}"
        L.append(f"def {b} : RI := ⟨{_int(nd.box[0])}, {_int(nd.box[1])}⟩")
        vbind = "".join(f" ({v} : ℝ)" for v in nd.vars)
        cb = [f"{p}_b{i}" for i in nd.args]
        cv = [app(i, "v") for i in nd.args]
        cm = [app(i, "m") for i in nd.args]
        if nd.op == "const":
            val = _real_rat(sp.Rational(nd.data[0], nd.data[1]))
            op_term = f"RI.ofFrac {S} {_int(nd.data[0])} {nd.data[1]}"
            mem = f"RI.mem_ofFrac {hS} (by norm_num) (by norm_num [{p}_v{k}])"
        elif nd.op == "var":
            name, p1, q1, p2, q2 = nd.data
            val = name
            op_term = f"RI.ofRange {S} {_int(p1)} {q1} {_int(p2)} {q2}"
            mem = (f"RI.mem_ofRange {hS} (by norm_num) (by norm_num) (by norm_num) "
                   f"(by norm_num) h_{name}_lo h_{name}_hi")
        elif nd.op in ("add", "sub", "mul"):
            sym = {"add": "+", "sub": "-", "mul": "*"}[nd.op]
            val = f"{cv[0]} {sym} {cv[1]}"
            if nd.op == "mul":
                op_term = f"RI.mul {S} {cb[0]} {cb[1]}"
                mem = f"RI.mem_mul {hS} {cm[0]} {cm[1]}"
            else:
                op_term = f"RI.{nd.op} {cb[0]} {cb[1]}"
                mem = f"RI.mem_{nd.op} {cm[0]} {cm[1]}"
        elif nd.op == "neg":
            val = f"-{cv[0]}"
            op_term = f"RI.neg {cb[0]}"
            mem = f"RI.mem_neg {cm[0]}"
        elif nd.op == "exp":
            kk, n, r = nd.data
            val = f"Real.exp {cv[0]}"
            op_term = f"RI.expR {S} {cb[0]} {kk} {n} {r}"
            L.append(f"theorem {b}_small : RI.expSmallOK {S} {cb[0]} {kk} = true := by "
                     "decide +kernel")
            L.append(f"theorem {b}_rem : RI.expRemOK {S} {n} {r} = true := by decide +kernel")
            n_thm += 2
            mem = f"RI.mem_expR {hS} {cm[0]} {b}_small {b}_rem"
        else:  # pragma: no cover -- the builder only makes _OPS
            raise ValueError(nd.op)
        L.append(f"noncomputable def {p}_v{k}{vbind} : ℝ := {val}")
        L.append(f"theorem {b}_calc : RI.subset ({op_term}) {b} = true := by decide +kernel")
        hyps = "".join(
            f" ({v} : ℝ) (h_{v}_lo : {_real_rat(ranges[v][0])} ≤ {v})"
            f" (h_{v}_hi : {v} ≤ {_real_rat(ranges[v][1])})" for v in nd.vars)
        L.append(f"theorem {b}_mem{hyps} : RI.Mem {S} {b} {app(k, 'v')} :=\n"
                 f"  RI.mem_of_subset ({mem}) {b}_calc")
        n_thm += 2
    root = cert.root
    rb = f"{p}_b{root}"
    lo, hi = cert.claim_lo, cert.claim_hi
    L.append(f"theorem {p}_lo_calc : RI.lowerOK {S} {rb} {_int(int(lo.p))} {int(lo.q)} = true "
             ":= by decide +kernel")
    L.append(f"theorem {p}_hi_calc : RI.upperOK {S} {rb} {_int(int(hi.p))} {int(hi.q)} = true "
             ":= by decide +kernel")
    n_thm += 2
    stmt = _statement(cert)
    body = _tree_text(cert, root)
    intro = "".join(f" {n} h_{n}_lo h_{n}_hi" for n, _, _ in cert.var_ranges)
    L.append(
        f"/-- `{p}`: the kernel-checked enclosure (exact-evaluated pre-emission). -/\n"
        f"theorem {p} : {stmt} := by\n"
        + (f"  intro{intro}\n" if intro else "")
        + f"  have h : RI.Mem {S} {rb} {body} := {app(root, 'm')}\n"
        f"  exact ⟨RI.le_of_mem {hS} h (by norm_num) (by norm_num) {p}_lo_calc,\n"
        f"    RI.ge_of_mem {hS} h (by norm_num) (by norm_num) {p}_hi_calc⟩")
    n_thm += 1
    return L, n_thm


@dataclass
class ScaledIntervalEvalEmitter(Emitter):
    """Emit literal boxes, per-node ``_calc`` (``decide +kernel``) and ``_mem`` lemmas, and
    the final real enclosure, against the ``ScaledInterval`` prelude (import it, or splice
    :func:`scaled_interval_prelude_body`)."""

    def __post_init__(self):
        self.kind = "scaled_interval_eval"
        self.requires_prelude = (
            "ScaledInterval.RI.mem_of_subset",
            "ScaledInterval.RI.mem_expR",
            "ScaledInterval.RI.le_of_mem",
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = ["open ScaledInterval", ""]
        n_thm = 0
        for inst in fam.instances:
            cert: ScaledIntervalEvalCert = inst.payload  # type: ignore[assignment]
            L, n = _render_instance(cert, inst.lean_name)
            lines.extend(L)
            lines.append(self.emit_gate(inst.lean_name, _statement(cert)))
            n_thm += n
        return "\n".join(lines) + "\n", n_thm


def scaled_interval_eval_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a scaled-interval-eval family (kind ``scaled_interval_eval``).

    ``spec: pt -> dict(expr=<sympy expr>, vars={name: (lo, hi)}, scale=S, lo=.., hi=..)``
    (all but ``expr`` optional).  Certification folds the DAG exactly in Python; the Lean
    kernel recomputes every box."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("scaled_interval_eval", spec),
        constants=dict(constants or {}),
    )


def scaled_interval_prelude_lean() -> str:
    """The full ``ScaledInterval.lean`` module text (header, ``import Mathlib``, body)."""
    return _PRELUDE


def scaled_interval_prelude_body() -> str:
    """The prelude without its ``import`` line, for splicing after the imports of a
    self-contained file (the negative-control harness's ``prelude``)."""
    return _PRELUDE.replace("import Mathlib\n", "", 1)


# The ScaledInterval prelude (single source; examples/scaled_interval_eval/generate.py writes it).
_PRELUDE = r'''/-
ScaledInterval -- the fixed-scale integer interval kernel behind Telperion's
`scaled_interval_eval` emitter.

Adapted from OpenAI's `openai/math` Lean library (Apache-2.0),
https://github.com/openai/math, file
`lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean`
(namespace `AtomicTriangular.Interval`: `RI`, `RI.Mem`, `add/neg/sub/mul/divNat/widen`,
their `mem_*` lemmas, `CI.taylor`, `CI.square`, `CI.exp`, `RI.mem_of_subset`).
Changes from the source: the scale `S` is a parameter rather than the constant `10^60`;
real intervals only; `exp` closes its Taylor remainder with Mathlib's `Real.exp_bound`
against an emitter-chosen widen `r` (checked by `decide`); Bool checks
(`subset`, `lowerOK`, `upperOK`, `expSmallOK`, `expRemOK`) so per-node facts are
decided by the kernel and lifted to `ℝ` by a once-proved soundness lemma.

Every operation is computable `ℤ` arithmetic with floor division and a one-ulp
outward round, so `decide +kernel` evaluates it on literal boxes.

conjecture1_proved = False.
-/
import Mathlib

namespace ScaledInterval

/-- A real interval at scale `S`: `(lo, hi)` encloses `x` when `lo ≤ S·x ≤ hi`. -/
structure RI where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

/-- `a` encloses `x` at scale `S`. -/
def RI.Mem (S : ℤ) (a : RI) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (S : ℝ) * x ∧ (S : ℝ) * x ≤ a.hi

/-! ### Operations (computable, kernel-reducible) -/

/-- The box of every `x ∈ [p₁/q₁, p₂/q₂]` (floor below, floor + 1 above). -/
def RI.ofRange (S p₁ : ℤ) (q₁ : ℕ) (p₂ : ℤ) (q₂ : ℕ) : RI :=
  ⟨S * p₁ / (q₁ : ℤ), S * p₂ / (q₂ : ℤ) + 1⟩

/-- The box of the rational `p / q`. -/
def RI.ofFrac (S p : ℤ) (q : ℕ) : RI := RI.ofRange S p q p q

def RI.add (a b : RI) : RI := ⟨a.lo + b.lo, a.hi + b.hi⟩
def RI.neg (a : RI) : RI := ⟨-a.hi, -a.lo⟩
def RI.sub (a b : RI) : RI := a.add b.neg

def imin4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def imax4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

/-- Product at scale `S`: the four corner products, floor-divided by `S`, plus one ulp. -/
def RI.mul (S : ℤ) (a b : RI) : RI :=
  ⟨imin4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi) / S,
   imax4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi) / S + 1⟩

def RI.divNat (a : RI) (n : ℕ) : RI := ⟨a.lo / (n : ℤ), a.hi / (n : ℤ) + 1⟩
def RI.widen (a : RI) (r : ℤ) : RI := ⟨a.lo - r, a.hi + r⟩

/-- `k` repeated squarings. -/
def RI.square (S : ℤ) (a : RI) : ℕ → RI
  | 0 => a
  | k + 1 => RI.square S (RI.mul S a a) k

/-- `(x^n / n!, ∑_{j ≤ n} x^j / j!)` enclosures. -/
def RI.taylor (S : ℤ) (a : RI) : ℕ → RI × RI
  | 0 => (⟨S, S⟩, ⟨S, S⟩)
  | n + 1 =>
    let p := RI.taylor S a n
    let t := (RI.mul S p.1 a).divNat (n + 1)
    (t, p.2.add t)

/-- `exp` by argument reduction `x / 2^k`, the order-`n` Taylor sum, an `r`-ulp
remainder widen, and `k` squarings. -/
def RI.expR (S : ℤ) (a : RI) (k n : ℕ) (r : ℤ) : RI :=
  RI.square S (((a.divNat (2 ^ k)).taylor S n).2.widen r) k

/-! ### Bool checks (decided per instance by `decide +kernel`) -/

def RI.subset (a b : RI) : Bool := decide (b.lo ≤ a.lo) && decide (a.hi ≤ b.hi)
def RI.lowerOK (S : ℤ) (a : RI) (p : ℤ) (q : ℕ) : Bool := decide (S * p ≤ a.lo * (q : ℤ))
def RI.upperOK (S : ℤ) (a : RI) (p : ℤ) (q : ℕ) : Bool := decide (a.hi * (q : ℤ) ≤ S * p)
/-- The reduced argument lies in `[-1, 1]`. -/
def RI.expSmallOK (S : ℤ) (a : RI) (k : ℕ) : Bool :=
  decide (-S ≤ (a.divNat (2 ^ k)).lo) && decide ((a.divNat (2 ^ k)).hi ≤ S)
/-- `r / S` dominates the `Real.exp_bound` remainder of the order-`(n+1)` partial sum. -/
def RI.expRemOK (S : ℤ) (n : ℕ) (r : ℤ) : Bool :=
  decide (S * ((n + 2 : ℕ) : ℤ) ≤ r * (((n + 1).factorial * (n + 1) : ℕ) : ℤ))

/-! ### Soundness (`mem_*`), each proved once -/

section
variable {S : ℤ}

lemma div_floor_bounds (a n : ℤ) (hn : 0 < n) :
    ((a / n : ℤ) : ℝ) * (n : ℝ) ≤ a ∧ (a : ℝ) ≤ ((a / n + 1 : ℤ) : ℝ) * (n : ℝ) := by
  constructor
  · exact_mod_cast Int.ediv_mul_le a (ne_of_gt hn)
  · exact_mod_cast (Int.lt_ediv_add_one_mul_self a hn).le

theorem RI.mem_ofRange (hS : 0 < S) {p₁ p₂ : ℤ} {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    {l u x : ℝ} (hl : l = (p₁ : ℝ) / (q₁ : ℝ)) (hu : u = (p₂ : ℝ) / (q₂ : ℝ))
    (h₁ : l ≤ x) (h₂ : x ≤ u) : (RI.ofRange S p₁ q₁ p₂ q₂).Mem S x := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hq₁' : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂' : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have A := (div_floor_bounds (S * p₁) q₁ (by exact_mod_cast hq₁)).1
  have B := (div_floor_bounds (S * p₂) q₂ (by exact_mod_cast hq₂)).2
  push_cast at A B
  subst hl hu
  constructor
  · show ((S * p₁ / (q₁ : ℤ) : ℤ) : ℝ) ≤ (S : ℝ) * x
    have h1 : ((S * p₁ / (q₁ : ℤ) : ℤ) : ℝ) ≤ (S : ℝ) * p₁ / q₁ := by
      rw [le_div_iff₀ hq₁']; exact A
    calc _ ≤ (S : ℝ) * p₁ / q₁ := h1
      _ = (S : ℝ) * ((p₁ : ℝ) / q₁) := by ring
      _ ≤ (S : ℝ) * x := by gcongr
  · show (S : ℝ) * x ≤ ((S * p₂ / (q₂ : ℤ) + 1 : ℤ) : ℝ)
    have h1 : (S : ℝ) * p₂ / q₂ ≤ ((S * p₂ / (q₂ : ℤ) + 1 : ℤ) : ℝ) := by
      rw [div_le_iff₀ hq₂']; push_cast; exact B
    calc (S : ℝ) * x ≤ (S : ℝ) * ((p₂ : ℝ) / q₂) := by gcongr
      _ = (S : ℝ) * p₂ / q₂ := by ring
      _ ≤ _ := h1

theorem RI.mem_ofFrac (hS : 0 < S) {p : ℤ} {q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : x = (p : ℝ) / (q : ℝ)) : (RI.ofFrac S p q).Mem S x :=
  RI.mem_ofRange hS hq hq hx hx le_rfl le_rfl

theorem RI.mem_add {a b : RI} {x y : ℝ} (hx : a.Mem S x) (hy : b.Mem S y) :
    (a.add b).Mem S (x + y) := by
  rcases hx with ⟨hx₀, hx₁⟩; rcases hy with ⟨hy₀, hy₁⟩
  constructor <;> simp only [RI.add, Int.cast_add] <;> linarith

theorem RI.mem_neg {a : RI} {x : ℝ} (hx : a.Mem S x) : a.neg.Mem S (-x) := by
  rcases hx with ⟨hx₀, hx₁⟩
  constructor <;> simp only [RI.neg, Int.cast_neg] <;> linarith

theorem RI.mem_sub {a b : RI} {x y : ℝ} (hx : a.Mem S x) (hy : b.Mem S y) :
    (a.sub b).Mem S (x - y) := by
  simpa [RI.sub, sub_eq_add_neg] using RI.mem_add hx (RI.mem_neg hy)

lemma mul_bounds {a b x t : ℝ} (h : a ≤ x ∧ x ≤ b) :
    min (a * t) (b * t) ≤ x * t ∧ x * t ≤ max (a * t) (b * t) := by
  rcases le_total 0 t with ht | ht
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h.1 ht),
      (mul_le_mul_of_nonneg_right h.2 ht).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h.2 ht),
      (mul_le_mul_of_nonpos_right h.1 ht).trans (le_max_left _ _)⟩

lemma four_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hxy := mul_bounds (t := y) hx
  have ha := mul_bounds (t := a) hy
  have hb := mul_bounds (t := b) hy
  simp only [mul_comm c, mul_comm d, mul_comm y] at ha hb
  constructor
  · apply le_trans _ hxy.1
    exact le_min ((min_le_left _ _).trans ha.1) ((min_le_right _ _).trans hb.1)
  · apply le_trans hxy.2
    exact max_le (ha.2.trans (le_max_left _ _)) (hb.2.trans (le_max_right _ _))

theorem RI.mem_mul (hS : 0 < S) {a b : RI} {x y : ℝ} (hx : a.Mem S x) (hy : b.Mem S y) :
    (RI.mul S a b).Mem S (x * y) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hh := four_bounds hx hy
  have hl := (div_floor_bounds (imin4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi))
    S hS).1
  have hu := (div_floor_bounds (imax4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi))
    S hS).2
  simp only [imin4, imax4, Int.cast_min, Int.cast_max, Int.cast_mul] at hl hu
  have e : ((S : ℝ) * x) * ((S : ℝ) * y) = (S : ℝ) * ((S : ℝ) * (x * y)) := by ring
  constructor
  · apply (mul_le_mul_iff_right₀ hS').mp
    dsimp only [RI.mul, imin4, imax4]
    rw [← e, mul_comm]
    exact hl.trans hh.1
  · apply (mul_le_mul_iff_right₀ hS').mp
    dsimp only [RI.mul, imin4, imax4]
    rw [← e, mul_comm (S : ℝ) (((_ : ℤ) : ℝ))]
    exact hh.2.trans hu

theorem RI.mem_divNat {a : RI} {x : ℝ} (hx : a.Mem S x) {n : ℕ} (hn : 0 < n) :
    (a.divNat n).Mem S (x / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnl : (0 : ℤ) < n := by exact_mod_cast hn
  have hl := (div_floor_bounds a.lo n hnl).1
  have hu := (div_floor_bounds a.hi n hnl).2
  push_cast at hl hu
  constructor
  · show ((a.lo / (n : ℤ) : ℤ) : ℝ) ≤ (S : ℝ) * (x / n)
    rw [← mul_div_assoc, le_div_iff₀ hn']
    exact hl.trans hx.1
  · show (S : ℝ) * (x / n) ≤ ((a.hi / (n : ℤ) + 1 : ℤ) : ℝ)
    rw [← mul_div_assoc, div_le_iff₀ hn']
    push_cast
    exact hx.2.trans hu

theorem RI.mem_widen (hS : 0 < S) {a : RI} {x y : ℝ} {r : ℤ} (hx : a.Mem S x)
    (hxy : |y - x| ≤ (r : ℝ) / (S : ℝ)) : (a.widen r).Mem S y := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hh := abs_le.mp hxy
  have hl := (div_le_iff₀ hS').mp
    (show -(r : ℝ) / (S : ℝ) ≤ y - x by simpa only [neg_div] using hh.1)
  have hu := (le_div_iff₀ hS').mp hh.2
  rcases hx with ⟨hx₀, hx₁⟩
  constructor <;> simp only [RI.widen, Int.cast_sub, Int.cast_add] <;> nlinarith

theorem RI.mem_square (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) (k : ℕ) :
    (RI.square S a k).Mem S (x ^ (2 ^ k)) := by
  induction k generalizing a x with
  | zero => simpa [RI.square] using hx
  | succ k ih =>
    have h := ih (RI.mem_mul hS hx hx)
    rw [RI.square]
    have e : (x * x) ^ (2 ^ k) = x ^ (2 ^ (k + 1)) := by
      rw [← pow_two, ← pow_mul, pow_succ, mul_comm (2 ^ k) 2]
    rwa [e] at h

theorem RI.mem_one : (⟨S, S⟩ : RI).Mem S 1 := by
  constructor <;> simp

theorem RI.mem_taylor (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) (n : ℕ) :
    (RI.taylor S a n).1.Mem S (x ^ n / (n.factorial : ℝ)) ∧
    (RI.taylor S a n).2.Mem S (∑ j ∈ Finset.range (n + 1), x ^ j / (j.factorial : ℝ)) := by
  induction n with
  | zero => simpa [RI.taylor] using And.intro (RI.mem_one (S := S)) (RI.mem_one (S := S))
  | succ n ih =>
    have hf : x ^ (n + 1) / ((n + 1).factorial : ℝ) =
        (x ^ n / (n.factorial : ℝ)) * x / ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      field_simp
    have ht := RI.mem_divNat (RI.mem_mul hS ih.1 hx) (Nat.succ_pos n)
    constructor
    · rw [hf]; exact ht
    · rw [Finset.sum_range_succ, hf]
      exact RI.mem_add ih.2 ht

theorem RI.mem_of_subset {a b : RI} {x : ℝ} (hx : a.Mem S x) (h : RI.subset a b = true) :
    b.Mem S x := by
  simp only [RI.subset, Bool.and_eq_true, decide_eq_true_eq] at h
  have hl' : (b.lo : ℝ) ≤ a.lo := by exact_mod_cast h.1
  have hu' : (a.hi : ℝ) ≤ b.hi := by exact_mod_cast h.2
  exact ⟨hl'.trans hx.1, hx.2.trans hu'⟩

theorem RI.le_of_mem (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) {p : ℤ} {q : ℕ}
    (hq : 0 < q) {l : ℝ} (hl : l = (p : ℝ) / (q : ℝ)) (h : RI.lowerOK S a p q = true) :
    l ≤ x := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [RI.lowerOK, decide_eq_true_eq] at h
  have h' : (S : ℝ) * p ≤ (a.lo : ℝ) * q := by exact_mod_cast h
  subst hl
  rw [div_le_iff₀ hq']
  have : (S : ℝ) * (p : ℝ) ≤ (S : ℝ) * (x * q) := by nlinarith [hx.1]
  exact le_of_mul_le_mul_left this hS'

theorem RI.ge_of_mem (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) {p : ℤ} {q : ℕ}
    (hq : 0 < q) {u : ℝ} (hu : u = (p : ℝ) / (q : ℝ)) (h : RI.upperOK S a p q = true) :
    x ≤ u := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [RI.upperOK, decide_eq_true_eq] at h
  have h' : (a.hi : ℝ) * q ≤ (S : ℝ) * p := by exact_mod_cast h
  subst hu
  rw [le_div_iff₀ hq']
  have : (S : ℝ) * (x * q) ≤ (S : ℝ) * (p : ℝ) := by nlinarith [hx.2]
  exact le_of_mul_le_mul_left this hS'

theorem RI.mem_expR (hS : 0 < S) {a : RI} {x : ℝ} (hx : a.Mem S x) {k n : ℕ} {r : ℤ}
    (hsmall : RI.expSmallOK S a k = true) (hrem : RI.expRemOK S n r = true) :
    (RI.expR S a k n r).Mem S (Real.exp x) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hd := RI.mem_divNat hx (show 0 < 2 ^ k from Nat.two_pow_pos k)
  set y : ℝ := x / ((2 ^ k : ℕ) : ℝ) with hy_def
  -- the reduced argument is in [-1, 1]
  have hy : |y| ≤ 1 := by
    simp only [RI.expSmallOK, Bool.and_eq_true, decide_eq_true_eq] at hsmall
    have h1 : (-(S : ℝ)) ≤ ((a.divNat (2 ^ k)).lo : ℝ) := by exact_mod_cast hsmall.1
    have h2 : ((a.divNat (2 ^ k)).hi : ℝ) ≤ (S : ℝ) := by exact_mod_cast hsmall.2
    rw [abs_le]
    constructor <;> nlinarith [hd.1, hd.2]
  have ht := (RI.mem_taylor hS hd n).2
  have hb := Real.exp_bound hy (n := n + 1) (Nat.succ_pos n)
  have hr : (S : ℝ) * ((n + 2 : ℕ) : ℝ) ≤ (r : ℝ) * (((n + 1).factorial * (n + 1) : ℕ) : ℝ) := by
    simp only [RI.expRemOK, decide_eq_true_eq] at hrem
    exact_mod_cast hrem
  have hF : (0 : ℝ) < (((n + 1).factorial * (n + 1) : ℕ) : ℝ) := by positivity
  have herr : |Real.exp y - ∑ j ∈ Finset.range (n + 1), y ^ j / (j.factorial : ℝ)| ≤
      (r : ℝ) / (S : ℝ) := by
    refine hb.trans ?_
    have hpow : |y| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
    have hq : (((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ)) ≤
        (r : ℝ) / (S : ℝ) := by
      rw [div_le_div_iff₀ (by push_cast; positivity) hS']
      have e1 : (((n + 1).succ : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
      have e2 : (((n + 1).factorial : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) =
          (((n + 1).factorial * (n + 1) : ℕ) : ℝ) := by push_cast; ring
      rw [e1, e2]; linarith
    have hnn : (0 : ℝ) ≤ (((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ)) := by
      positivity
    calc |y| ^ (n + 1) * ((((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ)))
        ≤ 1 * ((((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℕ) * ((n + 1 : ℕ) : ℝ))) := by
          gcongr
      _ ≤ (r : ℝ) / (S : ℝ) := by rw [one_mul]; exact hq
  have hw := RI.mem_widen hS ht herr
  have hsq := RI.mem_square hS hw k
  have hpow : Real.exp y ^ (2 ^ k) = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hy_def]
    field_simp
  rw [hpow] at hsq
  exact hsq

end

end ScaledInterval
'''
