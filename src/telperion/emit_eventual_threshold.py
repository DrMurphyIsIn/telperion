"""EventualScalingThreshold emitter — "holds for all sufficiently large scale"
with a computed max-of-ratios witness, distilled from the OpenAI Navier--Stokes
blowup formalization (``github.com/openai/NavierStokesAndEuler``,
``NavierStokes/ConeAlgebra.lean`` ``sufficiently_large_amplitude_cone``,
Apache-2.0).

No prior kind produces EXISTENTIAL large-scale certificates (``monotone_tail``
is sequence tails, ``affine_param_endpoint`` is box endpoints).  The generic
core of the source's cone theorem: for finitely many affine threshold
conditions ``aᵢ < p·cᵢ`` with positive slopes, the explicit witness
``p₀ = max(a₁/c₁, …, aₙ/cₙ)`` makes ALL of them hold for every ``p > p₀``:

    ∃ p₀, ∀ p > p₀,  a₁ < p·c₁ ∧ … ∧ aₙ < p·cₙ,

each conjunct by ``div_lt_iff₀`` + a ``le_max`` chain.  Per-instance data: the
arity ``n ∈ [1, 6]`` (the aᵢ, cᵢ are fully symbolic theorem variables with
``0 < cᵢ`` hypotheses).  Domain-specific consequents (the source's
``coneBound``) then compose downstream, e.g. with ``sqrt_root_elimination``.

HONESTY SEAM: the slope positivity is a HYPOTHESIS; the kernel certifies the
witness assembly.

QUADRATIC SIGN RACE face (``QuadraticSignRaceCert``).  The concrete integer
counterpart: for a quadratic ``P(m) = a·m² + b·m + c`` with rational
coefficients, certify its exact sign pattern on the integers ``m ≥ m₀`` with an
explicit switch point, hypothesis-free:

* ``switch``   (``a > 0``): ``P(m) < 0`` for ``m₀ ≤ m ≤ r`` and ``P(m) > 0`` for
  ``m ≥ r+1`` — the eventual threshold ``r+1`` is SHARP;
* ``positive`` (``a > 0``): ``P(m) > 0`` for all ``m ≥ m₀``;
* ``negative`` (``a < 0``): ``P(m) < 0`` for all ``m ≥ m₀``;

each with the corollary ``P(m) ≠ 0`` for every integer ``m ≥ m₀``.  The
certificate is the vertex condition ``-b/(2a) ≤ m₀`` (``P`` monotone on
``[m₀, ∞)``) plus the endpoint signs ``P(r) < 0 < P(r+1)`` (resp. the sign of
``P(m₀)``).  The kernel re-checks it through two ``ring`` identities with the
certificate's literals baked in: the Taylor expansion at the anchor ``k``,
``P(m) = a(m−k)² + P'(k)(m−k) + P(k)``, whose three summands are sign-definite
(``mul_nonneg`` + ``norm_num``), and, for the head of a switch, the difference
``P(r) − P(m) = (r−m)(a(r+m)+b)``.

Why here (not ``sturm_positive`` or ``tails``): ``sturm_positive`` is bounded-
interval root exclusion via Bernstein, and ``tails.py`` wraps a Polya
certificate on a shifted variable.  This face is an eventual-threshold claim
("holds for all sufficiently large m") with an explicit, computed witness, and it
also certifies the complementary sign below the witness.  The quadratic sign race
pattern is distilled from unpublished work communicated by Professor John L.
Goldwasser; only the generic pattern is used.

``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class EventualThresholdCert:
    """The arity ``n ∈ [1, 6]`` of the conjunction."""

    n: int


@dataclass(frozen=True)
class QuadraticSignRaceCert:
    """Sign pattern of ``P(m) = a·m² + b·m + c`` on the integers ``m ≥ m0``.

    ``mode`` is ``"switch"`` (negative on ``[m0, r]``, positive from ``r+1``),
    ``"positive"`` or ``"negative"`` (one sign throughout).  ``r`` is set only for
    ``switch``.  ``anchor`` is the tail anchor ``k`` (``r+1`` or ``m0``) and
    ``slope`` / ``value`` are ``P'(k) = 2ak+b`` and ``P(k)``, the literals of the
    kernel's Taylor identity.  ``head_value`` is ``P(r)`` (switch only)."""

    mode: str
    a: sp.Rational
    b: sp.Rational
    c: sp.Rational
    m0: int
    r: int | None
    anchor: int
    slope: sp.Rational
    value: sp.Rational
    head_value: sp.Rational | None = None


def _quad_eval(a, b, c, m):
    return a * m * m + b * m + c


def quadratic_sign_race_certificate(a, b, c, m0, mode, r=None) -> QuadraticSignRaceCert:
    """Build and EXACTLY self-check a quadratic sign race (exact over ℚ).

    REFUSED (``ValueError``) unless: ``a ≠ 0`` with the sign the mode needs
    (``a > 0`` for switch/positive, ``a < 0`` for negative); the vertex
    ``-b/(2a) ≤ m0`` (so ``P`` is monotone on ``[m0, ∞)``); and the endpoint signs
    ``P(r) < 0 < P(r+1)`` with ``m0 ≤ r`` (switch), ``P(m0) > 0`` (positive),
    ``P(m0) < 0`` (negative)."""
    a, b, c = sp.Rational(a), sp.Rational(b), sp.Rational(c)
    m0 = int(m0)
    if mode not in ("switch", "positive", "negative"):
        raise ValueError(f"quadratic_sign_race REFUSED: unknown mode {mode!r}")
    if a == 0:
        raise ValueError("quadratic_sign_race REFUSED: a = 0 (not a quadratic)")
    if mode in ("switch", "positive") and not a > 0:
        raise ValueError(f"quadratic_sign_race REFUSED: mode {mode} needs a > 0, got {a}")
    if mode == "negative" and not a < 0:
        raise ValueError(f"quadratic_sign_race REFUSED: mode negative needs a < 0, got {a}")
    vertex = -b / (2 * a)
    if not vertex <= m0:
        raise ValueError(
            f"quadratic_sign_race REFUSED: vertex -b/(2a) = {vertex} > m0 = {m0}; "
            "P is not monotone on [m0, oo)")
    head = None
    if mode == "switch":
        if r is None or int(r) < m0:
            raise ValueError(f"quadratic_sign_race REFUSED: switch needs r >= m0, got r = {r}")
        r = int(r)
        head = _quad_eval(a, b, c, r)
        if not head < 0:
            raise ValueError(f"quadratic_sign_race REFUSED: P({r}) = {head} is not < 0")
        k = r + 1
    else:
        if r is not None:
            raise ValueError(f"quadratic_sign_race REFUSED: r is only for mode switch")
        k = m0
    value = _quad_eval(a, b, c, k)
    if mode == "negative" and not value < 0:
        raise ValueError(f"quadratic_sign_race REFUSED: P({k}) = {value} is not < 0")
    if mode != "negative" and not value > 0:
        raise ValueError(f"quadratic_sign_race REFUSED: P({k}) = {value} is not > 0")
    return QuadraticSignRaceCert(
        mode=mode, a=a, b=b, c=c, m0=m0, r=r, anchor=k,
        slope=2 * a * k + b, value=value, head_value=head)


def eventual_threshold_certificate(n) -> EventualThresholdCert:
    """Build and re-check an eventual-threshold instance."""
    n = int(n)
    if not (1 <= n <= 6):
        raise ValueError(f"eventual_threshold REFUSED: arity 1 ≤ n ≤ 6; got {n}")
    return EventualThresholdCert(n=n)


def certify_eventual_threshold_point(family, pt, name):
    """``spec(pt) -> n`` (arity).  One structural check.

    Quadratic sign race face: ``spec(pt) -> {"quadratic": (a, b, c), "m0": ...,
    "mode": "switch"|"positive"|"negative", "r": ...}``."""
    n = family.special[1](pt)
    if isinstance(n, dict):
        a, b, c = n["quadratic"]
        cert = quadratic_sign_race_certificate(a, b, c, n["m0"], n["mode"], n.get("r"))
        inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
        return inst, 3
    cert = eventual_threshold_certificate(n)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def _nested_max(terms: list[str]) -> str:
    if len(terms) == 1:
        return terms[0]
    return f"max {terms[0]} ({_nested_max(terms[1:])})"


def _rl(q) -> str:
    """A rational as a real Lean literal ``(p/q : ℝ)``."""
    q = sp.Rational(q)
    return f"({q.p} : ℝ)" if q.q == 1 else f"({q.p}/{q.q} : ℝ)"


def _quad_lean(cert: QuadraticSignRaceCert, x: str) -> str:
    return f"{_rl(cert.a)} * {x} ^ 2 + {_rl(cert.b)} * {x} + {_rl(cert.c)}"


def _tail_block(cert: QuadraticSignRaceCert, name: str, positive: bool) -> str:
    """``have name : ∀ m : ℤ, k ≤ m → (0 < P m | P m < 0)`` via the Taylor
    identity at the anchor ``k``, all three summands sign-definite."""
    k = cert.anchor
    P = _quad_lean(cert, "(m : ℝ)")
    d = f"((m : ℝ) - {_rl(k)})"
    sg = 1 if positive else -1
    concl = f"0 < {P}" if positive else f"{P} < 0"
    fin = f"(0 : ℝ) < {_rl(cert.value)}" if positive else f"{_rl(cert.value)} < 0"
    return (
        f"  have {name} : ∀ m : ℤ, {k} ≤ m → {concl} := by\n"
        f"    intro m h\n"
        f"    have h' : {_rl(k)} ≤ (m : ℝ) := by exact_mod_cast h\n"
        f"    have hid : {P}\n"
        f"        = {_rl(cert.a)} * {d} ^ 2 + {_rl(cert.slope)} * {d} + {_rl(cert.value)} := by ring\n"
        f"    rw [hid]\n"
        f"    have t1 : (0 : ℝ) ≤ {_rl(sg * cert.a)} * {d} ^ 2 := "
        f"mul_nonneg (by norm_num) (sq_nonneg _)\n"
        f"    have t2 : (0 : ℝ) ≤ {_rl(sg * cert.slope)} * {d} := "
        f"mul_nonneg (by norm_num) (by linarith)\n"
        f"    have t3 : {fin} := by norm_num\n"
        f"    linarith\n"
    )


def _emit_quadratic_race(cert: QuadraticSignRaceCert, nm: str) -> str:
    P = _quad_lean(cert, "(m : ℝ)")
    m0 = cert.m0
    hne = f"(∀ m : ℤ, {m0} ≤ m → {P} ≠ 0)"
    pat = (f"{_rl(cert.a)}·m² + {_rl(cert.b)}·m + {_rl(cert.c)}")
    if cert.mode == "switch":
        r = cert.r
        Pr = _quad_lean(cert, _rl(r))
        stmt = (f"(∀ m : ℤ, {m0} ≤ m → m ≤ {r} → {P} < 0) ∧\n"
                f"    (∀ m : ℤ, {r + 1} ≤ m → 0 < {P}) ∧\n    {hne}")
        body = (
            f"  have hneg : ∀ m : ℤ, {m0} ≤ m → m ≤ {r} → {P} < 0 := by\n"
            f"    intro m h1 h2\n"
            f"    have h1' : {_rl(m0)} ≤ (m : ℝ) := by exact_mod_cast h1\n"
            f"    have h2' : (m : ℝ) ≤ {_rl(r)} := by exact_mod_cast h2\n"
            f"    have hid : ({Pr}) - ({P})\n"
            f"        = ({_rl(r)} - (m : ℝ)) * ({_rl(cert.a)} * ({_rl(r)} + (m : ℝ)) + "
            f"{_rl(cert.b)}) := by ring\n"
            f"    have hf : (0 : ℝ) ≤ {_rl(cert.a)} * ({_rl(r)} + (m : ℝ)) + {_rl(cert.b)} := "
            f"by linarith\n"
            f"    have hp : (0 : ℝ) ≤ ({_rl(r)} - (m : ℝ)) * ({_rl(cert.a)} * ({_rl(r)} + (m : ℝ)) + "
            f"{_rl(cert.b)}) :=\n"
            f"      mul_nonneg (by linarith) hf\n"
            f"    have hr : {Pr} < 0 := by norm_num\n"
            f"    linarith\n"
            + _tail_block(cert, "hpos", True)
            + f"  refine ⟨hneg, hpos, fun m h => ?_⟩\n"
            f"  by_cases hm : m ≤ {r}\n"
            f"  · exact (hneg m h hm).ne\n"
            f"  · exact (hpos m (by omega)).ne'\n"
        )
        what = f"negative on [{m0}, {r}], positive from {r + 1} (sharp switch)"
    else:
        positive = cert.mode == "positive"
        concl = f"0 < {P}" if positive else f"{P} < 0"
        stmt = f"(∀ m : ℤ, {m0} ≤ m → {concl}) ∧\n    {hne}"
        body = (
            _tail_block(cert, "htail", positive)
            + "  refine ⟨htail, fun m h => ?_⟩\n"
            + ("  exact (htail m h).ne'\n" if positive else "  exact (htail m h).ne\n")
        )
        what = f"{'positive' if positive else 'negative'} for all m ≥ {m0}"
    return (
        f"-- {nm}: quadratic sign race, P(m) = {pat}: {what}; never zero at an\n"
        f"-- integer m ≥ {m0}.  Certificate: vertex -b/(2a) ≤ {m0} (monotone), endpoint\n"
        f"-- signs by norm_num, Taylor identity at the anchor {cert.anchor} by ring.\n"
        f"theorem {nm} :\n    {stmt} := by\n" + body
    )


@dataclass
class EventualThresholdEmitter(Emitter):
    """Emit the arity-n large-scale threshold with the explicit nested-max
    witness; each conjunct by ``div_lt_iff₀`` + a generated ``le_max`` chain.
    Quadratic-sign-race payloads (``QuadraticSignRaceCert``) emit the concrete
    integer sign pattern instead (see the module docstring)."""

    def __post_init__(self):
        self.kind = "eventual_threshold"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: EventualThresholdCert = inst.payload  # type: ignore[assignment]
            if isinstance(cert, QuadraticSignRaceCert):
                lines.append(_emit_quadratic_race(cert, inst.lean_name))
                n_thm += 1
                continue
            nm, n = inst.lean_name, cert.n
            avars = [f"a{i+1}" for i in range(n)]
            cvars = [f"c{i+1}" for i in range(n)]
            binder = " ".join(avars + cvars)
            hyps = " ".join(f"(hc{i+1} : 0 < c{i+1})" for i in range(n))
            ratios = [f"(a{i+1} / c{i+1})" for i in range(n)]
            witness = _nested_max(ratios)
            concl = " ∧ ".join(f"a{i+1} < p * c{i+1}" for i in range(n))
            body: list[str] = []
            # per-conjunct: ratio_i ≤ p₀ via a le_max chain into the right-nested
            # max (position i = i × le_max_right wraps around a le_max_left, or
            # le_refl for the last), then div_lt_iff₀ against p₀ < p.
            for i in range(n):
                expr = "le_max_left _ _" if i < n - 1 else "le_refl _"
                for _ in range(i):
                    expr = f"le_trans ({expr}) (le_max_right _ _)"
                body.append(
                    f"  have hm{i+1} : a{i+1} / c{i+1} ≤ p₀ := {expr}")
                body.append(
                    f"  have hp{i+1} : a{i+1} < p * c{i+1} := "
                    f"(div_lt_iff₀ hc{i+1}).mp (lt_of_le_of_lt hm{i+1} hlarge)")
            tuple_expr = ("hp1" if n == 1
                          else "⟨" + ", ".join(f"hp{i+1}" for i in range(n)) + "⟩")
            lines.append(
                f"-- {nm}: eventual scaling threshold, arity {n} — explicit witness\n"
                f"-- p₀ = max of the {n} coefficient ratio(s).  Ported/genericized from\n"
                f"-- NavierStokesAndEuler ConeAlgebra.lean\n"
                f"-- sufficiently_large_amplitude_cone (Apache-2.0).\n"
                f"-- Trust seam: slope positivity 0 < cᵢ are HYPOTHESES.\n"
                f"theorem {nm} ({binder} : ℝ) {hyps} :\n"
                f"    ∃ p₀ : ℝ, ∀ p : ℝ, p₀ < p → ({concl}) := by\n"
                f"  refine ⟨{witness}, fun p hlarge => ?_⟩\n"
                f"  set p₀ : ℝ := {witness} with hp₀\n"
                + "\n".join(body) + "\n"
                f"  exact {tuple_expr}\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def eventual_threshold_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Kind ``eventual_threshold``; ``spec: pt -> n`` (arity 1–6), or a
    quadratic-sign-race dict (see ``certify_eventual_threshold_point``)."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("eventual_threshold", spec),
        constants=dict(constants or {}),
    )
