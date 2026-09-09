"""PolytopeMoment emitter — exact-rational simplex-moment certificates, the shape
of Axiom Math's ``bgp212`` development (the *"H1 ≤ 212"* paper), Lemma 10.1 /
identity (10.1).

The analytic identity (10.1) gives the closed form of a monomial moment over the
standard rational simplex ``{z ≥ 0, Σᵢ zᵢ ≤ R}``:

    ∫_{z≥0, Σzᵢ≤R} Πᵢ zᵢ^{eᵢ} dz  =  R^{m+Σeᵢ} · (Πᵢ eᵢ!) / (m + Σeᵢ)!

Consequently EVERY integral of a rational polynomial over a rational simplex is
an EXACT rational.  A moment computation over a rational polytope, once it has
been triangulated into simplices and each piece linearly substituted onto the
standard simplex, is a finite ℚ-linear combination of these closed forms — an
exact rational.

The generator supplies an already-triangulated/substituted computation: a list of
simplices, each carrying a rational scale ``R``, an ambient dimension ``m``, and a
list of monomial pieces ``(coeff, (e₁, …, e_k))``; plus the claimed total ``q ∈
ℚ``.  It evaluates every piece via the closed form and the grand total EXACTLY in
sympy (and REFUSES if the recomputed total ≠ ``q``, or any structural gate fails).

KERNEL-CHECKABLE LAYER (honest split).  The emitted Lean carries a prelude
definition

    def simplexMoment (R : ℚ) (m : ℕ) (es : List ℕ) : ℚ :=
      R ^ (m + es.sum) * (es.map (Nat.factorial)).prod / (Nat.factorial (m + es.sum))

and, per instance, a theorem asserting the ℚ-linear combination of
``simplexMoment`` calls equals ``q``, closed by ``norm_num [simplexMoment]``.  The
kernel then RE-EXECUTES the entire moment computation over the defined closed
form — a real, non-vacuous arithmetic verification of the exact-rational layer.

DOCUMENTED TRUST SEAM (stated in the emitted comment as well):

  (i)  That ``simplexMoment`` IS the integral over the simplex — identity
       (10.1) — is the ANALYTIC PRELUDE.  It is citable to Mathlib measure
       theory as future work; it is NOT emitted and NOT kernel-checked here.
  (ii) That the supplied simplices are a valid triangulation/substitution of the
       intended polytope is a GENERATOR-side fact.  We verify what is checkable
       in Python (coefficients rational, exponents nonneg ints, R > 0, m a nonneg
       int); the geometric validity of the decomposition itself is NOT
       kernel-checked.

The kernel certifies the ARITHMETIC layer — exactly the layer Axiom's Appendix A
leaves as an out-of-kernel hypothesis.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

# norm_num re-executes each monomial term over the closed form; cap the total
# number of terms so the kernel cost stays bounded.
_MAX_TERMS = 400


@dataclass(frozen=True)
class SimplexPiece:
    """One monomial contribution ``coeff · ∫ Πᵢ zᵢ^{eᵢ}`` over a rational simplex.

    ``R`` — rational scale of the simplex ``{z ≥ 0, Σ zᵢ ≤ R}`` (``> 0``).
    ``m`` — ambient dimension (number of integration variables, a nonneg int).
    ``es`` — exponents ``(e₁, …, e_k)``, each a nonneg int (``k`` may be ``< m``;
        absent variables carry exponent 0 and simply raise the factorial degree
        via ``m`` in the closed form).
    ``coeff`` — the rational polynomial coefficient multiplying this monomial.
    ``value`` — the EXACT rational ``coeff · simplexMoment(R, m, es)``.
    """

    R: sp.Rational
    m: int
    es: tuple[int, ...]
    coeff: sp.Rational
    value: sp.Rational


@dataclass(frozen=True)
class PolytopeMomentCert:
    """A certified exact-rational polytope-moment computation.

    ``pieces`` — the flattened monomial contributions across all simplices.
    ``total`` — the exact rational grand total (== the claimed ``q``).
    """

    pieces: tuple[SimplexPiece, ...]
    total: sp.Rational


def _simplex_moment(R: sp.Rational, m: int, es: Sequence[int]) -> sp.Rational:
    """The closed form of identity (10.1): ``R^{m+Σe} · Πeᵢ! / (m+Σe)!``, exact."""
    deg = m + sum(es)
    num = sp.Integer(1)
    for e in es:
        num *= sp.factorial(e)
    return sp.Rational(R ** deg * num, 1) / sp.factorial(deg)


def polytope_moment_certificate(
    simplices: Sequence,
    total: sp.Rational,
) -> PolytopeMomentCert:
    """Build (and exactly re-check) a polytope-moment certificate.

    ``simplices`` — a sequence of ``(R, m, pieces)`` where ``pieces`` is a list
    of ``(coeff, exponents)``.  Each ``exponents`` is a tuple/list of nonneg ints.

    Refuses, in order: empty ``simplices``; a non-integer or negative ``m``; a
    non-positive ``R``; an empty piece list for a simplex; a non-rational
    ``coeff``; a negative or non-integer exponent; a total monomial-term count
    exceeding ``_MAX_TERMS`` (the ``norm_num`` cost cap); and — finally — a
    claimed ``total`` that does NOT equal the exact recomputation.  Each refusal
    is a ``ValueError`` (the negative control), so a wrong total is never
    emitted."""
    if not simplices:
        raise ValueError(
            "polytope_moment REFUSED: empty simplex list (nothing to certify)")

    flat: list[SimplexPiece] = []
    n_terms = 0
    running = sp.Integer(0)
    for si, simplex in enumerate(simplices):
        R_raw, m_raw, pieces = simplex
        # m: nonneg integer ambient dimension
        m = sp.Integer(sp.nsimplify(m_raw))
        if m < 0 or sp.Integer(m) != m:
            raise ValueError(
                f"polytope_moment REFUSED: simplex {si} ambient dimension "
                f"m={m_raw} must be a nonneg integer")
        m = int(m)
        # R: positive rational scale
        R = sp.Rational(sp.nsimplify(R_raw))
        if not (R > 0):
            raise ValueError(
                f"polytope_moment REFUSED: simplex {si} scale R={R} ≤ 0 "
                "(the simplex {z≥0, Σz≤R} must be non-degenerate)")
        if not pieces:
            raise ValueError(
                f"polytope_moment REFUSED: simplex {si} has no monomial pieces")
        for pj, (coeff_raw, es_raw) in enumerate(pieces):
            coeff = sp.nsimplify(coeff_raw)
            if not coeff.is_rational:
                raise ValueError(
                    f"polytope_moment REFUSED: simplex {si} piece {pj} "
                    f"coefficient {coeff_raw} is not rational")
            coeff = sp.Rational(coeff)
            es = tuple(sp.Integer(sp.nsimplify(e)) for e in es_raw)
            for e in es:
                if e < 0 or sp.Integer(e) != e:
                    raise ValueError(
                        f"polytope_moment REFUSED: simplex {si} piece {pj} "
                        f"exponent {e} must be a nonneg integer")
            es_int = tuple(int(e) for e in es)
            n_terms += 1
            if n_terms > _MAX_TERMS:
                raise ValueError(
                    f"polytope_moment REFUSED: total monomial terms exceed "
                    f"{_MAX_TERMS} (norm_num cost cap)")
            val = sp.Rational(coeff * _simplex_moment(R, m, es_int))
            running += val
            flat.append(SimplexPiece(
                R=R, m=m, es=es_int, coeff=coeff, value=val))

    total_q = sp.Rational(sp.nsimplify(total))
    if sp.Rational(running) != total_q:
        raise ValueError(
            f"polytope_moment REFUSED: exact recomputed total {running} ≠ "
            f"claimed total {total_q} (the arithmetic layer would be FALSE; "
            "a wrong total is never emitted — honest refusal)")

    return PolytopeMomentCert(pieces=tuple(flat), total=total_q)


def certify_polytope_moment_point(family, pt, name):
    """Certify one polytope-moment instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(simplices, total) = family.special[1](pt)``.  ``n_checks`` counts
    the arithmetic gates exercised: one exact closed-form evaluation per monomial
    term plus the final total-vs-claim comparison, all re-verified in
    ``polytope_moment_certificate``."""
    simplices, total = family.special[1](pt)
    cert = polytope_moment_certificate(simplices, total)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(), payload=cert)
    n_checks = len(cert.pieces) + 1  # per-term evaluation + the total check
    return inst, n_checks


# The Lean prelude: the closed form of identity (10.1), as an executable ℚ term
# the kernel re-runs.  Emitted once per file (idempotent header).
_PRELUDE = (
    "-- Prelude: the closed form of the simplex moment, identity (10.1) of the\n"
    "-- Axiom Math bgp212 (\"H1 ≤ 212\") development, Lemma 10.1.  This is the\n"
    "-- ANALYTIC PRELUDE (that this ℚ term equals the integral over the simplex\n"
    "-- {z≥0, Σz≤R} of Πᵢ zᵢ^{eᵢ}); it is citable to Mathlib measure theory as\n"
    "-- future work and is NOT kernel-checked here.  The kernel re-executes the\n"
    "-- ARITHMETIC over this definition.\n"
    "def simplexMoment (R : ℚ) (m : ℕ) (es : List ℕ) : ℚ :=\n"
    "  R ^ (m + es.sum) * (es.map (Nat.factorial)).prod / "
    "(Nat.factorial (m + es.sum))\n"
)


def _es_lean(es: tuple[int, ...]) -> str:
    """Render an exponent tuple as a Lean ``List ℕ`` literal, e.g. ``[1, 1]``."""
    return "[" + ", ".join(str(e) for e in es) + "]"


@dataclass
class PolytopeMomentEmitter(Emitter):
    """Emit an exact-rational polytope-moment certificate (shape of bgp212
    Lemma 10.1 / (10.1)).  For each instance:

        theorem <name> : (Σ pieces  coeff * simplexMoment R m es : ℚ) = q :=
          by norm_num [simplexMoment]

    The kernel re-executes the entire moment computation over the emitted
    ``simplexMoment`` closed form — a real, non-vacuous arithmetic verification.
    Trust seam (see module docstring / emitted comment): the integral semantics
    of ``simplexMoment`` (identity (10.1)) and the geometric validity of the
    triangulation are the documented generator-side / analytic-prelude seam, NOT
    kernel-checked.  Self-contained over ℚ."""

    def __post_init__(self):
        self.kind = "polytope_moment"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = [_PRELUDE]
        n_thm = 0
        for inst in fam.instances:
            cert: PolytopeMomentCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            terms = []
            for p in cert.pieces:
                terms.append(
                    f"{rat_lean(p.coeff)} * simplexMoment "
                    f"{rat_lean(p.R)} {p.m} {_es_lean(p.es)}")
            sum_src = " + ".join(terms)
            q_src = rat_lean(cert.total)
            lines.append(
                f"-- {nm}: exact rational polytope-moment certificate (shape of\n"
                f"-- bgp212 Lemma 10.1/(10.1)); kernel re-executes the simplex-\n"
                f"-- moment arithmetic over `simplexMoment`.  {len(cert.pieces)} "
                f"monomial term(s), total = {cert.total}.\n"
                f"-- TRUST SEAM: integral semantics (identity (10.1)) + "
                f"triangulation validity are the documented generator-side seam,\n"
                f"-- NOT kernel-checked.  conjecture1_proved = False.\n"
                f"theorem {nm} : ({sum_src} : ℚ) = {q_src} := by\n"
                f"  norm_num [simplexMoment]\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def polytope_moment_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a polytope-moment family (kind ``polytope_moment``).

    ``spec: pt -> (simplices, total)`` where ``simplices`` is a sequence of
    ``(R, m, [(coeff, exponents), …])`` and ``total`` is the claimed exact
    rational.  The theorem is a closed rational equality, so a single dummy
    symbol carries the grid."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("n", nonnegative=True),),
        grid=grid,
        lean_name=lean_name,
        special=("polytope_moment", spec),
        constants=dict(constants or {}),
    )
