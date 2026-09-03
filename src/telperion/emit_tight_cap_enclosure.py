"""BG g-step "tight-cap enclosure" emitter — the FIXED-named-config closure faces.

This certifies the Brualdi–Goldwasser per(L)/∏deg g-step closure

    (baseOf l)¹¹ · prodBcap l / (W · (5/3)¹¹)  ≤  1

for a NAMED child-message config ``l`` (a list of rational cavity messages μ),
with the EXACT rational definitions of ``proof/formalization/R3Cert/``:

    W          = 64/621
    glemma μ   = W²·(5/3)¹¹ / (1 + μ/3)¹¹
    master_ub μ= W·(3/(2+μ))¹¹
    Bcap μ     = min(master_ub μ, min(glemma μ, 1))          (three-way min)
    baseOf l   = (3(|l|+1) + 3·Σl + 1) / (3(|l|+1))          (boostR at j=|l|)
    prodBcap l = ∏_{μ∈l} Bcap μ

Two emission modes, mirroring the two proven in-repo model lemmas of
``CappedJointAchievable.lean``:

* ``mode="concrete"`` (default): every μ ∈ l is a concrete rational, so the whole
  LHS is a concrete rational and the emitted proof is a single ``norm_num`` over
  the unfolded defs.  HEADLINE: the d=6 all-cherry config ``[1/3]*5`` (5 children,
  μ = 1/3), the "27·23 = 621" integrality-tie config.
* ``mode="symbolic1"``: a single symbolic child μ over the box ``0 < μ ≤ 1/2``.
  Emits the reduce → fraction-cap → constant-cap → assemble chain mirroring
  ``single_child_le_one`` EXACTLY (symbolic μ : ℚ), via
  ``baseOf[μ]¹¹·glemma μ = W²(5/3)¹¹·((7+3μ)/(2(3+μ)))¹¹``,
  ``(7+3μ)/(2(3+μ)) ≤ 17/14`` on [0,1/2], and ``W·(17/14)¹¹ ≤ 1``.

HONEST SCOPE.  This emitter does the FIXED-named-config closures — the concrete
tie face and the ``single_child_le_one`` symbolic arm face (the cert_jk faces).
It does NOT do the general-arity g-lemma open core (``gV_le`` /
``gstep_lt_gamma`` in the cavity model); that remains the open analytic wall
(``Case2PropertyAchievable``).  The emitted file is self-contained (only
``import Mathlib``; the W/glemma/master_ub/Bcap/baseOf/prodBcap defs are inlined
in the example namespace — it does NOT import the R3Cert project).

conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

import sympy as sp

try:  # normal package import
    from .certify import CertifiedInstance
    from .family import GridSpec, InequalityFamily
    from .lean import LeanProfile
    from .workflow import Emitter
except ImportError:  # run directly
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from telperion.certify import CertifiedInstance
    from telperion.family import GridSpec, InequalityFamily
    from telperion.lean import LeanProfile
    from telperion.workflow import Emitter


# ---- exact sympy model of the g-step (mirrors R3Cert defs) -------------------
_W = sp.Rational(64, 621)


def _glemma(mu: sp.Rational) -> sp.Rational:
    return _W**2 * sp.Rational(5, 3) ** 11 / (1 + mu / sp.Integer(3)) ** 11


def _master_ub(mu: sp.Rational) -> sp.Rational:
    return _W * (sp.Integer(3) / (2 + mu)) ** 11


def _Bcap(mu: sp.Rational) -> sp.Rational:
    return sp.Min(_master_ub(mu), sp.Min(_glemma(mu), sp.Integer(1)))


def _baseOf(l: list[sp.Rational]) -> sp.Rational:
    L = len(l)
    S = sum(l, sp.Integer(0))
    return (3 * (L + 1) + 3 * S + 1) / (3 * (L + 1))


def _prodBcap(l: list[sp.Rational]) -> sp.Rational:
    out = sp.Integer(1)
    for mu in l:
        out *= _Bcap(mu)
    return out


def _lhs(l: list[sp.Rational]) -> sp.Rational:
    return _baseOf(l) ** 11 * _prodBcap(l) / (_W * sp.Rational(5, 3) ** 11)


def _lean_rat(q: sp.Rational) -> str:
    """Render an exact rational as a Lean ℚ literal (n or n/d)."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"{q.p}"
    return f"{q.p}/{q.q}"


def _lean_list(l: list[sp.Rational]) -> str:
    return "[" + ", ".join(_lean_rat(m) for m in l) + "]"


@dataclass(frozen=True)
class TightCapEnclosureCertificate:
    """A verified BG g-step tight-cap enclosure certificate for a named config.

    ``mode`` is ``"concrete"`` or ``"symbolic1"``.

    concrete: ``children`` is the tuple of exact rational child messages μ; the
    EXACT rational LHS ``(baseOf l)¹¹·prodBcap l/(W(5/3)¹¹)`` is computed in sympy
    and checked ``≤ 1`` (a violating config raises — the negative control).
    ``lhs_value`` records that exact rational.

    symbolic1: the single-child box ``0 < μ ≤ 1/2``; ``frac_cap`` = 17/14 is the
    verified fraction cap on ``(7+3μ)/(2(3+μ))`` over the box, and ``const_cap``
    = W·(17/14)¹¹ ≤ 1 is the closing constant certificate.  ``children`` = ().
    """

    mode: str
    children: tuple                          # concrete: exact μ's; symbolic1: ()
    lhs_value: object = None                 # concrete: exact rational LHS
    frac_cap: object = None                  # symbolic1: 17/14
    const_cap: object = None                 # symbolic1: W·(17/14)¹¹
    box_hi: object = None                    # symbolic1: 1/2 (box upper bound)


def tight_cap_enclosure_certificate(
    *, mode: str = "concrete", children=None, frac_cap=None
) -> TightCapEnclosureCertificate:
    """Build and EXACTLY self-check (over ℚ) a g-step tight-cap enclosure cert.

    concrete mode (``children`` a list of exact rational μ): computes the EXACT
    rational LHS and asserts ``≤ 1``.  NEGATIVE CONTROL: a config whose exact LHS
    exceeds 1 (e.g. the single child ``μ = 13/16 ∈ (1/2,1)`` where the arm peaks
    ≈ 1.076) is REFUSED with ``ValueError``.

    symbolic1 mode: verifies in exact sympy that the fraction cap ``frac_cap``
    (default 17/14) is an actual upper bound of ``(7+3μ)/(2(3+μ))`` on ``[0,1/2]``
    (endpoints + monotone-increasing derivative) AND that
    ``W·(5/3)¹¹·(W/(W)·frac_cap)`` closes — precisely ``W·frac_cap¹¹ ≤ 1``.
    NEGATIVE CONTROL: refuse if ``frac_cap`` is NOT an upper bound on the box, or
    if ``W·frac_cap¹¹ > 1``.
    """
    if mode == "concrete":
        if not children:
            raise ValueError("REFUSED: concrete mode needs a non-empty child list")
        l = [sp.nsimplify(sp.Rational(m)) for m in children]
        lhs = sp.nsimplify(_lhs(l))
        if not (lhs.is_number and lhs <= 1):
            raise ValueError(
                f"REFUSED: concrete config {[_lean_rat(m) for m in l]} VIOLATES the "
                f"g-step enclosure — exact LHS = {lhs} > 1 (negative control)"
            )
        return TightCapEnclosureCertificate(
            mode="concrete", children=tuple(l), lhs_value=lhs
        )

    if mode == "symbolic1":
        cap = sp.nsimplify(sp.Rational(frac_cap if frac_cap is not None else sp.Rational(17, 14)))
        mu = sp.Symbol("mu", nonnegative=True)
        f = (7 + 3 * mu) / (2 * (3 + mu))
        # (1) cap must be an upper bound of f on [0, 1/2]: f increasing (deriv > 0)
        # on the box, so the max is at μ = 1/2 — verify f(1/2) ≤ cap AND f(0) ≤ cap.
        d = sp.simplify(sp.diff(f, mu))
        # derivative is 1/(μ+3)² > 0 everywhere on the box (monotone increasing)
        if not sp.simplify(d - 1 / (mu + 3) ** 2) == 0:
            raise ValueError(
                f"REFUSED: unexpected derivative {d} of the arm fraction "
                f"(negative control)"
            )
        f0 = sp.nsimplify(f.subs(mu, 0))
        f_hi = sp.nsimplify(f.subs(mu, sp.Rational(1, 2)))
        if not (f_hi <= cap and f0 <= cap):
            raise ValueError(
                f"REFUSED: fraction cap {cap} is NOT an upper bound of "
                f"(7+3μ)/(2(3+μ)) on [0,1/2] — f(1/2) = {f_hi} (negative control)"
            )
        # (2) closing constant certificate W·cap¹¹ ≤ 1.
        const_cap = sp.nsimplify(_W * cap**11)
        if not (const_cap <= 1):
            raise ValueError(
                f"REFUSED: constant certificate W·({cap})¹¹ = {const_cap} > 1 — "
                f"the arm face does not close (negative control)"
            )
        return TightCapEnclosureCertificate(
            mode="symbolic1", children=(), frac_cap=cap, const_cap=const_cap,
            box_hi=sp.Rational(1, 2),
        )

    raise ValueError(f"REFUSED: unknown mode {mode!r} (expected concrete|symbolic1)")


def certify_tight_cap_enclosure_point(family, pt, name):
    """Certify one tight-cap-enclosure instance from ``family.special[1](pt)``.

    ``spec`` is a dict: ``{"mode": "concrete"|"symbolic1", "children": [...],
    "frac_cap": ...}`` (children required for concrete; frac_cap optional for
    symbolic1)."""
    spec = family.special[1](pt)
    cert = tight_cap_enclosure_certificate(
        mode=spec.get("mode", "concrete"),
        children=spec.get("children"),
        frac_cap=spec.get("frac_cap"),
    )
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


# the inline self-contained defs emitted once at the top of the example file
# (only `import Mathlib`; does NOT import R3Cert).
_INLINE_DEFS = """\
/-- Base constant `W = 64/621`. -/
def W : ℚ := 64 / 621
/-- `glemma(μ) = W²(5/3)¹¹/(1+μ/3)¹¹`. -/
def glemma (μ : ℚ) : ℚ := W ^ 2 * (5 / 3) ^ 11 / (1 + μ / 3) ^ 11
/-- `master_ub(μ) = W(3/(2+μ))¹¹`. -/
def master_ub (μ : ℚ) : ℚ := W * (3 / (2 + μ)) ^ 11
/-- `Bcap(μ) = min(master_ub, glemma, 1)` — the per-child three-way-min cap. -/
def Bcap (μ : ℚ) : ℚ := min (master_ub μ) (min (glemma μ) 1)
/-- `baseOf l = (3(|l|+1)+3Σl+1)/(3(|l|+1))` — the g-step base of config `l`. -/
def baseOf (l : List ℚ) : ℚ :=
  (3 * ((l.length : ℚ) + 1) + 3 * l.sum + 1) / (3 * ((l.length : ℚ) + 1))
/-- `prodBcap l = ∏ Bcap(μ)` over the config. -/
def prodBcap (l : List ℚ) : ℚ := (l.map Bcap).prod"""


@dataclass
class TightCapEnclosureEmitter(Emitter):
    """Emit the BG g-step tight-cap enclosure theorem(s) for named configs.

    concrete instances emit

        theorem <name> :
            (baseOf L)¹¹ * prodBcap L / (W * (5/3)¹¹) ≤ 1 := by
          norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, ...]

    (the whole LHS is a concrete rational; ``norm_num`` over the unfolded defs
    closes it — this is the tie/cert_jk face).

    symbolic1 instances emit the single-child box theorem, mirroring
    ``single_child_le_one`` EXACTLY:

        theorem <name> (μ : ℚ) (h0 : 0 < μ) (h1 : μ ≤ 1/2) :
            (baseOf [μ])¹¹ * prodBcap [μ] / (W * (5/3)¹¹) ≤ 1 := by …

    The self-contained W/glemma/master_ub/Bcap/baseOf/prodBcap defs are supplied
    once via the ``LeanProfile.prelude`` (the module constant ``_INLINE_DEFS``,
    used by the example ``generate.py``); this emitter emits ONLY the theorems.
    HONEST SCOPE: fixed-named-config closures only, NOT the general-arity g-lemma
    open core.  conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "tight_cap_enclosure"

    def _emit_concrete(self, cert: TightCapEnclosureCertificate, name: str) -> str:
        L = _lean_list(list(cert.children))
        return (
            f"-- CONCRETE g-step tight-cap enclosure for the named config "
            f"{L}.\n"
            f"-- The whole LHS is a concrete rational; norm_num over the unfolded "
            f"defs closes it.\n"
            f"-- (fixed-config cert_jk / tie face — NOT the general-arity g-lemma.)\n"
            f"theorem {name} :\n"
            f"    (baseOf {L}) ^ 11 * prodBcap {L}\n"
            f"      / (W * (5 / 3) ^ 11) ≤ 1 := by\n"
            f"  norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, List.map,\n"
            f"    List.prod, List.sum, List.length, List.foldr]\n"
        )

    def _emit_symbolic1(self, cert: TightCapEnclosureCertificate, name: str) -> str:
        cap = _lean_rat(cert.frac_cap)
        # cap = p/q -> render the const-cap literal as W*(p/q)^11
        return (
            f"-- SYMBOLIC single non-leaf child over the box 0 < μ ≤ 1/2 "
            f"(the arm face).\n"
            f"-- Mirrors R3Cert.CappedJointAchievable.single_child_le_one EXACTLY:\n"
            f"--   baseOf[μ]¹¹·glemma μ = W²(5/3)¹¹·((7+3μ)/(2(3+μ)))¹¹,\n"
            f"--   (7+3μ)/(2(3+μ)) ≤ {cap} on [0,1/2], and W·({cap})¹¹ ≤ 1.\n"
            f"theorem {name} (μ : ℚ) (h0 : 0 < μ) (h1 : μ ≤ 1 / 2) :\n"
            f"    (baseOf [μ]) ^ 11 * prodBcap [μ] / (W * (5 / 3) ^ 11) ≤ 1 := by\n"
            f"  have hμ0 : (0 : ℚ) ≤ μ := le_of_lt h0\n"
            f"  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]\n"
            f"  have hbase : baseOf [μ] = (7 + 3 * μ) / 6 := by\n"
            f"    unfold baseOf\n"
            f"    simp only [List.length_cons, List.length_nil, List.sum_cons, "
            f"List.sum_nil]\n"
            f"    push_cast; ring\n"
            f"  have hprod : prodBcap [μ] = Bcap μ := by simp [prodBcap]\n"
            f"  have hb11 : (0 : ℚ) ≤ (baseOf [μ]) ^ 11 := by rw [hbase]; positivity\n"
            f"  have hBle : Bcap μ ≤ glemma μ :=\n"
            f"    le_trans (min_le_right _ _) (min_le_left _ _)\n"
            f"  have hreduce : (baseOf [μ]) ^ 11 * glemma μ\n"
            f"      = W ^ 2 * (5 / 3) ^ 11 * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 := by\n"
            f"    have hden1 : (1 : ℚ) + μ / 3 ≠ 0 := by positivity\n"
            f"    have h3 : (3 : ℚ) + μ ≠ 0 := by positivity\n"
            f"    rw [hbase, glemma]; field_simp; ring\n"
            f"  have hrle : (7 + 3 * μ) / (2 * (3 + μ)) ≤ {cap} := by\n"
            f"    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith\n"
            f"  have hcert : W * ({cap} : ℚ) ^ 11 ≤ 1 := by norm_num [W]\n"
            f"  have hcap : W * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 ≤ 1 := by\n"
            f"    have hWnn : (0 : ℚ) ≤ W := by norm_num [W]\n"
            f"    refine le_trans ?_ hcert\n"
            f"    apply mul_le_mul_of_nonneg_left _ hWnn\n"
            f"    gcongr\n"
            f"  rw [div_le_one hden, hprod]\n"
            f"  calc (baseOf [μ]) ^ 11 * Bcap μ\n"
            f"      ≤ (baseOf [μ]) ^ 11 * glemma μ :=\n"
            f"        mul_le_mul_of_nonneg_left hBle hb11\n"
            f"    _ = W ^ 2 * (5 / 3) ^ 11 * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 := "
            f"hreduce\n"
            f"    _ = (W * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11) * (W * (5 / 3) ^ 11) := "
            f"by ring\n"
            f"    _ ≤ 1 * (W * (5 / 3) ^ 11) :=\n"
            f"        mul_le_mul_of_nonneg_right hcap (le_of_lt hden)\n"
            f"    _ = W * (5 / 3) ^ 11 := one_mul _\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: TightCapEnclosureCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            if cert.mode == "concrete":
                lines.append(self._emit_concrete(cert, name))
            elif cert.mode == "symbolic1":
                lines.append(self._emit_symbolic1(cert, name))
            else:  # pragma: no cover — guarded at certify time
                raise ValueError(f"unknown cert mode {cert.mode!r}")
            nthm += 1
        return "\n".join(lines), nthm


def tight_cap_enclosure_family(name, grid, lean_name, spec, constants=None):
    """Build a BG g-step tight-cap-enclosure family (kind='tight_cap_enclosure').

    ``spec``: a callable ``pt -> {"mode": "concrete"|"symbolic1",
    "children": [...], "frac_cap": ...}``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("tight_cap_enclosure", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive: d=6 all-cherry tie config [1/3]*5 (concrete) ===")
    c = tight_cap_enclosure_certificate(
        mode="concrete", children=[Fraction(1, 3)] * 5
    )
    print(f"  cert OK: mode={c.mode}, exact LHS = {c.lhs_value} "
          f"(≈ {float(c.lhs_value):.6f}) ≤ 1")

    print("\n=== positive: symbolic single-child box 0 < μ ≤ 1/2 ===")
    cs = tight_cap_enclosure_certificate(mode="symbolic1")
    print(f"  cert OK: mode={cs.mode}, frac_cap = {cs.frac_cap}, "
          f"const_cap = W·(17/14)¹¹ = {cs.const_cap} (≈ {float(cs.const_cap):.4f}) ≤ 1")

    print("\n=== NEGATIVE CONTROL: single child μ = 13/16 ∈ (1/2,1), LHS > 1 ===")
    try:
        tight_cap_enclosure_certificate(mode="concrete", children=[Fraction(13, 16)])
        raise SystemExit("FAIL: violating config was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")

    print("\n=== NEGATIVE CONTROL: symbolic1 with a too-small frac_cap 6/5 ===")
    try:
        tight_cap_enclosure_certificate(mode="symbolic1", frac_cap=Fraction(6, 5))
        raise SystemExit("FAIL: bad fraction cap was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:90]}...")
