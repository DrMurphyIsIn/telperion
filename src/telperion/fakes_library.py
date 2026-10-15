"""Standing library of calibration fakes: every object with a certified OFF-line zero that the RH tracks use to
calibrate their mechanisms, registered once, with its Arb evaluator, its declared poles and its metadata.

conjecture1_proved = False.  Nothing here is progress on RH.  This is tooling: each entry is a function that has some
of the ingredients an RH-type argument might use and an off-line zero all the same, so a mechanism that "proves"
no off-line zeros from those ingredients alone is refuted by the entry.  ``calibrate`` runs that check.

ENTRY CONTRACT.  A ``FakeEntry`` carries
  * ``series``: an analytic function of a python-flint ``acb_series`` (the form ``arb_fakes.rigorous_winding`` and
    ``certify_zero_box`` take as a callable; ctx.cap <= 2 is all they use), and ``eval``: the acb -> acb point form;
  * ``poles``: the DECLARED poles (exact rational points, all simple) inside ``region``, and ``region``: the closed
    rectangle (None = all of C) on which that list is COMPLETE.  ``pole_basis`` says why, with its label;
    ``pole_exclusion`` lists the zeta zero-free boxes that make it ARB where the basis is a certificate.  Objects
    with transcendental poles (TW, SYM, the FF fake) get a region that avoids them instead of an inexact pole list;
  * ``zero_box``: one off-line box that holds exactly one zero, or None;
  * metadata: ``ingredients`` (has / lacks / partial / n/a / not recorded, each with its evidence label),
    ``conditional``, ``known_zeros``, ``provenance`` (memo, review, prior certificates, script).

``certify_entry_box`` and ``count_entry`` pass the declared poles to ``arb_fakes`` automatically and REFUSE a box
that leaves ``region`` (outside it the pole list is not claimed complete, so a winding number could silently count
zeros minus undeclared poles).  ``arb_fakes`` itself refuses a pole on the box boundary.

LABELS.  P = PROVED in the memo named; ARB = python-flint ball arithmetic (not kernel); N/COMPUTED = floating point;
C = CITED; FROM MEMORY = the memo's own label.  A registered zero box is ARB only once ``certify_entry_box`` has been
run on it (tests/test_fakes_library.py does this at 128 bits; the slow ones are opt-in, TELPERION_ARB_SLOW=1).

PROVENANCE PATHS are written "rh-team:<path>" and "e9-research:<path>".  ``resolve_provenance`` maps the prefixes to
$TELPERION_RH_TEAM (default ~/rh-team) and $TELPERION_E9_RESEARCH (default ~/e9-research).

rho0.  Every twist object uses rho0 = 0.85 + 14.134725141734693 i, the decimal string read EXACTLY (selberg.md
section 3.4).  Track B's runs and the earlier T certificates used gamma0 = 14.134725, and S's SYM script used 14.1347;
those are different (nearby) objects, so the boxes here are re-certified for the full-precision rho0, not inherited.
"""
from __future__ import annotations

import math
import os
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable

from . import arb_fakes

__all__ = [
    "RHO0_RE", "RHO0_IM", "FakeEntry", "Box", "Claim", "REGISTRY", "get", "names", "certify_entry_box",
    "count_entry", "certify_pole_exclusion", "calibrate", "resolve_provenance", "INGREDIENTS",
]

RHO0_RE = "0.85"
RHO0_IM = "14.134725141734693"          # FULL precision, read exactly; never truncate

# EP = Euler product; R = property (R) of the WALL-3/B memos (the coefficients of 1/F are bounded like those of
# 1/zeta, e.g. |coeff| <= d_k(n)) -- NOT the Ramanujan axiom (iv), which is noted in the evidence where it fails;
# F_theta = N(x) = A x + O(x^theta); FE / Gamma = functional equation / standard Gamma-factor.
INGREDIENTS = ("EP", "R", "F_theta", "FE", "Gamma", "integer_coefficients", "positivity", "density")
STATUSES = ("has", "lacks", "partial", "n/a", "not recorded")


def _flint():
    from flint import acb, acb_series, arb, ctx
    return acb, acb_series, arb, ctx


def _q(x) -> Fraction:
    return Fraction(x)


def _arbq(x):
    _, _, arb, _ = _flint()
    x = Fraction(x)
    return arb(f"{x.numerator}/{x.denominator}")


def _rho0():
    acb, _, _, _ = _flint()
    return acb(_arbq(RHO0_RE), _arbq(RHO0_IM))


# ------------------------------------------------------------------------------------------------ data types
@dataclass(frozen=True)
class Box:
    """Closed rational rectangle [re0, re1] x [im0, im1]."""
    re0: Fraction
    re1: Fraction
    im0: Fraction
    im1: Fraction

    @staticmethod
    def of(re0, re1, im0, im1) -> "Box":
        b = Box(_q(re0), _q(re1), _q(im0), _q(im1))
        if not (b.re0 < b.re1 and b.im0 < b.im1):
            raise ValueError(f"Box: inverted {b}")
        return b

    def tuple(self):
        return (self.re0, self.re1, self.im0, self.im1)

    def contains_box(self, o: "Box") -> bool:
        return self.re0 <= o.re0 and o.re1 <= self.re1 and self.im0 <= o.im0 and o.im1 <= self.im1

    def meets(self, o: "Box") -> bool:
        return not (o.re1 < self.re0 or self.re1 < o.re0 or o.im1 < self.im0 or self.im1 < o.im0)

    def contains_point(self, re, im) -> bool:
        return self.re0 <= re <= self.re1 and self.im0 <= im <= self.im1

    def shifted(self, dre, dim) -> "Box":
        return Box(self.re0 + dre, self.re1 + dre, self.im0 + dim, self.im1 + dim)

    def as_dict(self):
        return {"re0": str(self.re0), "re1": str(self.re1), "im0": str(self.im0), "im1": str(self.im1)}


@dataclass(frozen=True)
class ZetaZeroFree:
    """A zeta zero-free box that excludes poles of an entry from its region (certify with expected=0)."""
    box: Box
    ack_poles: tuple = ()          # zeta's pole s = 1, when the box contains it
    reason: str = ""


@dataclass(frozen=True)
class FakeEntry:
    name: str
    description: str
    series: Callable                       # f(acb_series) -> acb_series, ctx.cap <= 2
    poles: tuple                           # exact simple poles (re, im) as Fractions, inside region
    region: Box | None                     # where `poles` is complete; None = C
    pole_basis: str
    zero_box: Box | None
    ingredients: dict
    conditional: str
    known_zeros: str
    provenance: dict
    pole_exclusion: tuple = ()
    slow: bool = False                     # zero-box certification too slow for the default test run
    notes: str = ""

    def eval(self, z, prec: int = 128):
        """f(z) as an acb ball, z an acb (or anything acb() takes)."""
        acb, acb_series, arb, ctx = _flint()
        old = (ctx.prec, ctx.cap)
        try:
            ctx.prec, ctx.cap = prec, 1
            return self.series(acb_series([acb(z)])).coeffs()[0]
        finally:
            ctx.prec, ctx.cap = old

    def public_meta(self) -> dict:
        """What a mechanism under calibration may see: everything except the zero box and the zero list."""
        return {"name": self.name, "description": self.description, "ingredients": dict(self.ingredients),
                "conditional": self.conditional, "poles": [(str(a), str(b)) for a, b in self.poles],
                "region": None if self.region is None else self.region.as_dict(), "pole_basis": self.pole_basis}

    def meta(self) -> dict:
        d = self.public_meta()
        d.update(zero_box=None if self.zero_box is None else self.zero_box.as_dict(), known_zeros=self.known_zeros,
                 provenance=dict(self.provenance), notes=self.notes, conjecture1_proved=False)
        return d


def _ing(**kw):
    out = {}
    for k in INGREDIENTS:
        st, ev = kw.pop(k, ("not recorded", "not stated in the memos read for this entry"))
        if st not in STATUSES:
            raise ValueError(f"ingredient status {st!r}")
        out[k] = (st, ev)
    if kw:
        raise ValueError(f"unknown ingredients {sorted(kw)}")
    return out


# ------------------------------------------------------------------------------------------------ evaluators
def _guarded(f):
    """Wrap an evaluator: a ValueError from flint (a ball meeting a pole of an inner factor) or a non-finite result
    becomes a huge finite ball, so arb_fakes' segment test fails and it bisects (and refuses at max depth).  A
    huge ball is a valid enclosure of 'unknown'; it can never make a segment pass."""
    def g(s):
        acb, acb_series, arb, ctx = _flint()
        try:
            v = f(s)
            # finite AND moderate: Arb balls with astronomically large exponents are "finite" but make every later
            # operation (exp of such a ball) cost unbounded time and memory
            if all(math.isfinite(float(abs(c).upper())) and float(abs(c).upper()) < 1e300 for c in v.coeffs()):
                return v
        except (ValueError, ZeroDivisionError):
            pass
        big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100))
        return acb_series([big] * ctx.cap)
    g.__name__ = getattr(f, "__name__", "f")
    return g


def _named(name):
    def f(s):
        return arb_fakes.fake_series(name, s)
    f.__name__ = name
    return f


def _tw_raw(s):
    """zeta(s) / (zeta(s+1-rho0) zeta(s+1-conj rho0))."""
    r = _rho0()
    return s.zeta() / ((s + (1 - r)).zeta() * (s + (1 - r.conjugate())).zeta())


def _small_primes(beta0=RHO0_RE):
    """Primes p < x1 = 2^(1/(1-beta0)) (101.59... at beta0 = 0.85): track B's untwisted set, B/twist.py
    make_params, tw = (P >= x1) with TWIST_TAPER off."""
    from flint import fmpz
    x1 = 2 ** (1 / (1 - float(beta0)))
    return [p for p in range(2, int(x1) + 1) if p < x1 and fmpz(p).is_prime()]


def _tw_fix(s):
    """TW_raw times prod_{p < x1} [(1 - p^(rho0-1-s))(1 - p^(conj rho0-1-s))]^-1: the twisted Euler factors at the
    small primes are replaced by zeta's (B's 'small-prime fix'), so a(n) >= 0."""
    acb, acb_series, arb, ctx = _flint()
    r = _rho0()
    one = acb_series([1])
    v = _tw_raw(s)
    for p in _small_primes():
        lp = acb(p).log()
        v = v / ((one - ((r - 1) * lp - s * lp).exp()) * (one - ((r.conjugate() - 1) * lp - s * lp).exp()))
    return v


def _zp(s):
    """zeta(s) (1 - 29/10 2^-s + 2 4^-s)."""
    acb, acb_series, arb, ctx = _flint()
    u = (-s * acb(2).log()).exp()
    return s.zeta() * (acb_series([1]) - _arbq("29/10") * u + 2 * u * u)


def _zp5(s):
    """zeta(s) (1 - 5 5^-s + 5 25^-s): integer coefficients."""
    acb, acb_series, arb, ctx = _flint()
    u = (-s * acb(5).log()).exp()
    return s.zeta() * (acb_series([1]) - 5 * u + 5 * u * u)


def _sh(s):
    """L(s + 3/10, chi_-4) L(s - 3/10, chi_-4) (Hurwitz form, as arb_fakes)."""
    a = _arbq("3/10")
    return arb_fakes._L_series(s + a, arb_fakes.CHI_M4) * arb_fakes._L_series(s - a, arb_fakes.CHI_M4)


def _sym(s):
    """zeta(s) / [zeta(s+1-rho0) zeta(s+1-conj rho0) zeta(s+rho0-1) zeta(s+conj rho0-1)]."""
    r = _rho0()
    rb = r.conjugate()
    return s.zeta() / ((s + (1 - r)).zeta() * (s + (1 - rb)).zeta() * (s + (r - 1)).zeta() * (s + (rb - 1)).zeta())


P_FAKE = (1, -2, 9, -6, 9)        # wall3/E e3: q = 3, genus 2, P(T) = 1 - 2T + 9T^2 - 6T^3 + 9T^4
Q_FAKE = 3


def _ppoly(T):
    acc = None
    for c in reversed(P_FAKE):
        acc = (c if acc is None else acc * T + c)
    return acc


def _ff(s):
    """Z(3^-s) = P(T) / ((1 - T)(1 - 3T)), T = 3^-s."""
    acb, acb_series, arb, ctx = _flint()
    one = acb_series([1])
    T = (-s * acb(Q_FAKE).log()).exp()
    return _ppoly(T) / ((one - T) * (one - Q_FAKE * T))


def _hyb(s):
    """H = zeta(s) P_fake(3^-s)."""
    acb, acb_series, arb, ctx = _flint()
    T = (-s * acb(Q_FAKE).log()).exp()
    return s.zeta() * _ppoly(T)


N8_U0 = 103                       # u0 = ceil(2^(1/(1-beta0))) + 1 (wall5/n8_continuous.py), v0 = log u0
EIN_TAYLOR_MAX = 120              # |w| <= this: Ein by Taylor series with tail bound; beyond: E1 + log w + gamma
EXPINT_PRECS = (53, 64, 96, 128, 192, 256)


def tightest_ball(fn, precs=EXPINT_PRECS, rel=1e-30):
    """Evaluate ``fn()`` (an acb) at each working precision in ``precs`` and keep the tightest finite ball.

    TOOLING BUG CLASS (wall3-T, 2026-10-14): python-flint's acb.expint ball widths are erratic in the precision for
    |w| ~ 1e2, e.g. E1(5.33 + 79.4i) is tight at 64 bits but +-1e-4 at 128.  Every result is a rigorous enclosure,
    so keeping the smallest one is still rigorous; it only avoids a needlessly degraded ball (which would make
    arb_fakes bisect and, at worst, refuse -- never certify falsely).
    Stops early once the radius is below rel * |value|.  Raises ValueError if no precision gives a finite ball."""
    _, _, _, ctx = _flint()
    old = ctx.prec
    best = None
    try:
        for p in precs:
            ctx.prec = p
            z = fn()
            if not z.is_finite():
                continue
            if best is None or float(z.rad()) < float(best.rad()):
                best = z
            if float(best.rad()) <= rel * max(1e-300, float(abs(best).mid())):
                break
    finally:
        ctx.prec = old
    if best is None:
        raise ValueError("tightest_ball: no finite enclosure at any precision")
    return best


def _ein_taylor(c):
    """(Ein(c), Ein'(c)) at an exact point c by Taylor series, with the tail bounded rigorously:
    Ein(w) = sum_{k>=1} (-1)^{k+1} w^k / (k k!),  Ein'(w) = sum_{k>=0} (-1)^k w^k / (k+1)!;
    both tails beyond K are <= R^{K+1}/(K+1)! / (1 - R/(K+2)), R = |c|.  The working precision is raised by
    ~1.5 R bits because the alternating sum cancels like e^R."""
    acb, _, arb, ctx = _flint()
    # The tail bound uses Ra = |c|.upper() as an ARB (outward); float(...) can round DOWN, so it is used only as a
    # ceiling for the term count K and the extra precision, never inside the bound (bb, follow-up to PR #744).
    Ra = abs(c).upper()
    R = math.ceil(float(Ra)) + 1
    K = 3 * R + 60
    old = ctx.prec
    ctx.prec = old + int(1.5 * R) + 30
    try:
        s0, d, term = acb(0), acb(0), acb(1)            # term = c^k / k!
        for k in range(1, K + 2):
            d += (term if (k - 1) % 2 == 0 else -term) / k          # (-1)^(k-1) c^(k-1)/k!
            term = term * c / k
            if k <= K:
                s0 += (term if k % 2 == 1 else -term) / k            # (-1)^(k+1) c^k/(k k!)
        tb = Ra ** (K + 1) / arb(K + 1).fac() / (1 - Ra / (K + 2))
        e = arb(0, tb.upper())
        return s0 + acb(e, e), d + acb(e, e)
    finally:
        ctx.prec = old


def _ein_point(c):
    """(Ein(c), Ein'(c)) at an exact point c: Taylor for |c| <= EIN_TAYLOR_MAX or near the negative real axis,
    else Ein = E1 + log c + gamma with E1 from acb.expint via tightest_ball (c off the cut)."""
    acb, _, arb, ctx = _flint()
    if float(abs(c).upper()) <= EIN_TAYLOR_MAX or (float(c.real.mid()) < 0 and abs(float(c.imag.mid())) < 1):
        return _ein_taylor(c)
    e1 = tightest_ball(lambda: c.expint(1))
    return e1 + c.log() + arb.const_euler(), -((-c).expm1()) / c


def _ein_ball(w):
    """(Ein, Ein') enclosed over the whole ball w by the centred form: value at the exact centre c plus
    r * sup_w |Ein'| (resp. |Ein''|), r = |re rad| + |im rad|.  Evaluating the Taylor series directly on the ball would
    amplify its radius by ~e^|w| (wall3-T); the centred form does not.  sup bounds: Ein' = (1 - e^-w)/w and
    Ein'' = ((1 + w)e^-w - 1)/w^2 evaluated on the ball when it stays away from 0, else the series bound e^|w|."""
    acb, _, arb, ctx = _flint()
    c = acb(w.real.mid(), w.imag.mid())
    r = arb(w.real.rad()) + arb(w.imag.rad())
    v, d = _ein_point(c)
    if r == 0:
        return v, d
    if float(abs(w).lower()) < 0.5:
        d1 = d2 = abs(w).upper().exp()
    else:
        d1 = abs((1 - (-w).exp()) / w).upper()
        d2 = abs(((1 + w) * (-w).exp() - 1) / (w * w)).upper()
    e0, e1 = arb(0, (r * d1).upper()), arb(0, (r * d2).upper())
    return v + acb(e0, e0), d + acb(e1, e1)


def _n8_series(s):
    """zeta_P(s) = exp(E1((s-1)v0) - E1((s-rho0)v0) - E1((s-conj rho0)v0)), v0 = log 103 (LEAD_NOTES N8), in the
    branch-free closed form (E1(w) = -gamma - log w + Ein(w), Ein entire; the 2 pi i jumps of E1 vanish under exp;
    wall3-T eda45e020):
        zeta_P(s) = e^gamma v0 (s - rho0)(s - conj rho0)/(s - 1) * exp(Ein(a) - Ein(b) - Ein(bb)),
        a = (s-1) v0, b = (s-rho0) v0, bb = (s - conj rho0) v0.
    So zeta_P is meromorphic on C with exactly a simple pole at s = 1 and simple zeros at rho0, conj rho0 (PROVED from
    the form).  Jets: d/ds Ein((s-x)v0) = v0 Ein'.  Supports ctx.cap <= 2 (all arb_fakes uses).

    E1's cut.  bb (PR #744 review) found the earlier two-branch E1 evaluator valid but useless exactly ON the rho0 cut
    (s = -1/2 + i gamma0: relative radius 3.9).  This form has no cut: Ein is entire, the centre of each w-ball is
    exact, and a centre on or near the negative real axis is always evaluated by Taylor (_ein_point).  At
    s = -1/2 + i gamma0 the relative radius is ~1e-34 and a winding box straddling the cut certifies (tests).
    Further left, |zeta_P| is astronomically large (log10 |zeta_P| ~ 8e9 at sigma = -5 on that line, mpmath) and
    _guarded's 1e300 cap turns the value into 'unknown', so boxes there are REFUSED, never mis-counted."""
    acb, acb_series, arb, ctx = _flint()
    cap = ctx.cap
    if cap > 2:
        raise ValueError("N8 evaluator supports jets of order <= 1 (ctx.cap <= 2)")
    co = list(s.coeffs()) + [acb(0)] * 2
    c0, c1 = co[0], co[1]
    v0 = acb(N8_U0).log()
    r = _rho0()
    rb = r.conjugate()
    L0, L1 = acb(0), acb(0)
    for x, sgn in ((acb(1), 1), (r, -1), (rb, -1)):
        e, de = _ein_ball((c0 - x) * v0)
        L0 += sgn * e
        L1 += sgn * de * v0
    one = acb_series([1])
    pre = acb(arb.const_euler().exp()) * v0 * (s - r * one) * (s - rb * one) * (s - one).inv()
    return pre * acb_series([L0, L1 * c1][:cap]).exp()


def _n8(s):
    return _n8_series(s)


# ------------------------------------------------------------------------------------------------ registry
G0 = Fraction(RHO0_IM)
B0 = Fraction(RHO0_RE)
_TWIST_REGION = Box.of("4/5", "9/10", "14", "143/10")
_TWIST_BOX = Box.of("0.84", "0.86", "14.12", "14.15")


def _shift_exclusions(region: Box, shifts, why):
    """Zeta zero-free boxes covering w = s + shift for s in region; zeta's pole w = 1 acknowledged when inside."""
    out = []
    for (dre, dim), label in shifts:
        b = region.shifted(dre, dim)
        ack = ((1, 0),) if (b.re0 < 1 < b.re1 and b.im0 < 0 < b.im1) else ()
        if not ack and b.contains_point(1, 0):
            raise AssertionError("pole of zeta on an exclusion-box boundary")
        out.append(ZetaZeroFree(b, ack, f"{why}: no zero of zeta({label}) for s in the region"))
    return tuple(out)


_TW_SHIFTS = ((((1 - B0), -G0), "s+1-rho0"), (((1 - B0), G0), "s+1-conj rho0"))
_SYM_SHIFTS = _TW_SHIFTS + ((((B0 - 1), G0), "s+rho0-1"), (((B0 - 1), -G0), "s+conj rho0-1"))

_S_MEMO = "rh-team:wall4/S/selberg.md"
_S_REVIEW = "e9-research:review_wall4_S/REVIEW_wall4_S_2026-10-14.md"
_B_MEMO = "rh-team:wall3/B/beurling3.md"
_B_REVIEW = "e9-research:review_wall3_B/REVIEW_wall3_B_2026-10-14.md"

_TW_COMMON = dict(
    EP=("has", "P (selberg.md 3.4): b(p^k) = (1 - p^{k(rho0-1)} - p^{k(conj rho0-1)})/k, theta = 0, rational primes"),
    R=("has", "P (selberg.md 3.4): |coefficients of 1/TW| <= d_3(n)"),
    F_theta=("partial", "UNDER RH: theta = 1/(4 - 2 beta0) = 0.435 pointwise, theta_2 = beta0 - 1/2 mean square "
                        "(gate0.md, B; bb review); unconditionally only theta <= beta0 + eps"),
    FE=("lacks", "ARB (bb, e9-research:review_wall4_S/out_r2_tw_no_fe.txt): a Gamma-FE would force TW(1-conj rho0) "
                 "= 0, but TW(1-conj rho0) = 0.0875640 + 0.0706352i +- 1e-36"),
    Gamma=("lacks", "no FE at all (see FE)"),
    integer_coefficients=("lacks", "N (selberg.md 3.0): real, non-integer coefficients"),
    density=("has", "P (selberg.md 3.4, unconditional): N_TW(sigma, T) <= N_zeta(sigma, T) + 2"),
)

_ENTRIES = [
    FakeEntry(
        name="EP5", description="Epstein zeta of m^2 + 5n^2: zeta L(chi_-20) + L(chi_-4) L(chi_5) (arb_fakes)",
        series=_named("EP5"), poles=((Fraction(1), Fraction(0)),), region=None,
        pole_basis="P: only pole s = 1, simple (arb_fakes.POLES; from zeta L(chi_-20))",
        zero_box=Box.of("923/1000", "943/1000", "7829/500", "7839/500"),
        ingredients=_ing(
            EP=("lacks", "F (selberg.md 3.0): not multiplicative, a(1) = 2"),
            FE=("has", "P + N (arb_fakes._fe_selfcheck; H validate): Lambda = A^s Gamma(s) Z(s)"),
            Gamma=("has", "P: Gamma(s), mu = 0 (standard)"),
            integer_coefficients=("has", "P: a(n) = r_Q(n)"),
            positivity=("has", "P: a(n) = r_Q(n) >= 0"),
            density=("lacks", "C (Voronin / Lee, via selberg.md 3.1): N(sigma1, sigma2, T) >> T"),
        ),
        conditional="unconditional", known_zeros="off-line zeros >> T (C); first at 0.932969697485 + 15.668249531278i",
        provenance={"memo": "rh-team:wall2/H/README.md; " + _S_MEMO + " 3.1",
                    "review": "e9-research:review_fakes/REVIEW_fakes_EP5_EPQ2_2026-10-14.md",
                    "prior_cert": "telperion/examples/wall2_fakes/certs/offline_zero_boxes.cert.json (same box)"},
    ),
    FakeEntry(
        name="EPQ2", description="Epstein zeta of 2m^2 + 2mn + 3n^2: zeta L(chi_-20) - L(chi_-4) L(chi_5) (arb_fakes)",
        series=_named("EPQ2"), poles=((Fraction(1), Fraction(0)),), region=None,
        pole_basis="P: only pole s = 1, simple (arb_fakes.POLES)",
        zero_box=Box.of("213/250", "109/125", "41757/1000", "41777/1000"),
        ingredients=_ing(
            EP=("lacks", "F: a(1) = 0, a(2) = 2 (arb_fakes docstring), not multiplicative"),
            FE=("has", "P + N (arb_fakes._fe_selfcheck)"),
            Gamma=("has", "P: Gamma(s), mu = 0"),
            integer_coefficients=("has", "P: a(n) = r_Q(n)"),
            positivity=("has", "P: a(n) = r_Q(n) >= 0"),
            density=("lacks", "C (Voronin / Lee, via selberg.md 3.1)"),
        ),
        conditional="unconditional", known_zeros="off-line zeros >> T (C); one at 0.86238551488 + 41.76697325913i",
        provenance={"memo": "rh-team:wall2/H/README.md; " + _S_MEMO + " 3.1",
                    "review": "e9-research:review_fakes/REVIEW_fakes_EP5_EPQ2_2026-10-14.md",
                    "prior_cert": "telperion/examples/wall2_fakes/certs/offline_zero_boxes.cert.json (same box)"},
    ),
    FakeEntry(
        name="DH", description="Davenport-Heilbronn, c = [1, kappa, -kappa, -1, 0] mod 5 (arb_fakes)",
        series=_named("DH"), poles=(), region=None, pole_basis="P: entire (combination of L(s, chi mod 5), chi != chi0)",
        zero_box=Box.of("799/1000", "819/1000", "85689/1000", "85709/1000"),
        ingredients=_ing(
            EP=("lacks", "F (selberg.md 3.0): a(2)a(3) = -kappa^2 != a(6) = 1"),
            FE=("has", "P + N (selberg.md 3.0; arb_fakes._fe_selfcheck)"),
            Gamma=("has", "P: Gamma((s+1)/2), mu = 1/2"),
            integer_coefficients=("lacks", "P: kappa irrational"),
            positivity=("lacks", "P: c(3) = -kappa < 0"),
            density=("lacks", "C (Voronin, Kaczorowski-Kulas, via selberg.md 3.0)"),
        ),
        conditional="unconditional", known_zeros="off-line zeros >> T (C); one at 0.808517 + 85.699348i",
        provenance={"memo": "rh-team:wall2/H/README.md; " + _S_MEMO + " 3.1",
                    "review": "e9-research:review_wall2_H (out_r2_DH.txt)",
                    "prior_cert": "telperion/examples/wall2_fakes/certs/offline_zero_boxes.cert.json (same box)"},
    ),
    FakeEntry(
        name="TW_raw", description="track B's twist zeta(s)/(zeta(s+1-rho0) zeta(s+1-conj rho0)), full twist",
        series=_guarded(_tw_raw), poles=(), region=_TWIST_REGION,
        pole_basis="ARB (certify_pole_exclusion): in the region, a pole needs zeta(s+1-rho0) = 0 or "
                   "zeta(s+1-conj rho0) = 0; zeta is certified zero-free on both image boxes (its pole w = 1 is the "
                   "zero rho0 of TW, acknowledged). Outside the region the poles rho_zeta + rho0 - 1 (Re < 0.85; Re = "
                   "0.35 UNDER RH) and rho0 - 1 - 2k are NOT declared, so boxes there are refused",
        pole_exclusion=_shift_exclusions(_TWIST_REGION, _TW_SHIFTS, "TW"),
        zero_box=_TWIST_BOX,
        ingredients=_ing(**_TW_COMMON, positivity=(
            "lacks", "N (selberg.md 3.0): RAW TW coefficients have mixed sign, min -7.51, 1170 negative for n <= 2e4; "
                     "prime weights negative at p = 23, 53 (S s3_tw_coeffs; T S_almost_s.cert.json)")),
        conditional="zero at rho0 unconditional (ARB); (F)_theta, holomorphy in sigma > 1/2 and Lindelof growth "
                    "there UNDER RH for zeta; poles at rho0 - 1 - 2k unconditional",
        known_zeros="rho0, conj rho0 (simple, from the pole of zeta(s+1-rho0)), and zeta's zeros",
        provenance={"memo": _B_MEMO + "; " + _S_MEMO + " 3.4, 4.3", "review": _B_REVIEW + "; " + _S_REVIEW,
                    "prior_cert": "rh-team:wall3/T/certs/S_request_boxes.cert.json (T's TW box at "
                                  "gamma0 = 14.134725141734693790..., S's string; not in the repo)"},
    ),
    FakeEntry(
        name="TW_fix", description="TW with the primes p < x1 = 2^(1/0.15) = 101.59 left untwisted (track B, "
                                   "B/twist.py make_params: tw = p >= x1)",
        series=_guarded(_tw_fix), poles=(), region=_TWIST_REGION,
        pole_basis="ARB as TW_raw (same zeta exclusion boxes), plus P: the small-prime factors "
                   "(1 - p^(rho0-1-s))^-1 have poles only on Re s = beta0 - 1 = -0.15",
        pole_exclusion=_shift_exclusions(_TWIST_REGION, _TW_SHIFTS, "TW_fix"),
        zero_box=_TWIST_BOX,
        ingredients=_ing(**_TW_COMMON, positivity=(
            "has", "a(n) >= 0 after the small-prime fix (bb, e9-research:review_wall4_S/out_r3_tw_fixed_sign.txt; "
                   "selberg.md 4.3)")),
        conditional="as TW_raw: zero at rho0 unconditional; (F)_theta etc. UNDER RH",
        known_zeros="rho0, conj rho0, and zeta's zeros",
        provenance={"memo": _B_MEMO + " (small-prime fix); rh-team:wall3/B/twist.py make_params; " + _S_MEMO + " 4.3",
                    "review": _B_REVIEW + "; " + _S_REVIEW,
                    "prior_cert": "telperion/examples/wall3/certs/B_twist_REAL.cert.json (gamma0 = 14.134725, a "
                                  "different nearby object)",
                    "script": "telperion/examples/wall3/scripts/b_twist_real.py"},
        notes="TWIST_TAPER (B's alternative fix, all primes twisted with |alpha_p| capped at 0.45) is NOT this entry.",
    ),
    FakeEntry(
        name="ZP", description="zeta(s) P(2^-s), P(T) = 1 - (29/10) T + 2 T^2 (S, drops only theta < 1/2)",
        series=_zp, poles=((Fraction(1), Fraction(0)),), region=None,
        pole_basis="P (selberg.md 3.0): pole only at s = 1 (P(1/2) = 0.05 != 0)",
        zero_box=Box.of("0.823876", "0.823878", "9.064719", "9.064721"),
        ingredients=_ing(
            EP=("partial", "P: Euler product exists, theta = log2 alpha = 0.82388 > 1/2 (the one failing clause)"),
            R=("lacks", "COMPUTED (selberg.md 3.2): coefficients of 1/P grow like (2^k)^0.824"),
            F_theta=("has", "P (selberg.md 3.2): (F)_cnt at theta = 0"),
            FE=("has", "P + N (selberg.md 3.2): Lambda_P(s) = 2^s - c + 2^(1-s) symmetric"),
            Gamma=("has", "P: Gamma(s/2), mu = 0"),
            integer_coefficients=("lacks", "c = 2.9"),
            positivity=("lacks", "a(2) = 1 - 2.9 < 0"),
            density=("lacks", "P: zeros at 0.82388 + 2 pi i k / log 2 for every k"),
        ),
        conditional="unconditional", known_zeros="log2(alpha) + 2 pi i k / log 2 and log2(beta) + 2 pi i k / log 2 for every "
                                                 "integer k (k = 0: real zeros), and zeta's",
        provenance={"memo": _S_MEMO + " 3.2", "review": _S_REVIEW,
                    "prior_cert": "rh-team:wall4/S/out/s2_arb_boxes.cert.json (same box); "
                                  "telperion/examples/wall3/certs/S_almost_s.cert.json (a +-0.01 box)",
                    "script": "rh-team:wall4/S/s2_arb_boxes.py; telperion/examples/wall3/scripts/s_almost_s.py"},
    ),
    FakeEntry(
        name="ZP5", description="zeta(s) (1 - 5 5^-s + 5 25^-s): integer-coefficient ZP",
        series=_zp5, poles=((Fraction(1), Fraction(0)),), region=None,
        pole_basis="P: pole only at s = 1 (factor at s = 1 is 1 - 1 + 1/5 != 0)",
        zero_box=Box.of("0.79898", "0.79902", "3.90395", "3.90398"),
        ingredients=_ing(
            EP=("partial", "P: Euler product, theta = log5((5 + sqrt5)/2) = 0.79899 > 1/2"),
            FE=("has", "P + N (selberg.md 3.0): Lambda_P = 5^s - 5 + 5^(1-s)"),
            Gamma=("has", "P: standard"),
            integer_coefficients=("has", "P: a(n) = 1 - 5[5|n] + 5[25|n]"),
            positivity=("lacks", "a(5) = -4"),
            density=("lacks", "P: periodic zeros"),
        ),
        conditional="unconditional", known_zeros="log5((5 +- sqrt5)/2) + 2 pi i k / log 5, and zeta's",
        provenance={"memo": _S_MEMO + " 3.0", "review": _S_REVIEW,
                    "prior_cert": "telperion/examples/wall3/certs/S_almost_s.cert.json (ZP5_zero_box, +-0.01 box)",
                    "script": "rh-team:wall4/S/s2_arb_boxes.py"},
    ),
    FakeEntry(
        name="SH", description="L(s + 3/10, chi_-4) L(s - 3/10, chi_-4) (S, drops Ramanujan)",
        series=_sh, poles=(), region=None, pole_basis="P: entire (chi_-4 non-principal)",
        zero_box=Box.of("0.79999", "0.80001", "6.02094", "6.02096"),
        ingredients=_ing(
            EP=("has", "P (selberg.md 3.3): theta = 0.3 < 1/2"),
            R=("lacks", "P (elementary): 1/SH has coefficient -chi(p)(p^0.3 + p^-0.3) at primes, unbounded "
                        "(Ramanujan (iv) fails too, selberg.md 3.3)"),
            FE=("has", "P + N (selberg.md 3.3)"),
            Gamma=("has", "P: mu = (1 +- 0.3)/2 >= 0, standard"),
            integer_coefficients=("lacks", "a(p) = chi(p)(p^0.3 + p^-0.3)"),
            positivity=("lacks", "chi_-4(3) = -1"),
            density=("lacks", "P: >> T log T zeros on Re 0.8"),
        ),
        conditional="unconditional", known_zeros="rho_L + 3/10 and rho_L - 3/10 for every zero rho_L of L(s, chi_-4)",
        provenance={"memo": _S_MEMO + " 3.3", "review": _S_REVIEW,
                    "prior_cert": "rh-team:wall4/S/out/s2_arb_boxes.cert.json; "
                                  "rh-team:wall3/T/certs/S_request_boxes.cert.json (same box)",
                    "script": "rh-team:wall4/S/s1_almost_s.py"},
        notes="Ramanujan (iv) and absolute convergence for sigma > 1 (i) fail.",
    ),
    FakeEntry(
        name="SYM", description="zeta(s) / [zeta(s+1-rho0) zeta(s+1-conj rho0) zeta(s+rho0-1) zeta(s+conj rho0-1)]",
        series=_guarded(_sym), poles=(), region=_TWIST_REGION,
        pole_basis="ARB (certify_pole_exclusion): in the region a pole needs one of the four shifted zetas to vanish; "
                   "zeta is certified zero-free on all four image boxes. Outside: poles at rho_zeta +- (1 - rho0) "
                   "(Re 0.65 / 0.35 UNDER RH), not declared",
        pole_exclusion=_shift_exclusions(_TWIST_REGION, _SYM_SHIFTS, "SYM"),
        zero_box=_TWIST_BOX,
        ingredients=_ing(
            EP=("has", "P (selberg.md 3.5): theta = 1 - beta0 = 0.15"),
            R=("lacks", "Dirichlet series converges absolutely only for sigma > 1.15"),
            FE=("has", "P + N (selberg.md 3.5): Lambda_SYM(1-s) = Lambda_SYM(s)"),
            Gamma=("lacks", "F: Gamma-ratio of degree -3, not Selberg type"),
            integer_coefficients=("lacks", "complex shifts"),
            density=("has", "P: finitely many off-line zeros"),
        ),
        conditional="unconditional for the zero at rho0; pole locations Re 0.65 / 0.35 UNDER RH",
        known_zeros="rho0, conj rho0, 2 - rho0, 2 - conj rho0 (Re 1.15), and zeta's. NOT 1 - rho0 or rho0 - 1: those "
                    "are zeros of Lambda_SYM from the Gamma-ratio only (bb N: |SYM| = 0.0544, 0.199 there)",
        provenance={"memo": _S_MEMO + " 3.5", "review": _S_REVIEW,
                    "prior_cert": "telperion/examples/wall3/certs/S_almost_s.cert.json (r0 = 0.85 + 14.1347i, a "
                                  "different nearby object)",
                    "script": "telperion/examples/wall3/scripts/s_almost_s.py"},
        notes="Fails (i), (ii), (iv) and the standard Gamma: a scope note, not a single-axiom fake.",
    ),
    FakeEntry(
        name="FF", description="genus-2 function-field fake, q = 3: Z(T) = P(T)/((1-T)(1-3T)), T = 3^-s, "
                               "P = 1 - 2T + 9T^2 - 6T^3 + 9T^4",
        series=_guarded(_ff), poles=(), region=Box.of("3/5", "19/20", -10 ** 6, 10 ** 6),
        pole_basis="P: poles where 3^-s in {1, 1/3}, i.e. on Re s = 0 and Re s = 1 only (outside the region)",
        zero_box=Box.of("0.8747", "0.8749", "1.1848", "1.185"),
        ingredients=_ing(
            EP=("has", "P (e3_ff_fake.py; T E_ff_fake.cert.json): product over places, n_d >= 0 integers, EXACT"),
            FE=("has", "P + EXACT (fe.md 3.3): c4 = q^2 c0, c3 = q c1; chi(s) = q^{(2g-2)(1/2-s)}"),
            Gamma=("lacks", "no archimedean place"),
            integer_coefficients=("has", "EXACT: integer place counts"),
            positivity=("has", "EXACT: n_d >= 0 for all d (T E_ff_fake.cert.json)"),
            density=("lacks", "P: zeros exactly periodic in t, >> T off-line"),
        ),
        conditional="unconditional", known_zeros="Re s = 0.874791603842523617 and 0.125208..., Im = +-1.184895153117 "
                                                 "+ 2 pi k / log 3",
        provenance={"memo": "rh-team:wall3/E/fe.md 3.3", "review": "e9-research:review_wall3_E/REVIEW_wall3_E_2026-10-14.md",
                    "prior_cert": "telperion/examples/wall3/certs/E_ff_fake.cert.json (roots ARB, no winding box)",
                    "script": "rh-team:wall3/E/e3_ff_fake.py; telperion/examples/wall3/scripts/e_ff_fake.py"},
    ),
    FakeEntry(
        name="H", description="H = zeta(s) P_fake(3^-s): the FF fake grafted on as the Euler factor at 3 (a ZP variant)",
        series=_hyb, poles=((Fraction(1), Fraction(0)),), region=None,
        pole_basis="P: pole only at s = 1 (P_fake(1/3) = 99/81 != 0)",
        zero_box=Box.of("0.8747", "0.8749", "1.1848", "1.185"),
        ingredients=_ing(
            EP=("partial", "P (archimedean.md 3.2): Euler product, theta = 0.87479 > 1/2"),
            FE=("has", "P + N (archimedean.md 3.2): Lambda_H = pi^{-s/2} Gamma(s/2) 9^s H"),
            Gamma=("has", "P: Gamma(s/2), standard"),
            integer_coefficients=("has", "P: a(n) = c_{v_3(n)}, partial sums of P"),
            positivity=("lacks", "a(3) = c_1 = -1"),
            density=("lacks", "P: >> T zeros at beta = 0.874792, exactly periodic"),
        ),
        conditional="unconditional", known_zeros="the FF fake's zeros (Re 0.874792 / 0.125208 + 2 pi i k / log 3) and "
                                                 "zeta's",
        provenance={"memo": "rh-team:wall5/D2/archimedean.md 3.2",
                    "review": "e9-research:review_wall5_D2/REVIEW_wall5_D2_2026-10-15.md",
                    "script": "rh-team:wall5/D2/d2_calib.py"},
    ),
    FakeEntry(
        name="N8", description="continuous Beurling system: zeta_P = exp(E1((s-1)v0) - E1((s-rho0)v0) - "
                               "E1((s-conj rho0)v0)), v0 = log 103",
        series=_guarded(_n8), poles=((Fraction(1), Fraction(0)),), region=None,
        pole_basis="P (LEAD_NOTES N8; the Ein form in _n8_series): meromorphic on C, only pole s = 1 (simple)",
        zero_box=_TWIST_BOX,
        ingredients=_ing(
            EP=("has", "formal, positive measure: dPi = (1 - 2u^{beta0-1} cos(gamma0 log u)) du / log u >= 0 on "
                       "[103, inf) (LEAD_NOTES N8; bb in-session check)"),
            R=("has", "measure analogue: total variation of exp*(-dPi) <= dN (LEAD_NOTES N8)"),
            F_theta=("has", "N = Ax + B + O_a(x^-a) for every a > 0 (bb in-session check: holds, theta = 0)"),
            FE=("not recorded", "no FE claimed"),
            Gamma=("n/a", "no FE"),
            integer_coefficients=("n/a", "continuous system: no generalized integers"),
            positivity=("has", "dN = exp*(dPi) is a positive measure"),
            density=("has", "P: only zeros rho0, conj rho0"),
        ),
        conditional="unconditional; status HEURISTIC per LEAD_NOTES N8 until D1 checks it and bb reviews it "
                    "(bb in-session check: HOLDS); the count is wall3-T-telperion's, not this library's",
        known_zeros="rho0 and conj rho0 only (simple)",
        provenance={"memo": "rh-team:wall5/LEAD_NOTES.md N8", "review": "bb in-session check (LEAD_NOTES N8); full "
                    "referee pending", "script": "rh-team:wall5/n8_continuous.py (uses gamma0 = 14.134725; this entry "
                    "uses the full-precision string)",
                    "prior_cert": "telperion/examples/wall3/certs/N8_continuous.cert.json (wall3-T, eda45e020; "
                                  "gamma0 = 14.134725, a different nearby object; its count is T's, not this library's)"},
    ),
]

REGISTRY: dict[str, FakeEntry] = {e.name: e for e in _ENTRIES}


def get(name: str) -> FakeEntry:
    try:
        return REGISTRY[name]
    except KeyError:
        raise KeyError(f"fakes_library: unknown entry {name!r}; have {sorted(REGISTRY)}") from None


def names() -> list[str]:
    return list(REGISTRY)


def _entry(e) -> FakeEntry:
    return e if isinstance(e, FakeEntry) else get(e)


# ------------------------------------------------------------------------------------------------ certification
def _require_region(e: FakeEntry, box: Box):
    if e.region is not None and not e.region.contains_box(box):
        raise ValueError(f"{e.name}: box {box.as_dict()} leaves the region {e.region.as_dict()} on which the declared "
                         f"poles are complete; refused ({e.pole_basis})")


def _poles_in(e: FakeEntry, box: Box):
    return [p for p in e.poles if box.contains_point(*p)]


def certify_entry_box(e, box: Box | None = None, expected: int | None = None, prec: int = 128) -> dict:
    """arb_fakes.certify_zero_box on the entry's evaluator with its declared poles passed automatically.
    Defaults: the registered zero box, expected 1.  Refuses a box outside the entry's region; arb_fakes refuses a
    declared pole on the boundary.  Returns arb_fakes' sidecar plus the entry name."""
    e = _entry(e)
    if box is None:
        if e.zero_box is None:
            raise ValueError(f"{e.name}: no registered zero box")
        box, expected = e.zero_box, (1 if expected is None else expected)
    elif expected is None:
        raise ValueError("certify_entry_box: pass expected with an explicit box")
    _require_region(e, box)
    poles = _poles_in(e, box)
    c = arb_fakes.certify_zero_box(e.series, *box.tuple(), expected=expected, prec=prec,
                                   poles=[(a, b) for a, b in poles])
    c["object"] = e.name
    c["declared_poles_passed"] = [(str(a), str(b)) for a, b in poles]
    return c


def count_entry(e, box: Box, cuts=(), prec: int = 96) -> dict:
    """Rigorous zero count in ``box``, split at the heights ``cuts`` (like arb_fakes.count_offline), with the declared
    poles passed per strip, so each strip's count is winding + poles inside.  Refuses outside the region, and on any
    declared pole lying on a strip boundary (arb_fakes).  ``cuts`` must be strictly increasing and strictly inside
    (im0, im1); this is checked before any winding is computed."""
    e = _entry(e)
    _require_region(e, box)
    cs = [Fraction(c) for c in cuts]
    if any(not (box.im0 < c < box.im1) for c in cs) or any(a >= b for a, b in zip(cs, cs[1:])):
        raise ValueError(f"count_entry({e.name}): cuts {[str(c) for c in cs]} must be strictly increasing and strictly "
                         f"inside ({box.im0}, {box.im1}); refused")
    hs = [box.im0] + cs + [box.im1]
    strips = []
    for a, b in zip(hs, hs[1:]):
        sb = Box(box.re0, box.re1, a, b)
        poles = _poles_in(e, sb)
        st = {}
        w = arb_fakes.rigorous_winding(e.series, *sb.tuple(), prec=prec, stats=st, poles=poles)
        strips.append({"im0": str(a), "im1": str(b), "winding": w, "poles": len(poles), "zeros": w + len(poles),
                       "segments": st["segments"]})
    return {"kind": "offline_zero_count", "trust_class": "arb", "object": e.name, "box": box.as_dict(),
            "strips": strips, "total": sum(s["zeros"] for s in strips), "prec": prec, "conjecture1_proved": False}


def certify_pole_exclusion(e, prec: int = 96) -> list[dict]:
    """Certify every zeta zero-free box behind the entry's pole declaration (expected 0 zeros, zeta's pole at 1
    acknowledged where inside).  Returns the sidecars; raises if any box fails."""
    e = _entry(e)
    out = []
    for z in e.pole_exclusion:
        c = arb_fakes.certify_zero_box("zeta", *z.box.tuple(), expected=0, prec=prec, poles=list(z.ack_poles))
        c["reason"] = z.reason
        out.append(c)
    return out


# ------------------------------------------------------------------------------------------------ calibration
@dataclass(frozen=True)
class Claim:
    """A mechanism's verdict: 'f has no off-line zeros (zeros with Re s != 1/2) in the closed rectangle region'."""
    region: Box
    statement: str = "no off-line zeros"


def _judge(e: FakeEntry, claim, recertify: bool, prec: int) -> dict:
    """One entry's verdict on one claim (raises on a malformed claim; calibrate turns that into an error row)."""
    if claim is None:
        return {"status": "declined"}
    if not isinstance(claim, Claim) or not isinstance(claim.region, Box):
        raise TypeError(f"mechanism returned {type(claim).__name__}, expected Claim(region=Box) or None")
    row = {"claim": claim.region.as_dict()}
    if e.zero_box is None:
        row["status"] = "no_reference_zero"
        return row
    if e.zero_box.re0 <= Fraction(1, 2) <= e.zero_box.re1:
        raise AssertionError(f"{e.name}: registered zero box is not off-line")
    if claim.region.contains_box(e.zero_box):
        if recertify:
            c = certify_entry_box(e, prec=prec)
            row["zero_box_cert"] = {k: c[k] for k in ("zeros_in_box", "winding", "poles_in_box", "prec")}
            if e.pole_exclusion:
                row["pole_exclusion"] = [p["zeros_in_box"] for p in certify_pole_exclusion(e)]
        row.update(status="contradicted", zero_box=e.zero_box.as_dict(),
                   detail=f"{e.name} has a zero in {e.zero_box.as_dict()} inside the claimed region")
    elif claim.region.meets(e.zero_box):
        row["status"] = "inconclusive"
    else:
        row["status"] = "not_contradicted"
    return row


def calibrate(mechanism, entries=None, recertify: bool = False, prec: int = 128) -> dict:
    """Negative-control harness.  ``mechanism(evaluator, meta)`` gets the entry's acb -> acb evaluator (``entry.eval``)
    and its PUBLIC metadata (no zero box, no zero list) and returns a ``Claim`` or None (declines).

    A claim is CONTRADICTED by an entry when the entry's zero box (off-line, exactly one zero; ARB once certified)
    lies inside the claimed region.  A box that only overlaps the region is INCONCLUSIVE (the zero might sit in the
    part outside).  With ``recertify`` the box is re-certified before use, and for region-based entries (TW, SYM)
    so are the zeta zero-free boxes behind the pole list, so "exactly one zero" is ARB end to end.  (Without the
    pole exclusion the verdict is still sound: zeros = winding + poles >= 1.)

    ONE REFERENCE ZERO PER ENTRY.  Each entry carries a single registered zero box, so "not_contradicted" means
    "this entry's reference zero is not in the claimed region", NOT "the claim survives the entry": EP5 has >> T
    off-line zeros, but a claim covering only Im s > 20 is not caught by its box at Im 15.67.  There is no aggregate
    pass flag.  The mechanism sees the entry's name in the metadata; as a negative control that is acceptable.

    Errors are captured PER ENTRY: a mechanism that raises, or returns something that is not Claim(region=Box) or
    None, gets an "error" row and the run continues.
    Returns {"rows": [...], "contradicted": [...], "inconclusive": [...], "declined": [...], "errors": [...]}."""
    rows = []
    for e in (REGISTRY.values() if entries is None else [_entry(x) for x in entries]):
        row = {"entry": e.name}
        try:
            row.update(_judge(e, mechanism(e.eval, e.public_meta()), recertify, prec))
        except Exception as exc:  # a crashing mechanism or a malformed claim is a finding, not a pass
            row.update(status="error", detail=f"{type(exc).__name__}: {exc}")
        rows.append(row)
    by = lambda st: [r["entry"] for r in rows if r["status"] == st]
    return {"rows": rows, "contradicted": by("contradicted"), "inconclusive": by("inconclusive"),
            "declined": by("declined"), "errors": by("error"), "recertified": recertify, "conjecture1_proved": False}


# ------------------------------------------------------------------------------------------------ provenance
_ROOTS = {"rh-team": ("TELPERION_RH_TEAM", "~/rh-team"), "e9-research": ("TELPERION_E9_RESEARCH", "~/e9-research")}


def resolve_provenance(ref: str) -> Path | None:
    """'rh-team:wall4/S/selberg.md 3.2' -> $TELPERION_RH_TEAM/wall4/S/selberg.md (section suffix dropped).
    Repo-relative 'telperion/...' paths resolve against this checkout.  Returns None for free text."""
    ref = ref.split(";")[0].strip()
    if ":" in ref.split(" ")[0]:
        root, rest = ref.split(":", 1)
        if root in _ROOTS:
            env, default = _ROOTS[root]
            return Path(os.environ.get(env, default)).expanduser() / rest.split(" ")[0]
    if ref.startswith("telperion/"):
        return Path(__file__).resolve().parents[3] / ref.split(" ")[0]
    return None
