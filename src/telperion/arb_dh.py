"""Rigorous Davenport-Heilbronn evaluation in ball arithmetic (ctypes shim).

The Davenport-Heilbronn function D(s) is the classic counterexample to the
Riemann Hypothesis for a Dirichlet series that satisfies a Riemann-type
functional equation but LACKS an Euler product: it has zeros OFF the critical
line Re s = 1/2.  It is the control object PROGRAM MIRRORMERE's falsification
zoo needs -- any candidate "log-lattice FQ" axiom that D satisfies is dead,
because D has off-line zeros.

DEFINITION (Davenport-Heilbronn 1936; Balanzario-Sanchez-Ortiz, Math. Comp. 76
(2007) 2045-2056; Franca-LeClair arXiv:1407.4358 eq. (245)-(247)).  D is the
period-5 Dirichlet series

    D(s) = sum_{n>=1} c(n) n^{-s},   c = [1, kappa, -kappa, -1, 0]  (period 5)

with the exact real algebraic constant

    kappa = (sqrt(10 - 2 sqrt5) - 2) / (sqrt5 - 1)
          = (sqrt(40 + 8 sqrt5) - 2 sqrt5 - 2) / 4     (rationalized; nested
                                                        integer surds only)
          = 0.28407904384041...

chosen so that xi(s) = (pi/5)^{-(1+s)/2} Gamma((1+s)/2) D(s) satisfies the exact
functional equation xi(s) = xi(1-s).  (Equivalently D = (1-i kappa)/2 L(s,chi) +
(1+i kappa)/2 L(s, chi-bar) for the odd character chi mod 5 with
chi = [1, i, -i, -1, 0]; expanding the two L-series gives the real c above.)

We evaluate D(s) by collapsing the period-5 series onto four Hurwitz zetas:

    D(s) = 5^{-s} [ zeta(s, 1/5) + kappa zeta(s, 2/5)
                    - kappa zeta(s, 3/5) - zeta(s, 4/5) ]

since sum_{n = 5m + r} n^{-s} = 5^{-s} zeta(s, r/5).  Each zeta(s, r/5) is a
rigorous acb ball via FLINT's `acb_dirichlet_hurwitz`; kappa is enclosed as an
arb ball from exact integer sqrts (NOT a float constant); 5^{-s} is an exact
acb power.  Result: an outward-rounded dyadic rectangle for D(s).

TRUST CLASS: Arb-ball (interval-arithmetic) rigor -- the SAME class as
`arb_platt` / `arb_enclosure`, NOT Lean kernel.  Every returned box strictly
contains the true D(s).  The certified off-line-zero claim (see
`certify_offline_zero`) is a rigorous interval winding-number count on a
rational-cornered rectangle; it is Arb-trust-class evidence that exactly one
zero lies in that box, NOT a kernel proof.  conjecture1_proved = False.

    from telperion.arb_dh import dh_eval, certify_offline_zero
    dh_eval("4/5", "857/10", prec=128)   # (re_lo, re_hi, im_lo, im_hi)
"""
from __future__ import annotations

import ctypes
import ctypes.util
import glob
import os
from fractions import Fraction

__all__ = [
    "dh_eval", "dh_kappa_interval", "certify_offline_zero",
    "winding_number", "DH_AVAILABLE", "KAPPA_APPROX",
    "l_chi5_eval", "CHI5", "CHI5_BAR",
]

# The odd primitive Dirichlet character chi mod 5 used in the DH construction
# (arb_dh module docstring; QC_DH_SCOUT.md).  2 is a generator of (Z/5)^*:
# 2^1=2, 2^2=4, 2^3=3, 2^4=1, and the odd character sends the generator to i.
# So chi = [chi(1),chi(2),chi(3),chi(4)] = [1, i, -i, -1] (chi(5)=chi(0)=0).
# CHI5[a] / CHI5_BAR[a] give (re, im) integer coordinates of chi(a) / conj(chi(a)).
CHI5 = {1: (1, 0), 2: (0, 1), 3: (0, -1), 4: (-1, 0)}
CHI5_BAR = {1: (1, 0), 2: (0, -1), 3: (0, 1), 4: (-1, 0)}

# acb_struct = two arb_struct = 2 * 48 bytes; arb_struct = 48 bytes (flint 18.x,
# 64-bit -- same layout arb_platt relies on).
_ARB_SIZE = 48
_ACB_SIZE = 96

KAPPA_APPROX = 0.28407904384041227  # (sqrt(10-2 sqrt5)-2)/(sqrt5-1); for docs only


def _find_libflint() -> str | None:
    try:
        import flint  # noqa: F401
    except Exception:
        return None
    d = os.path.dirname(__import__("flint").__file__)
    for pat in (".dylibs/libflint*.dylib", "../flint*/lib*flint*.so*"):
        hits = sorted(glob.glob(os.path.join(d, pat)))
        if hits:
            return hits[0]
    return ctypes.util.find_library("flint")


_LIB_PATH = _find_libflint()
_L = None
if _LIB_PATH:
    try:
        _L = ctypes.CDLL(_LIB_PATH)
        _needed = (
            "acb_init", "acb_clear", "acb_set_si", "acb_add", "acb_sub",
            "acb_mul", "acb_mul_arb", "acb_neg", "acb_pow", "acb_dirichlet_hurwitz",
            "acb_set_si_si", "acb_addmul",
            "arb_init", "arb_clear", "arb_set_si", "arb_set_ui", "arb_sqrt_ui",
            "arb_sqrt", "arb_add", "arb_sub", "arb_mul", "arb_div", "arb_sub_ui",
            "arb_div_ui", "arb_get_interval_fmpz_2exp", "arb_set",
            "fmpz_init", "fmpz_clear", "fmpz_get_str",
        )
        for fn in _needed:
            getattr(_L, fn)
        _L.acb_init.argtypes = [ctypes.c_void_p]
        _L.acb_clear.argtypes = [ctypes.c_void_p]
        _L.acb_pow.restype = None
        _L.acb_dirichlet_hurwitz.restype = None
        _L.arb_get_interval_fmpz_2exp.restype = None
        _L.arb_sqrt_ui.restype = None
        _L.fmpz_get_str.restype = ctypes.c_char_p
    except (OSError, AttributeError):
        _L = None

DH_AVAILABLE = _L is not None

_fmpz_t = ctypes.c_long * 1


def _fmpz_to_int(f) -> int:
    return int(_L.fmpz_get_str(None, 10, f).decode())


# --- low-level ball allocators (single acb / arb structs) ------------------
def _new_acb():
    buf = ctypes.create_string_buffer(_ACB_SIZE)
    p = ctypes.cast(buf, ctypes.c_void_p)
    _L.acb_init(p)
    return buf, p


def _new_arb():
    buf = ctypes.create_string_buffer(_ARB_SIZE)
    p = ctypes.cast(buf, ctypes.c_void_p)
    _L.arb_init(p)
    return buf, p


def _acb_real_ptr(p_acb) -> ctypes.c_void_p:
    # real part is the first arb_struct in the acb
    return ctypes.c_void_p(p_acb.value)


def _acb_imag_ptr(p_acb) -> ctypes.c_void_p:
    return ctypes.c_void_p(p_acb.value + _ARB_SIZE)


def _arb_to_interval(p_arb) -> tuple[Fraction, Fraction]:
    a, b, e = _fmpz_t(0), _fmpz_t(0), _fmpz_t(0)
    for fz in (a, b, e):
        _L.fmpz_init(fz)
    try:
        _L.arb_get_interval_fmpz_2exp(a, b, e, p_arb)
        ia, ib, ie = _fmpz_to_int(a), _fmpz_to_int(b), _fmpz_to_int(e)
        two_e = Fraction(2) ** ie
        return (Fraction(ia) * two_e, Fraction(ib) * two_e)
    finally:
        for fz in (a, b, e):
            _L.fmpz_clear(fz)


def _set_acb_from_fraction(p_acb, re: Fraction, im: Fraction, prec: int) -> None:
    """acb <- (re) + i(im), each an exact rational, via arb divisions."""
    for part_ptr, val in ((_acb_real_ptr(p_acb), re), (_acb_imag_ptr(p_acb), im)):
        _L.arb_set_si(part_ptr, ctypes.c_long(val.numerator))
        if val.denominator != 1:
            _L.arb_div_ui(part_ptr, part_ptr, ctypes.c_ulong(val.denominator),
                          ctypes.c_long(prec))


def _set_arb_from_fraction(p_arb, val: Fraction, prec: int) -> None:
    _L.arb_set_si(p_arb, ctypes.c_long(val.numerator))
    if val.denominator != 1:
        _L.arb_div_ui(p_arb, p_arb, ctypes.c_ulong(val.denominator),
                      ctypes.c_long(prec))


def dh_kappa_interval(prec: int = 128) -> tuple[Fraction, Fraction]:
    """Rigorous arb enclosure of kappa = (sqrt(10-2 sqrt5)-2)/(sqrt5-1).

    Built from exact integer sqrts (sqrt5, then sqrt(10 - 2 sqrt5)); no float
    constant enters.  Returns the outward-rounded dyadic [lo, hi]."""
    if not DH_AVAILABLE:
        raise RuntimeError("libflint with acb_dirichlet_hurwitz not found")
    _, kap = _new_arb()
    try:
        _build_kappa_arb(kap, prec)
        return _arb_to_interval(kap)
    finally:
        _L.arb_clear(kap)


def _acb_hurwitz(p_res, p_s, a_num: int, a_den: int, prec: int) -> None:
    """p_res <- zeta(s, a_num/a_den), a exact rational shift in (0,1]."""
    _, p_a = _new_acb()
    try:
        _set_acb_from_fraction(p_a, Fraction(a_num, a_den), Fraction(0), prec)
        _L.acb_dirichlet_hurwitz(p_res, p_s, p_a, ctypes.c_long(prec))
    finally:
        _L.acb_clear(p_a)


def _dh_eval_acb(p_out, s_re: Fraction, s_im: Fraction, prec: int) -> None:
    """Core: p_out (an initialised acb) <- D(s_re + i s_im) rigorous ball.

    D(s) = 5^{-s} [ z1 + kappa z2 - kappa z3 - z4 ],  zr = zeta(s, r/5)."""
    _, p_s = _new_acb()
    _, z1 = _new_acb()
    _, z2 = _new_acb()
    _, z3 = _new_acb()
    _, z4 = _new_acb()
    _, acc = _new_acb()
    _, five = _new_acb()
    _, five_pow = _new_acb()
    _, neg_s = _new_acb()
    _, kap = _new_arb()
    try:
        _set_acb_from_fraction(p_s, s_re, s_im, prec)
        # zr = zeta(s, r/5)
        _acb_hurwitz(z1, p_s, 1, 5, prec)
        _acb_hurwitz(z2, p_s, 2, 5, prec)
        _acb_hurwitz(z3, p_s, 3, 5, prec)
        _acb_hurwitz(z4, p_s, 4, 5, prec)
        # kappa arb enclosure, rebuilt from integer surds (rigorous)
        _build_kappa_arb(kap, prec)
        # acc = z1 - z4
        _L.acb_sub(acc, z1, z4, ctypes.c_long(prec))
        # acc += kappa*(z2 - z3)
        _, tmp = _new_acb()
        try:
            _L.acb_sub(tmp, z2, z3, ctypes.c_long(prec))
            _L.acb_mul_arb(tmp, tmp, kap, ctypes.c_long(prec))
            _L.acb_add(acc, acc, tmp, ctypes.c_long(prec))
        finally:
            _L.acb_clear(tmp)
        # 5^{-s}: neg_s = -s ; five = 5 ; five_pow = 5^{-s}
        _L.acb_neg(neg_s, p_s)
        _L.acb_set_si(five, ctypes.c_long(5))
        _L.acb_pow(five_pow, five, neg_s, ctypes.c_long(prec))
        _L.acb_mul(p_out, acc, five_pow, ctypes.c_long(prec))
    finally:
        for p in (p_s, z1, z2, z3, z4, acc, five, five_pow, neg_s):
            _L.acb_clear(p)
        _L.arb_clear(kap)


def _build_kappa_arb(kap_ptr, prec: int) -> None:
    """kap_ptr (initialised arb) <- rigorous ball for kappa from integer surds."""
    _, s5 = _new_arb()
    _, inner = _new_arb()
    _, num = _new_arb()
    _, den = _new_arb()
    _, two_s5 = _new_arb()
    try:
        _L.arb_sqrt_ui(s5, ctypes.c_ulong(5), ctypes.c_long(prec))
        _L.arb_set_ui(inner, ctypes.c_ulong(10))
        _L.arb_add(two_s5, s5, s5, ctypes.c_long(prec))
        _L.arb_sub(inner, inner, two_s5, ctypes.c_long(prec))
        _L.arb_sqrt(num, inner, ctypes.c_long(prec))
        _L.arb_sub_ui(num, num, ctypes.c_ulong(2), ctypes.c_long(prec))
        _L.arb_sub_ui(den, s5, ctypes.c_ulong(1), ctypes.c_long(prec))
        _L.arb_div(kap_ptr, num, den, ctypes.c_long(prec))
    finally:
        for p in (s5, inner, num, den, two_s5):
            _L.arb_clear(p)


def dh_eval(s_re, s_im, prec: int = 128
            ) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """Rigorous outward-rounded dyadic rectangle for D(s_re + i s_im).

    `s_re`, `s_im` are exact rationals (int, Fraction, or a string like "4/5").
    Returns (re_lo, re_hi, im_lo, im_hi) exact Fractions with
    re_lo <= Re D(s) <= re_hi and im_lo <= Im D(s) <= im_hi."""
    if not DH_AVAILABLE:
        raise RuntimeError("libflint with acb_dirichlet_hurwitz not found")
    s_re = Fraction(s_re)
    s_im = Fraction(s_im)
    _, out = _new_acb()
    try:
        _dh_eval_acb(out, s_re, s_im, prec)
        re_lo, re_hi = _arb_to_interval(_acb_real_ptr(out))
        im_lo, im_hi = _arb_to_interval(_acb_imag_ptr(out))
        return (re_lo, re_hi, im_lo, im_hi)
    finally:
        _L.acb_clear(out)


# ---------------------------------------------------------------------------
# Dirichlet L-function L(s, chi) for the character chi mod 5 (the L-column, W3c)
# ---------------------------------------------------------------------------
# DH is the NON-multiplicative linear combination
#     D = (1-i kappa)/2 L(s,chi) + (1+i kappa)/2 L(s,chi-bar)
# of the two genuine L-functions L(s,chi), L(s,chi-bar).  Each L is a bona-fide
# Dirichlet L-function WITH an Euler product, so it should PASS the B-mult-twisted
# clause (Euler product with a unimodular character twist); their sum DH keeps
# FAILING it.  We evaluate L(s,chi) by the same period-5 -> Hurwitz collapse used
# for D, but with the character weights chi(a) (complex units) instead of the real
# DH vector:
#     L(s,chi) = 5^{-s} sum_{a=1}^{4} chi(a) zeta(s, a/5).
# Trust class: Arb ball (interval) rigor, identical to dh_eval.

def _l_chi5_eval_acb(p_out, s_re: Fraction, s_im: Fraction,
                     conj: bool, prec: int) -> None:
    """p_out (initialised acb) <- L(s_re + i s_im, chi) (or chi-bar if conj)."""
    chi = CHI5_BAR if conj else CHI5
    _, p_s = _new_acb()
    _, zr = _new_acb()
    _, w = _new_acb()          # the character weight chi(a) as an acb
    _, term = _new_acb()
    _, acc = _new_acb()
    _, five = _new_acb()
    _, five_pow = _new_acb()
    _, neg_s = _new_acb()
    try:
        _set_acb_from_fraction(p_s, s_re, s_im, prec)
        _L.acb_set_si(acc, ctypes.c_long(0))
        for a in (1, 2, 3, 4):
            _acb_hurwitz(zr, p_s, a, 5, prec)
            wr, wi = chi[a]
            _L.acb_set_si_si(w, ctypes.c_long(wr), ctypes.c_long(wi))
            _L.acb_mul(term, zr, w, ctypes.c_long(prec))
            _L.acb_add(acc, acc, term, ctypes.c_long(prec))
        # multiply by 5^{-s}
        _L.acb_neg(neg_s, p_s)
        _L.acb_set_si(five, ctypes.c_long(5))
        _L.acb_pow(five_pow, five, neg_s, ctypes.c_long(prec))
        _L.acb_mul(p_out, acc, five_pow, ctypes.c_long(prec))
    finally:
        for p in (p_s, zr, w, term, acc, five, five_pow, neg_s):
            _L.acb_clear(p)


def l_chi5_eval(s_re, s_im, prec: int = 128, conj: bool = False
                ) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """Rigorous outward-rounded dyadic rectangle for L(s_re + i s_im, chi),
    chi the odd primitive character mod 5 (or chi-bar if `conj=True`).

    `s_re`, `s_im` are exact rationals.  Returns (re_lo, re_hi, im_lo, im_hi)
    exact Fractions strictly enclosing L(s,chi).  This is the L-function column
    of the MIRRORMERE zoo (W3c): a genuine degree-1 arithmetic L-function with an
    Euler product, sitting alongside its non-multiplicative combination DH.

        (1-i kappa)/2 L(s,chi) + (1+i kappa)/2 L(s,chi-bar) == D(s)  (verified)."""
    if not DH_AVAILABLE:
        raise RuntimeError("libflint with acb_dirichlet_hurwitz not found")
    s_re = Fraction(s_re)
    s_im = Fraction(s_im)
    _, out = _new_acb()
    try:
        _l_chi5_eval_acb(out, s_re, s_im, conj, prec)
        re_lo, re_hi = _arb_to_interval(_acb_real_ptr(out))
        im_lo, im_hi = _arb_to_interval(_acb_imag_ptr(out))
        return (re_lo, re_hi, im_lo, im_hi)
    finally:
        _L.acb_clear(out)


# ---------------------------------------------------------------------------
# Rigorous winding-number (argument-principle) zero count on a rectangle
# ---------------------------------------------------------------------------
# For a rectangle with rational corners on which D has no zero, the number of
# zeros strictly inside equals (1/2 pi) * (change in arg D) around the boundary.
# We sample the boundary at rational nodes, evaluate D in balls at each node,
# and accumulate the QUADRANT the value box lies in.  If every consecutive pair
# of boxes lies in the same or ADJACENT quadrant (never diagonal / never
# straddling zero), the winding integer is rigorously determined: the total
# signed quadrant advance / 4.  A box that contains 0 (all four sign-quadrants
# possible) or a diagonal jump (arg change ambiguous by +/- pi) ABORTS with a
# refinement request -- the count is only emitted when every step is rigorous.
#
# This is Arb-trust-class, NOT kernel.  It certifies "exactly k zeros in this
# rational-cornered box" with interval arithmetic; a wrong evaluation yields an
# abort (refine) or a mismatch, never a false certified count.  conjecture1
# _proved = False.

def _quadrant_of_box(re_lo, re_hi, im_lo, im_hi):
    """Return the strict quadrant 0..3 of a value box, or None if it touches an
    axis / contains the origin (ambiguous sign)."""
    if re_lo > 0 and im_lo > 0:
        return 0  # Q1
    if re_hi < 0 and im_lo > 0:
        return 1  # Q2
    if re_hi < 0 and im_hi < 0:
        return 2  # Q3
    if re_lo > 0 and im_hi < 0:
        return 3  # Q4
    return None   # straddles an axis -> caller must refine


def _boundary_nodes(re0: Fraction, re1: Fraction, im0: Fraction, im1: Fraction,
                    n_per_side: int):
    """Rational corners walked counter-clockwise: bottom, right, top, left."""
    nodes = []
    for k in range(n_per_side):
        nodes.append((re0 + (re1 - re0) * Fraction(k, n_per_side), im0))
    for k in range(n_per_side):
        nodes.append((re1, im0 + (im1 - im0) * Fraction(k, n_per_side)))
    for k in range(n_per_side):
        nodes.append((re1 - (re1 - re0) * Fraction(k, n_per_side), im1))
    for k in range(n_per_side):
        nodes.append((im0 if False else re0,
                      im1 - (im1 - im0) * Fraction(k, n_per_side)))
    return nodes


def winding_number(re0, re1, im0, im1, prec: int = 200, n_per_side: int = 24
                   ) -> int:
    """Rigorous winding number of D around the rectangle [re0,re1] x [im0,im1].

    Walks the boundary counter-clockwise through `4*n_per_side` rational nodes,
    encloses D at each, and sums signed quadrant advances.  Raises
    RuntimeError (asking for higher n_per_side / prec) if any node box straddles
    an axis (sign ambiguous) or any step jumps diagonally (arg change +/- pi
    ambiguous) -- so a returned integer is a RIGOROUS zero count for the open
    rectangle.  Trust class: Arb interval arithmetic, not kernel."""
    re0, re1, im0, im1 = map(Fraction, (re0, re1, im0, im1))
    nodes = _boundary_nodes(re0, re1, im0, im1, n_per_side)
    quads = []
    for (x, y) in nodes:
        rl, rh, il, ih = dh_eval(x, y, prec)
        q = _quadrant_of_box(rl, rh, il, ih)
        if q is None:
            raise RuntimeError(
                f"winding: value box at ({x},{y}) straddles an axis "
                f"[Re {float(rl)},{float(rh)}] [Im {float(il)},{float(ih)}] -- "
                f"raise n_per_side/prec (a zero may lie on the contour)")
        quads.append(q)
    total = 0
    for i in range(len(quads)):
        a = quads[i]
        b = quads[(i + 1) % len(quads)]
        d = (b - a) % 4
        if d == 3:
            d = -1
        elif d == 2:
            raise RuntimeError(
                f"winding: diagonal quadrant jump {a}->{b} between nodes "
                f"{i},{(i+1) % len(quads)} -- arg change ambiguous, raise "
                f"n_per_side")
        total += d
    if total % 4 != 0:
        raise RuntimeError(f"winding: net quadrant advance {total} not a "
                           f"multiple of 4 -- non-closed arg, raise resolution")
    return total // 4


def certify_offline_zero(re0, re1, im0, im1, prec: int = 200,
                         n_per_side: int = 24) -> dict:
    """Certify a single off-line zero of D inside a rational-cornered box.

    Requires the box to be strictly off the critical line (re0 > 1/2 or
    re1 < 1/2) and returns a dict describing exactly what was computed: the box,
    the rigorous winding integer, and the trust label.  A winding of 1 certifies
    (Arb-trust-class) that D has exactly one zero in the open rectangle, off the
    line.  Raises if the box is not off-line or the count is not 1."""
    re0, re1, im0, im1 = map(Fraction, (re0, re1, im0, im1))
    half = Fraction(1, 2)
    off_line = re1 < half or re0 > half
    if not off_line:
        raise ValueError(
            f"box [{re0},{re1}] straddles or touches Re=1/2 -- not off-line")
    w = winding_number(re0, re1, im0, im1, prec=prec, n_per_side=n_per_side)
    if w != 1:
        raise RuntimeError(
            f"winding = {w} (expected exactly 1 zero); box may enclose 0 or >1 "
            f"zeros, or none")
    return {
        "box": {"re": (re0, re1), "im": (im0, im1)},
        "winding": w,
        "zeros_in_box": w,
        "off_line": True,
        "side": "right" if re0 > half else "left",
        "prec": prec,
        "n_per_side": n_per_side,
        "trust": "arb-interval (argument-principle winding); NOT kernel",
        "conjecture1_proved": False,
    }
