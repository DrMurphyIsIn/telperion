"""Rigorous Hardy Z zero enclosures via FLINT's Platt machinery (ctypes shim).

python-flint 0.6.0 bundles libflint with David Platt's rigorous zero-isolation
functions (`acb_dirichlet_hardy_z_zeros`, backed by the FFT-amortized
`acb_dirichlet_platt_multieval` at scale) but does not wrap them.  This module
exposes them through ctypes, returning exact outward-rounded rational intervals
extracted dyadically (`arb_get_interval_fmpz_2exp` — no decimal string parsing).

ROLE IN THE TRUST BOUNDARY: **hints only**.  The campaign driver uses these
enclosures to PLACE rational sign-bracket endpoints (close-pair resolution, the
B0 Bragg refinement pass); every emitted certificate still derives its sign
facts from `arb_enclosure.enclose_lambda` at rational points, exactly as before.
Nothing in the emitted Lean depends on this module's output being correct —
a wrong hint yields a refused or failed certificate, never a wrong one.
conjecture1_proved = False.

    from telperion.arb_platt import hardy_z_zeros
    zs = hardy_z_zeros(1, 5, prec=128)   # [(Fraction lo, Fraction hi), ...]
"""
from __future__ import annotations

import ctypes
import ctypes.util
import glob
import os
from fractions import Fraction

__all__ = ["hardy_z_zeros", "zeta_nzeros", "zeros_in_interval", "PLATT_AVAILABLE"]

# arb_struct in flint 3.x / arb 2.x on 64-bit:
#   arf_struct { fmpz exp; mp_size_t size; mantissa (2 words) } = 32 bytes
#   mag_struct { fmpz exp; mp_limb_t man }                      = 16 bytes
_ARB_SIZE = 48


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
        for fn in ("_arb_vec_init", "_arb_vec_clear", "acb_dirichlet_hardy_z_zeros",
                   "arb_get_interval_fmpz_2exp", "fmpz_init", "fmpz_clear",
                   "fmpz_get_str", "acb_dirichlet_zeta_nzeros", "arb_init",
                   "arb_clear", "arb_set_fmpz", "arb_div_ui"):
            getattr(_L, fn)
        _L._arb_vec_init.restype = ctypes.c_void_p
        _L._arb_vec_init.argtypes = [ctypes.c_long]
        _L._arb_vec_clear.argtypes = [ctypes.c_void_p, ctypes.c_long]
        _L.acb_dirichlet_hardy_z_zeros.restype = None
        _L.fmpz_get_str.restype = ctypes.c_char_p
    except (OSError, AttributeError):
        _L = None

PLATT_AVAILABLE = _L is not None

_fmpz_t = ctypes.c_long * 1


def _fmpz_to_int(f) -> int:
    return int(_L.fmpz_get_str(None, 10, f).decode())


def zeta_nzeros(t: int, prec: int = 96) -> tuple[Fraction, Fraction]:
    """Rigorous enclosure of N(t), the number of zeta zeros with 0 < Im <= t.

    `t` is taken as an exact integer (band edges are integers).  Returns the
    rational [lo, hi] enclosure; when hi - lo < 1 the integer N(t) is pinned."""
    if not PLATT_AVAILABLE:
        raise RuntimeError("libflint with Platt machinery not found")
    # arb_t: single arb_struct
    res = _L._arb_vec_init(1)
    tt = _L._arb_vec_init(1)
    try:
        ft = _fmpz_t(t)
        _L.arb_set_fmpz(ctypes.c_void_p(tt), ft)
        _L.acb_dirichlet_zeta_nzeros(ctypes.c_void_p(res), ctypes.c_void_p(tt),
                                     ctypes.c_long(prec))
        a, b, e = _fmpz_t(0), _fmpz_t(0), _fmpz_t(0)
        for fz in (a, b, e):
            _L.fmpz_init(fz)
        try:
            _L.arb_get_interval_fmpz_2exp(a, b, e, ctypes.c_void_p(res))
            ia, ib, ie = _fmpz_to_int(a), _fmpz_to_int(b), _fmpz_to_int(e)
            return (Fraction(ia) * Fraction(2) ** ie, Fraction(ib) * Fraction(2) ** ie)
        finally:
            for fz in (a, b, e):
                _L.fmpz_clear(fz)
    finally:
        _L._arb_vec_clear(ctypes.c_void_p(res), 1)
        _L._arb_vec_clear(ctypes.c_void_p(tt), 1)


def zeros_in_interval(im_lo: int, im_hi: int, prec: int = 128
                      ) -> list[tuple[Fraction, Fraction]]:
    """Enclosures of every zero ordinate in [im_lo, im_hi] (integer band edges).

    Pins N(im_lo) and N(im_hi) rigorously, fetches the consecutive zeros by
    index, and checks they all fall inside the interval with their neighbours
    outside — a fully rigorous (Arb-level) zero inventory for the band."""
    nlo_l, nlo_h = zeta_nzeros(im_lo)
    nhi_l, nhi_h = zeta_nzeros(im_hi)
    import math as _m
    n_lo = _m.floor(nlo_l)
    n_hi = _m.floor(nhi_l)
    if _m.floor(nlo_h) != n_lo:
        raise RuntimeError(f"N({im_lo}) not pinned: [{float(nlo_l)}, {float(nlo_h)}]")
    if _m.floor(nhi_h) != n_hi:
        raise RuntimeError(f"N({im_hi}) not pinned: [{float(nhi_l)}, {float(nhi_h)}]")
    count = n_hi - n_lo
    if count == 0:
        return []
    zs = hardy_z_zeros(n_lo + 1, count, prec)
    for lo, hi in zs:
        if not (im_lo < lo and hi < im_hi):
            raise RuntimeError(f"zero enclosure [{float(lo)},{float(hi)}] escapes band")
    return zs


def hardy_z_zeros(n_start: int, count: int, prec: int = 128) -> list[tuple[Fraction, Fraction]]:
    """Enclosures of consecutive Hardy Z zeros gamma_n, n = n_start .. n_start+count-1.

    Returns exact rational [lo, hi] per zero (outward dyadic endpoints of the Arb
    ball).  1-indexed: n_start = 1 is the first nontrivial zero ~14.1347."""
    if not PLATT_AVAILABLE:
        raise RuntimeError("libflint with Platt machinery not found")
    if n_start < 1 or count < 1:
        raise ValueError("n_start and count must be >= 1")
    vec = _L._arb_vec_init(count)
    try:
        n = _fmpz_t(n_start)
        _L.acb_dirichlet_hardy_z_zeros(ctypes.c_void_p(vec), n,
                                       ctypes.c_long(count), ctypes.c_long(prec))
        out = []
        a, b, e = _fmpz_t(0), _fmpz_t(0), _fmpz_t(0)
        for fz in (a, b, e):
            _L.fmpz_init(fz)
        try:
            for i in range(count):
                p = ctypes.c_void_p(vec + i * _ARB_SIZE)
                _L.arb_get_interval_fmpz_2exp(a, b, e, p)
                ia, ib, ie = _fmpz_to_int(a), _fmpz_to_int(b), _fmpz_to_int(e)
                lo = Fraction(ia) * Fraction(2) ** ie
                hi = Fraction(ib) * Fraction(2) ** ie
                if not lo <= hi:
                    raise RuntimeError(f"non-ordered enclosure at index {i}")
                out.append((lo, hi))
        finally:
            for fz in (a, b, e):
                _L.fmpz_clear(fz)
        return out
    finally:
        _L._arb_vec_clear(ctypes.c_void_p(vec), count)
