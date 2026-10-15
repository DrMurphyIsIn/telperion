"""Arb-rigorous evaluation, zero counting and Li coefficients for the WALL-2 calibration fakes.

conjecture1_proved = False.  Nothing here is progress on RH.  The fakes are functions with a Riemann-type
functional equation and OFF-line zeros; certifying those zeros (and checking that RH-type emitters refuse
them) calibrates the instruments, it says nothing about zeta.

OBJECTS (normalisations match ~/rh-team/wall2/H/harness.py and arb_dh):

    zeta   Riemann zeta.
    EP5    zeta L(chi_-20) + L(chi_-4) L(chi_5) = sum' (m^2 + 5 n^2)^{-s}            (Epstein, a(1) = 2)
    EPQ2   zeta L(chi_-20) - L(chi_-4) L(chi_5) = sum' (2m^2 + 2mn + 3n^2)^{-s}      (Epstein, a(2) = 2)
    DH     Davenport-Heilbronn, c = [1, kappa, -kappa, -1, 0] mod 5 (see arb_dh).

Each L(s, chi mod q) is collapsed onto Hurwitz zetas, L(s, chi) = q^{-s} sum_a chi(a) zeta(s, a/q), exactly as
arb_dh does for DH.  The characters are the Kronecker symbols chi_-4 = (-4/.), chi_5 = (5/.) and
chi_-20 = chi_-4 chi_5, as integer tables.  Every evaluation goes through python-flint ``acb_series``, so the
same code yields a point value, a value on a ball, or a jet (f, f') on a ball.

COMPLETED FUNCTIONS (used for Li coefficients; verified numerically in ``_fe_selfcheck``):

    EP5, EPQ2:  Lambda(s) = A^s Gamma(s) Z(s),  A = sqrt(20)/(2 pi),  Lambda(s) = Lambda(1-s);
                Z has a simple pole at s = 1 and Z(0) = -1, so xi(s) = s(s-1) Lambda(s) is entire with
                xi(0) = xi(1) = 1.
    DH:         xi(s) = (pi/5)^{-(1+s)/2} Gamma((1+s)/2) D(s), entire, xi(s) = xi(1-s), xi(0) = sqrt5 (3+kappa)/5.
    zeta:       xi(s) = (s-1) pi^{-s/2} Gamma(s/2+1) zeta(s)  (as in li_coeff).

RIGOROUS WINDING (why arb_dh.winding_number is not enough).  ``arb_dh.winding_number`` looks at f only at
boundary NODES and assumes the argument moves by less than pi between consecutive nodes.  Nothing enforces
this.  Two zeros close to an edge between two nodes can add 2 pi to the true argument change without changing
the sampled quadrants, so the count comes out wrong.  ``rigorous_winding`` encloses f on every boundary SEGMENT
instead.  For a segment with midpoint m and half-length r, it uses the centred form
|f(z) - f(m)| <= r sup_B |f'|, where B is an Arb ball covering the segment and sup_B |f'| comes from an
``acb_series`` jet on B.  It requires the whole image to lie in the disc |w - c| <= |c|/2, with c an exact
centre for f(m).  Then Arg(w/c) is in [-pi/6, pi/6] along the segment, and the continuous argument change over
the segment is exactly Arg(f(q)/c) - Arg(f(p)/c).  A segment that fails is bisected, up to a depth limit, and
past that the routine REFUSES.  The total, divided by 2 pi, is an Arb ball, and it is accepted only if it lies
within 1/4 of a unique integer.  Trust class: Arb interval arithmetic, not kernel.
"""
from __future__ import annotations

import math
from fractions import Fraction

__all__ = [
    "FAKES", "fake_series", "fake_eval", "fake_jet", "rigorous_winding", "certify_zero_box",
    "count_offline", "right_halfplane_nonvanishing", "enclose_li_fake", "CHI_M4", "CHI_5", "CHI_M20",
]

FAKES = ("zeta", "EP5", "EPQ2", "DH")

# Kronecker-symbol tables chi[a] for a = 0..q-1.
CHI_M4 = (0, 1, 0, -1)
CHI_5 = (0, 1, -1, -1, 1)
CHI_M20 = tuple(CHI_M4[a % 4] * CHI_5[a % 5] for a in range(20))


def _flint():
    from flint import acb, acb_series, arb, ctx
    return acb, acb_series, arb, ctx


def _kappa():
    acb, _, arb, _ = _flint()
    s5 = arb(5).sqrt()
    return ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)


def _L_series(s, chi):
    """L(s, chi) for a power series s, chi an integer table mod q."""
    acb, acb_series, arb, _ = _flint()
    q = len(chi)
    acc = None
    for a in range(1, q):
        if chi[a] == 0:
            continue
        term = s.zeta(acb(arb(f"{a}/{q}"))) * chi[a]
        acc = term if acc is None else acc + term
    return (-s * acb(q).log()).exp() * acc


def fake_series(name: str, s):
    """The fake ``name`` composed with the acb_series ``s`` (truncated at ctx.cap)."""
    acb, acb_series, arb, _ = _flint()
    if callable(name):  # a user-supplied analytic function of an acb_series (tests, negative controls)
        return name(s)
    if name == "zeta":
        return s.zeta()
    if name in ("EP5", "EPQ2"):
        sign = 1 if name == "EP5" else -1
        return s.zeta() * _L_series(s, CHI_M20) + sign * (_L_series(s, CHI_M4) * _L_series(s, CHI_5))
    if name == "DH":
        k = acb(_kappa())
        z = [s.zeta(acb(arb(f"{a}/5"))) for a in (1, 2, 3, 4)]
        return (-s * acb(5).log()).exp() * (z[0] - z[3] + k * (z[1] - z[2]))
    raise ValueError(f"arb_fakes: unknown object {name!r}; expected one of {FAKES}")


def _acb_point(re: Fraction, im: Fraction):
    acb, _, arb, _ = _flint()
    return acb(arb(f"{re.numerator}/{re.denominator}"), arb(f"{im.numerator}/{im.denominator}"))


def _frac_interval(x):
    """Outward exact Fraction interval of an arb ball."""
    from .rh_jensen.coefficients import _arb_ball_to_fractions
    return _arb_ball_to_fractions(x)


def _eval_point(name, re: Fraction, im: Fraction, prec: int):
    acb, acb_series, arb, ctx = _flint()
    old = (ctx.prec, ctx.cap)
    try:
        ctx.prec, ctx.cap = prec, 1
        return fake_series(name, acb_series([_acb_point(re, im)])).coeffs()[0]
    finally:
        ctx.prec, ctx.cap = old


def fake_eval(name: str, s_re, s_im, prec: int = 128):
    """Rigorous outward-rounded rectangle (re_lo, re_hi, im_lo, im_hi) of exact Fractions for f(s)."""
    v = _eval_point(name, Fraction(s_re), Fraction(s_im), prec)
    rl, rh = _frac_interval(v.real)
    il, ih = _frac_interval(v.imag)
    return rl, rh, il, ih


def fake_jet(name: str, center, prec: int = 128):
    """(f(B), f'(B)) as acb balls for an acb ball ``center`` (rigorous over the whole ball)."""
    acb, acb_series, arb, ctx = _flint()
    old = (ctx.prec, ctx.cap)
    try:
        ctx.prec, ctx.cap = prec, 2
        c = fake_series(name, acb_series([center, 1])).coeffs()
        return c[0], c[1]
    finally:
        ctx.prec, ctx.cap = old


# ------------------------------------------------------------------------------------------------ winding
def _upper(x) -> Fraction:
    return _frac_interval(x)[1]


def _segment_arg_change(name, p, q, prec, cache):
    """Rigorous argument change of f along the straight segment p -> q (axis-aligned, exact Fraction pairs),
    as an arb ball, or None if the centred-form disc test fails (caller bisects)."""
    acb, acb_series, arb, ctx = _flint()
    (pr, pi_), (qr, qi) = p, q
    mr, mi = (pr + qr) / 2, (pi_ + qi) / 2
    r = max(abs(qr - pr), abs(qi - pi_)) / 2
    old = ctx.prec
    try:
        ctx.prec = prec
        fm = _eval_point(name, mr, mi, prec)
        rad = arb(0, float(r) * (1 + 2.0 ** -40))
        mid = _acb_point(mr, mi)
        ball = mid + (acb(rad) if qi == pi_ else acb(0, rad))
        _, d = fake_jet(name, ball, prec)
        # Arb's zeta/Hurwitz series can return non-finite balls (wide balls at Re s < 0, some sigma = 2 verticals):
        # that is a failed enclosure, so the segment fails and the caller bisects -- it must not crash.
        if not (fm.is_finite() and d.is_finite()):
            return None
        D = _upper(d.abs_upper())
        cr_lo, cr_hi = _frac_interval(fm.real)
        ci_lo, ci_hi = _frac_interval(fm.imag)
        cr, ci = (cr_lo + cr_hi) / 2, (ci_lo + ci_hi) / 2
        rho = r * D + (cr_hi - cr_lo) / 2 + (ci_hi - ci_lo) / 2
        if 4 * rho * rho >= cr * cr + ci * ci:  # need |c| >= 2 rho (strictly)
            return None
        c = _acb_point(cr, ci)
        out = None
        for pt, sgn in ((q, 1), (p, -1)):
            if pt not in cache:
                cache[pt] = _eval_point(name, pt[0], pt[1], prec)
            if not cache[pt].is_finite():
                return None
            a = (cache[pt] / c).arg()
            out = a * sgn if out is None else out + a * sgn
        return out
    finally:
        ctx.prec = old


def _edges(re0, re1, im0, im1):
    c = [(re0, im0), (re1, im0), (re1, im1), (re0, im1)]
    return [(c[k], c[(k + 1) % 4]) for k in range(4)]


def rigorous_winding(name: str, re0, re1, im0, im1, prec: int = 96, init_per_side: int = 8,
                     max_depth: int = 40, stats: dict | None = None, poles=()) -> int:
    """Rigorous winding number of f around [re0,re1] x [im0,im1] (= zeros minus poles inside).

    Returns zeros - poles; for guarded zero counts use certify_zero_box / count_offline.  A box whose CLOSURE
    contains a declared pole (POLES) is refused unless that pole is passed in ``poles`` and lies strictly inside.

    Raises RuntimeError if some boundary segment cannot be certified zero-free down to ``max_depth``
    bisections (a zero on or extremely near the contour), or if the total is not within 1/4 of an integer."""
    acb, acb_series, arb, ctx = _flint()
    re0, re1, im0, im1 = map(Fraction, (re0, re1, im0, im1))
    if not (re0 < re1 and im0 < im1):
        raise ValueError("rigorous_winding: inverted box")
    _pole_guard(name, re0, re1, im0, im1, poles)
    cache: dict = {}
    total = arb(0)
    nseg = 0
    min_len = None
    stack = []
    for (a, b) in reversed(_edges(re0, re1, im0, im1)):
        pts = [(a[0] + (b[0] - a[0]) * Fraction(k, init_per_side), a[1] + (b[1] - a[1]) * Fraction(k, init_per_side))
               for k in range(init_per_side + 1)]
        for k in reversed(range(init_per_side)):
            stack.append((pts[k], pts[k + 1], 0))
    while stack:
        p, q, depth = stack.pop()
        dlt = _segment_arg_change(name, p, q, prec, cache)
        if dlt is None:
            if depth >= max_depth:
                raise RuntimeError(f"rigorous_winding({name}): cannot certify segment {p}->{q} zero-free at depth "
                                   f"{depth}; a zero may lie on the contour -- move the box edge")
            m = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
            stack.append((m, q, depth + 1))
            stack.append((p, m, depth + 1))
            continue
        total += dlt
        nseg += 1
        L = max(abs(q[0] - p[0]), abs(q[1] - p[1]))
        min_len = L if min_len is None else min(min_len, L)
    old = ctx.prec
    ctx.prec = prec
    try:
        w = total / (2 * arb.pi())
    finally:
        ctx.prec = old
    lo, hi = _frac_interval(w)
    k = round((lo + hi) / 2)
    if not (k - Fraction(1, 4) < lo and hi < k + Fraction(1, 4)):
        raise RuntimeError(f"rigorous_winding({name}): total/2pi = [{float(lo)}, {float(hi)}] not near an integer")
    if stats is not None:
        stats.update(segments=nseg, min_segment=str(min_len), evals=len(cache), winding_ball=(str(lo), str(hi)))
    return k


# Declared poles (all simple): zeta, EP5, EPQ2 have s = 1; DH is entire.  A callable has none declared.
POLES = {"zeta": ((1, 0),), "EP5": ((1, 0),), "EPQ2": ((1, 0),), "DH": ()}


def _pole_guard(name, re0, re1, im0, im1, poles):
    """Refuse a box whose CLOSURE contains a declared pole, unless the caller passes that pole in ``poles``
    (then it must lie strictly inside, and the winding counts zeros minus poles).  Returns #acknowledged poles."""
    re0, re1, im0, im1 = map(Fraction, (re0, re1, im0, im1))
    ack = {(Fraction(a), Fraction(b)) for a, b in (poles or ())}
    declared = {(Fraction(a), Fraction(b)) for a, b in (POLES.get(name, ()) if not callable(name) else ())}
    for (a, b) in declared | ack:
        inside_closed = re0 <= a <= re1 and im0 <= b <= im1
        if not inside_closed:
            continue
        if (a, b) not in ack:
            raise ValueError(f"{name}: declared pole {a}+{b}i lies in the closed box [{re0},{re1}]x[{im0},{im1}]; "
                             f"refused (pass poles=[({a}, {b})] to count zeros minus poles)")
        if not (re0 < a < re1 and im0 < b < im1):
            raise ValueError(f"{name}: pole {a}+{b}i lies on the box boundary; refused")
    return sum(1 for (a, b) in ack if re0 < a < re1 and im0 < b < im1)


def certify_zero_box(name: str, re0, re1, im0, im1, expected: int = 1, prec: int = 96, poles=()) -> dict:
    """Rigorous zero count ``expected`` in an open rational box.  A box whose closure contains a declared pole is
    refused unless the pole is passed in ``poles`` (simple poles; then zeros = winding + #poles).
    Re-run at 1.5x precision with a different initial subdivision; both must agree.  Returns a sidecar dict."""
    npoles = _pole_guard(name, re0, re1, im0, im1, poles)
    st1, st2 = {}, {}
    w1 = rigorous_winding(name, re0, re1, im0, im1, prec=prec, init_per_side=8, stats=st1, poles=poles)
    w2 = rigorous_winding(name, re0, re1, im0, im1, prec=prec + prec // 2, init_per_side=13, stats=st2, poles=poles)
    if w1 != w2 or w1 + npoles != expected:
        raise ValueError(f"certify_zero_box({name}): windings {w1}, {w2} with {npoles} pole(s); expected "
                         f"{expected} zeros -- refused")
    re0, re1, im0, im1 = map(Fraction, (re0, re1, im0, im1))
    return {
        "kind": "winding_box_zero", "trust_class": "arb", "object": name,
        "box": {"re0": str(re0), "re1": str(re1), "im0": str(im0), "im1": str(im1)},
        "winding": w1, "zeros_in_box": w1 + npoles, "poles_in_box": npoles,
        "method": "segment-enclosure (centred form, |f - c| <= |c|/2 per segment)",
        "prec": prec, "recheck_prec": prec + prec // 2, "segments": st1["segments"],
        "recheck_segments": st2["segments"], "min_segment": st1["min_segment"],
        "off_line": bool(re0 > Fraction(1, 2) or re1 < Fraction(1, 2)),
        "conjecture1_proved": False,
    }


def right_halfplane_nonvanishing(name: str, sigma, prec: int = 128) -> dict:
    """Certify f(s) != 0 for all Re s >= sigma by a dominant-term bound.

    Every fake has a Dirichlet series sum a(n) n^{-s} whose |a(n)| is an explicit nonnegative series:
      EP5/EPQ2: a(n) = r_Q(n) >= 0, so sum |a(n)| n^{-sigma} = f(sigma) itself;
      DH: sum |c(n)| n^{-sigma} = 5^{-sigma}[zeta(sigma,1/5) + kappa zeta(sigma,2/5) + kappa zeta(sigma,3/5) + zeta(sigma,4/5)].
    With n0 the first index where a(n0) != 0 (EP5, DH: n0 = 1; EPQ2: n0 = 2), we need
      R(sigma) = sum_{n > n0} |a(n)| (n0/n)^sigma < |a(n0)|,
    which is monotone in sigma, so it holds on the whole half-plane Re s >= sigma."""
    acb, acb_series, arb, ctx = _flint()
    sig = Fraction(sigma)
    old = ctx.prec
    ctx.prec = prec
    try:
        x = arb(f"{sig.numerator}/{sig.denominator}")
        if name in ("EP5", "EPQ2"):
            total = _eval_point(name, sig, Fraction(0), prec).real
            n0, a0 = (1, 2) if name == "EP5" else (2, 2)
        elif name == "DH":
            k = _kappa()
            zs = [acb(x).zeta(acb(arb(f"{a}/5"))).real for a in (1, 2, 3, 4)]
            total = (-x * arb(5).log()).exp() * (zs[0] + k * zs[1] + k * zs[2] + zs[3])
            n0, a0 = 1, 1
        else:
            raise ValueError("right_halfplane_nonvanishing: EP5, EPQ2 or DH")
        tail = (total - a0 * (-x * arb(n0).log()).exp()) * (x * arb(n0).log()).exp()
        lo, hi = _frac_interval(tail)
    finally:
        ctx.prec = old
    ok = hi < a0
    return {"kind": "dominant_term_nonvanishing", "trust_class": "arb", "object": name, "sigma": str(sig),
            "n0": n0, "a_n0": a0, "tail_upper": str(hi), "tail_upper_float": float(hi), "certified": bool(ok),
            "claim": f"{name}(s) != 0 for all Re s >= {sig}", "conjecture1_proved": False}


def count_offline(name: str, sigma0, sigma1, t0, t1, cuts, prec: int = 96, log=None) -> dict:
    """Rigorous zero count of f in [sigma0, sigma1] x [t0, t1], split into strips at the heights ``cuts``.
    Returns per-strip counts and the total.  Every strip is an independent rigorous winding.
    Refuses if a declared pole lies in the closed box (no pole acknowledgement here: counts are zeros only)."""
    _pole_guard(name, sigma0, sigma1, t0, t1, ())
    hs = [Fraction(t0)] + [Fraction(c) for c in cuts] + [Fraction(t1)]
    strips = []
    for a, b in zip(hs, hs[1:]):
        st = {}
        w = rigorous_winding(name, sigma0, sigma1, a, b, prec=prec, stats=st)
        strips.append({"im0": str(a), "im1": str(b), "winding": w, "segments": st["segments"],
                       "min_segment": st["min_segment"]})
        if log:
            log(f"{name} sigma0={sigma0} [{float(a)},{float(b)}]: {w} ({st['segments']} segs)")
    return {"kind": "offline_zero_count", "trust_class": "arb", "object": name,
            "box": {"re0": str(Fraction(sigma0)), "re1": str(Fraction(sigma1)), "im0": str(hs[0]), "im1": str(hs[-1])},
            "strips": strips, "total": sum(s["winding"] for s in strips), "prec": prec,
            "conjecture1_proved": False}


# ------------------------------------------------------------------------------------------------ Li
def _xi_at(name, g):
    """xi_name(g) for a power series g with constant term 0 (expansion at s = 0)."""
    acb, acb_series, arb, ctx = _flint()
    one = acb_series([1])
    if name == "zeta":
        return (g - one) * (-(g / 2) * acb.pi().log()).exp() * (g / 2 + one).gamma() * g.zeta()
    if name in ("EP5", "EPQ2"):
        logA = (acb(20).sqrt() / (2 * acb.pi())).log()
        return (g - one) * (g + one).gamma() * (g * logA).exp() * fake_series(name, g)
    if name == "DH":
        return (-((one + g) / 2) * (acb.pi() / 5).log()).exp() * ((one + g) / 2).gamma() * fake_series("DH", g)
    raise ValueError(name)


def enclose_li_fake(name: str, count: int, prec_bits: int = 512):
    """Rigorous Fraction enclosures of taylorCoeff xi_name n = [z^n] F'/F, F(z) = xi(1/(1-z)) = xi(-z/(1-z)),
    for n < count; index n is Li's lambda_{n+1} (the li_coeff convention).  Uses the FE xi(s) = xi(1-s)."""
    acb, acb_series, arb, ctx = _flint()
    old = (ctx.prec, ctx.cap)
    try:
        ctx.prec, ctx.cap = prec_bits, count + 1
        z = acb_series([0, 1])
        one = acb_series([1])
        g = -z * (one - z).inv()
        xi = _xi_at(name, g)
        ld = xi.derivative() * xi.inv()
        coeffs = ld.coeffs()[:count]
    finally:
        ctx.prec, ctx.cap = old
    boxes = []
    for c in coeffs:
        im_lo, im_hi = _frac_interval(c.imag)
        if not (im_lo <= 0 <= im_hi):
            raise ValueError(f"enclose_li_fake({name}): coefficient not real -- normalisation broke")
        boxes.append(_frac_interval(c.real))
    return boxes


def _fe_selfcheck(name: str, s=(Fraction(3, 10), Fraction(7)), prec: int = 128) -> float:
    """|xi(s) - xi(1-s)| / |xi(s)| at a test point (float; a guard against a wrong completed function)."""
    acb, acb_series, arb, ctx = _flint()
    old = (ctx.prec, ctx.cap)
    try:
        ctx.prec, ctx.cap = prec, 1
        vals = []
        for (a, b) in (s, (1 - s[0], -s[1])):
            p = _acb_point(a, b)
            gs = acb_series([p])
            one = acb_series([1])
            if name in ("EP5", "EPQ2"):
                logA = (acb(20).sqrt() / (2 * acb.pi())).log()
                v = gs * (gs - one) * gs.gamma() * (gs * logA).exp() * fake_series(name, gs)
            else:
                v = _xi_at(name, gs)
            vals.append(v.coeffs()[0])
        return float(abs(vals[0] - vals[1]).mid()) / float(abs(vals[0]).mid())
    finally:
        ctx.prec, ctx.cap = old
