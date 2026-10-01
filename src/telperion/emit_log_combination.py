"""Log-combination emitter — the "F*-folding" companion to
``transcendental_enclosure``.

Certifies a rational linear combination of logs-of-rationals bounded by a
rational,

    Σ_i c_i · log(r_i)  ≤  q        (c_i, r_i > 0, q rational),

kernel-checked via Mathlib, by FOLDING the whole combination into a single log
of a rational:

    Σ c_i·log(r_i) = log(∏ r_i^{c_i}),

and then discharging by ONE of two routes:

* **monotone route** (used when ``q = 0``, or absorbable into the fold): reduce
  to the rational power inequality ``∏ r_i^{c_i} ≤ 1``.  After clearing
  denominators this is a ``norm_num`` fact on integer powers, and the log side
  closes with ``Real.log_le_log`` (monotonicity) / ``Real.log_nonpos``.
* **tangent route** (used when ``q > 0``): ``log(∏ r_i^{c_i}) ≤ ∏ r_i^{c_i} − 1``
  via ``Real.log_le_sub_one_of_pos``, then ``norm_num`` on ``∏ − 1 ≤ scale·q``.

WHY FOLD (the point vs. independent per-term bounds).  Bounding each ``log(r_i)``
independently above/below (e.g. an ``F*`` lower bound on a subtracted log) loses
slack and is NOT tight at the tie.  Folding into a single log carries the exact
cancellation, so the certificate is TIGHT AT THE TIE — precisely the tightness
the BG ``transcendental_enclosure`` log face is missing.

DOGFOOD (cross-front port validation).  This emitter regenerates, byte-for-proof-
structure, the two kernel-green theorems of the BG proof at
``proof/formalization/R3Cert/BGSCLSubaction.lean`` (``origin/bg/scl-on-main``):

* ``log74_le_4fstar``   : ``Real.log (7/4) ≤ 4 * FSTAR``            (monotone route)
* ``log54_sub_fstar_le``: ``Real.log (5/4) − FSTAR ≤ 1/20``         (tangent route)

with ``FSTAR := Real.log (621/64) / 11`` matching ``BGSCLInduction``.  Both are two
instances of the same parameterized ``emit_body``: an ``FSTAR``-scaled log
combination ``c·log(r) − k·FSTAR ≤ q`` where ``FSTAR = log(B)/N``, folded via the
``N``-th power against ``B``.

EXACT-CANCELLATION face (routes ``exact`` / ``mixed``, see the section below
``log_combination_certificate``): ``Σ cᵢ·log rᵢ = 0`` from the rational identity
``∏ rᵢ^{D·cᵢ} = 1`` (zero margin, for tie points where any enclosure fails), and
"value = exact part + bounded part" where only the remainder is enclosed.

Untrusted sympy generator emits Lean 4; the Lean KERNEL is the sole arbiter.  A
wrong certificate is a ``lake build`` FAILURE, never a false theorem.  The
generation-time ``log_combination_certificate`` self-check RAISES ``ValueError``
on a false instance (the negative control).

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
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


def _lean_rat(q) -> str:
    """Render an exact rational as a Lean literal fragment (n or n/d)."""
    q = sp.Rational(q)
    if q.q == 1:
        return f"{q.p}"
    return f"{q.p}/{q.q}"


@dataclass(frozen=True)
class LogCombinationCertificate:
    """A verified rational log-combination bound ``Σ c_i·log(r_i) ≤ q``.

    ``route`` is ``"monotone"`` (``q = 0``, reduce to ``∏ r_i^{c_i} ≤ 1``) or
    ``"tangent"`` (``q > 0``, use ``log ∏ ≤ ∏ − 1`` then a ``norm_num`` fact).

    The combination is expressed in an ``FSTAR``-normalized shape so the two BG
    dogfood targets are two instances of one body:

        ``c·log(r) − k·FSTAR ≤ q``   with   ``FSTAR = log(fstar_base)/fstar_den``.

    Fields (all exact sympy rationals / ints):

    * ``coeff``, ``rat``   — the leading log term ``coeff·log(rat)`` (``coeff`` a
      positive int, ``rat`` a positive rational).
    * ``fstar_coeff``      — the ``k`` in ``− k·FSTAR`` (a positive int).
    * ``fstar_base``, ``fstar_den`` — ``FSTAR = log(fstar_base)/fstar_den``.
    * ``q``                — the rational RHS threshold.
    * ``route``            — ``"monotone"`` | ``"tangent"``.
    * ``fold_value``       — exact rational ``∏ r_i^{c_i}`` (the folded argument):
        - monotone: ``rat^(coeff·fstar_den) / fstar_base^(fstar_coeff)`` compared
          ``≤ 1`` (equivalently ``rat^(coeff·fstar_den) ≤ fstar_base^fstar_coeff``).
        - tangent: ``rat^(coeff·fstar_den) · fstar_base^(−fstar_coeff)`` (here
          ``fstar_den`` scales, see ``tangent_bound``).
    * ``tangent_bound``    — tangent route only: the rational ``fold − 1`` and the
      ``norm_num`` RHS ``fstar_den·q`` it must not exceed.
    """

    coeff: object          # int coefficient c of the leading log term
    rat: object            # positive rational r (leading log argument)
    fstar_coeff: object    # int k in  − k·FSTAR
    fstar_base: object     # B in FSTAR = log(B)/N
    fstar_den: object      # N in FSTAR = log(B)/N
    q: object              # rational RHS threshold
    route: str             # "monotone" | "tangent"
    fold_value: object     # exact rational ∏ r_i^{c_i}
    tangent_bound: object = None   # tangent route: exact rational (fold − 1)


def log_combination_certificate(
    *, terms, q, route,
    fstar_base=sp.Integer(621) / 64, fstar_den=11,
):
    """Build and EXACTLY self-check a log-combination bound ``Σ c_i·log(r_i) ≤ q``.

    ``terms`` is a list ``[(coeff, rational), ...]`` in the ``FSTAR``-normalized
    encoding: the FIRST entry is the leading positive log term ``(c, r)`` and the
    SECOND is the ``FSTAR`` term ``(−k, fstar_base)`` (coefficient negative), so
    that ``Σ c_i·log(r_i) = c·log(r) − k·log(B)/1`` scaled — see below.  Concretely
    the certified statement is

        ``c·log(r) − k·FSTAR ≤ q``,   ``FSTAR = log(B)/N``  (``B=fstar_base``,
        ``N=fstar_den``),

    which multiplied by ``N`` folds to ``log( r^{cN} / B^{k} ) ≤ N·q``.

    Self-check (exact over ℚ where the argument is rational, else high precision;
    ANY failure raises ``ValueError`` — the NEGATIVE CONTROL):

    * **monotone route** (``q = 0``): the fold is ``F = r^{cN} / B^{k}`` and the
      bound ``c·log(r) − k·FSTAR ≤ 0`` holds iff ``F ≤ 1`` (i.e.
      ``r^{cN} ≤ B^{k}``).  REFUSE if ``F > 1``.
    * **tangent route** (``q > 0``): the fold is ``F = r^{cN} · B^{−k}`` and the
      Lean route discharges ``log F ≤ F − 1`` then ``F − 1 ≤ N·q`` by ``norm_num``.
      So the sufficient rational fact is ``F − 1 ≤ N·q``.  REFUSE if that fails.
      (This is a genuine sufficient condition: ``log F ≤ F − 1`` always, so
      ``N(c·log r − k·FSTAR) = log F ≤ F − 1 ≤ N·q``.)

    NEGATIVE CONTROL examples (see ``__main__``): raise the leading argument so the
    monotone fold ``F > 1`` (e.g. ``log(3) ≤ 4·FSTAR`` is FALSE — ``3^11 = 177147 >
    (621/64)^4`` so ``F ≈ 20 > 1``), or pick a ``q`` too small for the tangent route
    (``F − 1 > N·q``).
    """
    if route not in ("monotone", "tangent", "tight"):
        raise ValueError(
            f"REFUSED: unknown route {route!r} (expected monotone|tangent|tight)"
        )
    if len(terms) != 2:
        raise ValueError(
            "REFUSED: this FSTAR-normalized encoding expects exactly two terms "
            "[(c, r), (-k, fstar_base)] (leading log + FSTAR term)"
        )
    (coeff, rat), (fneg, fbase) = terms
    coeff = sp.Integer(coeff)
    rat = sp.Rational(rat)
    fneg = sp.Integer(fneg)
    fbase = sp.Rational(fbase)
    q = sp.Rational(q)
    B = sp.Rational(fstar_base)
    N = sp.Integer(fstar_den)

    if not (coeff > 0):
        raise ValueError(f"REFUSED: leading coeff must be positive, got {coeff}")
    if not (rat > 0):
        raise ValueError(f"REFUSED: leading log argument must be > 0, got {rat}")
    # The FSTAR term is written  − k·FSTAR  with  k = −fneg.  A NEGATIVE fneg
    # gives the classic subtracted term (+k·FSTAR removed, k>0).  A POSITIVE
    # fneg gives k<0, i.e. an ADDED  +|k|·FSTAR  term — the BG blocker
    # (log(7/9) + FSTAR + 1/24 ≤ 0, k = −1).  monotone/tangent-general-k below
    # keep requiring k>0; the `tight` route and the tangent-general-k branch
    # handle k<0 via a POSITIVE power B^{|k|} (no inverse).
    if fneg == 0:
        raise ValueError(
            f"REFUSED: the FSTAR term coefficient must be NONZERO (− k·FSTAR), "
            f"got {fneg}"
        )
    if route == "monotone" and fneg > 0:
        raise ValueError(
            f"REFUSED: monotone route requires a SUBTRACTED FSTAR term "
            f"(fneg < 0 ⇒ k > 0), got {fneg}"
        )
    if fbase != B:
        raise ValueError(
            f"REFUSED: FSTAR term base {fbase} must equal fstar_base {B}"
        )
    k = -fneg  # multiplier of FSTAR in the − k·FSTAR encoding (k<0 ⇒ +|k|·FSTAR)

    if route == "monotone":
        if q != 0:
            raise ValueError(
                f"REFUSED: monotone route requires q = 0 (or absorbable), got q = {q}"
            )
        # fold F = r^{cN} / B^{k};  bound holds iff F ≤ 1.
        fold = sp.nsimplify(rat ** (coeff * N) / B ** k)
        if not (fold <= 1):
            raise ValueError(
                f"REFUSED: monotone fold r^(cN)/B^k = {fold} > 1 — the bound "
                f"{coeff}·log({rat}) ≤ {k}·FSTAR is FALSE (negative control)"
            )
        return LogCombinationCertificate(
            coeff=coeff, rat=rat, fstar_coeff=k, fstar_base=B, fstar_den=N,
            q=q, route="monotone", fold_value=fold,
        )

    if route == "tight":
        # TIGHT route: for the folded  X = r^{cN}·B^{-k}  and  Q = N·q, discharge
        #   log X ≤ Q   ⟺   X ≤ exp Q   (Real.log_le_iff_le_exp, X>0)
        # with  exp Q = (exp(−Q))⁻¹  (Real.exp_neg), bounding  exp(−Q) ≤ U  by the
        # degree-3 Taylor UPPER bound (Real.exp_bound', needs −Q ∈ [0,1]), then the
        # rational  X·U ≤ 1  (norm_num).  Used exactly where the degree-1 tangent
        # (`log x ≤ x − 1`) is TOO LOOSE: X − 1 > Q.
        fold = sp.nsimplify(rat ** (coeff * N) * B ** (-k))
        if not (fold > 0):
            raise ValueError(
                f"REFUSED: tight route needs fold X > 0, got X = {fold}"
            )
        Q = sp.nsimplify(N * q)
        if not (Q < 0):
            raise ValueError(
                f"REFUSED: tight route requires the folded Q = N·q < 0, got Q = {Q} "
                f"(use the tangent/monotone route for Q ≥ 0)"
            )
        if not (fold < 1):
            raise ValueError(
                f"REFUSED: tight route requires the folded X = r^(cN)·B^(−k) < 1, "
                f"got X = {fold}"
            )
        negQ = -Q  # = −N·q > 0; the exponent for the Taylor exp upper bound.
        if not (0 <= negQ <= 1):
            raise ValueError(
                f"REFUSED: tight route needs −Q = {negQ} ∈ [0, 1] for the degree-3 "
                f"exp Taylor upper bound (Real.exp_bound')"
            )
        # NEGATIVE CONTROL (the bound itself): the theorem log X ≤ Q must hold.
        # log is transcendental, so check at high precision.
        log_fold = sp.log(fold)
        if not bool((log_fold - Q).evalf(50) <= 0):
            raise ValueError(
                f"REFUSED: tight bound FALSE — log(X) = {float(log_fold):.6f} > Q = "
                f"{float(Q):.6f}; {coeff}·log({rat}) − {k}·FSTAR ≤ {q} does not hold "
                f"(negative control)"
            )
        # STEER: the tight route is only warranted when the degree-1 tangent is too
        # loose (X − 1 > Q).  Otherwise steer the caller to the cheaper tangent.
        if not (fold - 1 > Q):
            raise ValueError(
                f"REFUSED: tight route unnecessary — tangent suffices "
                f"(X − 1 = {sp.nsimplify(fold - 1)} ≤ Q = {Q}); use route='tangent'"
            )
        # Degree-3 Taylor UPPER bound on exp(−Q): U = 1 + x + x²/2 + 2·x³/9  (x=−Q),
        # matching Real.exp_bound' at n=3:  ∑_{m<3} x^m/m! + x³·4/(6·3).
        x = negQ
        taylor_ub = sp.nsimplify(1 + x + x ** 2 / 2 + sp.Rational(2, 9) * x ** 3)
        # The kernel norm_num fact the emitted proof discharges: X · U ≤ 1.
        if not (fold * taylor_ub <= 1):
            raise ValueError(
                f"REFUSED: tight Taylor upper bound too weak — X·U = "
                f"{sp.nsimplify(fold * taylor_ub)} > 1 (X = {fold}, U = {taylor_ub}); "
                f"the degree-3 exp bound does not close X ≤ exp(Q)"
            )
        return LogCombinationCertificate(
            coeff=coeff, rat=rat, fstar_coeff=k, fstar_base=B, fstar_den=N,
            q=q, route="tight", fold_value=fold, tangent_bound=taylor_ub,
        )

    # tangent route: valid for ANY sign of q. `log x ≤ x − 1` holds for all
    # x > 0, so the only real gate is the norm_num fact `fold − 1 ≤ N·q` below.
    # A negative q is legitimate when the folded product is < 1 — e.g. a parent
    # ρ term tightening the bound, as in the corrected BG broom cell
    # (`log(7/4) − 4·FSTAR ≤ −1/2688`, fold ≈ 0.053 < 1).
    fold = sp.nsimplify(rat ** (coeff * N) * B ** (-k))
    if not (fold > 0):
        raise ValueError(f"REFUSED: tangent route needs fold > 0, got fold = {fold}")
    tb = sp.nsimplify(fold - 1)
    if not (tb <= N * q):
        raise ValueError(
            f"REFUSED: tangent norm_num fact fails — fold − 1 = {tb} > N·q = "
            f"{N * q}; the tangent route cannot close {coeff}·log({rat}) − "
            f"{k}·FSTAR ≤ {q} (negative control)"
        )
    return LogCombinationCertificate(
        coeff=coeff, rat=rat, fstar_coeff=k, fstar_base=B, fstar_den=N,
        q=q, route="tangent", fold_value=fold, tangent_bound=tb,
    )


# ---------------------------------------------------------------------------
# EXACT-CANCELLATION face (routes "exact" and "mixed")
# ---------------------------------------------------------------------------
#
# The three routes above certify an INEQUALITY with a rational margin.  At a tie
# point the value is forced to be EXACTLY zero, e.g.
#
#     11·F* = 5·log(3/2) + log(23/18),   F* = log(621/64)/11,
#
# because (3/2)^5·(23/18) = 621/64.  Any enclosure-based check fails there at zero
# margin.  This face certifies the equality itself from the rational identity
# ∏ rᵢ^{eᵢ} = 1 (eᵢ = D·cᵢ integers, D the lcm of the cᵢ denominators), and the
# MIXED form "value = exact part + bounded part": the exact group cancels to 0 and
# only the remainder (further logs of rationals, folded and enclosed by the two
# tangent bounds 1 − 1/X ≤ log X ≤ X − 1, plus an optional opaque real R carried
# with hypothesis bounds) needs an enclosure.
#
# Acknowledgement: distilled from unpublished work communicated by Professor John L.
# Goldwasser.  Only the generic certificate shape is taken; no data from that work is
# used.


@dataclass(frozen=True)
class LogCancellationCertificate:
    """Exact-cancellation certificate (``route`` ``"exact"`` or ``"mixed"``).

    * ``exact_terms`` — ``((cᵢ, rᵢ), ...)`` with ``Σ cᵢ·log rᵢ = 0`` exactly.
    * ``exact_pos`` / ``exact_neg`` — ``((rᵢ, eᵢ), ...)``: the integer-exponent
      split of ``∏ rᵢ^{D·cᵢ} = 1`` into ``∏_pos rᵢ^{eᵢ} = ∏_neg rᵢ^{eᵢ}``
      (all ``eᵢ > 0``); ``exact_scale`` is ``D``.
    * ``rem_terms`` / ``rem_pos`` / ``rem_neg`` / ``rem_scale`` — the same data for
      the remainder group (mixed route only), and ``rem_fold`` the rational
      ``X = ∏_pos / ∏_neg`` with ``Σ dⱼ·log sⱼ = log(X)/D'``.
    * ``opaque`` — ``None`` or ``(R_lo, R_hi)``: an extra real ``R`` with
      hypotheses ``R_lo ≤ R ≤ R_hi`` (the "bounded part" supplied by another
      certificate).
    * ``lo`` / ``hi`` — the certified bounds on the total (``None`` = not claimed).
    """

    route: str
    exact_terms: tuple
    exact_scale: object
    exact_pos: tuple
    exact_neg: tuple
    rem_terms: tuple = ()
    rem_scale: object = 1
    rem_pos: tuple = ()
    rem_neg: tuple = ()
    rem_fold: object = 1
    opaque: object = None
    lo: object = None
    hi: object = None


def _integer_split(terms):
    """``[(c, r)]`` -> ``(D, pos, neg)`` with ``Σ c·log r = (log ∏pos − log ∏neg)/D``."""
    D = sp.Integer(1)
    for c, _ in terms:
        D = sp.ilcm(D, sp.Rational(c).q)
    pos, neg = [], []
    for c, r in terms:
        e = sp.Integer(sp.Rational(c) * D)
        (pos if e > 0 else neg).append((r, abs(e)))
    return sp.Integer(D), tuple(pos), tuple(neg)


def _normalize_terms(terms, what):
    out = []
    for c, r in terms:
        c, r = sp.Rational(c), sp.Rational(r)
        if c == 0:
            raise ValueError(f"REFUSED: zero coefficient in the {what} group")
        if not (r > 0):
            raise ValueError(f"REFUSED: log argument must be > 0 in the {what} group, got {r}")
        out.append((c, r))
    return tuple(out)


def _side_product(side):
    prod = sp.Integer(1)
    for r, e in side:
        prod *= sp.Rational(r) ** int(e)
    return prod


def log_cancellation_certificate(
    *, route, exact_terms, rem_terms=(), opaque=None, lo=None, hi=None,
):
    """Build and EXACTLY self-check an exact-cancellation certificate.

    ``route="exact"``: certify ``Σ cᵢ·log rᵢ = 0`` from ``∏ rᵢ^{D·cᵢ} = 1`` (exact
    over ℚ).  REFUSE if the product is not exactly 1 — the negative control.

    ``route="mixed"``: certify ``lo ≤ V`` and/or ``V ≤ hi`` for
    ``V = Σ_exact cᵢ·log rᵢ + Σ_rem dⱼ·log sⱼ (+ R)``.  The exact group must
    cancel exactly (as above); the remainder folds to ``log(X)/D'`` and is
    enclosed by ``(1 − 1/X)/D' ≤ rem ≤ (X − 1)/D'``; ``R`` (if given) by its
    hypothesis bounds.  REFUSE if the exact group does not cancel, if neither
    bound is claimed, or if a claimed bound does not follow from the enclosure
    (sufficient condition, exact over ℚ).
    """
    if route not in ("exact", "mixed"):
        raise ValueError(f"REFUSED: unknown cancellation route {route!r} (exact|mixed)")
    ex = _normalize_terms(exact_terms, "exact")
    if not ex:
        raise ValueError("REFUSED: the exact group is empty")
    D, pos, neg = _integer_split(ex)
    if _side_product(pos) != _side_product(neg):
        ratio = _side_product(pos) / _side_product(neg)
        raise ValueError(
            f"REFUSED: exact group does not cancel — ∏ rᵢ^(D·cᵢ) = {ratio} ≠ 1 "
            f"(D = {D}); Σ cᵢ·log rᵢ ≠ 0 (negative control)"
        )
    if route == "exact":
        if rem_terms or opaque is not None or lo is not None or hi is not None:
            raise ValueError(
                "REFUSED: route='exact' takes only exact_terms (use route='mixed')")
        return LogCancellationCertificate(
            route="exact", exact_terms=ex, exact_scale=D, exact_pos=pos, exact_neg=neg)

    rem = _normalize_terms(rem_terms, "remainder")
    if not rem and opaque is None:
        raise ValueError(
            "REFUSED: mixed route needs a remainder (log terms and/or an opaque R)")
    if lo is None and hi is None:
        raise ValueError("REFUSED: mixed route needs at least one of lo / hi")
    Dr, rpos, rneg = _integer_split(rem)
    X = _side_product(rpos) / _side_product(rneg)
    rem_hi = (X - 1) / Dr if rem else sp.Integer(0)
    rem_lo = (1 - 1 / X) / Dr if rem else sp.Integer(0)
    if opaque is not None:
        R_lo, R_hi = sp.Rational(opaque[0]), sp.Rational(opaque[1])
        if R_lo > R_hi:
            raise ValueError(f"REFUSED: opaque bounds R_lo = {R_lo} > R_hi = {R_hi}")
        opaque = (R_lo, R_hi)
        rem_hi, rem_lo = rem_hi + R_hi, rem_lo + R_lo
    if hi is not None:
        hi = sp.Rational(hi)
        if not (rem_hi <= hi):
            raise ValueError(
                f"REFUSED: upper enclosure fails — remainder ≤ {rem_hi} > hi = {hi} "
                f"(tangent log X ≤ X − 1 too loose or bound false; negative control)")
    if lo is not None:
        lo = sp.Rational(lo)
        if not (lo <= rem_lo):
            raise ValueError(
                f"REFUSED: lower enclosure fails — remainder ≥ {rem_lo} < lo = {lo} "
                f"(tangent 1 − 1/X ≤ log X too loose or bound false; negative control)")
    return LogCancellationCertificate(
        route="mixed", exact_terms=ex, exact_scale=D, exact_pos=pos, exact_neg=neg,
        rem_terms=rem, rem_scale=Dr, rem_pos=rpos, rem_neg=rneg, rem_fold=X,
        opaque=opaque, lo=lo, hi=hi,
    )


def certify_log_combination_point(family, pt, name):
    """Certify one log-combination instance from ``family.special[1](pt)``.

    ``spec`` is a dict ``{"terms": [(c, r), (-k, fstar_base)], "q": ...,
    "route": "monotone"|"tangent", "fstar_base": ..., "fstar_den": ...}``
    (``fstar_base``/``fstar_den`` optional; default the BG ``621/64`` and ``11``).

    Exact-cancellation face: ``{"route": "exact", "terms": [(c, r), ...]}`` or
    ``{"route": "mixed", "exact_terms": [...], "rem_terms": [...],
    "opaque": (R_lo, R_hi) | None, "lo": ..., "hi": ...}``.
    """
    spec = family.special[1](pt)
    if spec["route"] in ("exact", "mixed"):
        if spec["route"] == "exact":
            cert = log_cancellation_certificate(route="exact", exact_terms=spec["terms"])
        else:
            cert = log_cancellation_certificate(
                route="mixed", exact_terms=spec["exact_terms"],
                rem_terms=spec.get("rem_terms", ()), opaque=spec.get("opaque"),
                lo=spec.get("lo"), hi=spec.get("hi"),
            )
        inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
        return inst, 1
    kwargs = dict(terms=spec["terms"], q=spec["q"], route=spec["route"])
    if "fstar_base" in spec:
        kwargs["fstar_base"] = spec["fstar_base"]
    if "fstar_den" in spec:
        kwargs["fstar_den"] = spec["fstar_den"]
    cert = log_combination_certificate(**kwargs)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class LogCombinationEmitter(Emitter):
    """Emit the F*-folding log-combination theorem for a normalized instance.

    The certified statement is ``c·log(r) − k·FSTAR ≤ q`` with
    ``FSTAR = log(B)/N`` supplied by the file prelude (``noncomputable def FSTAR``).

    monotone route (``q = 0``) emits (dogfood TARGET 1 shape, ``log74_le_4fstar``):

        theorem <name> : (c : ℝ) * Real.log (r) ≤ (k : ℝ) * FSTAR := by
          rw [FSTAR]
          have key : N * (c * Real.log r) ≤ k * Real.log B := by
            have e1 : Real.log (r ^ (cN : ℕ)) = (cN) * Real.log r := by rw [Real.log_pow]; norm_num
            have e2 : Real.log (B ^ (k : ℕ)) = k * Real.log B := by rw [Real.log_pow]; norm_num
            have hle : Real.log (r ^ (cN : ℕ)) ≤ Real.log (B ^ (k : ℕ)) :=
              Real.log_le_log (by positivity) (by norm_num)
            rw [e1, e2] at hle; linarith
          linarith

    tangent route (``q > 0``) emits (dogfood TARGET 2 shape, ``log54_sub_fstar_le``):

        theorem <name> : (c : ℝ) * Real.log r − (k : ℝ) * FSTAR ≤ q := by
          rw [FSTAR]
          have hpos : (0 : ℝ) < r ^ (cN : ℕ) * (B⁻¹) := by positivity
          have hr := Real.log_le_sub_one_of_pos hpos
          have hsplit : Real.log (r ^ (cN : ℕ) * (B⁻¹))
              = (cN) * Real.log r − Real.log B := by
            rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
                show (1/B : ℝ) = B⁻¹ by norm_num, Real.log_inv]; push_cast; ring
          rw [hsplit] at hr
          have hnum : r ^ (cN : ℕ) * (B⁻¹) − 1 ≤ N·q := by norm_num
          linarith

    (Where ``c = k = 1`` the leading/FSTAR coefficients degenerate to the exact BG
    surface syntax.)  conjecture1_proved=False."""

    def __post_init__(self):
        self.kind = "log_combination"

    def _emit_monotone(self, cert: LogCombinationCertificate, name: str) -> str:
        c = cert.coeff
        k = cert.fstar_coeff
        N = cert.fstar_den
        cN = int(c * N)
        r = _lean_rat(cert.rat)
        B = _lean_rat(cert.fstar_base)
        # LHS `c·log(r)`: drop the `c *` when c == 1 to match BG surface syntax.
        lhs = f"Real.log ({r} : ℝ)" if c == 1 else f"({c} : ℝ) * Real.log ({r} : ℝ)"
        # When N == 1, FSTAR = log(B) is a plain rational log, not the prelude
        # FSTAR symbol — emit the direct `k·log(B)` bound (generic non-BG reuse,
        # e.g. 2·log(3/2) ≤ log(9/4)) with NO `rw [FSTAR]` step.
        if N == 1:
            rhs = f"Real.log ({B} : ℝ)" if k == 1 else f"({k} : ℝ) * Real.log ({B} : ℝ)"
            key_lhs = f"{N} * Real.log ({r} : ℝ)" if c == 1 \
                else f"{N} * ({c} * Real.log ({r} : ℝ))"
            return (
                f"-- ===== F*-folding, MONOTONE route (generic, N=1): "
                f"{c}·log({r}) ≤ {k}·log({B}) =====\n"
                f"-- Fold: {c}·log {r} = log({r}^{cN}) ≤ log({B}^{k}) = {k}·log({B}).\n"
                f"-- Reduces to the rational power fact ({r})^{cN} ≤ ({B})^{k} (norm_num).\n"
                f"-- Reuse of the SAME fold beyond BG (no prelude FSTAR symbol).\n"
                f"theorem {name} : {lhs} ≤ {rhs} := by\n"
                f"  have e1 : Real.log (({r} : ℝ) ^ ({cN} : ℕ)) = "
                f"{cN} * Real.log ({r} : ℝ) := by\n"
                f"    rw [Real.log_pow]; norm_num\n"
                f"  have e2 : Real.log (({B} : ℝ) ^ ({k} : ℕ)) = "
                f"{k} * Real.log ({B} : ℝ) := by\n"
                f"    rw [Real.log_pow]; norm_num\n"
                f"  have hle : Real.log (({r} : ℝ) ^ ({cN} : ℕ)) ≤ "
                f"Real.log (({B} : ℝ) ^ ({k} : ℕ)) :=\n"
                f"    Real.log_le_log (by positivity) (by norm_num)\n"
                f"  rw [e1, e2] at hle; linarith\n"
            )
        rhs = f"FSTAR" if k == 1 else f"{k} * FSTAR"
        # key inner statement N·(c·log r) ≤ k·log B, simplified when c == 1.
        key_lhs = f"{N} * Real.log ({r} : ℝ)" if c == 1 \
            else f"{N} * ({c} * Real.log ({r} : ℝ))"
        return (
            f"-- ===== F*-folding, MONOTONE route: {c}·log({r}) ≤ {k}·FSTAR "
            f"(FSTAR = log({B})/{N}) =====\n"
            f"-- Fold: {N}·({c}·log {r}) = log({r}^{cN}) ≤ log({B}^{k}) = {k}·log({B}).\n"
            f"-- Reduces to the rational power fact ({r})^{cN} ≤ ({B})^{k} (norm_num);\n"
            f"-- log-monotonicity (Real.log_le_log) carries it, TIGHT AT THE TIE.\n"
            f"-- DOGFOOD: regenerates BG R3Cert.BGSCL.log74_le_4fstar.\n"
            f"theorem {name} : {lhs} ≤ ({rhs} : ℝ) := by\n"
            f"  rw [FSTAR]\n"
            f"  have key : {key_lhs} ≤ {k} * Real.log ({B} : ℝ) := by\n"
            f"    have e1 : Real.log (({r} : ℝ) ^ ({cN} : ℕ)) = "
            f"{cN} * Real.log ({r} : ℝ) := by\n"
            f"      rw [Real.log_pow]; norm_num\n"
            f"    have e2 : Real.log (({B} : ℝ) ^ ({k} : ℕ)) = "
            f"{k} * Real.log ({B} : ℝ) := by\n"
            f"      rw [Real.log_pow]; norm_num\n"
            f"    have hle : Real.log (({r} : ℝ) ^ ({cN} : ℕ)) ≤ "
            f"Real.log (({B} : ℝ) ^ ({k} : ℕ)) :=\n"
            f"      Real.log_le_log (by positivity) (by norm_num)\n"
            f"    rw [e1, e2] at hle; linarith\n"
            f"  linarith\n"
        )

    def _emit_tangent(self, cert: LogCombinationCertificate, name: str) -> str:
        c = cert.coeff
        k = cert.fstar_coeff
        N = cert.fstar_den
        cN = int(c * N)
        r = _lean_rat(cert.rat)
        B = _lean_rat(cert.fstar_base)
        q = _lean_rat(cert.q)
        Nq = _lean_rat(sp.Rational(cert.fstar_den) * sp.Rational(cert.q))
        Binv = _lean_rat(1 / sp.Rational(cert.fstar_base))  # = B^{-1} as a rational
        lhs = f"Real.log ({r} : ℝ)" if c == 1 else f"({c} : ℝ) * Real.log ({r} : ℝ)"
        fstar_term = f"FSTAR" if k == 1 else f"{k} * FSTAR"
        # folded argument (5/4)^cN * (Binv) with k folded (k==1 assumed for tangent BG).
        split_lhs = f"{cN} * Real.log ({r} : ℝ)" if c == 1 \
            else f"{cN} * ({c} * Real.log ({r} : ℝ))"
        if k != 1 and k > 0:
            # General-k tangent, k > 0: fold (r)^cN · ((B)^k)⁻¹, so the split carries
            # the matching k·log(B) coefficient (the k==1 path below hardcodes k=1 and
            # is kept byte-identical for the BG dogfood).  No log(B) ≥ 0 needed —
            # the coefficient matches exactly, so `linarith` closes for any q sign.
            return (
                f"-- ===== F*-folding, TANGENT route (general k={k}): {c}·log({r}) − "
                f"{k}·FSTAR ≤ {q} (FSTAR = log({B})/{N}) =====\n"
                f"-- Fold: {N}·({c}·log {r} − {k}·FSTAR) = log(({r})^{cN}·(({B})^{k})⁻¹)\n"
                f"-- ≤ ({r})^{cN}·(({B})^{k})⁻¹ − 1  (Real.log_le_sub_one_of_pos); the fold − 1\n"
                f"-- ≤ {Nq} is a rational norm_num fact.  TIGHT AT THE TIE (no F* lower bound).\n"
                f"theorem {name} : {lhs} - ({fstar_term} : ℝ) ≤ ({q} : ℝ) := by\n"
                f"  rw [FSTAR]\n"
                f"  have hpos : (0 : ℝ) < ({r} : ℝ) ^ ({cN} : ℕ) * ((({B} : ℝ) ^ ({k} : ℕ))⁻¹) "
                f":= by positivity\n"
                f"  have hr := Real.log_le_sub_one_of_pos hpos\n"
                f"  have hsplit : Real.log (({r} : ℝ) ^ ({cN} : ℕ) * ((({B} : ℝ) ^ ({k} : ℕ))⁻¹))\n"
                f"      = {split_lhs} - {k} * Real.log ({B} : ℝ) := by\n"
                f"    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,\n"
                f"        Real.log_inv, Real.log_pow]\n"
                f"    push_cast; ring\n"
                f"  rw [hsplit] at hr\n"
                f"  have hnum : ({r} : ℝ) ^ ({cN} : ℕ) * ((({B} : ℝ) ^ ({k} : ℕ))⁻¹) - 1 ≤ {Nq} "
                f":= by norm_num\n"
                f"  linarith\n"
            )
        if k < 0:
            # General-k tangent, k < 0 (ADDED +|k|·FSTAR): fold as a POSITIVE power
            # (r)^cN · (B)^{|k|} (NO inverse), split = cN·log r + |k|·log B via
            # Real.log_mul + Real.log_pow (no Real.log_inv).  linarith closes for any
            # q sign since the |k|·log B coefficient matches exactly.
            ak = -int(k)  # |k|
            # − k·FSTAR = + |k|·FSTAR, so the split is split_lhs + |k|·log B.
            return (
                f"-- ===== F*-folding, TANGENT route (general k={k}, ADDED FSTAR): "
                f"{c}·log({r}) − {k}·FSTAR ≤ {q} (FSTAR = log({B})/{N}) =====\n"
                f"-- Fold: {N}·({c}·log {r} − {k}·FSTAR) = log(({r})^{cN}·({B})^{ak})\n"
                f"-- ≤ ({r})^{cN}·({B})^{ak} − 1  (Real.log_le_sub_one_of_pos); the fold − 1\n"
                f"-- ≤ {Nq} is a rational norm_num fact.  Positive power (no inverse).\n"
                f"theorem {name} : {lhs} - ({fstar_term} : ℝ) ≤ ({q} : ℝ) := by\n"
                f"  rw [FSTAR]\n"
                f"  have hpos : (0 : ℝ) < ({r} : ℝ) ^ ({cN} : ℕ) * (({B} : ℝ) ^ ({ak} : ℕ)) "
                f":= by positivity\n"
                f"  have hr := Real.log_le_sub_one_of_pos hpos\n"
                f"  have hsplit : Real.log (({r} : ℝ) ^ ({cN} : ℕ) * (({B} : ℝ) ^ ({ak} : ℕ)))\n"
                f"      = {split_lhs} + {ak} * Real.log ({B} : ℝ) := by\n"
                f"    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,\n"
                f"        Real.log_pow]\n"
                f"    push_cast; ring\n"
                f"  rw [hsplit] at hr\n"
                f"  have hnum : ({r} : ℝ) ^ ({cN} : ℕ) * (({B} : ℝ) ^ ({ak} : ℕ)) - 1 ≤ {Nq} "
                f":= by norm_num\n"
                f"  linarith\n"
            )
        return (
            f"-- ===== F*-folding, TANGENT route: {c}·log({r}) − {k}·FSTAR ≤ {q} "
            f"(FSTAR = log({B})/{N}) =====\n"
            f"-- Fold: {N}·({c}·log {r} − {k}·FSTAR) = log(({r})^{cN}·({B})⁻¹)\n"
            f"-- ≤ ({r})^{cN}·({B})⁻¹ − 1  (Real.log_le_sub_one_of_pos), and the fold − 1\n"
            f"-- ≤ {Nq} is a rational norm_num fact.  TIGHT AT THE TIE (no F* lower bound).\n"
            f"-- DOGFOOD: regenerates BG R3Cert.BGSCL.log54_sub_fstar_le.\n"
            f"theorem {name} : {lhs} - ({fstar_term} : ℝ) ≤ ({q} : ℝ) := by\n"
            f"  rw [FSTAR]\n"
            f"  have hpos : (0 : ℝ) < ({r} : ℝ) ^ ({cN} : ℕ) * ({Binv}) := by positivity\n"
            f"  have hr := Real.log_le_sub_one_of_pos hpos\n"
            f"  have hsplit : Real.log (({r} : ℝ) ^ ({cN} : ℕ) * ({Binv}))\n"
            f"      = {split_lhs} - Real.log ({B} : ℝ) := by\n"
            f"    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,\n"
            f"        show ({Binv} : ℝ) = ({B} : ℝ)⁻¹ by norm_num, Real.log_inv]\n"
            f"    push_cast; ring\n"
            f"  rw [hsplit] at hr\n"
            f"  have hnum : ({r} : ℝ) ^ ({cN} : ℕ) * ({Binv}) - 1 ≤ {Nq} := by norm_num\n"
            f"  linarith\n"
        )

    def _emit_tight(self, cert: LogCombinationCertificate, name: str) -> str:
        # TIGHT route: discharge  log X ≤ Q  where the degree-1 tangent is too loose.
        #   X = r^{cN}·B^{|k|}  (folded, POSITIVE power for the ADDED +|k|·FSTAR term)
        #   Q = N·q < 0 ,  −Q ∈ [0,1]
        # via  log X ≤ Q ⟺ X ≤ exp Q  (Real.log_le_iff_le_exp, X>0);
        #      exp Q = (exp(−Q))⁻¹   (Real.exp_neg);
        #      exp(−Q) ≤ U           (Real.exp_bound', degree-3 Taylor upper);
        #      X·U ≤ 1               (norm_num).
        c = cert.coeff
        k = cert.fstar_coeff
        N = cert.fstar_den
        cN = int(c * N)
        r = _lean_rat(cert.rat)
        B = _lean_rat(cert.fstar_base)
        q = _lean_rat(cert.q)
        Q = sp.Rational(N) * sp.Rational(cert.q)   # folded threshold N·q (< 0)
        Qs = _lean_rat(Q)                          # Lean literal for Q
        negQ = _lean_rat(-Q)                       # −Q ∈ [0,1]
        U = _lean_rat(cert.tangent_bound)          # rational Taylor upper bound on exp(−Q)
        lhs = f"Real.log ({r} : ℝ)" if c == 1 else f"({c} : ℝ) * Real.log ({r} : ℝ)"
        fstar_term = f"FSTAR" if k == 1 else f"{k} * FSTAR"
        split_lhs = f"{cN} * Real.log ({r} : ℝ)" if c == 1 \
            else f"{cN} * ({c} * Real.log ({r} : ℝ))"
        # The fold X = r^{cN}·B^{-k}.  For k > 0 (standard −FSTAR) the B factor is an
        # INVERSE `(B^k)⁻¹` (a negative Nat exponent `B^(-k:ℕ)` is invalid — this is the
        # k>0 bug the BG crosscheck surfaced on log76_gap); for k < 0 (ADDED +|k|·FSTAR)
        # it is the positive power `B^{|k|}`.  The split sign / log_inv follow suit.
        if k >= 0:
            foldB = f"(({B} : ℝ) ^ ({k} : ℕ))⁻¹"
            split_rhs = f"{split_lhs} - {k} * Real.log ({B} : ℝ)"
            split_rw = ("rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,\n"
                        "        Real.log_inv, Real.log_pow]")
        else:
            ak = -int(k)
            foldB = f"(({B} : ℝ) ^ ({ak} : ℕ))"
            split_rhs = f"{split_lhs} + {ak} * Real.log ({B} : ℝ)"
            split_rw = ("rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,\n"
                        "        Real.log_pow]")
        X = f"({r} : ℝ) ^ ({cN} : ℕ) * {foldB}"
        return (
            f"-- ===== F*-folding, TIGHT route (k={k}): {c}·log({r}) − "
            f"{k}·FSTAR ≤ {q} (FSTAR = log({B})/{N}) =====\n"
            f"-- Fold X = ({r})^{cN}·({B})^(−{k}) (≈ {float(cert.fold_value):.4f}); goal ⟺ "
            f"log X ≤ Q = {Qs}.\n"
            f"-- Degree-1 tangent (log x ≤ x−1) is TOO LOOSE here (X−1 > Q); use the TIGHT\n"
            f"-- route: log X ≤ Q ⟺ X ≤ exp Q (Real.log_le_iff_le_exp), exp Q = (exp(−Q))⁻¹\n"
            f"-- (Real.exp_neg), exp(−Q) ≤ U via degree-3 Taylor (Real.exp_bound'), X·U ≤ 1.\n"
            f"theorem {name} : {lhs} - ({fstar_term} : ℝ) ≤ ({q} : ℝ) := by\n"
            f"  rw [FSTAR]\n"
            f"  have hXpos : (0 : ℝ) < {X} := by positivity\n"
            f"  have hsplit : Real.log ({X})\n"
            f"      = {split_rhs} := by\n"
            f"    {split_rw}\n"
            f"    push_cast; ring\n"
            f"  have hexp := Real.exp_bound' (x := ({negQ} : ℝ)) (by norm_num) (by norm_num)\n"
            f"    (n := 3) (by norm_num)\n"
            f"  have hU : (∑ m ∈ Finset.range 3, ({negQ} : ℝ) ^ m / m.factorial)\n"
            f"      + ({negQ} : ℝ) ^ 3 * (3 + 1) / ((3 : ℕ).factorial * 3) ≤ ({U} : ℝ) := by\n"
            f"    norm_num [Finset.sum_range_succ, Nat.factorial]\n"
            f"  have hexpU : Real.exp ({negQ} : ℝ) ≤ ({U} : ℝ) := le_trans hexp hU\n"
            f"  have hexppos : (0 : ℝ) < Real.exp ({negQ} : ℝ) := Real.exp_pos _\n"
            f"  have hprod : {X} * Real.exp ({negQ} : ℝ) ≤ 1 := by\n"
            f"    have hmono : {X} * Real.exp ({negQ} : ℝ)\n"
            f"        ≤ {X} * ({U} : ℝ) :=\n"
            f"      mul_le_mul_of_nonneg_left hexpU (le_of_lt hXpos)\n"
            f"    have hXU : {X} * ({U} : ℝ) ≤ 1 := by norm_num\n"
            f"    linarith\n"
            f"  have hXle : {X} ≤ Real.exp (-({negQ}) : ℝ) := by\n"
            # target the exp inverse explicitly: X may itself contain `(B^k)⁻¹`
            # (k>0 fold), so a bare `← one_div` would rewrite the wrong inverse.
            f"    rw [Real.exp_neg, inv_eq_one_div (Real.exp ({negQ}) : ℝ), "
            f"le_div_iff₀ hexppos]\n"
            f"    linarith [hprod]\n"
            f"  have hlogle : Real.log ({X}) ≤ ({Qs} : ℝ) := by\n"
            f"    rw [Real.log_le_iff_le_exp hXpos]\n"
            f"    have hEq : (-({negQ}) : ℝ) = ({Qs} : ℝ) := by norm_num\n"
            f"    rw [hEq] at hXle; exact hXle\n"
            f"  rw [hsplit] at hlogle\n"
            f"  linarith\n"
        )

    @staticmethod
    def _side_haves(side, tag) -> tuple[str, list[str]]:
        """Lean haves expanding ``log(∏ rᵢ^{eᵢ})`` into ``Σ eᵢ·log rᵢ`` for one side.

        Returns the product expression and the ``have`` lines (per-factor
        ``Real.log_pow`` and left-associated ``Real.log_mul`` steps)."""
        if not side:
            return "(1 : ℝ)", [f"  have {tag}_one : Real.log (1 : ℝ) = 0 := Real.log_one"]
        factors = [f"({_lean_rat(r)} : ℝ) ^ ({int(e)} : ℕ)" for r, e in side]
        out = []
        for j, ((r, e), F) in enumerate(zip(side, factors)):
            out.append(
                f"  have {tag}_f{j} : Real.log ({F}) = ({int(e)} : ℝ) * "
                f"Real.log ({_lean_rat(r)} : ℝ) := by\n"
                f"    rw [Real.log_pow]; norm_num")
        prod = factors[0]
        for j in range(1, len(factors)):
            new = f"{prod} * {factors[j]}"
            out.append(
                f"  have {tag}_m{j} : Real.log ({new})\n"
                f"      = Real.log ({prod}) + Real.log ({factors[j]}) :=\n"
                f"    Real.log_mul (by positivity) (by positivity)")
            prod = new
        return prod, out

    @staticmethod
    def _sum_expr(terms) -> str:
        return " + ".join(
            f"({_lean_rat(c)} : ℝ) * Real.log ({_lean_rat(r)} : ℝ)" for c, r in terms)

    def _emit_cancellation(self, cert: LogCancellationCertificate, name: str) -> str:
        """Emit the exact-cancellation face (``route`` exact | mixed).

        exact:  ``theorem name : Σ cᵢ * Real.log rᵢ = 0`` — per-factor
        ``Real.log_pow``, ``Real.log_mul`` chains on each side, the rational
        identity ``∏pos = ∏neg`` by ``norm_num`` (the load-bearing fact), then
        ``linarith``.  mixed: the same exact block, plus the remainder fold
        ``log(∏pos/∏neg) = log X`` (``Real.log_div`` + ``norm_num``), the tangent
        enclosures ``Real.log_le_sub_one_of_pos`` / ``Real.one_sub_inv_le_log_of_pos``
        and the opaque ``R`` hypotheses, closed by ``linarith``."""
        body: list[str] = []
        ppos, hp = self._side_haves(cert.exact_pos, "ep")
        pneg, hn = self._side_haves(cert.exact_neg, "en")
        body += hp + hn
        body.append(f"  have e_num : ({ppos}) = ({pneg}) := by norm_num")
        body.append(f"  have e_log : Real.log ({ppos}) = Real.log ({pneg}) := by rw [e_num]")
        V = self._sum_expr(cert.exact_terms)
        binders = ""
        if cert.route == "exact":
            head = (
                f"-- ===== log_combination EXACT CANCELLATION: {V} = 0 =====\n"
                f"-- Scale D = {cert.exact_scale}: ∏ rᵢ^(D·cᵢ) = 1 is the rational identity "
                f"below (norm_num);\n"
                f"-- no enclosure, so the certificate holds at ZERO margin.\n")
            stmt = f"{V} = 0"
            body.append("  linarith")
        else:
            if cert.rem_terms:
                V += " + " + self._sum_expr(cert.rem_terms)
                rpos, hrp = self._side_haves(cert.rem_pos, "rp")
                rneg, hrn = self._side_haves(cert.rem_neg, "rn")
                X = _lean_rat(cert.rem_fold)
                body += hrp + hrn
                body.append(
                    f"  have r_div : Real.log (({rpos}) / ({rneg}))\n"
                    f"      = Real.log ({rpos}) - Real.log ({rneg}) :=\n"
                    f"    Real.log_div (by positivity) (by positivity)")
                body.append(f"  have r_fold : (({rpos}) / ({rneg})) = ({X} : ℝ) := by norm_num")
                body.append("  rw [r_fold] at r_div")
                if cert.hi is not None:
                    body.append(f"  have r_up := Real.log_le_sub_one_of_pos "
                                f"(by norm_num : (0 : ℝ) < {X})")
                if cert.lo is not None:
                    inv = _lean_rat(1 - 1 / sp.Rational(cert.rem_fold))
                    body.append(f"  have r_lo := Real.one_sub_inv_le_log_of_pos "
                                f"(by norm_num : (0 : ℝ) < {X})")
                    body.append(f"  have r_inv : (1 : ℝ) - ({X} : ℝ)⁻¹ = {inv} := by norm_num")
            if cert.opaque is not None:
                R_lo, R_hi = cert.opaque
                V += " + R"
                binders = (f" (R : ℝ) (hR_lo : ({_lean_rat(R_lo)} : ℝ) ≤ R)"
                           f" (hR_hi : R ≤ ({_lean_rat(R_hi)} : ℝ))")
            parts = []
            if cert.lo is not None:
                parts.append(f"({_lean_rat(cert.lo)} : ℝ) ≤ {V}")
            if cert.hi is not None:
                parts.append(f"{V} ≤ ({_lean_rat(cert.hi)} : ℝ)")
            stmt = " ∧\n    ".join(parts)
            head = (
                f"-- ===== log_combination MIXED (exact + bounded): "
                f"lo = {cert.lo}, hi = {cert.hi} =====\n"
                f"-- Exact group cancels to 0 (rational identity, zero margin); the "
                f"remainder folds to\n"
                f"-- log({_lean_rat(cert.rem_fold)})/{cert.rem_scale} and is enclosed by "
                f"1 − 1/X ≤ log X ≤ X − 1"
                + (" plus the R hypotheses" if cert.opaque is not None else "") + ".\n")
            body.append("  constructor <;> linarith" if len(parts) == 2 else "  linarith")
        return (
            head
            + f"theorem {name}{binders} :\n    {stmt} := by\n"
            + "\n".join(body) + "\n"
        )

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        nthm = 0
        for inst in fam.instances:
            cert: LogCombinationCertificate = inst.payload  # type: ignore[assignment]
            name = inst.lean_name
            if isinstance(cert, LogCancellationCertificate):
                lines.append(self._emit_cancellation(cert, name))
            elif cert.route == "monotone":
                lines.append(self._emit_monotone(cert, name))
            elif cert.route == "tangent":
                lines.append(self._emit_tangent(cert, name))
            elif cert.route == "tight":
                lines.append(self._emit_tight(cert, name))
            else:  # pragma: no cover — guarded at certify time
                raise ValueError(f"unknown route {cert.route!r}")
            nthm += 1
        return "\n".join(lines), nthm


def log_combination_family(name, grid, lean_name, spec, constants=None):
    """Build a log-combination family (kind='log_combination').

    ``spec``: a callable ``pt -> {"terms": [(c, r), (-k, fstar_base)], "q": ...,
    "route": "monotone"|"tangent", "fstar_base": ..., "fstar_den": ...}``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("log_combination", spec),
        constants=dict(constants or {}),
    )


if __name__ == "__main__":
    print("=== positive: MONOTONE  log(7/4) ≤ 4·FSTAR  (BG log74_le_4fstar) ===")
    c1 = log_combination_certificate(
        terms=[(1, Fraction(7, 4)), (-4, Fraction(621, 64))], q=0, route="monotone",
    )
    print(f"  cert OK: route={c1.route}, fold (7/4)^11/(621/64)^4 = {c1.fold_value} "
          f"(≈ {float(c1.fold_value):.6f}) ≤ 1")

    print("\n=== positive: TANGENT  log(5/4) − FSTAR ≤ 1/20  (BG log54_sub_fstar_le) ===")
    c2 = log_combination_certificate(
        terms=[(1, Fraction(5, 4)), (-1, Fraction(621, 64))], q=Fraction(1, 20),
        route="tangent",
    )
    print(f"  cert OK: route={c2.route}, fold (5/4)^11·(64/621) = {c2.fold_value} "
          f"(≈ {float(c2.fold_value):.6f}); fold−1 = {c2.tangent_bound} "
          f"(≈ {float(c2.tangent_bound):.6f}) ≤ 11·(1/20) = 11/20")

    print("\n=== positive: GENERIC reuse  2·log(3/2) ≤ log(9/4)  (monotone, non-BG) ===")
    c3 = log_combination_certificate(
        terms=[(2, Fraction(3, 2)), (-1, Fraction(9, 4))], q=0, route="monotone",
        fstar_base=Fraction(9, 4), fstar_den=1,
    )
    print(f"  cert OK: route={c3.route}, fold (3/2)^2/(9/4)^1 = {c3.fold_value} ≤ 1")

    print("\n=== NEGATIVE CONTROL: MONOTONE  log(3) ≤ 4·FSTAR is FALSE (fold ≈ 20 > 1) ===")
    try:
        log_combination_certificate(
            terms=[(1, 3), (-4, Fraction(621, 64))], q=0, route="monotone",
        )
        raise SystemExit("FAIL: false monotone combination was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:100]}...")

    print("\n=== NEGATIVE CONTROL: TANGENT  q = 1/100 too small (fold−1 > 11/100) ===")
    try:
        log_combination_certificate(
            terms=[(1, Fraction(5, 4)), (-1, Fraction(621, 64))], q=Fraction(1, 100),
            route="tangent",
        )
        raise SystemExit("FAIL: too-small tangent q was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:100]}...")

    print("\n=== positive: TIGHT  log(7/9) + FSTAR ≤ −1/24  (BG blocker log79_add_fstar) ===")
    c5 = log_combination_certificate(
        terms=[(1, Fraction(7, 9)), (1, Fraction(621, 64))], q=Fraction(-1, 24),
        route="tight",
    )
    print(f"  cert OK: route={c5.route}, fold X = (7/9)^11·(621/64) = {c5.fold_value} "
          f"(≈ {float(c5.fold_value):.6f}) < 1; Taylor U = {c5.tangent_bound} "
          f"(≈ {float(c5.tangent_bound):.6f}); X·U ≈ "
          f"{float(c5.fold_value * c5.tangent_bound):.6f} ≤ 1 "
          f"(degree-1 tangent too loose: X−1 ≈ {float(c5.fold_value) - 1:.4f} > Q = −11/24)")

    print("\n=== NEGATIVE CONTROL: TIGHT  q = −1/12 makes log X > Q (bound FALSE) ===")
    try:
        log_combination_certificate(
            terms=[(1, Fraction(7, 9)), (1, Fraction(621, 64))], q=Fraction(-1, 12),
            route="tight",
        )
        raise SystemExit("FAIL: false tight combination was NOT refused")
    except ValueError as e:
        print(f"  correctly REFUSED: {str(e)[:100]}...")

    print("\n=== NEGATIVE CONTROL: TIGHT  steers to tangent when it suffices ===")
    try:
        log_combination_certificate(
            terms=[(1, Fraction(7, 4)), (-4, Fraction(621, 64))], q=Fraction(-1, 2688),
            route="tight",
        )
        raise SystemExit("FAIL: tangent-suffices tight instance was NOT steered")
    except ValueError as e:
        print(f"  correctly STEERED to tangent: {str(e)[:100]}...")
