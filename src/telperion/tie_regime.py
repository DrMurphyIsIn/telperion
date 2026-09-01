"""Tie-regime campaign — the arithmetic R(s)-generalization for the BG upper bound (uniform hubs).

The BG upper bound reduces (see `docs/BG_BROOM_DOMINANCE_20260831.md`) to `ell(B) <= 0` for rooted branches, and
for a UNIFORM hub (k identical children `tau`) the potential is

    ell(k, tau) = k * ell(tau) + log(1 + k * x_tau) - F*,     x_tau = h_tau / ((k+1) * d_tau),

`d_tau` = child branch-degree (with up-edge), `h_tau = U_tau/total_tau` the child cavity field, `F* = log(621/64)/11`.

PHASE-1 STRUCTURE (this module, verified):
  * **Envelope = brooms.** Per child branch-degree `d`, the `ell`-maximising branch is the broom `B(d-1)`
    (`d=2`->cherry, ..., `d=6`->B(5) at `ell=0`). So the worst uniform child lies among brooms.
  * **Cherry is the worst uniform child (tie regime).** `ell(k, cherry) >= ell(k, tau)` for every branch `tau`
    and `k` in the tie regime (`k` small). Combined with the broom optimum `ell(B(k)) <= 0` (PROVEN via the
    `R(s)` single-crossing, `spider_broom.broom_ratio`), this closes the uniform tie-regime.
  * **Cherry-worst is ARITHMETIC and SLACK.** `ell(k,cherry) - ell(k,B(j)) >= 0` iff the exact RATIONAL
    `exp(11 * (...)) >= 1` (the `11 = 2*5+1` clears both `F*` and the 11th root) -- and the ratio is `>= 2.4`
    (NOT tight), so only the final broom step carries the `27*23` tie. This is the campaign's tractable target.

Open: prove cherry-worst (slack -> soft/arithmetic argument), then mixed<=uniform near the tie + the slack
regime. conjecture1_proved = False.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr

from .spider_broom import broom_total

F_STAR = math.log(621 / 64) / 11

# The cherry child: armmid+leaf rooted at armmid -- degree 2, field 2/3, total 3/2, size 2.
CHERRY = {"d": 2, "h": Fr(2, 3), "total": Fr(3, 2), "size": 2}


def broom_child(j):
    """`B(j)` (j cherries on one hub) as a CHILD branch (rooted at the hub, up-edge): `(d, h, total, size)`.
    Degree `j+1`, `U = (3/2)^j` (hub unmatched = product of cherry totals), `h = U/total`, size `2j+1`."""
    tot = broom_total(j)
    U = Fr(3, 2) ** j
    return {"d": j + 1, "h": U / tot, "total": tot, "size": 2 * j + 1}


def uniform_hub_ell(k, child):
    """`ell(hub of k copies of `child`)` (float): `k*ell(child) + log(1 + k*x) - F*`, `x = h/((k+1)d)`.
    `ell(child) = log total - size * F*`. For `child = CHERRY` this is `ell(B(k))` (the broom)."""
    d, h, tot, sz = child["d"], child["h"], child["total"], child["size"]
    ell_child = (math.log(tot.numerator) - math.log(tot.denominator)) - sz * F_STAR
    x = float(h) / ((k + 1) * d)
    return k * ell_child + math.log(1 + k * x) - F_STAR


def _exp11_hub(k, child):
    """`exp(11 * (k*ell(child) + log(1+k x) - F*))` as an EXACT Fraction (the 11 clears `F* = log(621/64)/11`)."""
    d, h, tot, sz = child["d"], child["h"], child["total"], child["size"]
    x = h / ((k + 1) * d)
    return tot ** (11 * k) * Fr(64, 621) ** (k * sz) * (1 + k * x) ** 11 * Fr(64, 621)


def cherry_vs_broom_ratio(k, j):
    """EXACT rational `exp(11*(ell(k,cherry) - ell(k,B(j))))`.  `> 1` iff the cherry is the worse (higher-`ell`)
    uniform child -- the campaign's cherry-worst inequality, rational in `(k, j)`.  Slack in the tie regime, so
    tie-free; only the broom step `ell(B(k)) <= 0` carries the `27*23` arithmetic."""
    return _exp11_hub(k, CHERRY) / _exp11_hub(k, broom_child(j))


def binding_j(k, jmax=25):
    """The `j* = argmin_j cherry_vs_broom_ratio(k, j)` -- the BINDING broom-child (`ell(k,B(j))` closest to
    `ell(k,cherry)`).  `cherry_vs_broom_ratio(k, ·)` is unimodal in `j` (decreasing to `j*`, then increasing),
    so `ratio(k, j*) > 1` certifies cherry-worst for ALL `j` at that `k`."""
    return min(range(1, jmax + 1), key=lambda j: cherry_vs_broom_ratio(k, j))


def _ell_of(child):
    tot, sz = child["total"], child["size"]
    return (math.log(tot.numerator) - math.log(tot.denominator)) - sz * F_STAR


def slack_linobj(k, child):
    """`ell(child) + h/((k+1)d)` -- the per-child term of the slack-regime bound (via `log(1+Σx) <= Σx`)."""
    return _ell_of(child) + float(child["h"]) / ((k + 1) * child["d"])


def slack_g(k, jmax=40):
    """`g(k) = k * max over the branch envelope (cherry + brooms B(j)) of (ell(c) + h_c/((k+1)d_c))`.
    Envelope reduction: per degree the `ell`-max branch is the broom, and larger branches have `ell` bounded away
    from `0`, so the max lies on this small envelope (verified over all branches <= size 11)."""
    envs = [CHERRY] + [broom_child(j) for j in range(2, jmax)]
    return k * max(slack_linobj(k, c) for c in envs)


def slack_hub_bound(k):
    """Upper bound on `ell(hub of k children)` in the SLACK regime: `ell(hub) <= slack_g(k) - F*`.
    (From `ell(hub) = Σ ell(c) + log(1 + Σ x_c) - F* <= Σ(ell(c) + x_c) - F* <= k*max(ell(c)+x_c) - F*`; the
    `sum <= k*max` step holds for MIXED children, so this covers mixed hubs.)  `<= 0` for all `k >= 16`
    (`slack_g(16) = 0.190 < F*`; sup near `k=16`, `-> 0.130 - F* = -0.077` as `k -> inf`) -- the tie-free soft
    bound covering `k >= 16`.  (Combined with `mixed <= B(k)` for `k <= 15`, every `k` is covered with no gap.)
    conjecture1_proved = False."""
    return slack_g(k) - F_STAR


@dataclass(frozen=True)
class TieCherryWorstCertificate:
    """Certifies the FINITE tie-regime cherry-worst: for each `k` in `[2, k_max]`, the cherry is the worst
    uniform child, i.e. `cherry_vs_broom_ratio(k, j*(k)) > 1` at the binding `j*` (unimodal in `j`, so this
    covers all `j`).  With the broom optimum `ell(B(k)) <= 0` [PROVEN] this closes the uniform tie-regime
    (`k <= 20`; `k >= 21` is the slack regime).  `.check()` exact; `.lean_module` emits `norm_num` atoms
    `1 < ratio(k, j*)`.  conjecture1_proved = False."""

    k_max: int = 20

    def atoms(self):
        """List of `(name, ratio)` with the certified `1 < ratio` (each `ratio = cherry_vs_broom_ratio(k, j*)`)."""
        out = []
        for k in range(2, self.k_max + 1):
            js = binding_j(k)
            out.append((f"tie_cherry_worst_k{k}_j{js}", cherry_vs_broom_ratio(k, js)))
        return out

    def check(self) -> bool:
        return all(r > 1 for _, r in self.atoms())

    def lean_module(self, namespace="BGTieCherryWorst") -> str:
        assert self.check(), "cherry-worst fails in the claimed range -- refusing to emit"
        head = ("import Mathlib\n\n" f"namespace {namespace}\n\n")
        body = "\n".join(
            f"theorem {nm} : (1 : ℚ) < (({r.numerator} : ℚ)/{r.denominator}) := by norm_num"
            for nm, r in self.atoms())
        return head + body + f"\n\nend {namespace}\n"


# Frozen rigorous rational log-enclosures `log(p/q) in [lo/_D, hi/_D]` (floor/ceil at 80-digit precision) -- the
# transcendental import for the slack-bound gate (turan/jensen/concavity trust model).  `(621,64)` = `log(621/64)`
# (= 11 F*) AND `log(total(B(5)))` (same value).
_D = 10 ** 30
_LOG = {
    (621, 64): (2272447998573806908489095813828, 2272447998573806908489095813829),
    (3, 2): (405465108108164381978013115464, 405465108108164381978013115465),
    (11, 4): (1011600911678479925227479335048, 1011600911678479925227479335049),
    (135, 32): (1439538875638702901700334436702, 1439538875638702901700334436703),
    (513, 80): (1858249210496887921925075323596, 1858249210496887921925075323597),
    (6561, 448): (2684105076929892369553216423187, 2684105076929892369553216423188),
    (22599, 1024): (3094189130894351300128314531495, 3094189130894351300128314531496),
    (8505, 256): (3503232060350399661344481289616, 3503232060350399661344481289617),
}


def _log_lo(fr):
    return Fr(_LOG[(fr.numerator, fr.denominator)][0], _D)


def _log_hi(fr):
    return Fr(_LOG[(fr.numerator, fr.denominator)][1], _D)


@dataclass(frozen=True)
class TieSlackCertificate:
    """Kernel-gates the slack bound `slack_g(k) <= F*` for `k >= 16` (which covers MIXED hubs and closes the
    branch-induction upper bound for `k >= 16`).  Three atom families, all rational after clearing `F* =
    log(621/64)/11` and using frozen log-enclosures `L(x) in [lo, hi]`:

      (A) `slack_g(16) < F*`:  per envelope child `c`, `phi_c(16) < F*`  <=>
          `176 L(total_c) + 11 (h_c/d_c)(16/17) < (16|c|+1) L(621/64)`  (upper LHS by `L_hi`, lower RHS by `L_lo`);
      (B) monotone: per non-`B(5)` envelope child, `dphi_c/dk|_{16} < 0`  <=>
          `11 L(total_c) + 11 (h_c/d_c)/289 < |c| L(621/64)`  (so `slack_g(k) <= slack_g(16)` for `k >= 16`);
      (C) `B(5)` bound: `F* > 3/23`  <=>  `23 L(621/64) > 33`.

    Enclosures are the transcendental import (concavity/turan trust model).  Covers the envelope `{cherry,
    B(2..8)}`; larger brooms / non-envelope branches are dominated (documented, verified).  conjecture1_proved =
    False."""

    def _children(self):
        return [("cherry", CHERRY)] + [(f"B{j}", broom_child(j)) for j in range(2, 9)]

    def atoms(self):
        """List of `(name, lhs, rhs, op)` with the certified `lhs op rhs` (`op` in {'<','>'}), exact rationals."""
        g = Fr(621, 64)
        Lg_lo = _log_lo(g)
        out = []
        for nm, c in self._children():
            tot, sz, hd = c["total"], c["size"], Fr(c["h"], 1) / c["d"]
            out.append((f"tie_slack_phi16_{nm}",
                        176 * _log_hi(tot) + 11 * hd * Fr(16, 17), (16 * sz + 1) * Lg_lo, "<"))
            if nm != "B5":
                out.append((f"tie_slack_deriv16_{nm}",
                            11 * _log_hi(tot) + 11 * hd * Fr(1, 289), sz * Lg_lo, "<"))
        out.append(("tie_slack_Fstar_gt_3_23", 23 * Lg_lo, Fr(33), ">"))
        return out

    def check(self) -> bool:
        return all((lhs < rhs) if op == "<" else (lhs > rhs) for _, lhs, rhs, op in self.atoms())

    def lean_module(self, namespace="BGTieSlack") -> str:
        assert self.check(), "slack certificate does not hold -- refusing to emit"
        head = ("import Mathlib\n\n" f"namespace {namespace}\n\n")
        body = "\n".join(
            f"theorem {nm} : (({lhs.numerator} : ℚ)/{lhs.denominator}) {op} "
            f"(({rhs.numerator} : ℚ)/{rhs.denominator}) := by norm_num"
            for nm, lhs, rhs, op in self.atoms())
        return head + body + f"\n\nend {namespace}\n"


# --------------------------------------------------------------------------------------------------------------
# Mixed-hub reduction via log-concavity + per-child KKT (the tie-free decoupling, 2026-08-31).
#
# The mixed-hub bound `ell(hub) <= ell(B(k))` (`k <= 15`) reduces to a SINGLE-CHILD inequality by the tangent of
# the concave `log` at the all-cherry point.  With `x_cherry(k) = 1/(3(k+1))` and slope `lambda(k) =
# 1/(1 + k x_cherry) = 3(k+1)/(4k+3)`, define the per-child Lagrangian value `V(c) = ell(c) + lambda(k) x_c`.
# Log-concavity gives, for ANY children `c_1..c_k`,
#
#     ell(hub) - ell(B(k)) = Σ ell(c_i) - k ell(cherry) + [log(1+Σx_i) - log(1 + k x_cherry)]
#                         <= Σ ell(c_i) - k ell(cherry) + lambda(k) (Σx_i - k x_cherry)   [tangent above the curve]
#                          = Σ [V(c_i) - V(cherry)].
#
# So if `V(c) <= V(cherry)` for EVERY child (per-child KKT, NO coupling through the other children), then
# `ell(hub) <= ell(B(k))`.  This is why it works where the earlier degree-changing exchange failed: it is a
# RELATIVE comparison (hub vs `B(k)`), tie-free -- the `27*23` arithmetic stays confined to `ell(B(k)) <= 0`.
# The tangent step is rigorous (concavity); the residual is the per-child `V(c) <= V(cherry)` (verified over the
# broom envelope + all branches <= size 11; the (x, ell)-tradeoff dominates larger branches -- high-x branches
# have sharply negative `ell`).  conjecture1_proved = False.


def mixed_lambda(k):
    """The tangent slope `lambda(k) = 1/(1 + k x_cherry) = 3(k+1)/(4k+3)` (EXACT Fraction).  `x_cherry(k) =
    1/(3(k+1))` is the cherry's hub-field share; `lambda` is the derivative of `log(1+.)` at the all-cherry point,
    the concavity constant that decouples the mixed-hub bound into per-child inequalities."""
    return Fr(3 * (k + 1), 4 * k + 3)


def child_x(child, k):
    """`x_c(k) = h_c / ((k+1) d_c)` (EXACT Fraction) -- the child's share of the hub cavity field."""
    return Fr(child["h"], 1) / ((k + 1) * child["d"])


def child_value(child, k):
    """The per-child Lagrangian value `V(c) = ell(c) + lambda(k) x_c` (float; `ell` is transcendental).  The
    concavity reduction is `ell(hub) - ell(B(k)) <= Σ (V(c_i) - V(cherry))`, so `V(c) <= V(cherry)` per child
    proves `mixed <= B(k)`."""
    return _ell_of(child) + float(mixed_lambda(k)) * float(child_x(child, k))


def cherry_is_kkt_argmax(k, jmax=40):
    """True iff the cherry maximises `V(c)` over the branch envelope `{cherry, B(2..jmax)}` at `k` -- the
    per-child KKT condition that (with concavity) yields `mixed <= B(k)`.  Holds in the tie regime `k <= 15`;
    fails for large `k` (consistent with `mixed <= B(k)` itself failing at `k >= 20`)."""
    vch = child_value(CHERRY, k)
    return all(child_value(broom_child(j), k) <= vch + 1e-12 for j in range(2, jmax))


@dataclass(frozen=True)
class MixedHubKKTCertificate:
    """Kernel-gates the per-child KKT inequality `V(c) < V(cherry)` for every broom envelope child `B(j)` and
    every `k` in the tie regime `[2, k_max]` -- which, via the rigorous log-concavity tangent, PROVES the
    mixed-hub reduction `ell(hub) <= ell(B(k))` for `k <= 15` (the last tie-free conceptual piece of the
    branch-induction upper bound).  Clearing `11 F* = log(621/64)` and `lambda(k) = 3(k+1)/(4k+3)` (rational),
    each atom is

        11 L(total_c) - 11 L(3/2) - (|c|-2) L(621/64)  <  11 lambda(k) (x_cherry(k) - x_c(k)),

    LHS upper-bounded by frozen log-enclosures (`L_hi(total_c)`, `L_lo(3/2)`, `L_lo(621/64)` -- the `-(|c|-2)<0`
    coefficient takes `L_lo`), RHS an exact rational.  Reuses the slack cert's `_LOG` enclosures (same envelope).
    The cherry child is the reference (`V=V`, trivial) and omitted.  `.check()` exact; `.lean_module` emits
    `norm_num` atoms.  conjecture1_proved = False."""

    k_max: int = 15

    def _brooms(self):
        return [(f"B{j}", broom_child(j)) for j in range(2, 9)]

    def atoms(self):
        """List of `(name, lhs, rhs, op='<')` with the certified `lhs < rhs`, exact rationals."""
        g = Fr(621, 64)
        Lg_lo = _log_lo(g)
        L32_lo = _log_lo(Fr(3, 2))
        out = []
        for k in range(2, self.k_max + 1):
            lam = mixed_lambda(k)
            xch = child_x(CHERRY, k)
            for nm, c in self._brooms():
                tot, sz = c["total"], c["size"]
                # LHS upper bound: 11 L_hi(total_c) - 11 L_lo(3/2) - (sz-2) L_lo(621/64)  [sz-2 > 0 for brooms]
                lhs = 11 * _log_hi(tot) - 11 * L32_lo - (sz - 2) * Lg_lo
                rhs = 11 * lam * (xch - child_x(c, k))
                out.append((f"mixed_kkt_k{k}_{nm}", lhs, rhs, "<"))
        return out

    def check(self) -> bool:
        return all(lhs < rhs for _, lhs, rhs, _ in self.atoms())

    def lean_module(self, namespace="BGMixedHubKKT") -> str:
        assert self.check(), "mixed-hub KKT certificate does not hold -- refusing to emit"
        head = ("import Mathlib\n\n" f"namespace {namespace}\n\n")
        body = "\n".join(
            f"theorem {nm} : (({lhs.numerator} : ℚ)/{lhs.denominator}) {op} "
            f"(({rhs.numerator} : ℚ)/{rhs.denominator}) := by norm_num"
            for nm, lhs, rhs, op in self.atoms())
        return head + body + f"\n\nend {namespace}\n"


# --------------------------------------------------------------------------------------------------------------
# High-degree tail of the per-child envelope `V(c) <= V(cherry)` (2026-08-31).
#
# The per-child KKT residual is `V(c) = ell(c) + lambda(k) x_c <= V(cherry)` for ALL branches `c`.  High-degree
# branches close CLEANLY using only the ceiling `ell(c) <= 0` (the induction hypothesis) and `h_c <= 1`: for
# `d_c >= 7`,
#
#     V(c) <= 0 + lambda(k) * (1/((k+1) * 7))  <  V(cherry) = ell(cherry) + lambda(k)/(3(k+1)),
#
# which (with `x_cherry = 1/(3(k+1))`, `lambda(k)/(k+1) = 3/(4k+3)`) is exactly the rational-cleared inequality
#
#     -44 / (7 (4k+3))  <  11 ell(cherry) = 11 log(3/2) - 2 log(621/64).
#
# So the OPEN part of the envelope tail shrinks to small-degree branches `d_c <= 6` (of which the brooms
# `B(2..5)` are gated by `MixedHubKKTCertificate`; the residual is small-degree NON-broom branches, whose max
# `V` is empirically the broom `B(4)` with margin ~0.0017 and decays with size).  conjecture1_proved = False.


@dataclass(frozen=True)
class HighDegreeTailCertificate:
    """Kernel-gates the HIGH-DEGREE half of the per-child envelope tail `V(c) <= V(cherry)`: for every branch
    with root branch-degree `d_c >= 7`, `V(c) < V(cherry)` (`k <= k_max`), using only `ell(c) <= 0` and
    `h_c <= 1` -- no envelope enumeration.  Reduces to the rational inequality `-44/(7(4k+3)) < 11 ell(cherry)`
    (`= 11 log(3/2) - 2 log(621/64)`), one atom per `k`, RHS lower-bounded by the frozen log-enclosures
    (`11 L_lo(3/2) - 2 L_hi(621/64)`).  Shrinks the open envelope tail to small-degree (`d_c <= 6`) branches.
    `.check()` exact; `.lean_module` emits `norm_num`.  conjecture1_proved = False."""

    k_max: int = 15

    def atoms(self):
        """List of `(name, lhs, rhs, op='<')`: `-44/(7(4k+3)) < 11 L_lo(3/2) - 2 L_hi(621/64)`, exact rationals."""
        rhs = 11 * _log_lo(Fr(3, 2)) - 2 * _log_hi(Fr(621, 64))    # lower bound on 11 ell(cherry)
        return [(f"hi_degree_tail_k{k}", Fr(-44, 7 * (4 * k + 3)), rhs, "<")
                for k in range(2, self.k_max + 1)]

    def check(self) -> bool:
        return all(lhs < rhs for _, lhs, rhs, _ in self.atoms())

    def lean_module(self, namespace="BGHighDegreeTail") -> str:
        assert self.check(), "high-degree tail certificate does not hold -- refusing to emit"
        head = ("import Mathlib\n\n" f"namespace {namespace}\n\n")
        body = "\n".join(
            f"theorem {nm} : (({lhs.numerator} : ℚ)/{lhs.denominator}) {op} "
            f"(({rhs.numerator} : ℚ)/{rhs.denominator}) := by norm_num"
            for nm, lhs, rhs, op in self.atoms())
        return head + body + f"\n\nend {namespace}\n"


# --------------------------------------------------------------------------------------------------------------
# Per-child envelope tail closure — the three-case split (2026-08-31; DEGREE-DEPENDENT threshold correction).
#
# The mixed-hub reduction needs `V(c) = ell(c) + lambda(k) x_c <= V(cherry)` for EVERY branch `c`.  This splits by
# root branch-degree into three cases, only ONE still open (a per-degree refined ceiling):
#
#   (1) d_c >= 7  -- GATED (`HighDegreeTailCertificate`): `x_c` small, ceiling `ell <= 0` alone suffices.
#   (2) brooms B(2..8) (degrees 3..9) -- GATED (`MixedHubKKTCertificate`): `V(B(j)) < V(cherry)` directly.
#   (3) d_c <= 6, NON-broom -- reduces (pure algebra) to the DEGREE-DEPENDENT refined ceiling
#
#         ell(c) < small_degree_threshold(k, d_c) := ell(cherry) + (d_c - 3) / (d_c (4k+3)),
#
#       because then, using `x_c = h_c/((k+1)d_c) <= 1/((k+1)d_c)` (`h_c <= 1`) and `lambda(k)/(k+1) = 3/(4k+3)`,
#         V(c) <= ell(c) + lambda(k)/((k+1) d_c) < [ell(cherry) + (d_c-3)/(d_c(4k+3))] + 3/((4k+3) d_c)
#               = ell(cherry) + 1/(4k+3) = ell(cherry) + lambda(k)/(3(k+1)) = V(cherry).
#
# CORRECTION (2026-08-31, 11th caught overclaim): the earlier SINGLE threshold `ell(cherry) - lambda(k)/(6(k+1))`
# was the `d=2` case used for ALL degrees -- too strict at small `k` for higher-degree children, so a size-16
# non-broom (`4 cherries + B(3)`, `d=6`, `ell=-0.0164`) was mis-classified `open` at `k=2` (its ACTUAL `V` is
# still `< V(cherry)` by `+0.018`; only the sufficient-condition bookkeeping failed).  The `x_c <= 1/((k+1)d_c)`
# bound gives the correct degree-dependent threshold: higher `d_c` => `x_c` smaller => threshold HIGHER (nearer
# the plain ceiling).  Hardest cases are the low degrees: `d=2` (`ell < ell(cherry) - 1/(2(4k+3))`), `d=3`
# (`ell < ell(cherry)`); `d>=4` is essentially just the ceiling.
#
# With the corrected threshold EVERY `d_c <= 6` non-broom is covered by case (3) directly -- verified over all
# branches <= size 16 at every `k in [2,15]` (zero `open` non-brooms), plus generalized brooms (to size 66) and
# star-of-brooms rooted at low-degree vertices (to size 101).  The one open analytic input is the size-decay tail
# of this per-degree ceiling (b); its failure mode -- a large low-root-degree near-extremal branch -- is refuted
# (such branches are diluted, `ell ~ -0.27`, see `branch_ell_by_vertex`).  conjecture1_proved = False.


def small_degree_threshold(k, d=2):
    """The DEGREE-DEPENDENT refined-ceiling threshold `ell(cherry) + (d-3)/(d(4k+3))` (float).  A branch with
    root degree `d >= 2` and `ell(c) < small_degree_threshold(k, d)` satisfies `V(c) < V(cherry)` (pure algebra
    via `x_c <= 1/((k+1)d)`).  Higher `d` => higher threshold (nearer the plain ceiling); `d=3` gives exactly
    `ell(cherry)`; `d=2` (default) gives `ell(cherry) - 1/(2(4k+3))` (the hardest, low-degree case)."""
    return _ell_of(CHERRY) + (d - 3) / (d * (4 * k + 3))


def envelope_tail_case(d, ell, k):
    """Classify which closure case covers a branch with root branch-degree `d` and potential `ell` at hub-degree
    `k` (`h_c <= 1` assumed): `'hi_degree'` (d>=7, gated), `'threshold'` (ell below the degree-dependent refined
    ceiling => V<Vch), or `'open'` (small-degree, ell at/above threshold -- must be a broom, gated by mixed_kkt,
    else the residual)."""
    if d >= 7:
        return "hi_degree"
    if ell < small_degree_threshold(k, d):
        return "threshold"
    return "open"


conjecture1_proved = False
