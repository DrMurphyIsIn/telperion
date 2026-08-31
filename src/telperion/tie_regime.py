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
    uniform child -- the campaign's cherry-worst inequality, rational in `(k, j)`.  Slack (`>= 2.4` in the tie
    regime), so tie-free; only the broom step `ell(B(k)) <= 0` carries the `27*23` arithmetic."""
    return _exp11_hub(k, CHERRY) / _exp11_hub(k, broom_child(j))


conjecture1_proved = False
