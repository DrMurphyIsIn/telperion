"""Zero-free-region assembly emitter.

The de la Vallee Poussin / elementary route turns three growth-and-positivity bounds into a
zero-free region for the Riemann zeta function. At `sigma = 2 - beta`, height `gamma >= 1`, given

    (positivity)  1 <= Zσ^3 · Zσt^4 · Zσ2t        [the 3-4-1 product, |ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)| >= 1]
    (pole)        Zσ  <= c1 / (1 - beta)            [|ζ(σ)| <= c1/(σ-1) near the pole]
    (growth)      Zσ2t <= c2 · gamma^theta          [crude |ζ| <= c2|t| is theta=1; sharp log|t| smaller]
    (Cauchy)      Zσt <= 2(1-beta)·c4·gamma^theta    [the segment/Cauchy derivative estimate]

one derives  `1 - beta >= 1 / (16 c1^3 c2 c4^4 · gamma^{5 theta})`, i.e. the zero-free region

    Re s > 1 - c / |t|^{5 theta},   c = 1 / (16 c1^3 c2 c4^4).

WHY THIS IS A CERTIFICATE (not a template). Telperion is the CHECKER; this generator is UNTRUSTED.
The load-bearing claim is the exact identity

    (c1/(1-β))^3 · (2(1-β)c4·γ^θ)^4 · (c2·γ^θ)  ==  16 c1^3 c2 c4^4 · (1-β) · γ^{5θ}

-- the substitution of the three bounds into the 3-4-1 product, whose right side reads off the region
constant and exponent. `verify_region` re-derives BOTH sides symbolically (exact sympy) and REFUSES
to emit unless they coincide and the coefficients are positive (anti-phantom: a wrong constant, a wrong
exponent, or a nonpositive coefficient is rejected). Only then is Lean written; the emitted proof mirrors
the kernel-checked `zeta_zero_free_poly_of` (ZeroFreeElementary.lean): `gcongr` bounds the product,
`field_simp; ring` proves the identity, `nlinarith` closes.

theta = 1 is the crude-growth polynomial region (the current |t|^{-5}); a SHARPER growth bound (smaller
gamma-power, e.g. from an Euler-Maclaurin log bound) feeds the SAME assembly and improves the exponent
toward the de la Vallee Poussin log-region -- WITHOUT the Hadamard machinery.

A gap-filler FEEDING the region rate, NOT a proof of RH. conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field

import sympy as sp

from .expr import rat_lean


@dataclass(frozen=True)
class ZeroFreeRegionCert:
    """The three elementary-route bound coefficients + the growth power `theta`."""
    c1: sp.Rational       # pole coefficient
    c2: sp.Rational       # growth coefficient
    c4: sp.Rational       # Cauchy coefficient
    theta: sp.Rational = field(default_factory=lambda: sp.Integer(1))


def verify_region(cert: ZeroFreeRegionCert) -> tuple[bool, sp.Rational, sp.Expr]:
    """EXACT re-derivation. Substitute the three bounds into the 3-4-1 product and check the closed
    form. Returns (ok, region_constant, region_exponent). `ok=False` (REFUSE) on a symbolic mismatch
    or a nonpositive coefficient."""
    if cert.c1 <= 0 or cert.c2 <= 0 or cert.c4 <= 0:
        return False, sp.Integer(0), sp.Integer(0)
    beta, gamma = sp.symbols("beta gamma", positive=True)
    onemb = 1 - beta
    Zs = cert.c1 / onemb
    Zst = 2 * onemb * cert.c4 * gamma ** cert.theta
    Zs2t = cert.c2 * gamma ** cert.theta
    subst = sp.expand(Zs ** 3 * Zst ** 4 * Zs2t)
    const = 16 * cert.c1 ** 3 * cert.c2 * cert.c4 ** 4
    expo = 5 * cert.theta
    expected = sp.expand(const * onemb * gamma ** expo)
    ok = sp.simplify(subst - expected) == 0
    return bool(ok), sp.nsimplify(const), expo


def emit_zero_free_region_lean(cert: ZeroFreeRegionCert, thm_name: str) -> str:
    """Emit the kernel-ready region-assembly lemma for the given coefficients. REFUSES on a failed
    certificate. Currently emits the integer-`theta` case (natural power `gamma^{5 theta}` in Lean);
    `theta = 1` reproduces `zeta_zero_free_poly_of`."""
    ok, const, expo = verify_region(cert)
    if not ok:
        raise ValueError(
            f"region REFUSED: coefficients (c1={cert.c1}, c2={cert.c2}, c4={cert.c4}) nonpositive, "
            f"or the substituted 3-4-1 product does not reduce to 16 c1^3 c2 c4^4 (1-β) γ^{{5θ}}")
    if not (cert.theta.is_Integer and cert.theta > 0):
        raise ValueError(f"emit REFUSED: Lean emission needs a positive integer theta (got {cert.theta}); "
                         f"the region rate |t|^-{expo} is still computed for reference")
    c1, c2, c4 = rat_lean(cert.c1), rat_lean(cert.c2), rat_lean(cert.c4)
    K = rat_lean(const)
    e = int(expo)
    gpow = f"γ ^ {e}"
    gth = "γ" if cert.theta == 1 else f"γ ^ {int(cert.theta)}"
    return f"""\
/-- Zero-free-region assembly for `ζ` at `σ = 2 - β`: from the 3-4-1 positivity + pole (c1={cert.c1}),
    growth (c2={cert.c2}·γ^{int(cert.theta)}), Cauchy (c4={cert.c4}·γ^{int(cert.theta)}) bounds, the region
    constant is 1/{K} and the rate is `Re s > 1 - c/|t|^{e}`. Re-derived exactly before emission. -/
theorem {thm_name} {{β γ Zσ Zσt Zσ2t : ℝ}}
    (hβ1 : β < 1) (hγ : 1 ≤ γ)
    (hZσ : 0 ≤ Zσ) (hZσt : 0 ≤ Zσt) (hZσ2t : 0 ≤ Zσ2t)
    (hprod : 1 ≤ Zσ ^ 3 * Zσt ^ 4 * Zσ2t)
    (hpole : Zσ ≤ {c1} / (1 - β))
    (hstrip : Zσ2t ≤ {c2} * {gth})
    (hcauchy : Zσt ≤ 2 * (1 - β) * {c4} * {gth}) :
    1 / ({K} * {gpow}) ≤ 1 - β := by
  have hη : 0 < 1 - β := by linarith
  have hγ0 : 0 < γ := by linarith
  have hub : Zσ ^ 3 * Zσt ^ 4 * Zσ2t
      ≤ ({c1} / (1 - β)) ^ 3 * (2 * (1 - β) * {c4} * {gth}) ^ 4 * ({c2} * {gth}) := by
    gcongr
  have hsimp : ({c1} / (1 - β)) ^ 3 * (2 * (1 - β) * {c4} * {gth}) ^ 4 * ({c2} * {gth})
      = {K} * (1 - β) * {gpow} := by
    field_simp; ring
  rw [hsimp] at hub
  have h1 : (1 : ℝ) ≤ {K} * (1 - β) * {gpow} := le_trans hprod hub
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1]
"""


def _self_test() -> None:
    # The actual region instance (c1=2, c2=5, c4=24) -> constant 212336640, exponent 5.
    r = ZeroFreeRegionCert(sp.Integer(2), sp.Integer(5), sp.Integer(24))
    ok, const, expo = verify_region(r)
    assert ok and const == 212336640 and expo == 5, (ok, const, expo)
    lean = emit_zero_free_region_lean(r, "zeta_zero_free_poly_assembled")
    assert "212336640" in lean and "nlinarith" in lean and "γ ^ 5" in lean

    # A sharper growth power theta=2 doubles-and-more the exponent (5*theta) -- the rate-upgrade lever.
    r2 = ZeroFreeRegionCert(sp.Integer(2), sp.Integer(5), sp.Integer(24), sp.Integer(2))
    ok2, _, expo2 = verify_region(r2)
    assert ok2 and expo2 == 10

    # anti-phantom: nonpositive coefficient is REFUSED.
    bad = ZeroFreeRegionCert(sp.Integer(0), sp.Integer(5), sp.Integer(24))
    assert not verify_region(bad)[0]
    try:
        emit_zero_free_region_lean(bad, "forged")
        raise AssertionError("must refuse nonpositive coefficient")
    except ValueError:
        pass
    print("emit_zero_free_region self-test: OK")


if __name__ == "__main__":
    _self_test()
