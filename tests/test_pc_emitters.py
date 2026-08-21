"""Tests for the proof-complexity-derived emitter shapes (2026-08-20):
RationalIdentityEmitter, FiniteDecideEmitter, FwdTelescopeEmitter."""
import sympy as sp
import pytest

from telperion import (CertificationError, Cmp, FiniteDecideEmitter, ForallIn,
    FwdTelescopeEmitter, GridSpec, Imp, LeanProfile, Lit, Lookup, Mul as FMul,
    NatTable, PairTable, Pop, RationalIdentityEmitter, Var, Xor, certify,
    finite_decide_family, fwd_telescope_family, rational_identity_family)

n, q, u = sp.symbols("n q u")


def _ri(lhs, rhs, c0=3):
    return rational_identity_family("T", (n,), GridSpec([("i", [0])]),
        lambda pt: "t", lambda pt: (lhs, rhs, c0))


class TestRationalIdentity:
    def test_certifies_true_identity(self):
        fam = certify(_ri(n / (2 * (n - 1)) * (n / 2 - 1), n * (n - 2) / (4 * (n - 1))))
        assert fam.instances[0].payload[3] == [1]

    def test_refuses_non_identity(self):
        with pytest.raises(CertificationError):
            certify(_ri(n / (n - 1), n / (n - 2)))

    def test_refuses_root_above_ray(self):
        with pytest.raises(CertificationError):
            certify(_ri(n / (n - 5), n / (n - 5), 3))

    def test_refuses_nested_variable_division(self):
        with pytest.raises(CertificationError):
            certify(_ri((1 + 1 / (n - 1)) * (n - 1) / (n - 2), n / (n - 2)))

    def test_emits_distinct_shapes(self):
        fam = certify(_ri(n * (n - 2) / (4 * (n - 1) * (n - 3)),
                          (n / (2 * (n - 1))) * ((n - 2) / (2 * (n - 3)))))
        body, k = RationalIdentityEmitter().emit_body(fam, LeanProfile(namespace=("T",)))
        assert k == 1 and "div_eq_div_iff" in body and "mul_ne_zero" in body


def _fd(pairs, keys, idx):
    def spec(pt):
        tables = [PairTable("lam", pairs), NatTable("lamKeys", keys),
                  NatTable("idx", idx)]
        sgn = lambda e: Lookup("lam", e)
        prop = ForallIn("a", "lamKeys", ForallIn("b", "lamKeys",
            ForallIn("t", "idx",
              Imp(Cmp("le", Pop(Xor(Var("a"), Var("t"))), Lit(1)),
                Imp(Cmp("le", Pop(Xor(Var("b"), Var("t"))), Lit(1)),
                  Cmp("eq", sgn(Xor(Var("a"), Var("b"))),
                      FMul(sgn(Var("a")), sgn(Var("b")))))))))
        return tables, prop
    return finite_decide_family("T", GridSpec([("i", [0])]), lambda pt: "t", spec)


class TestFiniteDecide:
    def test_certifies_consistent_table(self):
        fam = certify(_fd([(0, 1)], [0], [0, 1, 2, 4]))
        assert fam.instances[0].lean_name == "t"

    def test_refuses_false_claim(self):
        # sgn(1 ^ 2) = sgn(3) = 0 but sgn(1)*sgn(2) = 1: guarded at t=0? pop(1^0)=1<=1,
        # pop(2^0)=1<=1 -> conclusion checked -> 0 != 1 -> refused
        with pytest.raises(CertificationError):
            certify(_fd([(0, 1), (1, 1), (2, 1)], [0, 1, 2], [0, 1, 2, 4]))

    def test_emits_decide(self):
        fam = certify(_fd([(0, 1)], [0], [0, 1, 2, 4]))
        body, k = FiniteDecideEmitter().emit_body(fam, LeanProfile(namespace=("T",)))
        assert k == 1 and "by decide" in body and "maxRecDepth" in body
        assert "ℚ" not in body  # the Rat-does-not-kernel-reduce contract


class TestFwdTelescope:
    def test_certifies_knapsack_contiguous(self):
        fam = certify(fwd_telescope_family("T", GridSpec([("i", [0])]),
            lambda pt: "t", lambda pt: {"A": n / 2 - q, "P": n, "N": n / 2 - u}))
        body, k = FwdTelescopeEmitter().emit_body(fam, LeanProfile(namespace=("T",)))
        assert k == 4 and "fwdDiff" in body and "linear_combination" in body

    def test_refuses_wrong_factor(self):
        with pytest.raises(CertificationError):
            certify(fwd_telescope_family("T", GridSpec([("i", [0])]),
                lambda pt: "t", lambda pt: {"A": n / 2 - q, "P": n, "N": n / 2 - 2 * u}))

    def test_refuses_stray_symbols(self):
        z = sp.symbols("z")
        with pytest.raises(CertificationError):
            certify(fwd_telescope_family("T", GridSpec([("i", [0])]),
                lambda pt: "t", lambda pt: {"A": n / 2 - q + z, "P": n, "N": n / 2 - u}))
