"""Signature / statement-match gate — the positive half of the trust boundary.

Offline unit tests for the PURE pieces (type builder, guard-block construction,
early-return contract).  The kernel-level check (a real weaker/∃ restatement is
REJECTED, the intended claim ACCEPTED) runs against the built zero_free_bridge env
in CI (job `rh-signature-gate`) and in scratch/rh_axle_apply.py #5.
conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.signature_gate import (  # noqa: E402
    SignatureResult, build_sig_guards, check_signatures, forall_type, sig_guard_name,
)


def test_forall_type_wraps_binders():
    assert forall_type("(x : ℝ) (hx : 0 ≤ x)", "Real.log (1 + x) ≤ x") == \
        "∀ (x : ℝ) (hx : 0 ≤ x), Real.log (1 + x) ≤ x"


def test_forall_type_no_binders_is_statement():
    assert forall_type("", "(0:ℝ) ≤ 6") == "(0:ℝ) ≤ 6"
    assert forall_type("   ", "P") == "P"


def test_forall_type_preserves_implicit_binder_info():
    # implicit `{s : ℂ}` must stay implicit so the guard body `:= <name>` matches
    # the decl's binder info exactly.
    t = forall_type("{s : ℂ} (hs : 1 ≤ s.re)", "P s")
    assert t == "∀ {s : ℂ} (hs : 1 ≤ s.re), P s"


def test_build_sig_guards_one_per_entry():
    guards = build_sig_guards({
        "foo": "∀ (x : ℝ), 0 ≤ x → Real.log (1 + x) ≤ x",
        "bar": "(0:ℝ) ≤ 6",
    })
    lines = guards.splitlines()
    assert lines[0] == "theorem foo__sig_guard : ∀ (x : ℝ), 0 ≤ x → Real.log (1 + x) ≤ x := foo"
    assert lines[1] == "theorem bar__sig_guard : (0:ℝ) ≤ 6 := bar"


def test_sig_guard_name():
    assert sig_guard_name("zeta_log_bound") == "zeta_log_bound__sig_guard"


def test_check_signatures_short_circuits_when_base_fails(monkeypatch):
    # If the proof itself does not compile, signatures are moot: return early with
    # matches=None and NO guard verification attempted.
    from telperion import signature_gate as SG

    calls = {"n": 0}

    def fake_verify(content, **kw):
        calls["n"] += 1
        # base call (decls=['foo']) -> not okay; a guard call would be a 2nd call.
        return SG.VerifyResult(okay=False, axioms_clean=False, errors=["boom"])

    monkeypatch.setattr(SG, "verify_lean", fake_verify)
    res = check_signatures("theorem foo : P := by sorry",
                           env_dir="/nonexistent", expected={"foo": "P"})
    assert isinstance(res, SignatureResult)
    assert res.okay is False and res.all_match is False
    assert res.matches["foo"].matches is None            # not reached
    assert calls["n"] == 1                               # base only; no guard pass
