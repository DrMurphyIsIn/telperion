"""Lean v4.34.0-rc2: the replay template and the probe and fingerprint callbacks compile, and run, on a toolchain
whose ``ConstantInfo`` derives no ``BEq``.

Island #19 (zeta-zeros-v2, pinned to rc2) failed at 289f078 on the template's ``a == b`` in ``sameConst``
(``failed to synthesize instance of type class BEq ConstantInfo``), and the probe and fingerprint callbacks had never
been compiled on rc2. The closure-audit callback is covered here too. The toolchain-only tests need just the rc2 toolchain (an env with no packages: trusted
imports ``Lean`` only). The env tests need ``TELPERION_LEAN_ENV_RC2``, a built Mathlib v4.34.0-rc2 project (the
negation probe's tactics and plausible come from Mathlib). Every Lean run goes through ``default_wrapper``
(leanlock)."""
from __future__ import annotations

import os
import secrets
import sys
from pathlib import Path

import pytest

from telperion.checks import fingerprint
from telperion.closure_audit import CLEAN_AXIOMS, AuditSpec, run_closure_audit_replayed
from telperion.checks.lean_replay import (build_trusted_manifest, default_wrapper, pinned_env, run_replay)

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_lean_replay import SAME_CB, check_same_lines  # noqa: E402

RC2 = "leanprover/lean4:v4.34.0-rc2"
V435 = "leanprover/lean4:v4.35.0"
ELAN = Path(os.environ.get("ELAN_HOME") or os.path.expanduser("~/.elan"))


def _installed(toolchain: str) -> bool:
    lean = ELAN / "toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin" / "lean"
    return os.access(lean, os.X_OK)


rc2 = pytest.mark.skipif(not _installed(RC2), reason="no v4.34.0-rc2 toolchain installed")
RC2_ENV = os.environ.get("TELPERION_LEAN_ENV_RC2")
rc2_env = pytest.mark.skipif(not RC2_ENV, reason="TELPERION_LEAN_ENV_RC2 not set (a built Mathlib v4.34.0-rc2 env)")

# A structure (an inductive, its constructor and recursor go through sameConst), a definition, a Prop definition
# and theorems over both.
BODY = """structure TpBox where
  val : Nat

def TpBox.double (b : TpBox) : Nat := b.val + b.val

def TpS : Prop := ∀ n : Nat, n + 0 = n

theorem TpBox.t : ∀ b : TpBox, b.double = b.val + b.val := fun _ => rfl

theorem TpS.t : TpS := fun _ => rfl
"""


def _bare_env(root: Path, toolchain: str) -> tuple[Path, Path]:
    """(env, manifest): a pinned env with no packages (its trusted prefix is the toolchain's lib/lean alone)."""
    env = root / "env"
    env.mkdir(parents=True)
    (env / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
    return env, build_trusted_manifest(env, root / "manifest.json")


def _compile(env: Path, body: str, cdir: Path) -> tuple[str, Path]:
    """(module, olean dir): `body` compiled with the env's pinned lean, LEAN_PATH = its trusted entries."""
    pinned = pinned_env(env)
    module = f"TpRc2_{secrets.token_hex(6)}"
    cdir.mkdir(parents=True)
    fingerprint._compile_body(body, module, cdir, list(pinned.entries), default_wrapper(), pinned.lean, 1800, None)
    return module, cdir / "build"


@pytest.fixture(scope="module")
def bare_rc2(tmp_path_factory):
    return _bare_env(tmp_path_factory.mktemp("rc2"), RC2)


def _fingerprints(env: Path, manifest: Path, cdir: Path, list_declared: bool = False) -> tuple[dict, dict, dict]:
    """(type-mode fingerprints of the two theorems, value-mode fingerprint of TpS, `parse_declared` of the type run)."""
    module, build = _compile(env, BODY, cdir)
    out = {}
    for mode, targets in (("type", ["TpBox.t", "TpS.t"]), ("value", ["TpS"])):
        nonce = secrets.token_hex(16)
        cb = fingerprint.render_fingerprint_callback(targets, nonce, mode=mode, list_declared=list_declared)
        r = run_replay(module, cb, untrusted_paths=[build], trusted_imports=("Lean",), trusted_env=env,
                       manifest=manifest, allow_sorry=True, callback_takes_closure=list_declared)
        assert r.status == "OK", (mode, r.status, r.detail, r.output[-3000:])
        out[mode] = (fingerprint.parse_fingerprints(r.output, nonce), fingerprint.parse_declared(r.output, nonce))
    return out["type"][0], out["value"][0], out["type"][1]


@rc2
def test_rc2_replay_template_compiles_and_same_const_rejects_each_field(bare_rc2, tmp_path):
    env, manifest = bare_rc2
    module, build = _compile(env, BODY, tmp_path / "c")
    # the list run (the _NO_CALLBACK template that failed at 289f078), the replay of a structure, then the controls
    r = run_replay(module, SAME_CB, untrusted_paths=[build], trusted_imports=("Lean",), trusted_env=env,
                   manifest=manifest)
    assert r.status == "OK" and f"modules=[{module}]" in r.detail, (r.status, r.detail, r.output[-3000:])
    check_same_lines(r.lines)


@rc2
def test_rc2_fingerprint_callback_compiles_and_matches_v4_35_0(bare_rc2, tmp_path, tmp_path_factory):
    env, manifest = bare_rc2
    types, values, _ = _fingerprints(env, manifest, tmp_path / "a")
    assert set(types) == {"TpBox.t", "TpS.t"} and set(values) == {"TpS"}
    # value mode of `def TpS : Prop` equals type mode of `theorem TpS.t : TpS` (the fingerprint module docstring)
    assert values["TpS"] == types["TpS.t"]
    # the list_declared variant (a callback that takes the replayed closure)
    t2, _, decl = _fingerprints(env, manifest, tmp_path / "b", list_declared=True)
    assert t2 == types and {"TpBox.t", "TpS.t"} <= set(decl["theorem"]) and decl["propdef"] == ["TpS"], decl
    if not _installed(V435):
        pytest.skip("no v4.35.0 toolchain: the cross-version comparison is skipped")
    env35, manifest35 = _bare_env(tmp_path_factory.mktemp("v435"), V435)
    types35, values35, _ = _fingerprints(env35, manifest35, tmp_path / "v")
    assert (types35, values35) == (types, values)


@rc2
def test_rc2_declaration_ranges_script(bare_rc2, tmp_path):
    env, _ = bare_rc2
    module, build = _compile(env, BODY, tmp_path / "c")
    ranges, sha = fingerprint._read_decl_ranges(build / f"{module}.olean", tmp_path / "c", default_wrapper(),
                                                pinned_env(env), 600)
    assert ranges["TpBox.t"][0] == 8 and ranges["TpS"][0] == 6 and len(sha) == 64, ranges


@rc2
def test_rc2_closure_audit_callback(bare_rc2, tmp_path):
    env, manifest = bare_rc2
    module, build = _compile(env, BODY, tmp_path / "c")
    spec = AuditSpec(imports=(module,), targets=("TpBox.t", "TpS.t"), scan_patterns=("tpbox",),
                     absent_module_prefixes=("TpNeg",))
    res = run_closure_audit_replayed(spec, None, untrusted_paths=[build], trusted_env=env, manifest=manifest)
    assert res.verdict == "PASS" and res.ok and res.isolated, (res.failures, res.raw_tail)
    assert "4.34.0-rc2" in res.lean_version, res.lean_version
    assert [(t.name, t.kind) for t in res.targets] == [("TpBox.t", "theorem"), ("TpS.t", "theorem")]
    assert set(res.closure_axioms) <= set(CLEAN_AXIOMS) and res.nonlib_modules.get(module)
    assert any(h["constant"].startswith("TpBox") for h in res.scan_hits), res.scan_hits
    # a must-fail control: a `sorry` in the closure fails the audit
    smod, sbuild = _compile(env, "theorem TpSorry.t : 1 = 2 := sorry\n", tmp_path / "s")
    bad = run_closure_audit_replayed(AuditSpec(imports=(smod,), targets=("TpSorry.t",)), None,
                                     untrusted_paths=[sbuild], trusted_env=env, manifest=manifest)
    assert bad.verdict == "FAIL" and not bad.ok and bad.isolated, (bad.failures, bad.raw_tail)


# ---------------------------------------------------------------------------------------------------------------
# With a built Mathlib v4.34.0-rc2 env: the negation probe (Mathlib tactics, plausible) and the fingerprint pins.
@pytest.fixture(scope="module")
def rc2_manifest(tmp_path_factory):
    return build_trusted_manifest(RC2_ENV, tmp_path_factory.mktemp("rc2m") / "trusted.json")


@rc2_env
def test_rc2_env_is_rc2():
    assert pinned_env(RC2_ENV).toolchain == RC2


@rc2_env
def test_rc2_env_fingerprint_pins_are_the_v4_35_0_pins(rc2_manifest):
    from test_fingerprint import PINS
    for body, want in PINS.items():
        assert fingerprint.run_fingerprint_on_text(Path(RC2_ENV), body, "t", trusted_env=Path(RC2_ENV),
                                                   manifest=rc2_manifest) == want, body
    vb = "import Mathlib\ndef S : Prop := ∀ n : ℕ, n + 0 = n\ntheorem t : S := fun n => rfl\n"
    assert fingerprint.run_fingerprint_on_text(Path(RC2_ENV), vb, "S", trusted_env=Path(RC2_ENV),
                                               manifest=rc2_manifest, mode="value") == \
        "8923733b8a40e2beb506ae45a77f22c6fadbd943885cee0389459abe0738652b"


@rc2_env
@pytest.mark.parametrize("theorem,witness,verdict", [
    ("Controls.vac", None, "VACUOUS"),                                   # MUST-FAIL control
    ("Controls.ref", None, "REFUTED"),                                   # MUST-FAIL control
    ("Controls.tru", None, "PROBE_ONLY"),                                # MUST-PASS control
    ("Controls.tru", "⟨2, by norm_num, trivial⟩", "WITNESSED"),
])
def test_rc2_env_negation_probe_callback(rc2_manifest, rc2_cases, theorem, witness, verdict):
    from telperion.checks.negation_probe import ProbeSpec, run_probe
    module, build = rc2_cases
    r = run_probe(ProbeSpec(module, theorem, witness), untrusted_paths=[build], trusted_env=RC2_ENV,
                  manifest=rc2_manifest)
    assert r.verdict == verdict, r.detail


@pytest.fixture(scope="module")
def rc2_cases(tmp_path_factory):
    from test_negation_probe import CASES
    return _compile(Path(RC2_ENV), "import Mathlib\n" + CASES, tmp_path_factory.mktemp("rc2cases") / "c")


@rc2_env
def test_rc2_env_closure_audit_callback(rc2_manifest, tmp_path):
    from test_lean_replay import HONEST
    module, build = _compile(Path(RC2_ENV), HONEST, tmp_path / "c")
    spec = AuditSpec(imports=(module,), targets=("TpHonest.sq_le", "TpHonest.Color.toNat"),
                     scan_patterns=("color", "nat.le_mul"), absent_module_prefixes=("TpNeg", "Mathlib.Tactic.Linarith"))
    res = run_closure_audit_replayed(spec, None, untrusted_paths=[build], trusted_env=RC2_ENV, manifest=rc2_manifest)
    assert res.verdict == "PASS" and res.ok and res.isolated, (res.failures, res.raw_tail)
    assert res.closure_size > 100 and set(res.closure_axioms) <= set(CLEAN_AXIOMS)
    assert [t.name for t in res.targets] == ["TpHonest.sq_le", "TpHonest.Color.toNat"]
