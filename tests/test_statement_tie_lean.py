"""Step 5 Task 6, in a real Lean env: the semantic theorem tie.

`mission freeze --fingerprints` records each node's statement fingerprint, computed by Lean from the statement file
(type mode for a `theorem` statement, value mode for a `def … : Prop` one), and for a post-cutoff node
`mission checks-record` and the gate require the checked theorem's fingerprint to EQUAL it.

- `test_freeze_fingerprints_*`: the real `freeze --fingerprints` agrees with the artifact theorem's type-mode
  fingerprint, for a theorem-form and a def-form statement alike.
- `test_evasion_*`: the five ways step 4's final re-review ("Residual round", final-rereview.md) fooled the gate's
  SYNTACTIC resolver (`guard_anchors.resolve_theorem`) into naming a decoy helper. Each artifact still fools the
  resolver (asserted, so the test documents the evasion), the honest operator fingerprints the declaration the resolver
  names (the decoy, whose type differs), and `checks-record` REFUSES it by fingerprint inequality. The probe and closure
  JSONs are synthetic, bound to the real fingerprint run's `olean_sha256`; the fingerprint JSON is the real
  `telperion fingerprint --json` output.
- `test_lean_e2e_*`: the whole statement-first flow with every check real: freeze --fingerprints, the probe, the
  fingerprint and the closure audit on the compiled artifact, checks-record, the deviations read-back and the grant.

Every artifact is compiled with the PINNED `lean` into a private temp dir (no lake), as the fingerprint's own body
compile does (`fingerprint._compile_body`), and replayed from there.
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from telperion.cli import main  # noqa: E402
from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import (  # noqa: E402
    Author, MissionManifest, Node, Proof, Readback, load_node, save_manifest, save_node,
)
from telperion.missions.statements import statement_path, write_statement  # noqa: E402

LEAN_ENV = os.environ.get("TELPERION_LEAN_ENV")
lean = pytest.mark.skipif(not LEAN_ENV, reason="TELPERION_LEAN_ENV not set (built Mathlib project)")
pytestmark = lean

ART_MODULE = "TpTieArt"
STATEMENT = "theorem main_thm : 1 + 1 = 2"
DECOY = "theorem Helper.main_thm (n : Nat) (h : n = 0) : n = n := rfl\n"

#: The five evasions of final-rereview.md's "Residual round", each with the decoy declared first. In every one, Lean
#: declares only the decoy `Helper.main_thm` (and harmless defs); the text `theorem main_thm : 1 + 1 = 2 := by rfl`
#: that the resolver reads as the node's theorem is inside a string, a name, after `#exit` or in a quotation.
EVASIONS = {
    # s! interpolation of a string term: Python pairs `"{"` and `"}"`, Lean reads one string inside `{…}`
    "s_interpolation": DECOY + 'def s : String := s!"{"\nnamespace Helper\ntheorem main_thm : 1 + 1 = 2 := '
                               'by rfl\n"}"\n',
    # a quote inside a `«»` name opens a Python string that the declaration text then sits outside of
    "quote_in_guillemets": DECOY + 'def «"» : String := "\nnamespace Helper\ntheorem main_thm : 1 + 1 = 2 := by rfl\n"'
                                   '\ndef «"x» := 0\n',
    # the whole declaration is a `«»` name
    "declaration_in_guillemets": DECOY + "namespace Helper\ndef «theorem main_thm : 1 + 1 = 2 := by rfl» : Nat := 0\n"
                                         "end Helper\n",
    # Lean stops reading at `#exit`
    "exit": DECOY + "#exit\nnamespace Helper\ntheorem main_thm : 1 + 1 = 2 := by rfl\nend Helper\n",
    # a `(command| …)` syntax quotation
    "command_quotation": "import Lean\n" + DECOY + "namespace Helper\ndef q : Lean.MacroM Lean.Syntax := "
                                                   "`(command| theorem main_thm : 1 + 1 = 2 := by rfl)\nend Helper\n",
}
HONEST = "theorem main_thm : 1 + 1 = 2 := by rfl\n"

AUTHOR = ("author@example.test", "author-session")
AUDITOR = ("auditor@example.test", "auditor-session")
DEVIATIONS_AUDITOR = ("deviations-auditor@example.test", "deviations-auditor-session")
GATE = ("gate@example.test", "gate-session")
READBACK_TEXT = ("read-back of Demo.ck: the formal statement says, in Lean, that every natural number n satisfies "
                 "n + 0 = n, a universally quantified identity over the naturals with no hypotheses at all.")


@pytest.fixture(scope="module", autouse=True)
def _manifest():
    from lean_env import session_trusted_manifest
    return session_trusted_manifest(LEAN_ENV)


def _compile(text: str, lib: Path, module: str = ART_MODULE) -> Path:
    """Compile `text` as `module` with the pinned lean (no lake) into `lib/build`; return that olean dir. Raises
    ValueError (the compile's own output) when it does not compile."""
    from telperion.checks.fingerprint import _compile_body
    from telperion.checks.lean_replay import DEFAULT_MEMORY_MB, default_wrapper, pinned_env
    pinned = pinned_env(LEAN_ENV)
    lib.mkdir(parents=True)
    _compile_body(text, module, lib, list(pinned.entries), default_wrapper(), pinned.lean, 1800, DEFAULT_MEMORY_MB)
    return lib / "build"


def _campaign(mroot: Path, statement: str, artifact: str) -> Path:
    """Campaign `demo`, node `Demo.ck` (slug Demo_ck): post-cutoff, an [author], an independent read-back, the
    statement file, and the artifact `proof/Demo_ck.lean` linked."""
    root = mroot / "demo"
    (root / "nodes").mkdir(parents=True)
    manifest = MissionManifest(name="Demo.ck", title="Demo Campaign", description="synthetic", goal_node="Demo_ck",
                               environment_toolchain="leanprover/lean4:v4.35.0",
                               environment_mathlib_rev="v4.35.0", sources=())
    save_manifest(manifest, root / "mission.toml")
    node = Node(name="Demo.ck", title="node awaiting grant", kind="lemma", status="open", depends_on=(),
                statement_module="Statements.Demo_ck",
                proof=Proof(artifact="proof/Demo_ck.lean", artifact_kind="lean_module", via="direct",
                            closure_clean=False),
                readback=Readback(text=READBACK_TEXT, auditor="test-auditor", date="2026-10-30"),
                author=Author(identity=AUTHOR[0], session=AUTHOR[1], date="2026-10-30"),
                created="2026-10-30", updated="2026-10-30")
    save_node(node, root / "nodes" / "Demo_ck.toml")
    write_statement(root, node, statement, manifest)
    art = root / "proof" / "Demo_ck.lean"
    art.parent.mkdir(parents=True)
    art.write_text(artifact, encoding="utf-8")
    return root


def _fingerprint_json(capsys, olean_dir: Path, target: str, art: Path) -> dict:
    """The real `telperion fingerprint --json` of `target` in the compiled artifact module."""
    capsys.readouterr()
    rc = main(["fingerprint", "--project", str(olean_dir), "--olean-dir", str(olean_dir), "--import", ART_MODULE,
               "--target", target, "--file", str(art), "--json"])
    out = capsys.readouterr().out
    assert rc == 0, out
    return json.loads(out)


def _synthetic_probe_and_closure(tmp_path: Path, fp: dict, target: str, art: Path) -> dict:
    """PROBE_ONLY and an isolated closure PASS, bound to the fingerprint run's closure and the artifact's source."""
    from telperion.closure_audit import AuditResult, TargetInfo
    cur = hashlib.sha256(art.read_bytes()).hexdigest()
    probe = {"verdict": "PROBE_ONLY", "detail": "synthetic", "olean_sha256": fp["olean_sha256"],
             "olean_closure": fp["olean_closure"], "axioms": fp["axioms"], "module": ART_MODULE, "theorem": target,
             "source_sha256": cur}
    closure = json.loads(AuditResult(verdict="PASS", lean_exit_code=0, targets=[
        TargetInfo(name=target, kind="theorem", statement="", axioms=list(fp["axioms"]))]).to_json())
    closure.update(isolated=True, olean_sha256=fp["olean_sha256"], olean_closure=fp["olean_closure"])
    paths = {}
    for name, doc in (("probe", probe), ("closure", closure), ("fp", fp)):
        paths[name] = tmp_path / f"{name}.json"
        paths[name].write_text(json.dumps(doc) + "\n")
    return paths


def _checks_record(mroot: Path, paths: dict, *extra: str) -> int:
    return main(["mission", "--missions-root", str(mroot), "checks-record", "Demo_ck", "--campaign", "demo",
                 "--probe-json", str(paths["probe"]), "--closure-json", str(paths["closure"]),
                 "--fingerprint-json", str(paths["fp"]), *extra])


@pytest.fixture(scope="module")
def frozen_statement_fp():
    """The statement's fingerprint as `mission freeze --fingerprints` computes it (statement file text, type mode)."""
    from telperion.checks.fingerprint import run_fingerprint_on_text
    return run_fingerprint_on_text(Path(LEAN_ENV), "-- statement\n" + STATEMENT + " := by sorry\n", "main_thm")


def _load_freeze(root: Path) -> dict:
    import tomllib
    return tomllib.loads((root / "FREEZE.toml").read_text())


# ---------------------------------------------------------------------------------------------------------------
# freeze --fingerprints, real
# ---------------------------------------------------------------------------------------------------------------

def test_freeze_fingerprints_agree_with_the_artifact_theorem(tmp_path, capsys, frozen_statement_fp):
    """A theorem-form statement (type mode) and a def-form one (value mode) of the same proposition get the same
    frozen fingerprint, which is the honest artifact theorem's type-mode fingerprint."""
    mroot = tmp_path / "missions"
    root = _campaign(mroot, STATEMENT, HONEST)
    manifest = load_campaign(root).manifest
    other = Node(name="Demo.def", title="def-form statement", kind="lemma", status="draft", depends_on=(),
                 statement_module="Statements.Demo_def")
    save_node(other, root / "nodes" / "Demo_def.toml")
    write_statement(root, other, "def StmtDef : Prop := 1 + 1 = 2", manifest)
    assert "def StmtDef : Prop := 1 + 1 = 2" in statement_path(root, other).read_text()

    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo", "--identity", GATE[0],
               "--session", GATE[1], "--fingerprints"])
    out = capsys.readouterr().out
    assert rc == 0 and "2 statement fingerprint(s) recorded" in out, out
    fps = _load_freeze(root)["fingerprints"]
    olean_dir = _compile(HONEST, tmp_path / "lib")
    art_fp = _fingerprint_json(capsys, olean_dir, "main_thm", root / "proof" / "Demo_ck.lean")
    assert fps == {"Demo_ck": art_fp["fingerprints"]["main_thm"], "Demo_def": art_fp["fingerprints"]["main_thm"]}
    assert fps["Demo_ck"] == frozen_statement_fp


def test_freeze_fingerprints_refuses_a_statement_it_cannot_fingerprint(tmp_path, capsys):
    """A def-form statement whose type is not Prop is refused in value mode, and the freeze writes nothing."""
    mroot = tmp_path / "missions"
    _campaign(mroot, "import Mathlib\n\ndef StmtN : ℕ := 3", HONEST)
    rc = main(["mission", "--missions-root", str(mroot), "freeze", "demo", "--identity", GATE[0],
               "--session", GATE[1], "--fingerprints"])
    out = capsys.readouterr().out
    assert rc == 1 and "value-mode-not-prop" in out and "'Demo_ck'" in out, out
    assert not (mroot / "demo" / "FREEZE.toml").exists()


# ---------------------------------------------------------------------------------------------------------------
# The five evasions, each REFUSED at checks-record by fingerprint inequality
# ---------------------------------------------------------------------------------------------------------------

@pytest.mark.parametrize("case", sorted(EVASIONS))
def test_evasion_refused_by_fingerprint_inequality(tmp_path, capsys, case, frozen_statement_fp):
    from telperion.missions import judge
    from telperion.missions.process import freeze
    text = EVASIONS[case]
    mroot = tmp_path / "missions"
    root = _campaign(mroot, STATEMENT, text)
    art = root / "proof" / "Demo_ck.lean"
    # the syntactic resolver is still fooled: it names the decoy (what the name tie alone would accept)
    assert judge._guard_anchors().resolve_theorem(text, statement_path(root, load_node(
        root / "nodes" / "Demo_ck.toml")).read_text()) == "Helper.main_thm"
    freeze(root, identity=GATE[0], session=GATE[1], date="2026-10-30", fingerprints={"Demo_ck": frozen_statement_fp})

    try:
        olean_dir = _compile(text, tmp_path / "lib")
    except ValueError as exc:                     # documented outcome: the artifact does not compile at all
        pytest.fail(f"evasion {case} did not compile, so it cannot reach checks-record: {exc}")
    fp = _fingerprint_json(capsys, olean_dir, "Helper.main_thm", art)
    assert fp["fingerprints"]["Helper.main_thm"] != frozen_statement_fp
    paths = _synthetic_probe_and_closure(tmp_path, fp, "Helper.main_thm", art)
    assert _checks_record(mroot, paths, "--note", "signoff: test") == 2
    err = capsys.readouterr().err
    assert "statement fingerprint mismatch" in err, err
    assert load_node(root / "nodes" / "Demo_ck.toml").checks is None


def test_honest_artifact_passes_the_fingerprint_tie(tmp_path, capsys, frozen_statement_fp):
    """The control for the evasions: the same campaign with an honest artifact records (synthetic probe/closure)."""
    from telperion.missions.process import freeze
    mroot = tmp_path / "missions"
    root = _campaign(mroot, STATEMENT, HONEST)
    art = root / "proof" / "Demo_ck.lean"
    freeze(root, identity=GATE[0], session=GATE[1], date="2026-10-30", fingerprints={"Demo_ck": frozen_statement_fp})
    olean_dir = _compile(HONEST, tmp_path / "lib")
    fp = _fingerprint_json(capsys, olean_dir, "main_thm", art)
    assert fp["fingerprints"]["main_thm"] == frozen_statement_fp
    paths = _synthetic_probe_and_closure(tmp_path, fp, "main_thm", art)
    assert _checks_record(mroot, paths, "--note", "signoff: test") == 0, capsys.readouterr().err
    assert load_node(root / "nodes" / "Demo_ck.toml").checks.statement_fingerprint == frozen_statement_fp


# ---------------------------------------------------------------------------------------------------------------
# The statement-first flow with every check real
# ---------------------------------------------------------------------------------------------------------------

def _git(root: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@example.invalid", *args],
                   check=True, capture_output=True)


def test_lean_e2e_freeze_checks_and_grant(tmp_path, capsys):
    mroot = tmp_path / "missions"
    croot = mroot / "demo"
    (croot / "nodes").mkdir(parents=True)
    save_manifest(MissionManifest(name="Demo.ck", title="Demo Campaign", description="synthetic",
                                  goal_node="Demo_ck", environment_toolchain="leanprover/lean4:v4.35.0",
                                  environment_mathlib_rev="v4.35.0", sources=()), croot / "mission.toml")

    def cli(*args: str) -> int:
        return main(["mission", "--missions-root", str(mroot), *args])

    stmt = "import Mathlib\n\ntheorem lemma_ck : ∀ n : ℕ, n + 0 = n"
    assert cli("add", "demo", "Demo.ck", "--title", "node awaiting grant", "--kind", "lemma", "--statement", stmt,
               "--identity", AUTHOR[0], "--session", AUTHOR[1]) == 0
    assert cli("audit", "Demo_ck", "--campaign", "demo", "--text", READBACK_TEXT, "--identity", AUDITOR[0],
               "--session", AUDITOR[1]) == 0
    art = croot / "proof" / "Demo_ck.lean"
    art.parent.mkdir(parents=True)
    artifact = "import Mathlib\n\ntheorem lemma_ck : ∀ n : ℕ, n + 0 = n := fun n => rfl\n"
    art.write_text(artifact, encoding="utf-8")
    assert cli("link", "Demo_ck", "--campaign", "demo", "--artifact", "proof/Demo_ck.lean", "--kind",
               "lean_module", "--via", "direct") == 0

    # freeze --fingerprints (real Lean), committed
    assert cli("freeze", "demo", "--identity", GATE[0], "--session", GATE[1], "--fingerprints") == 0
    frozen = _load_freeze(croot)["fingerprints"]["Demo_ck"]
    subprocess.run(["git", "-C", str(croot), "init", "-q"], check=True, capture_output=True)
    _git(croot, "add", "-A")
    _git(croot, "commit", "-q", "-m", "freeze")

    # the three checks, real, on the compiled artifact
    olean_dir = _compile(artifact, tmp_path / "lib")
    common = ["--project", str(olean_dir), "--olean-dir", str(olean_dir)]
    capsys.readouterr()
    main(["probe-negation", *common, "--module", ART_MODULE, "--theorem", "lemma_ck", "--file", str(art), "--json"])
    probe = capsys.readouterr().out
    fp = _fingerprint_json(capsys, olean_dir, "lemma_ck", art)
    assert fp["fingerprints"]["lemma_ck"] == frozen
    closure_json = tmp_path / "closure.json"
    rc = main(["audit-closure", *common, "--import", ART_MODULE, "--target", "lemma_ck", "--json", str(closure_json)])
    assert rc == 0, capsys.readouterr().out
    paths = {"probe": tmp_path / "probe.json", "fp": tmp_path / "fp.json", "closure": closure_json}
    paths["probe"].write_text(probe)
    paths["fp"].write_text(json.dumps(fp))
    assert json.loads(probe)["verdict"] == "PROBE_ONLY", probe
    capsys.readouterr()
    rc = _checks_record(mroot, paths, "--note", "signoff: bb read the statement")
    assert rc == 0, capsys.readouterr()

    assert cli("deviations-readback", "demo", "--identity", DEVIATIONS_AUDITOR[0], "--session",
               DEVIATIONS_AUDITOR[1]) == 0
    capsys.readouterr()
    rc = cli("grant", "Demo_ck", "--campaign", "demo", "--identity", GATE[0], "--session", GATE[1])
    out = capsys.readouterr().out
    assert rc == 0, out
    node = load_node(croot / "nodes" / "Demo_ck.toml")
    assert node.status == "proved" and node.grant.checks_required is True
    from telperion.missions.provenance import GATE_VERSION
    assert node.grant.gate_version == GATE_VERSION == "2026-10-31.1"
    assert node.checks.statement_fingerprint == frozen and node.checks.closure_isolated is True
    shutil.rmtree(tmp_path / "lib", ignore_errors=True)
