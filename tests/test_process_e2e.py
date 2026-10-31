"""Step 5, Task 5: an end-to-end dry run of the statement-first process on a synthetic
campaign, driven through the CLI wherever a CLI exists for the step.

Per the controller's Ruling 2 (`.superpowers/sdd/2026-10-27-step5-process/progress.md`),
by the time this task runs the grant gate checks FOUR post-cutoff preconditions in a fixed
order (`verify.grant_status`): `[checks]`, the node's `[author]` block, the campaign
freeze, then the deviation ledger -- in that order (`[checks]` is checked FIRST, ahead of
the freeze and the ledger). This test demonstrates each gate's refusal in the order the
gate actually raises them -- not the order the original task brief sketched (which
predates the gate's final shape). Every failure message asserted below is the EXACT
wording the gate raises, read straight out of `verify.py`/`process.py`, not just a
non-zero exit code.

Step 5 Task 6 (Ruling 2's extension): a post-cutoff `[checks]` record is tied to the
node's FROZEN statement fingerprint, so `checks-record` now refuses until the campaign is
frozen with one ("statement fingerprint not frozen"), and refuses a fingerprint that
differs from it. The order is therefore: `[checks]` missing; `checks-record` refused (not
frozen); freeze (no fingerprints) and `checks-record` still refused; the fingerprint
injected into FREEZE.toml through its own writer (standing for `mission freeze
--fingerprints`, which needs Lean -- tests/test_statement_tie_lean.py runs the real one);
a mismatched fingerprint refused; `checks-record` passes; the grant refused on the
freeze that is not in git yet; a node added after the freeze and recorded with `freeze
--add`; the grant refused on the missing DEVIATIONS read-back; then success. It ends (final
review M7) on a green `verify`, after the statement edit, the unfreeze, a re-audit and a
re-grant.

No Lean toolchain is needed: every artifact here is plain text and the gate's checks on
it (`checks_problem`, `freeze_problems`, `deviations_grant_problem`, ...) never shell out
to `lake` or `lean` for a synthetic, off-island fixture.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions.schema import MissionManifest, load_node, save_manifest  # noqa: E402
from telperion.missions.statements import write_statement  # noqa: E402

# The step-4 checks fixtures (tests/test_missions_checks.py): `_write_jsons` builds the
# three JSONs `checks-record` reads, in the exact shapes the real checks print, tied to
# the CLI campaign's own artifact sha256 by its own hardcoded path
# (tmp_path/"missions"/"demo"/"proof"/"Demo_ck.lean") -- which is exactly the layout this
# test builds below, campaign "demo", node "Demo.ck" / slug "Demo_ck", artifact
# "proof/Demo_ck.lean". `_record` runs `mission checks-record` through the CLI.
from test_missions_checks import FP_ENV, FPRINT, _record, _write_jsons  # noqa: E402
from telperion.missions.process import _load_freeze_safe, _write_freeze  # noqa: E402

#: Identities and sessions, each pair distinct from every other pair in both fields
#: (provenance.independence_of/`_auditor_matches` compare BOTH the session and the
#: identity): the author of the node, an independent auditor for its read-back, a
#: distinct auditor for the DEVIATIONS.md ledger, the gate's own runner, and (for the
#: later unfreeze) a process owner and a distinct reviewer of it.
AUTHOR = ("author@example.test", "author-session")
AUDITOR = ("auditor@example.test", "auditor-session")
DEVIATIONS_AUDITOR = ("deviations-auditor@example.test", "deviations-auditor-session")
GATE = ("gate@example.test", "gate-session")
UNFREEZE_OWNER = "unfreeze-owner@example.test"
UNFREEZE_READBACK = "unfreeze-reviewer@example.test"

#: The read-back text `mission audit` requires: >=120 characters (MIN_READBACK_CHARS),
#: an actual rendering of the formal statement rather than a repeat of the title.
READBACK_TEXT = (
    "read-back of Demo.ck: the formal statement declares, in Lean, the closed numeral "
    "proposition `1 + 1 = 2` over the natural numbers, with no free variables or "
    "hypotheses to quantify over; the linked artifact proves it by `simp`."
)


def _git_commit(croot: Path, message: str) -> None:
    """`git add -A && git commit -m message`, with a throwaway identity passed on the
    command line (`-c user.name=... -c user.email=...`) -- NEVER the global git config,
    which this sandbox must not touch or depend on."""
    subprocess.run(["git", "-C", str(croot), "add", "-A"], check=True, capture_output=True)
    subprocess.run(
        ["git", "-C", str(croot), "-c", "user.name=t", "-c", "user.email=t@example.invalid",
         "commit", "-q", "-m", message],
        check=True, capture_output=True,
    )


def _inject_frozen_fingerprint(croot: Path, slug: str, fp: str) -> None:
    """Record *fp* as *slug*'s frozen statement fingerprint, through FREEZE.toml's own reader and
    writer, BEFORE the freeze state is committed: what `mission freeze --fingerprints` (or
    `unfreeze --fingerprints`) writes when Lean computes *fp*."""
    doc, problem = _load_freeze_safe(croot)
    assert doc is not None and problem is None, problem
    doc["fingerprints"] = {**(doc.get("fingerprints") or {}), slug: fp}
    doc["fingerprints_env"] = FP_ENV            # the trusted env digest `--fingerprints` records with them
    _write_freeze(croot, doc)


def test_statement_first_process_e2e(tmp_path, capsys):
    mroot = tmp_path / "missions"
    croot = mroot / "demo"

    # --- Scaffold the campaign itself. There is no CLI verb that creates a campaign's
    # mission.toml (every CLI verb below operates on an EXISTING one), so this part is
    # written directly, the same way every other missions test bootstraps a campaign. ---
    (croot / "nodes").mkdir(parents=True)
    manifest = MissionManifest(
        name="Demo.ck", title="Demo Campaign", description="synthetic",
        goal_node="Demo_ck", environment_toolchain="leanprover/lean4:v4.32.0",
        environment_mathlib_rev="v4.32.0", sources=(),
    )
    save_manifest(manifest, croot / "mission.toml")

    def cli(*args: str) -> int:
        return main(["mission", "--missions-root", str(mroot), *args])

    def grant() -> int:
        return cli("grant", "Demo_ck", "--campaign", "demo", "--identity", GATE[0],
                   "--session", GATE[1])

    def node():
        return load_node(croot / "nodes" / "Demo_ck.toml")

    # ------------------------------------------------------------------
    # Step 1: `mission add` -- a post-cutoff node (CUTOFF = 2026-10-28; `created` is
    # today's real date, which this environment's clock already puts after the cutoff).
    # This writes the `[author]` block grants require (Ruling 13).
    # ------------------------------------------------------------------
    stmt = "import Mathlib\n\ntheorem lemma_ck : 1 + 1 = 2"
    rc = cli("add", "demo", "Demo.ck", "--title", "node awaiting grant", "--kind", "lemma",
             "--statement", stmt, "--identity", AUTHOR[0], "--session", AUTHOR[1])
    assert rc == 0
    n = node()
    assert n.status == "draft"
    assert n.author is not None and n.author.identity == AUTHOR[0]
    assert n.created and n.created >= "2026-10-28"   # post-cutoff

    # Independent read-back promotes draft -> open (MISSIONS_DESIGN_2026-09-11.md section 8).
    rc = cli("audit", "Demo_ck", "--campaign", "demo", "--text", READBACK_TEXT,
             "--identity", AUDITOR[0], "--session", AUDITOR[1])
    assert rc == 0
    assert node().status == "open"

    # The proof artifact: written by hand (no CLI authors Lean), then linked by `mission
    # link` (status unchanged -- `grant` is the only verb that flips status).
    art = croot / "proof" / "Demo_ck.lean"
    art.parent.mkdir(parents=True, exist_ok=True)
    art.write_text("theorem lemma_ck : 1 + 1 = 2 := by simp\n")
    rc = cli("link", "Demo_ck", "--campaign", "demo", "--artifact", "proof/Demo_ck.lean",
             "--kind", "lean_module", "--via", "direct")
    assert rc == 0

    # ------------------------------------------------------------------
    # Step 2: a grant attempt fails on `[checks]` -- nothing is recorded yet, and the
    # gate checks `[checks]` before it ever looks at the freeze or the deviation ledger.
    # ------------------------------------------------------------------
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 1 and "[checks]" in out, out
    assert node().status == "open"

    # The checks' JSONs, through the exact helper the step-4 tests use
    # (tests/test_missions_checks.py's `_write_jsons`/`_record`): a PROBE_ONLY verdict
    # with a reviewer `signoff:` note, tied to the node's registered theorem
    # (`lemma_ck`), the artifact's current source_sha256, and a clean replay axiom list.
    paths = _write_jsons(tmp_path, verdict="PROBE_ONLY")
    signoff = ("--note", "signoff: bb reviewed the hypotheses")

    # ------------------------------------------------------------------
    # Step 3 (step 5 Task 6): `checks-record` is refused -- the campaign is not frozen,
    # so there is no frozen statement fingerprint to tie the checked theorem to.
    # ------------------------------------------------------------------
    assert _record(mroot, paths, *signoff) == 2
    err = capsys.readouterr().err
    assert "statement fingerprint not frozen (no FREEZE.toml)" in err, err
    assert node().checks is None

    # `mission freeze` -- it also writes the DEVIATIONS.md template (`none`). Without
    # --fingerprints it records no statement fingerprint, and says what that means.
    rc = cli("freeze", "demo", "--identity", GATE[0], "--session", GATE[1])
    out = capsys.readouterr().out
    assert rc == 0
    assert "no statement fingerprints recorded" in out, out
    assert (croot / "FREEZE.toml").exists()
    assert (croot / "DEVIATIONS.md").exists()
    assert _record(mroot, paths, *signoff) == 2
    err = capsys.readouterr().err
    assert "statement fingerprint not frozen (FREEZE.toml has no [fingerprints] entry for 'Demo_ck')" in err, err

    # The frozen statement fingerprint, injected through FREEZE.toml's own writer before the
    # first commit (what `mission freeze --fingerprints` records, computed with Lean). A
    # fingerprint JSON whose theorem states something else is refused (the semantic tie);
    # the matching one passes.
    _inject_frozen_fingerprint(croot, "Demo_ck", FPRINT)
    other = _write_jsons(tmp_path, verdict="PROBE_ONLY", fingerprints={"lemma_ck": "a" * 64})
    assert _record(mroot, other, *signoff) == 2
    err = capsys.readouterr().err
    assert "statement fingerprint mismatch" in err, err
    assert node().checks is None
    paths = _write_jsons(tmp_path, verdict="PROBE_ONLY")
    assert _record(mroot, paths, *signoff) == 0
    assert node().checks is not None and node().checks.probe_verdict == "PROBE_ONLY"
    assert node().checks.statement_fingerprint == FPRINT

    # ------------------------------------------------------------------
    # Step 4: a grant attempt now fails on the freeze -- FREEZE.toml exists but is not in
    # git yet, so its history (Rulings 5-9) cannot be verified.
    # ------------------------------------------------------------------
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 1 and "freeze has unresolved problem(s)" in out and "freeze history unavailable" in out, out
    assert node().status == "open"

    # COMMIT the freeze: post-cutoff freezes must be verifiable against git history
    # (Rulings 5-9), so the tmp campaign becomes a git repo of its own, never touching the
    # ambient global git config.
    subprocess.run(["git", "-C", str(croot), "init", "-q"], check=True, capture_output=True)
    _git_commit(croot, "freeze demo campaign")

    # Final review I3: a second node, added AFTER the freeze. `mission add` says the campaign is
    # frozen; until `freeze --add` records it (at the unchanged version), the freeze check
    # reports it and blocks every post-cutoff grant in the campaign.
    rc = cli("add", "demo", "Demo.two", "--title", "a node added after the freeze", "--kind", "lemma",
             "--statement", "import Mathlib\n\ntheorem lemma_two : 2 + 2 = 4",
             "--identity", AUTHOR[0], "--session", AUTHOR[1])
    out = capsys.readouterr().out
    assert rc == 0 and "freeze demo --add" in out, out
    _git_commit(croot, "add Demo.two")
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 1 and "'Demo_two' has a statement file but is not recorded" in out, out
    rc = cli("freeze", "demo", "--add")
    out = capsys.readouterr().out
    assert rc == 0 and "recorded 1 new node(s) at version 1: Demo_two" in out, out
    _git_commit(croot, "freeze --add Demo.two")

    # ------------------------------------------------------------------
    # Step 5: a grant attempt now fails on the missing DEVIATIONS read-back -- the ledger
    # exists (the `none` template) and parses, but nobody has read it back yet.
    # ------------------------------------------------------------------
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 1 and "DEVIATIONS.readback.toml" in out, out
    assert node().status == "open"

    # `mission deviations-readback`, with an identity and session DIFFERENT from the
    # node's author (deviations_grant_problem's layer 4: a self-read-back cannot support
    # a grant, same comparison as the node's own read-back independence check).
    rc = cli("deviations-readback", "demo", "--identity", DEVIATIONS_AUDITOR[0],
             "--session", DEVIATIONS_AUDITOR[1])
    assert rc == 0
    assert (croot / "DEVIATIONS.readback.toml").exists()

    # ------------------------------------------------------------------
    # Step 6: the grant now succeeds.
    # ------------------------------------------------------------------
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 0, out
    assert node().status == "proved"
    assert node().grant is not None and node().grant.checks_required is True

    # ------------------------------------------------------------------
    # Step 7: edit the statement and commit it -- `verify` must fail with "statement
    # drift" (the campaign-wide freeze check, `process.freeze_problems`: the current
    # statement hash no longer matches the one FREEZE.toml recorded).
    #
    # The edit is a trailing Lean comment: `normalize_lean` strips comments before
    # matching, so the artifact still proves the (unchanged) normalized proposition --
    # this isolates the freeze-drift failure from an unrelated artifact/statement
    # mismatch, which is not what this step is testing.
    # ------------------------------------------------------------------
    edited_stmt = "import Mathlib\n\ntheorem lemma_ck : 1 + 1 = 2  -- annotated post-freeze"
    write_statement(croot, node(), edited_stmt, manifest)
    _git_commit(croot, "annotate the statement after freeze")

    rc = cli("verify", "demo")
    out = capsys.readouterr().out
    assert rc == 1
    assert "statement drift" in out, out

    # ------------------------------------------------------------------
    # Step 8: `mission unfreeze`, with a read-back identity distinct from its author --
    # `verify` now passes the freeze check (the drifted hash is gone; FREEZE.toml records
    # the current statement and an `[[unfreeze]]` entry for it). Without --fingerprints
    # the new version records no statement fingerprint (none is carried forward), so the
    # proved node's [checks] stop passing in `verify` until one is recorded for this
    # version; it is injected before the unfreeze is committed, as `unfreeze
    # --fingerprints` would write it.
    # ------------------------------------------------------------------
    rc = cli("unfreeze", "demo", "--author", UNFREEZE_OWNER,
             "--reason", "statement annotated after the freeze",
             "--readback-identity", UNFREEZE_READBACK)
    out = capsys.readouterr().out
    assert rc == 0 and "no statement fingerprints recorded" in out, out

    rc = cli("verify", "demo")
    out = capsys.readouterr().out
    assert "statement drift" not in out, out
    assert rc == 1 and "statement fingerprint not frozen" in out, out
    # final review I2: an uncommitted unfreeze counts for nothing
    assert "FREEZE.toml has uncommitted changes" in out, out

    _inject_frozen_fingerprint(croot, "Demo_ck", FPRINT)
    _git_commit(croot, "unfreeze after the statement annotation")

    rc = cli("verify", "demo")
    out = capsys.readouterr().out
    assert "statement drift" not in out, out
    assert "statement fingerprint" not in out, out

    # ------------------------------------------------------------------
    # Step 9: the provenance lint passes on the campaign (no ported files here, so
    # nothing requires a provenance header), and `mission audit-file` writes Audit.lean.
    # ------------------------------------------------------------------
    rc = main(["lint-provenance", str(croot)])
    out = capsys.readouterr().out
    assert rc == 0 and "OK" in out, out

    rc = cli("audit-file", "demo")
    out = capsys.readouterr().out
    assert rc == 0
    audit_path = croot / "lean" / "Audit.lean"
    assert audit_path.exists()
    assert "#print axioms lemma_ck" in audit_path.read_text()
    assert "audit-closure --project" in out and "--target lemma_ck" in out, out     # final review I5

    # ------------------------------------------------------------------
    # Step 10 (final review M7): close the loop. The statement changed after the grant, so
    # `verify` reports the grant's statement digest as stale until the node is re-granted.
    # There is no verb that reopens a proved node; it is set back to `draft` through the
    # schema, the way the campaign was scaffolded above. Then an independent re-audit, a
    # re-grant through the gate, and `verify` is green.
    # ------------------------------------------------------------------
    rc = cli("verify", "demo")
    out = capsys.readouterr().out
    assert rc == 1 and "statement file has changed since the gate granted this node" in out, out
    import dataclasses
    from telperion.missions.schema import save_node
    save_node(dataclasses.replace(node(), status="draft"), croot / "nodes" / "Demo_ck.toml")
    rc = cli("audit", "Demo_ck", "--campaign", "demo", "--text", READBACK_TEXT,
             "--identity", AUDITOR[0], "--session", AUDITOR[1])
    assert rc == 0 and node().status == "open"
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 0, out
    rc = cli("verify", "demo")
    out = capsys.readouterr().out
    assert rc == 0, out
