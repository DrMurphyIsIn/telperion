"""Step 5, Task 5: an end-to-end dry run of the statement-first process on a synthetic
campaign, driven through the CLI wherever a CLI exists for the step.

Per the controller's Ruling 2 (`.superpowers/sdd/2026-10-27-step5-process/progress.md`),
by the time this task runs the grant gate checks FOUR post-cutoff preconditions in a fixed
order (`verify.grant_status`): `[checks]`, the node's `[author]` block, the campaign
freeze, then the deviation ledger -- in that order (`[checks]` is checked FIRST, ahead of
the freeze and the ledger). This test demonstrates each gate's refusal in the order the
gate actually raises them, which is: `[checks]` missing, then "frozen", then the missing
DEVIATIONS read-back, then success -- not the order the original task brief sketched
(which predates the gate's final shape). Every failure message asserted below is the
EXACT wording the gate raises, read straight out of `verify.py`/`process.py`, not just a
non-zero exit code.

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
from test_missions_checks import _record, _write_jsons  # noqa: E402

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

    # Write a passing `[checks]` record, through the exact helper the step-4 tests use
    # (tests/test_missions_checks.py's `_write_jsons`/`_record`): a PROBE_ONLY verdict
    # with a reviewer `signoff:` note, tied to the node's registered theorem
    # (`lemma_ck`), the artifact's current source_sha256, and a clean replay axiom list.
    paths = _write_jsons(tmp_path, verdict="PROBE_ONLY")
    assert _record(mroot, paths, "--note", "signoff: bb reviewed the hypotheses") == 0
    assert node().checks is not None and node().checks.probe_verdict == "PROBE_ONLY"

    # ------------------------------------------------------------------
    # Step 3: a grant attempt now fails with "frozen" -- the campaign has no FREEZE.toml.
    # ------------------------------------------------------------------
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 1 and "frozen" in out, out
    assert node().status == "open"

    # `mission freeze` -- it also writes the DEVIATIONS.md template (`none`) -- then
    # COMMIT it: post-cutoff freezes must be verifiable against git history (Rulings 5-9),
    # so the tmp campaign becomes a git repo of its own, never touching the ambient
    # global git config.
    rc = cli("freeze", "demo", "--identity", GATE[0], "--session", GATE[1])
    assert rc == 0
    assert (croot / "FREEZE.toml").exists()
    assert (croot / "DEVIATIONS.md").exists()
    subprocess.run(["git", "-C", str(croot), "init", "-q"], check=True, capture_output=True)
    _git_commit(croot, "freeze demo campaign")

    # ------------------------------------------------------------------
    # Step 4: a grant attempt now fails on the missing DEVIATIONS read-back -- the ledger
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
    # Step 5: the grant now succeeds.
    # ------------------------------------------------------------------
    rc = grant()
    out = capsys.readouterr().out
    assert rc == 0, out
    assert node().status == "proved"
    assert node().grant is not None and node().grant.checks_required is True

    # ------------------------------------------------------------------
    # Step 6: edit the statement and commit it -- `verify` must fail with "statement
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
    # Step 7: `mission unfreeze`, with a read-back identity distinct from its author,
    # then commit -- `verify` now passes the freeze check (the drifted hash is gone;
    # FREEZE.toml records the current statement and an `[[unfreeze]]` entry for it).
    # ------------------------------------------------------------------
    rc = cli("unfreeze", "demo", "--author", UNFREEZE_OWNER,
             "--reason", "statement annotated after the freeze",
             "--readback-identity", UNFREEZE_READBACK)
    assert rc == 0
    _git_commit(croot, "unfreeze after the statement annotation")

    rc = cli("verify", "demo")
    out = capsys.readouterr().out
    assert "statement drift" not in out, out

    # ------------------------------------------------------------------
    # Step 8: the provenance lint passes on the campaign (no ported files here, so
    # nothing requires a provenance header), and `mission audit-file` writes Audit.lean.
    # ------------------------------------------------------------------
    rc = main(["lint-provenance", str(croot)])
    out = capsys.readouterr().out
    assert rc == 0 and "OK" in out, out

    rc = cli("audit-file", "demo")
    assert rc == 0
    audit_path = croot / "lean" / "Audit.lean"
    assert audit_path.exists()
    assert "#print axioms lemma_ck" in audit_path.read_text()
