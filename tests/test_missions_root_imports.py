"""Root-import gate: a statement CI never elaborates cannot pass `mission verify`.

Background (2026-09-24).  The `mission-statements-compile` CI job runs `lake build` in
`missions/<campaign>/lean`, which compiles exactly the import closure of the package root
`Statements.lean`.  `write_statement` wrote the module file but nothing ever added the
import line, so fifteen registered statements (eleven rh, four mirrormere, most of them
`status = "proved"`) had never been elaborated by any job, and one of them had no
`import` line at all.  These tests pin the gate that closes that hole:

  * `write_statement` (hence `mission add`) appends the module to the root;
  * `regen_diff` reports a statement the root does not import (staleness of the
    import list, not just of the file body);
  * `verify_campaign` fails on an un-imported statement, on a statement without the
    standard import header, and on a root import with no file behind it;
  * the four live campaigns pass (see test_missions_campaigns.py, which runs the
    whole battery against them).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cli import main  # noqa: E402
from telperion.missions.registry import load_campaign  # noqa: E402
from telperion.missions.schema import MissionManifest, Node, slug_of  # noqa: E402
from telperion.missions.statements import (  # noqa: E402
    ensure_root_import,
    import_header_error,
    missing_root_imports,
    regen_diff,
    regenerate_statement,
    root_imports,
    root_module_path,
    statement_path,
    write_statement,
)
from telperion.missions.verify import verify_campaign  # noqa: E402

from test_missions_cli import make_demo_root  # noqa: E402

MISSIONS = Path(__file__).resolve().parents[1] / "missions"
LIVE_CAMPAIGNS = sorted(p.name for p in MISSIONS.iterdir() if (p / "mission.toml").exists())


def _manifest() -> MissionManifest:
    return MissionManifest(
        name="Demo.goal", title="Demo", description="fixture", goal_node="Demo_goal",
        environment_toolchain="leanprover/lean4:v4.32.0", environment_mathlib_rev="v4.32.0",
    )


def _node(name: str) -> Node:
    return Node(
        name=name, title=name, kind="lemma", status="draft", depends_on=(),
        statement_module=f"Statements.{slug_of(name)}", created="2026-09-24", updated="2026-09-24",
    )


def _defs(root: Path) -> None:
    """Give the fixture a campaign Defs module so the header check has a real target."""
    d = root / "lean" / "Statements"
    d.mkdir(parents=True, exist_ok=True)
    (d / "DemoDefs.lean").write_text("import Mathlib\n")
    ensure_root_import(root, "Statements.DemoDefs")


def _unwire(root: Path, module: str) -> None:
    """Drop one import line from the root: the on-disk state of the fifteen."""
    p = root_module_path(root)
    p.write_text("".join(ln for ln in p.read_text().splitlines(keepends=True)
                         if ln.strip() != f"import {module}"))


# ---------------------------------------------------------------------------
# write_statement / ensure_root_import
# ---------------------------------------------------------------------------

def test_write_statement_appends_root_import(tmp_path):
    root = tmp_path / "demo"
    root.mkdir()
    node = _node("Demo.lemma_a")
    assert root_imports(root) == []
    write_statement(root, node, "import Mathlib\ntheorem a : 1 = 1", _manifest())
    assert root_imports(root) == ["Statements.Demo_lemma_a"]
    # idempotent: a second write does not duplicate the line
    write_statement(root, node, "import Mathlib\ntheorem a : 1 = 1", _manifest())
    assert root_imports(root) == ["Statements.Demo_lemma_a"]


def test_ensure_root_import_appends_without_reordering(tmp_path):
    root = tmp_path / "demo"
    root_module_path(root).parent.mkdir(parents=True)
    root_module_path(root).write_text("import Statements.Zed\nimport Statements.Alpha\n")
    assert ensure_root_import(root, "Statements.Mid") is True
    assert ensure_root_import(root, "Statements.Mid") is False
    assert root_imports(root) == ["Statements.Zed", "Statements.Alpha", "Statements.Mid"]


def test_mission_add_appends_root_import(tmp_path, capsys):
    mroot, campaign_root = make_demo_root(tmp_path)
    rc = main([
        "mission", "--missions-root", str(mroot), "add", "demo", "New.lemma_x",
        "--title", "New lemma X", "--kind", "lemma",
        "--statement", "import Mathlib\ntheorem new_x : 1 = 1",
    ])
    assert rc == 0
    assert "Statements.New_lemma_x" in root_imports(campaign_root)
    assert root_module_path(campaign_root).read_text().endswith("import Statements.New_lemma_x\n")
    # and the fresh node passes the whole battery, root import included
    report = verify_campaign(campaign_root)
    assert report.ok, report.errors


# ---------------------------------------------------------------------------
# regen_diff and missing_root_imports
# ---------------------------------------------------------------------------

def test_regen_diff_reports_unimported_statement(tmp_path):
    root = tmp_path / "demo"
    root.mkdir()
    node = _node("Demo.lemma_a")
    write_statement(root, node, "import Mathlib\ntheorem a : 1 = 1", _manifest())
    assert regen_diff(root, node, _manifest()) == ""
    _unwire(root, "Statements.Demo_lemma_a")
    diff = regen_diff(root, node, _manifest())
    assert "does not import Statements.Demo_lemma_a" in diff
    # a hash mismatch still takes precedence (the body is the first thing to trust)
    p = statement_path(root, node)
    p.write_text(p.read_text().replace("1 = 1", "2 = 2"))
    assert "hash mismatch" in regen_diff(root, node, _manifest())


def test_missing_root_imports_both_directions(tmp_path):
    root = tmp_path / "demo"
    root.mkdir()
    a, b = _node("Demo.lemma_a"), _node("Demo.lemma_b")
    for n in (a, b):
        write_statement(root, n, "import Mathlib\ntheorem t : 1 = 1", _manifest())
    assert missing_root_imports(root, [a, b]) == []
    _unwire(root, "Statements.Demo_lemma_b")
    ensure_root_import(root, "Statements.Ghost")           # named by the root, no file
    (root / "lean" / "Statements" / "Stray.lean").write_text("import Mathlib\n")  # file, no node
    assert missing_root_imports(root, [a, b]) == [
        "(no file) Statements.Ghost", "Statements.Demo_lemma_b", "Statements.Stray",
    ]


# ---------------------------------------------------------------------------
# import header
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("stmt, ok", [
    ("import Mathlib\ntheorem t : 1 = 1", True),
    ("import Statements.DemoDefs\ntheorem t : 1 = 1", True),
    ("import Mathlib.Tactic\ntheorem t : 1 = 1", True),
    ("import Mathlib\nimport Statements.DemoDefs\nopen Nat\ntheorem t : 1 = 1", True),
    ("theorem t : 1 = 1", False),                       # MM_weil_positivity_window_tenth's shape
    ("import Statements.Other\ntheorem t : 1 = 1", False),
])
def test_import_header_error(tmp_path, stmt, ok):
    root = tmp_path / "demo"
    root.mkdir()
    _defs(root)
    node = _node("Demo.lemma_a")
    write_statement(root, node, stmt, _manifest())
    err = import_header_error(root, node)
    assert (err == "") is ok, err


# ---------------------------------------------------------------------------
# verify_campaign: the negatives
# ---------------------------------------------------------------------------

def _fixture_with_statement(tmp_path, stmt="import Mathlib\ntheorem demo_lemma_a : 1 = 1"):
    mroot, campaign_root = make_demo_root(tmp_path)
    _defs(campaign_root)
    camp = load_campaign(campaign_root)
    node = camp.nodes["Demo_lemma_a"]
    write_statement(campaign_root, node, stmt, _manifest())
    return campaign_root, node


def test_verify_passes_wired_fixture(tmp_path):
    campaign_root, _ = _fixture_with_statement(tmp_path)
    report = verify_campaign(campaign_root)
    assert report.ok, report.errors


def test_verify_fails_unimported_statement(tmp_path):
    campaign_root, node = _fixture_with_statement(tmp_path)
    _unwire(campaign_root, node.statement_module)
    report = verify_campaign(campaign_root)
    assert not report.ok
    assert any("does not import Statements.Demo_lemma_a" in e for e in report.errors), report.errors


def test_verify_fails_statement_without_imports(tmp_path):
    campaign_root, _ = _fixture_with_statement(tmp_path, stmt="theorem demo_lemma_a : 1 = 1")
    report = verify_campaign(campaign_root)
    assert not report.ok
    assert any("no `import` line" in e for e in report.errors), report.errors


def test_verify_fails_root_import_without_file(tmp_path):
    campaign_root, _ = _fixture_with_statement(tmp_path)
    ensure_root_import(campaign_root, "Statements.Ghost")
    report = verify_campaign(campaign_root)
    assert not report.ok
    assert any("(no file) Statements.Ghost" in e for e in report.errors), report.errors


def test_verify_fails_stray_statement_file(tmp_path):
    campaign_root, _ = _fixture_with_statement(tmp_path)
    (campaign_root / "lean" / "Statements" / "Stray.lean").write_text("import Mathlib\n")
    report = verify_campaign(campaign_root)
    assert not report.ok
    assert any("Statements.Stray" in e for e in report.errors), report.errors


def test_verify_fixture_without_lean_dir_is_vacuous(tmp_path):
    mroot, campaign_root = make_demo_root(tmp_path)
    assert not (campaign_root / "lean").exists()
    assert verify_campaign(campaign_root).ok


# ---------------------------------------------------------------------------
# regenerate_statement (the tool the fifteen were repaired with)
# ---------------------------------------------------------------------------

def test_regenerate_statement_is_idempotent_and_wires_root(tmp_path):
    root = tmp_path / "demo"
    root.mkdir()
    node = _node("Demo.lemma_a")
    write_statement(root, node, "import Mathlib\nopen Nat\ntheorem a : 1 = 1", _manifest())
    before = statement_path(root, node).read_text()
    _unwire(root, "Statements.Demo_lemma_a")
    _, old, new = regenerate_statement(root, node, _manifest())
    assert old == new
    assert statement_path(root, node).read_text() == before
    assert "Statements.Demo_lemma_a" in root_imports(root)


def test_regenerate_statement_with_prepended_imports_changes_hash(tmp_path):
    root = tmp_path / "demo"
    root.mkdir()
    _defs(root)
    node = _node("Demo.lemma_a")
    write_statement(root, node, "theorem a : 1 = 1", _manifest())
    assert import_header_error(root, node)
    _, old, new = regenerate_statement(root, node, _manifest(),
                                       prepend_imports=("Mathlib", "Statements.DemoDefs"))
    assert old != new
    assert import_header_error(root, node) == ""
    assert regen_diff(root, node, _manifest()) == ""
    text = statement_path(root, node).read_text().split("\n")
    assert text[1:3] == ["import Mathlib", "import Statements.DemoDefs"]
# ---------------------------------------------------------------------------
# the live campaigns: every registered statement is in its root's import list
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("campaign", LIVE_CAMPAIGNS)
def test_live_campaign_root_imports_every_statement(campaign):
    root = MISSIONS / campaign
    camp = load_campaign(root)
    assert missing_root_imports(root, camp.nodes.values()) == []
    bad = {sl: import_header_error(root, n) for sl, n in camp.nodes.items()}
    assert not {k: v for k, v in bad.items() if v}
