"""Cross-campaign dependency edges in the missions registry.

A depends_on entry is either a bare slug (same campaign) or a qualified
reference "<campaign-dir>:<NodeSlug>".  The qualified form exists because real
dependencies cross campaigns; before it existed, five nodes carried a
same-campaign proxy edge while the node title named the real source.

The tests that matter here are the NEGATIVE ones.  A cross-campaign edge is a
new way for an unverified premise to reach a `proved` node, so most of this
file is about the anti-cascade rule: an edge that does not genuinely resolve to
a proved, closure-clean node must never count as satisfied.

conjecture1_proved = False.
"""
from __future__ import annotations

import pytest

from telperion.missions.registry import (
    Campaign, dep_ref, is_external, load_campaign, load_universe, parse_dep,
)
from telperion.missions.schema import SchemaError
from telperion.missions.verify import _compute_closures


# --------------------------------------------------------------------------- #
# fixture: a two-campaign missions root built from scratch
# --------------------------------------------------------------------------- #

MISSION = '''description = "test campaign"
environment_mathlib_rev = "de5ce8a9"
environment_toolchain = "leanprover/lean4:v4.34.0-rc1"
goal_node = "{goal}"
name = "{name}"
title = "{title}"
'''


def _node(tmp, camp, slug, *, status="open", deps=(), proof=None):
    body = [
        f'name = "{slug.replace("_", ".", 1)}"',
        f'title = "node {slug}"',
        'kind = "lemma"',
        f'status = "{status}"',
        f'statement_module = "Statements.{slug}"',
        "depends_on = [" + ", ".join(f'"{d}"' for d in deps) + "]",
        'created = "2026-09-19"',
        'updated = "2026-09-19"',
    ]
    if proof is not None:
        artifact, via, clean = proof
        body += [
            "",
            "[proof]",
            f'artifact = "{artifact}"',
            'artifact_kind = "lean_module"',
            f'via = "{via}"',
            f"closure_clean = {str(clean).lower()}",
        ]
    d = tmp / camp / "nodes"
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{slug}.toml").write_text("\n".join(body) + "\n")


@pytest.fixture
def root(tmp_path):
    """Two campaigns: 'up' (the source of truth) and 'down' (depends on it)."""
    for camp, name, goal in (("up", "UP.goal", "UP_goal"), ("down", "DOWN.goal", "DOWN_goal")):
        (tmp_path / camp).mkdir(parents=True, exist_ok=True)
        (tmp_path / camp / "mission.toml").write_text(
            MISSION.format(name=name, title=camp, goal=goal))
    _node(tmp_path, "up", "UP_goal")
    _node(tmp_path, "down", "DOWN_goal")
    return tmp_path


# --------------------------------------------------------------------------- #
# reference syntax
# --------------------------------------------------------------------------- #

def test_parse_dep_bare_slug_is_home_campaign():
    assert parse_dep("RH_corridor_bound", "rh") == ("rh", "RH_corridor_bound")
    assert not is_external("RH_corridor_bound", "rh")


def test_parse_dep_qualified_reference():
    assert parse_dep("rh:RH_rvm_unconditional", "mirrormere") == ("rh", "RH_rvm_unconditional")
    assert is_external("rh:RH_rvm_unconditional", "mirrormere")
    # a qualified ref naming the home campaign is internal, not external
    assert not is_external("rh:RH_x", "rh")
    assert dep_ref("rh", "RH_x") == "rh:RH_x"


@pytest.mark.parametrize("bad", ["", ":", "rh:", ":slug", "a:b:c"])
def test_parse_dep_rejects_malformed(bad):
    with pytest.raises(SchemaError):
        parse_dep(bad, "rh")


# --------------------------------------------------------------------------- #
# loading and validation
# --------------------------------------------------------------------------- #

def test_external_edge_loads_when_target_exists(root):
    _node(root, "up", "UP_thm", status="open")
    _node(root, "down", "DOWN_uses", deps=("up:UP_thm",))
    camp = load_campaign(root / "down")
    assert camp.nodes["DOWN_uses"].depends_on == ("up:UP_thm",)
    assert camp.cname == "down"


def test_external_edge_to_missing_node_is_rejected(root):
    _node(root, "down", "DOWN_uses", deps=("up:UP_absent",))
    with pytest.raises(SchemaError, match="external"):
        load_campaign(root / "down")


def test_external_edge_to_missing_campaign_is_rejected(root):
    _node(root, "down", "DOWN_uses", deps=("nosuch:UP_thm",))
    with pytest.raises(SchemaError):
        load_campaign(root / "down")


def test_internal_edge_still_validated(root):
    _node(root, "down", "DOWN_uses", deps=("DOWN_absent",))
    with pytest.raises(SchemaError, match="not in the campaign"):
        load_campaign(root / "down")


def test_universe_loads_every_campaign(root):
    _node(root, "up", "UP_thm")
    _node(root, "down", "DOWN_uses", deps=("up:UP_thm",))
    uni = load_universe(root)
    assert set(uni.campaigns) == {"up", "down"}
    assert uni.resolve("down", "up:UP_thm").status == "open"
    assert uni.resolve("down", "up:UP_absent") is None


def test_universe_rejects_cross_campaign_cycle(root):
    # up:UP_a -> down:DOWN_b -> up:UP_a  is invisible to any per-campaign check
    _node(root, "up", "UP_a", deps=("down:DOWN_b",))
    _node(root, "down", "DOWN_b", deps=("up:UP_a",))
    load_campaign(root / "up")     # each campaign alone is acyclic
    load_campaign(root / "down")
    with pytest.raises(SchemaError, match="cycle"):
        load_universe(root)


# --------------------------------------------------------------------------- #
# THE ANTI-CASCADE RULE
# --------------------------------------------------------------------------- #

def _down_closure(root, universe=None):
    camp = load_campaign(root / "down")
    return _compute_closures(camp, universe)


def test_reduction_over_external_dep_is_clean_only_when_target_is_proved(root):
    _node(root, "up", "UP_thm", status="proved",
          proof=("../../examples/x/Up.lean", "direct", True))
    _node(root, "down", "DOWN_uses", status="proved", deps=("up:UP_thm",),
          proof=("../../examples/x/Down.lean", "reduction", True))
    uni = load_universe(root)
    assert _down_closure(root, uni)["DOWN_uses"] is True


def test_external_dep_that_is_not_proved_makes_closure_dirty(root):
    _node(root, "up", "UP_thm", status="open")          # NOT proved
    _node(root, "down", "DOWN_uses", status="proved", deps=("up:UP_thm",),
          proof=("../../examples/x/Down.lean", "reduction", True))
    uni = load_universe(root)
    # stored flag says True; the fixpoint must overrule it
    assert _down_closure(root, uni)["DOWN_uses"] is False


def test_external_dep_proved_but_dirty_does_not_launder(root):
    """A proved-but-not-closure-clean target must not make the consumer clean."""
    _node(root, "up", "UP_thm", status="proved",
          proof=("../../examples/x/Up.lean", "direct", False))   # dirty on purpose
    _node(root, "down", "DOWN_uses", status="proved", deps=("up:UP_thm",),
          proof=("../../examples/x/Down.lean", "reduction", True))
    uni = load_universe(root)
    assert _down_closure(root, uni)["DOWN_uses"] is False


def test_external_dep_without_a_universe_is_never_clean(root):
    """Single-campaign closure cannot see across campaigns, so it must say False.

    This is the conservative direction: a caller who forgets to pass the
    universe gets a dirty closure, never a clean one.
    """
    _node(root, "up", "UP_thm", status="proved",
          proof=("../../examples/x/Up.lean", "direct", True))
    _node(root, "down", "DOWN_uses", status="proved", deps=("up:UP_thm",),
          proof=("../../examples/x/Down.lean", "reduction", True))
    assert _down_closure(root, universe=None)["DOWN_uses"] is False


def test_transitive_dirt_propagates_across_campaigns(root):
    """up:UP_mid is a reduction over an unproved node, so down must be dirty too."""
    _node(root, "up", "UP_base", status="open")
    _node(root, "up", "UP_mid", status="proved", deps=("UP_base",),
          proof=("../../examples/x/Mid.lean", "reduction", True))
    _node(root, "down", "DOWN_uses", status="proved", deps=("up:UP_mid",),
          proof=("../../examples/x/Down.lean", "reduction", True))
    uni = load_universe(root)
    assert _compute_closures(load_campaign(root / "up"), uni)["UP_mid"] is False
    assert _down_closure(root, uni)["DOWN_uses"] is False


def test_direct_proof_is_unaffected_by_an_external_dep(root):
    """A direct proof stands on its artifact; deps are documentary for it."""
    _node(root, "up", "UP_thm", status="open")
    _node(root, "down", "DOWN_direct", status="proved", deps=("up:UP_thm",),
          proof=("../../examples/x/Down.lean", "direct", True))
    uni = load_universe(root)
    assert _down_closure(root, uni)["DOWN_direct"] is True
