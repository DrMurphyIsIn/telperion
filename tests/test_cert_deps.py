"""Per-cert dependency extraction — the AXLE ``extract_decls`` lesson.

Pure text / graph tests (no Lean build): reference detection, transitive
dep/dependent closures, dead-atom detection, impact (re-verify blast radius), and
standalone single-cert snippet assembly (topo-ordered).

conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.cert_deps import extract_deps, DepGraph, minimal_snippet  # noqa: E402
from telperion.bundle import parse_theorems  # noqa: E402

# --- A small hand-built 4-theorem graph --------------------------------------
#   atom          (no deps)
#   mid  -> atom
#   goalA -> mid  (=> atom transitively)
#   goalB -> atom (independent of mid/goalA)
#   dead  -> atom (present but never a root or reachable-from-a-root goal)

_ATOM = (
    "theorem atom : Real.log (5/4 : ℝ) - FSTAR ≤ (1/20 : ℝ) := by sorry\n"
)
_MID = (
    "theorem mid : (2:ℝ) = 2 := by\n"
    "  have := atom\n"
    "  norm_num\n"
)
_GOALA = (
    "theorem goalA : (3:ℝ) = 3 := by\n"
    "  have := mid\n"
    "  norm_num\n"
)
_GOALB = (
    "theorem goalB : (4:ℝ) = 4 := by\n"
    "  have := atom\n"
    "  norm_num\n"
)
_DEAD = (
    "theorem dead : (5:ℝ) = 5 := by\n"
    "  have := atom\n"
    "  norm_num\n"
)

_ALL = _ATOM + _MID + _GOALA + _GOALB + _DEAD


def _graph():
    return DepGraph(parse_theorems(_ALL))


def test_extract_deps_finds_referenced_names():
    known = {"atom", "mid", "goalA", "goalB", "dead"}
    mid_block = parse_theorems(_MID)[0]["block"]
    assert extract_deps(mid_block, known) == {"atom"}

    goalA_block = parse_theorems(_GOALA)[0]["block"]
    assert extract_deps(goalA_block, known) == {"mid"}


def test_extract_deps_excludes_self_and_unknown():
    # atom references nothing in the corpus and never itself.
    atom_block = parse_theorems(_ATOM)[0]["block"]
    assert extract_deps(atom_block, {"atom", "mid"}) == set()
    # Mathlib names (Real.log, FSTAR) are not in known_names -> ignored.
    assert "Real.log" not in extract_deps(atom_block, {"atom", "mid"})


def test_direct_deps_and_transitive():
    g = _graph()
    assert g.deps("mid") == {"atom"}
    assert g.deps("goalA") == {"mid"}
    # goalA transitively pulls in mid and atom.
    assert g.transitive_deps("goalA") == {"mid", "atom"}
    assert g.transitive_deps("atom") == set()


def test_dependents_reverse_edges():
    g = _graph()
    # atom is referenced directly by mid, goalB, dead.
    assert g.dependents("atom") == {"mid", "goalB", "dead"}
    assert g.dependents("mid") == {"goalA"}


def test_impact_transitive_dependents():
    g = _graph()
    # Changing atom forces re-verify of everything that transitively uses it.
    assert g.impact("atom") == {"mid", "goalA", "goalB", "dead"}
    # Changing mid only touches goalA.
    assert g.impact("mid") == {"goalA"}


def test_dead_atoms_from_roots():
    g = _graph()
    # Assemble only goalA and goalB. Reachable: goalA, mid, atom, goalB.
    dead = g.dead_atoms({"goalA", "goalB"})
    assert dead == {"dead"}
    # With dead itself as a root, nothing is dead.
    assert g.dead_atoms({"goalA", "goalB", "dead"}) == set()
    # Only goalB as root -> mid, goalA, dead are all dead.
    assert g.dead_atoms({"goalB"}) == {"mid", "goalA", "dead"}


def test_minimal_snippet_includes_atom_and_deps_topo_ordered():
    snippet = minimal_snippet("goalA", parse_theorems(_ALL))
    # Must contain goalA + its transitive deps (mid, atom), NOT goalB/dead.
    assert "theorem goalA" in snippet
    assert "theorem mid" in snippet
    assert "theorem atom" in snippet
    assert "theorem goalB" not in snippet
    assert "theorem dead" not in snippet
    # Topo order: atom defined before mid before goalA.
    assert snippet.index("theorem atom") < snippet.index("theorem mid")
    assert snippet.index("theorem mid") < snippet.index("theorem goalA")


def test_minimal_snippet_leaf_atom_is_standalone():
    snippet = minimal_snippet("atom", parse_theorems(_ALL))
    assert "theorem atom" in snippet
    assert "theorem mid" not in snippet


def test_depgraph_accepts_pairs_and_parse_output():
    pairs = [("atom", _ATOM), ("mid", _MID)]
    g = DepGraph(pairs)
    assert g.deps("mid") == {"atom"}
    assert set(g.names) == {"atom", "mid"}
