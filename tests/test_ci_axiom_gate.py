"""Every axiom gate in .github/workflows/*.yml really rejects a non-standard axiom.

Each island job ends with a shell gate over `#print axioms` output: no `sorryAx`, and no
axiom outside Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`).
Two ways such a gate can lie, both found live in this repository on 2026-09-25:

1. `... | grep -vq "<the three>"` inside `if`.  `grep -q` exits at its FIRST match, the
   upstream `grep -oE` then dies of SIGPIPE, and under `set -o pipefail` (GitHub's default
   shell) the pipeline status goes non-zero -- so the `then` branch is SKIPPED and the gate
   passes silently.  Whether it fires depended on where the offending line sat: an offending
   line early in a large guard file passed.
2. Requiring the printed list to EQUAL the three.  Depending on FEWER axioms is strictly
   stronger, and a pure `decide` proof legitimately prints just `[propext]`, so equality
   turns a better proof into a red build (this is what broke PR #634 while PR #636, with the
   same axiom sets in a different order, went green).

A correct gate therefore: joins lines first (Lean wraps long axiom lists), tests the axiom
NAMES for membership in the three, and never pipes into `grep -q`.  The tests below extract
the gate pipelines the workflows really contain and run them against fixtures, so what is
pinned is behaviour, not wording.  `telperion/scripts/guard_anchors.py` already uses the
subset rule; `telperion-zeta-reflection.yml` is the reference shell implementation.

The tests that read the workflows live in test_ci_axiom_gate_lab.py, which stays with them in Arda; this file
keeps the harness self-checks: the extractor must flag the two lying gate shapes above.
"""
import subprocess

from _helpers.ci_axiom_gate import _fires, _fixture  # noqa: E402

_CONFORMING = "'Thm{}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
_SUBSET = ("'Decided{0}' depends on axioms: [propext]\n"
           "'Quotient{0}' depends on axioms: [propext, Quot.sound]\n"
           "'Pure{0}' does not depend on any axioms\n")
_FOREIGN = "'Cheat' depends on axioms: [propext, Classical.choice, Quot.sound, myAxiom]\n"


# The two broken shapes this file exists to keep out, kept verbatim as regression bait.
_LEGACY_Q = ('if tr "\\n" " " < axioms.out | grep -oE "depends on axioms: \\[[^]]*\\]" | tr -s " " \\\n'
             '     | grep -vq "^depends on axioms: \\[propext, Classical.choice, Quot.sound\\]$"; then')
_LEGACY_EQ = ('if tr "\\n" " " < axioms.out | grep -oE "depends on axioms: \\[[^]]*\\]" | tr -s " " \\\n'
              '     | grep -v "^depends on axioms: \\[propext, Classical.choice, Quot.sound\\]$"; then')


def test_harness_would_catch_the_silent_pass_shape(tmp_path):
    """The `grep -vq` shape must read as NOT firing on an early foreign axiom."""
    fx = _fixture(tmp_path, "legacy_early.out",
                  _FOREIGN + "".join(_CONFORMING.format(i) for i in range(3000)))
    assert not _fires(_LEGACY_Q, "", fx), "harness has no teeth: the -q shape appeared to fire"


def test_harness_would_catch_the_equality_shape(tmp_path):
    """The exact-match shape must read as firing on a clean subset (a false alarm)."""
    fx = _fixture(tmp_path, "legacy_subset.out", "".join(_SUBSET.format(i) for i in range(5)))
    assert _fires(_LEGACY_EQ, "", fx), "harness has no teeth: the equality shape looked subset-safe"


def test_harness_would_catch_the_echo_pipe_shape(tmp_path):
    """`echo "$out" | grep -q sorryAx` passes silently once $out exceeds the pipe buffer."""
    big = "'Cheat' depends on axioms: [propext, sorryAx]\n" + ("x" * 80 + "\n") * 16000
    fx = _fixture(tmp_path, "big.out", big)
    r = subprocess.run(
        ["/bin/bash", "--noprofile", "--norc", "-o", "pipefail", "-c",
         f'out="$(cat {fx})"; if echo "$out" | grep -q sorryAx; then echo FIRED; fi'],
        capture_output=True, text=True)
    assert "FIRED" not in r.stdout, (
        "the echo-pipe shape fired here, so this meta-test no longer demonstrates the hazard "
        "(pipe buffer or grep behaviour changed); keep the here-string rule anyway")
    r2 = subprocess.run(
        ["/bin/bash", "--noprofile", "--norc", "-o", "pipefail", "-c",
         f'out="$(cat {fx})"; if grep -q sorryAx <<< "$out"; then echo FIRED; fi'],
        capture_output=True, text=True)
    assert "FIRED" in r2.stdout, "the here-string form must catch sorryAx"
