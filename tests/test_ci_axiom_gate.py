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
"""
import re
import subprocess
from pathlib import Path

import pytest

_WF_DIR = Path(__file__).resolve().parents[2] / ".github" / "workflows"
_MARK = 'grep -oE "depends on axioms:'
# A floor, so a refactor that silently deletes gates fails here (17 gates on 2026-09-25).
_MIN_GATES = 15

_CONFORMING = "'Thm{}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
_SUBSET = ("'Decided{0}' depends on axioms: [propext]\n"
           "'Quotient{0}' depends on axioms: [propext, Quot.sound]\n"
           "'Pure{0}' does not depend on any axioms\n")
_FOREIGN = "'Cheat' depends on axioms: [propext, Classical.choice, Quot.sound, myAxiom]\n"
_SORRY = "'Cheat' depends on axioms: [propext, sorryAx]\n"
# Lean wraps a long list over several lines; a line-based gate sees a truncated list.
_WRAPPED = "'Wrapped' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]\n"


def _blocks(text: str):
    """Each gate, reassembled across backslash continuations."""
    lines = text.split("\n")
    out = []
    for i, line in enumerate(lines):
        if _MARK not in line:
            continue
        j, blk = i, []
        while True:
            blk.append(lines[j])
            if not lines[j].rstrip().endswith("\\"):
                break
            j += 1
        block = "\n".join(blk)
        if "wc -l" in block:
            continue  # an anchor COUNTER, not a gate
        out.append((i + 1, block))
    return out


def _gates():
    res = []
    for p in sorted(_WF_DIR.glob("*.yml")):
        t = p.read_text()
        if _MARK not in t:
            continue
        for lineno, block in _blocks(t):
            res.append((f"{p.name}:{lineno}", block, t))
    return res


def _pipeline(block: str, text: str, fixture: Path) -> str:
    """The gate's own pipeline, reading `fixture` as the guard output."""
    cmd = block.strip()
    cmd = re.sub(r"^if\s+", "", cmd)
    cmd = re.sub(r";\s*then$", "", cmd)
    cmd = re.sub(r'^\w+="\$\(', "", cmd)                  # bad="$( ... )"
    cmd = re.sub(r'(\|\|\s*true\s*)?\)"$', "", cmd.rstrip())
    joins_itself = 'tr "\\n" " "' in cmd
    if re.search(r"<<<\s*\"\$\w+\"", cmd):
        if joins_itself:
            # The gate joins the wrapped lines itself; feed it the fixture verbatim.
            cmd = re.sub(r"<<<\s*\"\$\w+\"", f'<<< "$(cat {fixture})"', cmd)
        else:
            # Input is a variable an earlier statement joined; require that, then emulate it.
            var = re.search(r"<<<\s*\"\$(\w+)\"", cmd).group(1)
            assert re.search(rf"{var}=\"\$\(tr\s+'?\\n'?", text), (
                f"gate reads ${var} but nothing joins wrapped lines into it")
            cmd = re.sub(r"<<<\s*\"\$\w+\"", f'<<< "$(tr "\\\\n" " " < {fixture})"', cmd)
    elif re.search(r"<\s*\S+", cmd):
        cmd = re.sub(r"<\s*\S+", f"< {fixture}", cmd, count=1)
    elif re.search(r"echo\s+\"\$\w+\"", cmd):
        cmd = re.sub(r"echo\s+\"\$\w+\"", f"cat {fixture}", cmd, count=1)
    else:
        raise AssertionError(f"gate reads its input in an unknown way:\n{block}")
    assert str(fixture) in cmd, f"fixture not substituted:\n{cmd}"
    return cmd


def _fires(block: str, text: str, fixture: Path) -> bool:
    """True when the gate reports the fixture unclean.

    Every shape ends in a `grep -v...` over the axiom names, so "printed something" is
    exactly the condition the job's `if` (or its `[ -n "$bad" ]`) acts on.  A gate that
    short-circuits with `grep -q` prints nothing and so reads as NOT firing, which is
    precisely the silent-pass bug.
    """
    cmd = _pipeline(block, text, fixture)
    r = subprocess.run(
        ["/bin/bash", "--noprofile", "--norc", "-o", "pipefail", "-c", cmd],
        capture_output=True, text=True)
    return bool(r.stdout.strip())


def _fixture(tmp_path: Path, name: str, body: str) -> Path:
    p = tmp_path / name
    p.write_text(body)
    return p


def test_workflows_carry_the_expected_number_of_axiom_gates():
    assert len(_gates()) >= _MIN_GATES, f"only {len(_gates())} axiom gates found"


def test_no_gate_consumes_a_pipe_with_grep_q():
    """`grep -q` fed BY A PIPE + `pipefail` can pass silently; reading a file is fine."""
    bad = [(name, block) for name, block, _ in _gates()
           if re.search(r"[|]\s*grep\s+-[A-Za-z]*q", block)]
    assert not bad, f"axiom gate pipes into grep -q (silent-pass hazard): {bad}"


@pytest.mark.parametrize("where", ["early", "late"])
def test_every_gate_catches_a_foreign_axiom(tmp_path, where):
    bulk = "".join(_CONFORMING.format(i) for i in range(3000))
    body = (_FOREIGN + bulk) if where == "early" else (bulk + _FOREIGN)
    fx = _fixture(tmp_path, f"foreign_{where}.out", body)
    for name, block, text in _gates():
        assert _fires(block, text, fx), f"{name}: MISSED a non-standard axiom ({where}):\n{block}"


def test_every_gate_catches_sorry_ax(tmp_path):
    fx = _fixture(tmp_path, "sorry.out", _SORRY + "".join(_CONFORMING.format(i) for i in range(20)))
    for name, block, text in _gates():
        assert _fires(block, text, fx), f"{name}: MISSED sorryAx in an axiom list:\n{block}"


def test_every_gate_accepts_fewer_axioms(tmp_path):
    """Depending on a subset of the three is strictly stronger, never a failure."""
    body = ("".join(_CONFORMING.format(i) for i in range(50))
            + "".join(_SUBSET.format(i) for i in range(50)))
    fx = _fixture(tmp_path, "clean_subset.out", body)
    for name, block, text in _gates():
        assert not _fires(block, text, fx), f"{name}: rejected a clean subset:\n{block}"


def test_every_gate_accepts_a_wrapped_standard_list(tmp_path):
    """Lean wraps long lists; a line-based gate would see a truncated list and cry wolf."""
    fx = _fixture(tmp_path, "wrapped.out", _WRAPPED * 5)
    for name, block, text in _gates():
        assert not _fires(block, text, fx), f"{name}: tripped on Lean's line wrapping:\n{block}"


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


_VERIFY_MARKS = ("sorryAx", "depends on axioms", "does not depend on any axioms",
                 "lean-kernel-only")


def test_no_verification_check_is_a_pipe_fed_grep_q():
    """A pipe-fed `grep -q` stops meaning "found" once the producer outruns the pipe buffer.

    `grep -q` exits at its first match; the producer then takes SIGPIPE, and under
    `pipefail` the pipeline status goes non-zero, so `if <pipeline>` does not fire.  Every
    such check must read a file or a here-string instead (`grep -q PAT <<< "$out"`).
    """
    bad = []
    for p in sorted(_WF_DIR.glob("*.yml")):
        for i, ln in enumerate(p.read_text().split("\n"), 1):
            if not any(m in ln for m in _VERIFY_MARKS):
                continue
            if re.search(r"[|]\s*(grep|cut|tr|sed)[^|]*\bgrep\s+-[A-Za-z]*q", ln) or \
               re.search(r"[|]\s*grep\s+-[A-Za-z]*q", ln):
                bad.append(f"{p.name}:{i}: {ln.strip()}")
    assert not bad, "verification check pipes into grep -q (silent-pass hazard):\n" + "\n".join(bad)


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
