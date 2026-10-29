"""Helpers shared by test_ci_axiom_gate.py (engine) and test_ci_axiom_gate_lab.py (Arda lab), moved verbatim (Task 2c).

pytest puts tests/ on sys.path when it collects a test file there (prepend import mode, no __init__.py),
so `from _helpers.ci_axiom_gate import ...` resolves, as `from missions_fixtures import ...` does.
"""
import re
import subprocess
from pathlib import Path


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
