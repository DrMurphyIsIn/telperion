"""A stand-in for the pinned `lean` in pure tests, used as the replay's wrapper:

    python fake_lean_cli.py LOG MODE env LEAN_PATH=... <lean> [--memory=N] <script>

It logs `LEAN_PATH|binary|cwd|cwd mode|memory flag|list or replay` to LOG and prints lean_env.fake_replay_output for
MODE: `ok`, `needs` (REPLAY NEEDS Foo.Bar until the script imports it), `always-needs` or `sleep` (60 s)."""
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_env import fake_replay_output  # noqa: E402

log, mode, *cmd = sys.argv[1:]
script = Path(cmd[-1]).read_text(encoding="utf-8")
mem = next((a for a in cmd if a.startswith("--memory=")), "")
kind = "list" if "def listOnly : Bool := true" in script else "replay"
with open(log, "a", encoding="utf-8") as fh:
    fh.write("|".join([cmd[1], cmd[2], os.getcwd(), oct(os.stat(".").st_mode & 0o777)[2:], mem, kind]) + "\n")
if mode == "sleep":
    time.sleep(60)
needs = {"needs": "Foo.Bar", "always-needs": "Foo.Bar"}.get(mode)
sys.stdout.write(fake_replay_output(script, "<TAG>-CB x\n", needs, always=mode == "always-needs"))
