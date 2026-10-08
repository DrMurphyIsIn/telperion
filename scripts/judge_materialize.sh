#!/bin/bash
# Install a missions-judge bundle of a MATERIALIZED island (judge.MATERIALIZED_ROOT_ISLANDS, today
# oai_qrh_bridge) into that island's materialized workspace.
#
# Why this exists: the island's workspace is a foreign root package (openai/math's lean/, whose
# lakefile must stay the workspace root), so the bundle cannot path-require the island the way
# every other bundle does. Instead the bridge modules are built INSIDE the workspace: this script
# copies the bundle's MissionChallenges modules and Comparator configs into the workspace root
# and appends the bundle's `lakefile-stanza.lean` (one `lean_lib MissionChallenges`) to the
# workspace lakefile, after the island recipe's own stanza.
#
# Usage: judge_materialize.sh <bundle dir> <materialized workspace>
#   e.g. telperion/scripts/judge_materialize.sh telperion/missions/judge/oai_qrh_bridge \
#          telperion/examples/oai_qrh_bridge/work/oai
# The workspace must already be materialized by the island recipe (materialize.sh). Re-running
# is idempotent: the stanza is appended once, files are refreshed. A Comparator config that would
# overwrite a DIFFERENT file of the same name already in the workspace is refused.
# conjecture1_proved = False.
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: $0 <bundle dir> <materialized workspace>" >&2; exit 2; }
B="$(cd "$1" && pwd)"; W="$(cd "$2" && pwd)"
for f in lean-toolchain lakefile-stanza.lean MissionChallenges.lean MANIFEST.json; do
  [ -f "$B/$f" ] || { echo "error: $B/$f missing (not a materialized-island bundle?)" >&2; exit 1; }
done
LAKEFILE="$W/lakefile.lean"
[ -f "$LAKEFILE" ] || { echo "error: $LAKEFILE missing (materialize the island first)" >&2; exit 1; }
# The bundle's toolchain is the island pin's; the workspace must be at the same pin.
if [ "$(cat "$B/lean-toolchain")" != "$(cat "$W/lean-toolchain")" ]; then
  echo "error: toolchain mismatch: bundle $(cat "$B/lean-toolchain"), workspace $(cat "$W/lean-toolchain")" >&2
  exit 1
fi
# The island's own stanza (ArdaQRHBridge etc.) must already be there: the bridges import it.
grep -q '^lean_lib AxiomGuard' "$LAKEFILE" || {
  echo "error: $LAKEFILE has no island AxiomGuard lean_lib; run the island's materialize.sh first" >&2; exit 1; }
for cfg in "$B"/*.comparator.json; do
  [ -e "$cfg" ] || continue
  dst="$W/$(basename "$cfg")"
  if [ -e "$dst" ] && ! cmp -s "$cfg" "$dst"; then
    echo "error: $dst exists and differs from the bundle's; refusing to overwrite" >&2; exit 1
  fi
done
rm -rf "$W/MissionChallenges"
mkdir -p "$W/MissionChallenges"
cp "$B/MissionChallenges.lean" "$W/MissionChallenges.lean"
if [ -d "$B/MissionChallenges" ]; then
  cp "$B"/MissionChallenges/*.lean "$W/MissionChallenges/"
fi
n=0
for cfg in "$B"/*.comparator.json; do
  [ -e "$cfg" ] || continue
  cp "$cfg" "$W/"; n=$((n+1))
done
if grep -q '^lean_lib MissionChallenges' "$LAKEFILE"; then
  echo "lakefile already carries lean_lib MissionChallenges; not appended again"
else
  { echo; cat "$B/lakefile-stanza.lean"; } >> "$LAKEFILE"
fi
echo "installed $(basename "$B") judge bundle into $W ($n Comparator config(s))"
echo "next, from $W:  lake build MissionChallenges.<Slug> ...; lake env comparator <Slug>.comparator.json"
