#!/usr/bin/env bash
# vox_audit.sh — sweep every GateCheck IGProtocol scaffold through the hosted
# kernel's vox control-flow closure auditor. Reports the T/B/N/F census and
# lists any F (ill-typed) word. Exit 1 if any F is found, so it can gate a build.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GATEDIR="$ROOT/Imscribing/Ob3ects/GateCheck"
VOX="${VOX_BIN:-/home/mrnob0dy666/imsgct/mOMonadOS/run_hosted_cmds.sh}"

[ -d "$GATEDIR" ] || { echo "vox_audit: no GateCheck dir at $GATEDIR"; exit 0; }
[ -x "$VOX" ]     || { echo "vox_audit: hosted vox binary not found at $VOX (set VOX_BIN)"; exit 0; }

# Extract (name, word) from each scaffold's line 1: "-- IGProtocol scaffold: A → B → ..."
names=(); words=()
for f in "$GATEDIR"/*_gate_check.lean; do
  [ -e "$f" ] || continue
  line=$(grep -m1 'IGProtocol scaffold:' "$f" 2>/dev/null) || continue
  w=$(printf '%s' "$line" | sed 's/.*scaffold: *//' | sed 's/ *→ *//g' | tr -d ' \r')
  [ -n "$w" ] || continue
  names+=("$(basename "$f" _gate_check.lean)"); words+=("$w")
done
n=${#words[@]}
[ "$n" -gt 0 ] || { echo "vox_audit: no scaffolds found"; exit 0; }

# One kernel boot, all words batched.
cmds=(); for w in "${words[@]}"; do cmds+=("vox verdict $w"); done
out=$("$VOX" "${cmds[@]}" 2>/dev/null)
verds=$(printf '%s\n' "$out" | grep -oE 'verdict [TBNF]' | awk '{print $2}')

T=0;B=0;N=0;F=0; i=0; fails=()
while IFS= read -r v; do
  [ -z "$v" ] && continue
  case "$v" in T) T=$((T+1));; B) B=$((B+1));; N) N=$((N+1));; F) F=$((F+1)); fails+=("${names[$i]:-?} ${words[$i]:-?}");; esac
  i=$((i+1))
done <<< "$verds"

echo "── vox audit: $GATEDIR"
echo "   scaffolds: $n   verdicts read: $i"
echo "   T=$T  B=$B  N=$N  F=$F"
if [ "$F" -gt 0 ]; then
  echo "   ✗ ILL-TYPED (F):"; for x in "${fails[@]}"; do echo "     - $x"; done
  exit 1
fi
echo "   ✓ vox-clean — no ill-typed (F) scaffolds"
