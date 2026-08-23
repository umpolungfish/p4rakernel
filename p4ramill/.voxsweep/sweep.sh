#!/usr/bin/env bash
# vox over every built olean; one row per module.
cd "$(dirname "$0")/../.lake/build/lib/lean/Imscribing" || exit 1
printf "module\tT\tB\tN\tF\tfns\n"
find . -name "*.olean" | sort | while read -r f; do
  out=$(timeout 300 vox "$f" 2>/dev/null) || continue
  v=$(printf '%s' "$out" | grep -m1 "verdicts")
  n=$(printf '%s' "$out" | grep -m1 -oE "^  [0-9]+ function" | grep -oE "[0-9]+")
  [ -z "$v" ] && continue
  T=$(printf '%s' "$v" | grep -oE "T [0-9]+" | grep -oE "[0-9]+")
  B=$(printf '%s' "$v" | grep -oE "B [0-9]+" | grep -oE "[0-9]+")
  N=$(printf '%s' "$v" | grep -oE "N [0-9]+" | grep -oE "[0-9]+")
  F=$(printf '%s' "$v" | grep -oE "F [0-9]+" | grep -oE "[0-9]+")
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "${f#./}" "$T" "$B" "$N" "$F" "${n:-0}"
done
