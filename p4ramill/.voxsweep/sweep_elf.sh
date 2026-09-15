#!/usr/bin/env bash
# vox over REAL compiled objects: Lean's C backend output, built to ELF.
# An .olean is a serialized object graph, not machine code; voxing one
# disassembles data. This sweep compiles each module's .c and voxes that.
cd "$(dirname "$0")/.." || exit 1
INC=/home/mrnob0dy666/.elan/toolchains/leanprover--lean4---v4.33.1/include
OUT=.voxsweep/elf; mkdir -p "$OUT"
printf "module\tT\tB\tN\tF\tfns\n"
find .lake/build/ir/Imscribing -name "*.c" | sort | while read -r c; do
  m=${c#.lake/build/ir/}; m=${m%.c}
  so="$OUT/$(echo "$m" | tr '/' '_').so"
  gcc -shared -fPIC -O1 -I"$INC" "$c" -o "$so" 2>/dev/null || continue
  out=$(timeout 300 vox "$so" 2>/dev/null) || continue
  v=$(printf '%s' "$out" | grep -m1 "verdicts"); [ -z "$v" ] && continue
  n=$(printf '%s' "$out" | grep -m1 -oE "^  [0-9]+ function" | grep -oE "[0-9]+")
  T=$(printf '%s' "$v"|grep -oE "T [0-9]+"|grep -oE "[0-9]+")
  B=$(printf '%s' "$v"|grep -oE "B [0-9]+"|grep -oE "[0-9]+")
  N=$(printf '%s' "$v"|grep -oE "N [0-9]+"|grep -oE "[0-9]+")
  F=$(printf '%s' "$v"|grep -oE "F [0-9]+"|grep -oE "[0-9]+")
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$m" "$T" "$B" "$N" "$F" "${n:-0}"
  rm -f "$so"
done
