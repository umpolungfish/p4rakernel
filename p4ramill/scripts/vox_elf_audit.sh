#!/usr/bin/env bash
# vox_elf_audit.sh — compile every Lean module's generated C to a real ELF
# object and sweep it through vox's binary control-flow auditor.
#
# This is a DIFFERENT question from scripts/vox_audit.sh. That script asks
# `vox verdict <word>` whether an ob3ect's twelve-mark WORD closes — F there
# is a legitimate open verdict, not a fault. This script asks vox to read
# compiled MACHINE CODE and report its control-flow census. The two vox
# questions share a binary but not a meaning; do not merge their reports.
#
# Why this exists: vox will disassemble ANY bytes handed to it, .olean
# included, and print verdicts on the garbage that produces (first line
# reads "raw", not "elf" — see ig-docs/IMSCRIBERS_GUIDE_TO_IMASM.md). A
# report against a .olean or bare .c is not a measurement of anything. The
# only valid target is real compiled code, which `lake build` does not
# normally produce for a lean_lib (only .olean + generated .c). This script
# closes that gap: compile every generated .c with leanc, then vox the
# result, so the audit runs against an artifact vox can actually read.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
IR_DIR="$ROOT/.lake/build/ir"
OUT_DIR="$ROOT/.lake/build/vox_native"
VOX="${VOX_BIN:-vox}"
LEANC="${LEANC_BIN:-leanc}"
JOBS="${VOX_AUDIT_JOBS:-4}"

command -v "$LEANC" >/dev/null 2>&1 || { echo "vox_elf_audit: leanc not found (set LEANC_BIN)"; exit 1; }
command -v "$VOX"   >/dev/null 2>&1 || { echo "vox_elf_audit: vox not found (set VOX_BIN)"; exit 1; }
[ -d "$IR_DIR" ] || { echo "vox_elf_audit: no generated C at $IR_DIR — run \`lake build\` first"; exit 1; }

mkdir -p "$OUT_DIR"

mapfile -t c_files < <(find "$IR_DIR" -name "*.c" | sort)
n=${#c_files[@]}
[ "$n" -gt 0 ] || { echo "vox_elf_audit: no .c files under $IR_DIR"; exit 0; }

REPORT="$OUT_DIR/report.tsv"
: > "$REPORT"

compile_and_vox() {
  local c="$1"
  local rel="${c#"$IR_DIR"/}"
  local mod="${rel%.c}"
  local o="$OUT_DIR/${rel%.c}.o"
  mkdir -p "$(dirname "$o")"

  if ! "$LEANC" -c "$c" -o "$o" >"$o.compile_log" 2>&1; then
    printf '%s\tCOMPILE_FAIL\t\t\t\t\n' "$mod"
    return
  fi
  rm -f "$o.compile_log"

  local out
  out=$("$VOX" "$o" 2>&1)
  local kind
  kind=$(printf '%s' "$out" | awk 'NR==1{print $2}')
  if [ "$kind" != "elf" ]; then
    printf '%s\tNOT_ELF(%s)\t\t\t\t\n' "$mod" "$kind"
    return
  fi
  local t b nn f
  t=$(printf '%s' "$out" | command grep -oE 'T [0-9]+' | awk '{print $2}')
  b=$(printf '%s' "$out" | command grep -oE 'B [0-9]+' | awk '{print $2}')
  nn=$(printf '%s' "$out" | command grep -oE 'N [0-9]+' | awk '{print $2}')
  f=$(printf '%s' "$out" | command grep -oE 'F [0-9]+' | awk '{print $2}')
  printf '%s\tOK\t%s\t%s\t%s\t%s\n' "$mod" "${t:-0}" "${b:-0}" "${nn:-0}" "${f:-0}"
}
export -f compile_and_vox
export IR_DIR OUT_DIR VOX LEANC

printf '%s\n' "${c_files[@]}" | xargs -P "$JOBS" -I{} bash -c 'compile_and_vox "$@"' _ {} >> "$REPORT"

echo "── vox ELF audit: $n Lean module(s) compiled and swept"
tot_t=0; tot_b=0; tot_n=0; tot_f=0; fail_compile=0; not_elf=0
flagged=()
while IFS=$'\t' read -r mod status t b nn f; do
  case "$status" in
    COMPILE_FAIL) fail_compile=$((fail_compile+1)); continue ;;
    NOT_ELF*) not_elf=$((not_elf+1)); continue ;;
  esac
  tot_t=$((tot_t+t)); tot_b=$((tot_b+b)); tot_n=$((tot_n+nn)); tot_f=$((tot_f+f))
  if [ "$f" -gt 0 ]; then flagged+=("$mod ($f)"); fi
done < "$REPORT"

echo "   compiled+audited: $((n-fail_compile-not_elf))   compile failures: $fail_compile   non-elf results: $not_elf"
echo "   T=$tot_t  B=$tot_b  N=$tot_n  F=$tot_f"
if [ "${#flagged[@]}" -gt 0 ]; then
  echo "   modules with F>0 (control-flow F on real compiled code — worth reading, not auto-failed):"
  for x in "${flagged[@]}"; do echo "     - $x"; done
fi
echo "   full per-module report: $REPORT"
