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
#
# Set VOX_AUDIT_REPAIR=1 to also, for every module with B>0 or F>0, extract
# each flagged function's own word (`vox word`), run it through `insert` (the
# mOMonadOS kernel's single-glyph repair search) and print a plain-English
# decomposition of the word, mark by mark. Off by default: it shells to a
# second binary (mOMonadOS, built if needed) and is only worth the time on a
# module already known to be flagged.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
IR_DIR="$ROOT/.lake/build/ir"
OUT_DIR="$ROOT/.lake/build/vox_native"
VOX="${VOX_BIN:-vox}"
LEANC="${LEANC_BIN:-leanc}"
JOBS="${VOX_AUDIT_JOBS:-4}"
REPAIR="${VOX_AUDIT_REPAIR:-0}"
MOMONADOS_CMDS="${MOMONADOS_CMDS:-$ROOT/../../mOMonadOS/run_hosted_cmds.sh}"

command -v "$LEANC" >/dev/null 2>&1 || { echo "vox_elf_audit: leanc not found (set LEANC_BIN)"; exit 1; }
command -v "$VOX"   >/dev/null 2>&1 || { echo "vox_elf_audit: vox not found (set VOX_BIN)"; exit 1; }
[ -d "$IR_DIR" ] || { echo "vox_elf_audit: no generated C at $IR_DIR — run \`lake build\` first"; exit 1; }
if [ "$REPAIR" = "1" ] && [ ! -x "$MOMONADOS_CMDS" ]; then
  echo "vox_elf_audit: VOX_AUDIT_REPAIR=1 but $MOMONADOS_CMDS not found (set MOMONADOS_CMDS)"; exit 1
fi

# The twelve marks' plain opcode meaning — the fixed decomposition table for
# ANY word `vox word` hands back. This is NOT the CL8NK per-VALUE table (that
# decomposes a grounded TUPLE's values, a different object — a word is not a
# tuple; see ig-docs/IMSCRIBERS_GUIDE_TO_IMASM.md).
decompose_word() {
  local word="$1" i ch
  for (( i=0; i<${#word}; i++ )); do
    ch="${word:$i:1}"
    case "$ch" in
      ⊢) echo "    ⊢ VINIT   initial object ∅ — void/uninitialized state before anything is named" ;;
      ⊣) echo "    ⊣ TANCH   terminal anchor ⊤ — the closed boundary containing the whole system" ;;
      ≻) echo "    ≻ AFWD    forward morphism → — directed transformation toward a target" ;;
      ≺) echo "    ≺ AREV    contravariant ← — reverse/descent transformation" ;;
      ⋈) echo "    ⋈ CLINK   composition ∘ — sequential chaining of morphisms" ;;
      ⊙) echo "    ⊙ IMSCRIB identity id — self-reference, self-recognition" ;;
      ∈) echo "    ∈ FSPLIT  co-multiplication δ — one state opens into two or more arms" ;;
      ∋) echo "    ∋ FFUSE   multiplication μ — the arms rejoin into one B4 verdict" ;;
      ⊤) echo "    ⊤ EVALT   touches constructive truth T (the affirmative arm)" ;;
      ⊥) echo "    ⊥ EVALF   touches constructive falsity F (the negative arm)" ;;
      ⊞) echo "    ⊞ ENGAGR  holds BOTH at once — the B state, a contradiction kept live" ;;
      ⊡) echo "    ⊡ IFIX    ROM fixation — permanent, append-only, cannot be undone" ;;
      *) echo "    $ch  (not one of the twelve marks)" ;;
    esac
  done
}

# Global cap across the WHOLE repair pass, not per-object: a corpus this size
# can carry thousands of B-verdict functions (13101 counted on the first full
# sweep here), and running `insert` on all of them, one mOMonadOS boot each,
# is an hours-long, not a session-long, operation. Cap it and say so rather
# than let a single `repair` invocation run unbounded — no silent truncation.
REPAIR_MAX="${VOX_AUDIT_REPAIR_MAX:-20}"
REPAIR_DONE=0
REPAIR_SEEN=0

# For one compiled object: every function `vox word` finds, kept only if its
# OWN verdict (not the module aggregate) is B or F, repaired and decomposed.
# Uses process substitution (not a pipe) so REPAIR_DONE/REPAIR_SEEN, updated
# inside the loop, are visible to the caller — a `cmd | while` loop runs the
# body in a subshell and would silently lose the count.
repair_flagged_functions() {
  local obj="$1"
  while IFS=$'\t' read -r addr word; do
    [ -n "$word" ] || continue
    local v
    v=$("$VOX" verdict "$word" 2>/dev/null | tail -1 | awk '{print $2}')
    [ "$v" = "B" ] || [ "$v" = "F" ] || continue
    REPAIR_SEEN=$((REPAIR_SEEN+1))
    if [ "$REPAIR_DONE" -ge "$REPAIR_MAX" ]; then
      continue
    fi
    REPAIR_DONE=$((REPAIR_DONE+1))
    echo "  -- $addr  verdict $v --"
    echo "  word: $word"
    echo "  decompose:"
    decompose_word "$word"
    echo "  repair (insert, via mOMonadOS):"
    "$MOMONADOS_CMDS" "insert $word" 2>/dev/null | sed -n '/^word   :/,/^⊙>/p' | sed '$d' | sed 's/^/    /'
  done < <("$VOX" word "$obj" 2>/dev/null)
}

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
flagged_objs=()
while IFS=$'\t' read -r mod status t b nn f; do
  case "$status" in
    COMPILE_FAIL) fail_compile=$((fail_compile+1)); continue ;;
    NOT_ELF*) not_elf=$((not_elf+1)); continue ;;
  esac
  tot_t=$((tot_t+t)); tot_b=$((tot_b+b)); tot_n=$((tot_n+nn)); tot_f=$((tot_f+f))
  if [ "$f" -gt 0 ]; then flagged+=("$mod ($f)"); fi
  if [ "${b:-0}" -gt 0 ] || [ "${f:-0}" -gt 0 ]; then flagged_objs+=("$OUT_DIR/$mod.o"); fi
done < "$REPORT"

echo "   compiled+audited: $((n-fail_compile-not_elf))   compile failures: $fail_compile   non-elf results: $not_elf"
echo "   T=$tot_t  B=$tot_b  N=$tot_n  F=$tot_f"
if [ "${#flagged[@]}" -gt 0 ]; then
  echo "   modules with F>0 (control-flow F on real compiled code — worth reading, not auto-failed):"
  for x in "${flagged[@]}"; do echo "     - $x"; done
fi
echo "   full per-module report: $REPORT"

if [ "$REPAIR" = "1" ]; then
  if [ "${#flagged_objs[@]}" -eq 0 ]; then
    echo
    echo "── repair pass: nothing flagged (no module carries B>0 or F>0)"
  else
    echo
    echo "── repair pass: ${#flagged_objs[@]} flagged module(s), capped at $REPAIR_MAX function(s) (VOX_AUDIT_REPAIR_MAX to change)"
    objs_opened=0
    for o in "${flagged_objs[@]}"; do
      [ "$REPAIR_DONE" -lt "$REPAIR_MAX" ] || break
      objs_opened=$((objs_opened+1))
      echo "  ${o#"$OUT_DIR"/}:"
      repair_flagged_functions "$o"
    done
    # Two things can go unrepaired: functions past the cap WITHIN an opened
    # module (REPAIR_SEEN counts those — the inner loop never breaks early),
    # and whole modules never opened at all because the cap was already hit.
    # Report both; the second is the one a per-function count alone would hide.
    objs_unopened=$(( ${#flagged_objs[@]} - objs_opened ))
    if [ "$REPAIR_SEEN" -gt "$REPAIR_DONE" ] || [ "$objs_unopened" -gt 0 ]; then
      echo
      if [ "$REPAIR_SEEN" -gt "$REPAIR_DONE" ]; then
        echo "   $((REPAIR_SEEN-REPAIR_DONE)) further flagged function(s) not repaired in the module(s) opened (cap reached)"
      fi
      if [ "$objs_unopened" -gt 0 ]; then
        echo "   $objs_unopened further flagged module(s) never opened at all (cap reached before reaching them)"
      fi
      echo "   rerun with VOX_AUDIT_REPAIR_MAX=<n> for more, or target one module directly."
    fi
  fi
fi
