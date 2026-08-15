#!/usr/bin/env bash
# The Vox proof sweep, end to end, in the repo.
#
#   ./sweep/run_sweep.sh sweep/Lift0003.lean
#
# One module at a time. Importing the whole corpus into one environment is
# blocked by name collisions between modules, and the lift never needed it — it
# is per declaration, so nothing has to coexist.
#
# Lean lifts, Vox verdicts, and nothing else verdicts anything: there is one
# implementation of the closure law and it is in the Rust crate.
set -euo pipefail
LIFT="${1:?usage: run_sweep.sh sweep/LiftXXXX.lean}"
BASE="$(basename "$LIFT" .lean)"
OUT="${BASE#Lift}"
VOX="${VOX:-$HOME/imsgct/Vox/target/release/vox}"

lake env lean "$LIFT" 2>/dev/null > "sweep/words${OUT}.tsv"
cut -f1,2 "sweep/words${OUT}.tsv" > "sweep/.w.tsv"
"$VOX" verdict --tsv "sweep/.w.tsv" > "sweep/verdicts${OUT}.tsv"
rm -f "sweep/.w.tsv"

# The cross-check. `#print axioms` knows nothing about the twelve, so where the
# two agree the verdict is corroborated, and where they disagree it is a finding
# in one direction or the other. Neither overrules the other.
paste <(cut -f1,2 "sweep/verdicts${OUT}.tsv") <(cut -f3 "sweep/words${OUT}.tsv") \
  | awk -F'\t' '{ax=($3=="clean")?"clean":"assumed"; printf "%-2s %-8s %s\n",$2,ax,$1}' \
  | sort | tee "sweep/crosscheck${OUT}.txt"
