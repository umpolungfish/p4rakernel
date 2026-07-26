#!/usr/bin/env bash
# Check the SIC moduli conductor result and print what was checked.
#
#   ./verify_sic_moduli.sh
#
# Elaborates the SIC modules for d = 2, 4, 8, 12, 16, 20 and 2048 through the Lean
# kernel, then prints the claim list and the axiom dependencies of the headline
# theorems. The axioms are the PARI/GP field data — class numbers, ray class
# degrees, abelian types — which enter as computed input rather than as proof.
#
# Needs elan (https://github.com/leanprover/elan). The first run builds Mathlib
# and takes a while; later runs are cached and finish in seconds.

set -euo pipefail

cd "$(dirname "$0")/p4ramill"

REPORT="Imscribing/Millennium/SIC_Moduli_Report.lean"

LOG="$(mktemp)"
trap 'rm -f "$LOG"' EXIT

echo "Building the moduli modules (first run fetches and builds Mathlib)..."
if ! lake build \
  Imscribing.Millennium.Ring2048_Bridge \
  Imscribing.Millennium.SIC_D12_Embedding \
  Imscribing.Millennium.SIC_D12_Equiangularity \
  Imscribing.Millennium.SIC_D12_RayTower \
  Imscribing.Millennium.SIC_D12_SymmetricModuli \
  Imscribing.Millennium.SIC_D16_Moduli \
  Imscribing.Millennium.SIC_D20_Moduli \
  Imscribing.Millennium.SIC_D2048_Moduli \
  Imscribing.Millennium.SIC_D2048_Unconditional > "$LOG" 2>&1; then
  echo "Build failed:" >&2
  cat "$LOG" >&2
  exit 1
fi
echo "Build clean. Elaborating the report..."
echo

# The style linter objects to `native_decide` on Mathlib's house rules; the
# arithmetic it discharges is reported honestly in the axiom lists below, where
# it shows up as Lean.ofReduceBool and Lean.trustCompiler.
lake env lean "$REPORT" 2>&1 \
  | grep -vE "has local changes|native_decide|linter.style.nativeDecide|^Note: |^$"
