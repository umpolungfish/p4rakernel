#!/usr/bin/env bash
# build.sh — `lake build` with an automatic vox audit of the GateCheck scaffolds.
# Every build reports the T/B/N/F control-flow-closure census alongside the Lean
# result, so ill-typed (F) imscriptions surface at build time rather than silently.
#
# Usage:  ./build.sh [lake build args...]
#   VOX_BIN=path  -> override the hosted vox binary
set -uo pipefail
cd "$(dirname "$0")"

echo "== lake build =="
lake build "$@"; lake_rc=$?
echo "   lake build exit: $lake_rc"

echo
if [ -x scripts/vox_audit.sh ]; then
  scripts/vox_audit.sh; vox_rc=$?
else
  echo "vox_audit.sh missing — skipping vox audit"; vox_rc=0
fi

if [ "$lake_rc" -ne 0 ]; then exit "$lake_rc"; fi
# F is a legitimate verdict, not a build fault — the vox census is relayed,
# never used to fail a build (that would collapse four values to pass/fail).
exit 0
