#!/usr/bin/env bash
# build.sh — `lake build` with an automatic vox audit of the GateCheck scaffolds.
# Every build reports the T/B/N/F control-flow-closure census alongside the Lean
# result, so ill-typed (F) imscriptions surface at build time rather than silently.
#
# Usage:  ./build.sh [lake build args...]
#   VOX_STRICT=1  -> a non-empty F census fails the build (exit 1)
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
if [ "${VOX_STRICT:-0}" = "1" ] && [ "$vox_rc" -ne 0 ]; then
  echo "VOX_STRICT: failing build on non-empty F census"; exit 1
fi
exit 0
