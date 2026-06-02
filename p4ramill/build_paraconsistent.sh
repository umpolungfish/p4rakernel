#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FORK_DIR="$(dirname "$SCRIPT_DIR")"
LAKE_BIN="${FORK_DIR}/build/stage1/bin/lake"
LEAN_BIN="${FORK_DIR}/build/stage1/bin/lean"

echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║  p4rakernel Build — Paraconsistent MillenniumAnkh            ║"
echo "╚═══════════════════════════════════════════════════════════════╝"

if [ ! -f "$LAKE_BIN" ]; then
    echo "ERROR: Paraconsistent lake not found at $LAKE_BIN"
    echo "Build the fork first: cd $FORK_DIR && mkdir -p build && cd build"
    echo "  cmake .. -DCMAKE_BUILD_TYPE=Release && make stage0 -j\$(nproc) && make stage1 -j\$(nproc)"
    exit 1
fi

cd "$SCRIPT_DIR"
export PATH="${FORK_DIR}/build/stage1/bin:$PATH"
TARGET="${1:-all}"

echo "Target: $TARGET | Lake: $LAKE_BIN"

case "$TARGET" in
    all)
        echo ">>> Building all..."
        "$LAKE_BIN" build
        echo ">>> Running ParaconsistentMillennium..."
        "$LEAN_BIN" --run ParaconsistentMillennium.lean
        ;;
    Imscribing)
        "$LAKE_BIN" build Imscribing
        ;;
    ParaconsistentMillennium)
        "$LEAN_BIN" --run ParaconsistentMillennium.lean
        ;;
    ParaconsistentKernelTest)
        "$LEAN_BIN" --run ParaconsistentKernelTest.lean
        ;;
    clean)
        "$LAKE_BIN" clean && rm -rf .lake/build
        echo "Clean done."
        ;;
    *)
        echo "Usage: $0 [all|Imscribing|ParaconsistentMillennium|ParaconsistentKernelTest|clean]"
        exit 1
        ;;
esac

echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║  Build complete — μ∘δ = id                                   ║"
echo "╚═══════════════════════════════════════════════════════════════╝"
