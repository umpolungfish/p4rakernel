#!/usr/bin/env bash
set -euo pipefail

mkdir -p Imscribing
cp PerronPositiveLimit.lean Imscribing/PerronPositiveLimit.lean
cp PerronFiniteInversion.lean Imscribing/PerronFiniteInversion.lean
cp PerronExplicitFormulaAssembly.lean Imscribing/PerronExplicitFormulaAssembly.lean
cp PerronCompletion.lean Imscribing/PerronCompletion.lean
cp PerronBuildAll.lean Imscribing/PerronBuildAll.lean

lake build Imscribing.PerronBuildAll
