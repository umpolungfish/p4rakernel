#!/usr/bin/env bash
set -euo pipefail

readme_kernel_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
readme_checks="$readme_kernel_root/measurements/temporal_reentry_20261010"
cd "$readme_kernel_root/p4ramill"

for readme_name in root corpus; do
  readme_source="$readme_kernel_root/README.md"
  if [[ "$readme_name" == corpus ]]; then
    readme_source="$readme_kernel_root/p4ramill/README.md"
  fi
  # Collect the imports before the example bodies so every Markdown block
  # remains a valid standalone example and the combined check is valid Lean.
  awk '
    /^```lean$/ { inside = 1; next }
    /^```$/ { inside = 0; next }
    inside && /^import / {
      if (!seen[$0]++) imports[++count] = $0
      next
    }
    inside { body = body $0 "\n" }
    END {
      for (i = 1; i <= count; i++) print imports[i]
      printf "%s", body
    }
  ' "$readme_source" > "$readme_checks/cycle_${readme_name}_readme_examples.lean"
  lake env lean -j1 "$readme_checks/cycle_${readme_name}_readme_examples.lean" \
    > "$readme_checks/cycle_${readme_name}_readme_examples.log" 2>&1
done
