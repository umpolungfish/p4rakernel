#!/usr/bin/env bash
# Cleanup script for lake build Imscribing warnings
set -e
cd /home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing

echo "=== 1. Remove trailing whitespace ==="
find . -name '*.lean' -exec sed -i 's/[[:space:]]*$//' {} \;

echo "=== 2. Replace λ with fun ==="
find . -name '*.lean' -exec sed -i 's/λ /fun /g' {} \;

echo "=== 3. Move commands to column 0 ==="
find . -name '*.lean' -exec sed -i 's/^[[:space:]]*\(#eval\|#check\|#print\|#reduce\)/\1/' {} \;

echo "=== 4. Fix doc-string spacing ==="
find . -name '*.lean' -exec sed -i 's|--\([^[:space:]]\)|-- \1|g' {} \;

echo "=== 5. Replace induction' with induction ==="
find . -name '*.lean' -exec sed -i "s/induction'/induction/g" {} \;

echo "=== 6. Replace cases' with cases ==="
find . -name '*.lean' -exec sed -i "s/cases'/cases/g" {} \;

echo "=== Done ==="
