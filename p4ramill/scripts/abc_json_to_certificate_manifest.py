#!/usr/bin/env python3
"""Validate a G-mOMonadOS ABC stream JSON artifact.

The output is a compact manifest for the exact Lean certificate generator:
floating-point measurements are never promoted to proof terms.
"""
import json
import sys

def main() -> int:
    if len(sys.argv) == 2 and sys.argv[1] in ("-h", "--help"):
        print("usage: abc_json_to_certificate_manifest.py STREAM.json")
        print("validate a G-mOMonadOS abc stream JSON artifact and emit Lean-generator input")
        return 0
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} STREAM.json", file=sys.stderr)
        return 2
    raw = open(sys.argv[1], encoding="utf-8").read().splitlines()
    line = next((s for s in raw if s.lstrip().startswith('{')), None)
    if line is None:
        raise SystemExit("no JSON object found")
    doc = json.loads(line)
    eps = float(doc["epsilon"])
    rows = doc["measurements"]
    if not rows:
        raise SystemExit("measurements is empty")
    cutoffs = [int(row["cutoff"]) for row in rows]
    if cutoffs != sorted(set(cutoffs)):
        raise SystemExit("cutoffs must be strictly increasing")
    for row in rows:
        t = row["triple"]
        if int(t["a"]) + int(t["b"]) != int(t["c"]):
            raise SystemExit(f"invalid sum at cutoff {row['cutoff']}")
        if not all(row[k] for k in ("radical_calibrated", "height_calibrated", "cofinal")):
            raise SystemExit(f"calibration/cofinal flag is false at cutoff {row['cutoff']}")
    print(f"epsilon={eps:.12g}")
    print("# cutoff a b c discrepancy")
    for row in rows:
        t = row["triple"]
        print(f"{int(row['cutoff'])} {int(t['a'])} {int(t['b'])} {int(t['c'])} {float(row['discrepancy']):.12f}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
