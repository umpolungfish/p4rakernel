#!/usr/bin/env python3
"""Measure the native Y/SIXTEEN_3 divisor executable on exact semiprimes."""
import csv
import json
import statistics
import subprocess
import sys
import time
from pathlib import Path

import sympy

ROOT = Path(__file__).resolve().parents[3]
BINARY = ROOT / ".lake/build/bin/divisor_reentry"
OUT = Path(__file__).resolve().parent
REPEATS = int(sys.argv[1]) if len(sys.argv) > 1 else 3
ONLY = set(sys.argv[2:])

# Two orthogonal series: bit length at fixed search depth, then search depth
# at fixed bit length. A prime cofactor makes the first returned divisor known.
cases = []
for bits in (32, 64, 128, 256, 512, 895, 1024, 2048, 4096, 8192):
    p = 101
    q = int(sympy.nextprime(((1 << (bits - 1)) + p - 1) // p))
    n = p * q
    assert n.bit_length() == bits and sympy.isprime(p) and sympy.isprime(q)
    cases.append((f"bits_{bits}", bits, p, q, n))
for p in (11, 101, 1009, 10007, 100003):
    q = int(sympy.nextprime(((1 << 127) + p - 1) // p))
    n = p * q
    assert n.bit_length() == 128 and sympy.isprime(p) and sympy.isprime(q)
    cases.append((f"scan_{p}", n.bit_length(), p, q, n))

prior = json.loads((OUT / "results.json").read_text()) if (OUT / "results.json").exists() else {"cases": []}
rows = prior["cases"]
for name, bits, expected, q, n in cases:
    if ONLY and name not in ONLY:
        continue
    elapsed = []
    outputs = []
    for _ in range(REPEATS):
        start = time.perf_counter_ns()
        result = subprocess.run(
            [str(BINARY), "factor", str(n)],
            check=True, capture_output=True, text=True,
        )
        elapsed.append((time.perf_counter_ns() - start) / 1e9)
        outputs.append(result.stdout.strip())
        assert not result.stderr
    assert len(set(outputs)) == 1, (name, outputs)
    output = outputs[0]
    prefix = "factor="
    factor = int(output.split(prefix, 1)[1].split()[0])
    cofactor = int(output.split("cofactor=", 1)[1].split()[0])
    product = int(output.split("product=", 1)[1].split()[0])
    assert factor == expected, (name, expected, factor, output)
    assert factor * cofactor == n == product
    row = {
        "case": name,
        "bit_length": bits,
        "expected_factor": str(expected),
        "cofactor": str(q),
        "target": str(n),
        "runs_seconds": elapsed,
        "median_seconds": statistics.median(elapsed),
        "factor_returned": str(factor),
        "product_verified": product == n,
        "stdout": output,
    }
    rows = [saved_row for saved_row in rows if saved_row["case"] != name]
    rows.append(row)
    meta = {
        "binary": str(BINARY),
        "binary_sha256": __import__("hashlib").sha256(BINARY.read_bytes()).hexdigest(),
        "repeats": REPEATS,
        "clock": "time.perf_counter_ns around complete executable process",
        "fixture": "product of two independently primality-checked primes; expected factor is the smaller prime",
        "cases": rows,
    }
    (OUT / "results.json").write_text(json.dumps(meta, indent=2) + "\n")
    with (OUT / "results.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=[
            "case", "bit_length", "expected_factor", "median_seconds", "runs_seconds", "product_verified"
        ])
        writer.writeheader()
        for saved_row in rows:
            writer.writerow({k: saved_row[k] for k in writer.fieldnames})
    print(f"{name}: {bits} bits, factor {factor}, median {row['median_seconds']:.6f}s", flush=True)

print(f"saved {len(rows)} exact verified cases to {OUT}")
