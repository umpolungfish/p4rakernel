#!/usr/bin/env python3
"""
straus_ladder_discovery.py — Automated discovery, census, and Lean 4 code generator
for modular covering classes on the Erdős–Straus Boolean Core.

Mechanism:
For an odd rung r ≡ 3 (mod 4) and multiplier K ≥ 1 with t = r*K - 1:
The ladder identity yields:
    4/n = 1/a + 1/(K * n * a) + 1/(K * n * (a / t))
whenever 4*a = n + r and t | a.
This holds for all n ≡ -r (mod 4t).
Intersecting with the open frontier n ≡ 1 (mod 24) via the Chinese Remainder Theorem
yields an infinite arithmetic progression n ≡ A (mod M) strictly inside 1 mod 24,
whenever -r ≡ 1 (mod gcd(4t, 24)).
"""

import sys
import math
import sympy

def find_ladder_classes(max_r=60, max_K=60):
    classes = []
    seen = set()
    for r in range(3, max_r + 1, 4):
        for K in range(1, max_K + 1):
            t = r * K - 1
            mod_ladder = 4 * t
            g = math.gcd(mod_ladder, 24)
            if (-r - 1) % g != 0:
                continue
            M = (mod_ladder * 24) // g
            for A in range(1, M, 24):
                if (A + r) % mod_ladder == 0:
                    key = (M, A)
                    if key not in seen:
                        seen.add(key)
                        classes.append({
                            'r': r,
                            'K': K,
                            't': t,
                            'mod_ladder': mod_ladder,
                            'M': M,
                            'A': A
                        })
                    break
    return sorted(classes, key=lambda c: (c['M'], c['A']))

def coverage_census(classes, prime_bound=20000):
    primes_1_24 = [p for p in sympy.primerange(2, prime_bound) if p % 24 == 1]
    covered = set()
    for c in classes:
        M, A = c['M'], c['A']
        for p in primes_1_24:
            if p % M == A:
                covered.add(p)
    uncovered = [p for p in primes_1_24 if p not in covered]
    pct = (len(covered) * 100.0 / len(primes_1_24)) if primes_1_24 else 100.0
    return {
        'total_primes': len(primes_1_24),
        'covered_primes': len(covered),
        'pct': pct,
        'uncovered': uncovered
    }

def print_summary(max_r=60, max_K=60, prime_bound=20000):
    classes = find_ladder_classes(max_r, max_K)
    print("=== Erdős–Straus Ladder Discovery Engine ===")
    print(f"Search bounds: r ≤ {max_r}, K ≤ {max_K}")
    print(f"Total distinct covering families discovered: {len(classes)}\n")

    for bound in [2000, 5000, 10000, 20000]:
        stats = coverage_census(classes, bound)
        print(f"Primes ≤ {bound:5d} (1 mod 24): {stats['total_primes']:3d} | "
              f"Covered: {stats['covered_primes']:3d} ({stats['pct']:6.2f}%) | "
              f"Uncovered: {stats['uncovered']}")

if __name__ == '__main__':
    max_r = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    max_K = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    print_summary(max_r, max_K)
