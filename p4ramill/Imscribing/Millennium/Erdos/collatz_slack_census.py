"""The slack coordinate on the survivor tree.

A survivor at depth k with odd-step count j has slack

    s = j * log2(3) - k  >=  0,

and one more step moves it by +log2(3)-1 = +0.584963 (odd) or -1 (even).  The
survivor tree is that walk conditioned to stay non-negative, so the census
splits: a survivor with s >= 1 keeps both lifts, one with s < 1 keeps only the
odd one.  S_{k+1} = 2*A_k + B_k with A = #(s >= 1), B = #(s < 1).
"""
import sys
from math import log2, exp, log

def T(n): return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

L3 = log2(3)

def chernoff():
    """min over theta of E[e^{theta X}], X in {log2(3)-1, -1} with equal weight."""
    lo, hi = 0.0, 20.0
    f = lambda th: 0.5 * (exp(th * (L3 - 1)) + exp(-th))
    for _ in range(200):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(m1) < f(m2): hi = m2
        else: lo = m1
    th = (lo + hi) / 2
    return f(th), th

def census(kmax):
    nodes = [(0, 0, 0)]
    rho, th = chernoff()
    print(f"Chernoff rate rho = {rho:.6f} (theta = {th:.4f}), per-level density factor", flush=True)
    print(f"{'k':>3} {'survivors':>10} {'density':>10} {'A(s>=1)':>9} {'B(s<1)':>8} "
          f"{'mean s':>8} {'max s':>8} {'pred S+1':>10}", flush=True)
    for k in range(1, kmax + 1):
        new = []
        half = 1 << (k - 1)
        for (r, j, v) in nodes:
            p3 = 3 ** j
            for b in (0, 1):
                w = p3 * b + v
                jj = j + (w & 1)
                if 3 ** jj < (1 << k):
                    continue
                new.append((r + b * half, jj, T(w)))
        nodes = new
        if not nodes:
            print(f"{k:>3} {'0':>10}"); break
        slacks = [j * L3 - k for (_, j, _) in nodes]
        A = sum(1 for s in slacks if s >= 1)
        B = len(nodes) - A
        print(f"{k:>3} {len(nodes):>10} {len(nodes)/(1<<k):>10.6f} {A:>9} {B:>8} "
              f"{sum(slacks)/len(slacks):>8.4f} {max(slacks):>8.4f} {2*A+B:>10}", flush=True)
    return nodes

if __name__ == "__main__":
    census(int(sys.argv[1]) if len(sys.argv) > 1 else 24)
