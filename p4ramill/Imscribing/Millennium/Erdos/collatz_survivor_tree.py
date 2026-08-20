"""Composition census: residues surviving EVERY depth up to k.

A class r mod 2^k descends at depth i when 3^(j(r,i)) < 2^i.  Survivors are the
residues failing that at every i <= k.  By the shift identity the first k parities
depend only on r mod 2^k, so survivors branch: r mod 2^k extends to r and
r + 2^k mod 2^(k+1), and one new step decides each child.

State per survivor: (r, j, v) with v = T^k(r), which carries the next parity.
"""
import sys

def T(n): return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def census(kmax):
    nodes = [(0, 0, 0)]
    prev = 1
    print(f"{'k':>3} {'survivors':>12} {'density':>10} {'branch':>7}", flush=True)
    for k in range(1, kmax + 1):
        new = []
        half = 1 << (k - 1)
        for (r, j, v) in nodes:
            p3 = 3 ** j
            for b in (0, 1):
                w = p3 * b + v                 # T^(k-1)(r + b*2^(k-1))
                jj = j + (w & 1)
                if 3 ** jj < (1 << k):
                    continue
                new.append((r + b * half, jj, T(w)))
        nodes = new
        print(f"{k:>3} {len(nodes):>12} {len(nodes)/(1<<k):>10.6f} {len(nodes)/prev:>7.3f}",
              flush=True)
        prev = max(len(nodes), 1)
        if k <= 7:
            print(f"     survivors mod {1<<k}: {sorted(r for r,_,_ in nodes)}", flush=True)
    return nodes

if __name__ == "__main__":
    census(int(sys.argv[1]) if len(sys.argv) > 1 else 24)
