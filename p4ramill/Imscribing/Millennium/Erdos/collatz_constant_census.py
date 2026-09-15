"""The constant inside a surviving class.

A survivor mod 2^k has 3^j > 2^k, so T^k(2^k t + r) = 3^j t + c with c = T^k(r)
grows in t.  A member still descends within k steps exactly when
    (3^j - 2^k) t < r - c,
which needs c < r and then bounds t.  Those are the n whose true stopping time is
at most k while the class multiplier says otherwise: the whole discrepancy
between the coefficient criterion and the map.
"""
import sys

def T(n): return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def census(kmax):
    nodes = [(0, 0, 0)]
    print(f"{'k':>3} {'survivors':>10} {'c<r':>7} {'members':>8} {'largest n':>12}", flush=True)
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
        below, members, biggest = 0, 0, 0
        for (r, j, c) in nodes:
            if c < r:
                below += 1
                gap = 3 ** j - (1 << k)
                cnt = (r - c + gap - 1) // gap        # t = 0 .. cnt-1
                members += cnt
                biggest = max(biggest, (1 << k) * (cnt - 1) + r)
        print(f"{k:>3} {len(nodes):>10} {below:>7} {members:>8} {biggest:>12}", flush=True)
    return nodes

if __name__ == "__main__":
    census(int(sys.argv[1]) if len(sys.argv) > 1 else 20)
