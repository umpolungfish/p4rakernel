"""Depth-k residue split for the Collatz shortcut map T(n)=n/2 | (3n+1)/2.

For r mod 2^k, T^k(2^k*t + r) = 3^j * t + T^k(r), where j = the number of odd
steps taken from r in k steps.  The class contracts iff 3^j < 2^k, and then the
threshold t0 = the least t with (2^k - 3^j)*t > T^k(r) - r.
"""
from math import log

def T(n): return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def trace(r, k):
    n, j = r, 0
    for _ in range(k):
        if n % 2: j += 1
        n = T(n)
    return n, j                      # T^k(r), odd-step count

def level(k):
    """(contracting, surviving) residues mod 2^k, odd r only."""
    con, surv = [], []
    for r in range(1, 1 << k, 2):
        c, j = trace(r, k)
        rec = (r, j, 3**j, c)
        (con if 3**j < (1 << k) else surv).append(rec)
    return con, surv

def t0(r, k, j, c):
    """least t with 3^j*t + c < 2^k*t + r"""
    gap, need = (1 << k) - 3**j, c - r
    if gap <= 0: return None
    t = need // gap + 1
    return max(t, 0)

if __name__ == "__main__":
    R = log(2) / log(3)
    print(f"threshold j/k > {R:.6f}")
    print(f"{'k':>3} {'odd res':>8} {'contract':>9} {'survive':>8} {'surv frac':>10} {'2^-k tail':>10}")
    prev = None
    for k in range(1, 25):
        con, surv = level(k)
        tot = 1 << (k - 1)
        print(f"{k:>3} {tot:>8} {len(con):>9} {len(surv):>8} {len(surv)/tot:>10.6f} {len(surv)/2**k:>10.3e}")
    print()
    for k in (4, 5, 6, 8):
        con, surv = level(k)
        print(f"k={k}: surviving residues mod {1<<k}: {[r for r,_,_,_ in surv]}")
    print()
    print("worst thresholds t0 among contracting classes:")
    for k in range(2, 13):
        con, _ = level(k)
        worst = max(((t0(r, k, j, c), r) for r, j, _, c in con), key=lambda p: p[0])
        print(f"  k={k:>2}  max t0 = {worst[0]}  at r={worst[1]} (mod {1<<k})")
