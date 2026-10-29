"""Survivor counts by DP on the odd-step count alone.

A survivor is determined by its parity vector, and the only state the survival
condition reads is j, the running odd-step count: the class survives depth i when
3^j >= 2^i.  From 3^j >= 2^k, the odd child always satisfies 3^(j+1) >= 2^(k+1),
while the even child needs 3^j >= 2^(k+1).  So

    dp[k+1][j+1] += dp[k][j]                     always
    dp[k+1][j]   += dp[k][j]   when 3^j >= 2^(k+1)

and S_k = sum_j dp[k][j] is the survivor count mod 2^k.  This is the same count
the residue tree produces, at a fraction of the cost, which is what lets the
decay rate be read rather than extrapolated.
"""
import sys
from math import log2, exp

L3 = log2(3)

def chernoff():
    f = lambda th: 0.5 * (exp(th * (L3 - 1)) + exp(-th))
    lo, hi = 0.0, 20.0
    for _ in range(300):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(m1) < f(m2): hi = m2
        else: lo = m1
    th = (lo + hi) / 2
    return f(th), th

def run(kmax, report):
    dp = {0: 1}
    p3 = {0: 1}
    rows = []
    for k in range(1, kmax + 1):
        two = 1 << k
        nd = {}
        for j, c in dp.items():
            nd[j + 1] = nd.get(j + 1, 0) + c
            if 3 ** j >= two:
                nd[j] = nd.get(j, 0) + c
        dp = nd
        S = sum(dp.values())
        rows.append((k, S))
        if k in report or k % report_every == 0:
            dens = S / two
            print(f"{k:>5} {S:>28} {dens:>12.8f} {dens ** (1.0 / k):>10.6f}", flush=True)
    return rows

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    report_every = max(kmax // 20, 1)
    rho, th = chernoff()
    print(f"Chernoff rate rho = {rho:.8f} at theta = {th:.6f}")
    print(f"{'k':>5} {'survivors':>28} {'density':>12} {'dens^(1/k)':>10}")
    rows = run(kmax, set())
    print()
    for a, b in ((kmax // 4, kmax // 2), (kmax // 2, kmax)):
        sa = rows[a - 1][1] / 2 ** a
        sb = rows[b - 1][1] / 2 ** b
        print(f"per-level density factor over k = {a}..{b}: {(sb / sa) ** (1.0 / (b - a)):.8f}")
