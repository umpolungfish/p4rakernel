"""The predecessor transfer at conductor 3^r, and the lag on which deviation returns.

`cnt_predStep_mod_nine` is the r = 2 case of

    cnt 3^r c (predStep L) = cnt 3^r (inv2_r * c) L + cnt 3^(r+1) (src_r c) L

with inv2_r = (3^r + 1)/2 the inverse of 2 mod 3^r, and src_r c = 3*(inv2_r*(c-1) mod
3^r) + 2 the junction class mod 3^(r+1) whose odd child lands in c.  The level costs a
3-adic digit and it shows up as the modulus of the second term.

The doubling permutation on residues mod 3^r has order 2*3^(r-1) -- 2, 6, 18, 54.  At
r = 1 that is the involution, and the deviation alternates.  At r >= 2 there is no
per-level sign, and the claim is that the deviation returns only after a full cycle.
This measures that as an autocorrelation over lags, on the real tree.
"""
import sys

def predStep(L):
    return set(2 * m for m in L) | set(2 * (m // 3) + 1 for m in L if m % 3 == 2)

def inv2(r):
    return (3 ** r + 1) // 2

def src(r, c):
    return 3 * ((inv2(r) * (c - 1)) % 3 ** r) + 2

def check_transfer(dmax, rmax):
    print("exactness of the conductor-3^r transfer, on the real tree")
    print(f"{'r':>3} {'modulus':>8} {'classes':>8} {'levels':>7} {'mismatches':>11}")
    for r in range(1, rmax + 1):
        M = 3 ** r
        L, bad = {1}, 0
        for d in range(1, dmax + 1):
            nxt = predStep(L)
            for c in range(M):
                lhs = sum(1 for x in nxt if x % M == c)
                rhs = (sum(1 for m in L if m % M == (inv2(r) * c) % M)
                       + sum(1 for m in L if m % (3 * M) == src(r, c)))
                if lhs != rhs: bad += 1
            L = nxt
        print(f"{r:>3} {M:>8} {M:>8} {dmax:>7} {bad:>11}")

def dev_vec(L, M):
    N = len(L)
    c = [0] * M
    for m in L: c[m % M] += 1
    return [x - N / M for x in c]

def lags(dmax, r, lagmax):
    M = 3 ** r
    L, vs = {1}, []
    for d in range(1, dmax + 1):
        L = predStep(L)
        v = dev_vec(L, M)
        n = sum(x * x for x in v) ** 0.5
        vs.append([x / n for x in v] if n > 0 else v)
    print(f"\nconductor {M}: normalised deviation autocorrelation by lag "
          f"(doubling order {2 * 3 ** (r - 1)})")
    burn = dmax // 2
    for k in range(1, lagmax + 1):
        acc = [sum(a * b for a, b in zip(vs[i], vs[i + k])) for i in range(burn, dmax - k)]
        m = sum(acc) / len(acc)
        print(f"  lag {k:>3}   mean corr {m:>8.4f}" + ("   <-- doubling order" if k == 2 * 3 ** (r - 1) else ""))

if __name__ == "__main__":
    check_transfer(28, 4)
    lags(46, 1, 8)
    lags(46, 2, 14)
    lags(46, 3, 22)
