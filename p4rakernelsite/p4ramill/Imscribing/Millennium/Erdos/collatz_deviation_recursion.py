"""The deviation recursion the level-contraction ob3ect names, exactly.

Write L for a level, O = {m in L : m = 2 mod 3}, and L' for the next level, so
|L'| = |L| + |O|.  Every class c mod 3^r in L' is fed by exactly two sources:

  the doubling image, from the class 2^{-1}c mod 3^r of L, weight |L|/|L'|;
  the odd image, from the single class of O mod 3^{r+1} that lifts to c,
      weight |O|/|L'|.

Doubling is a bijection mod 3^r, so its term carries D_r(L) across unchanged.
The odd term is a CONDITIONAL deviation: the parent's distribution one digit
finer, normalized by |O| rather than |L|.  That normalization is the factor a
naive reading drops, and it is why

    D_r(L') <= (3/4) D_r(L) + (1/4) D_{r+1}(L)

is false — measured, it breaks at k = 18, 23, 25, 29, 30 with ratio up to 1.97.
The exact statement is

    D_r(L') <= w_e * D_r(L) + w_o * E_r(L),
    E_r(L) = max over c of | N_L(lift(c) mod 3^(r+1)) / |O| - 3^(-r) |

with w_e = |L|/|L'| and w_o = |O|/|L'|.  Contraction of D_r therefore needs
E_r bounded, which is the hierarchy one digit down: the digit spent per level.
"""
import sys

def preds(m):
    out = [2 * m]
    if m % 3 == 2:
        n = (2 * m - 1) // 3
        if n != 1:
            out.append(n)
    return out

def counts(level, mod):
    c = [0] * mod
    for m in level:
        c[m % mod] += 1
    return c

def D(level, r):
    mod = 3 ** r
    n = len(level)
    return max(abs(x / n - 1 / mod) for x in counts(level, mod))

def E(level, r):
    """conditional deviation of the odd branch: parent classes mod 3^(r+1)
    that carry m = 2 mod 3, normalized by the size of that third."""
    mod, fine = 3 ** r, 3 ** (r + 1)
    cf = counts(level, fine)
    nO = sum(1 for m in level if m % 3 == 2)
    if nO == 0:
        return 0.0
    worst = 0.0
    for c in range(mod):
        # the parent class mod 3^(r+1) with (2m-1)/3 = c : m = (3c+1)/2 mod 3^(r+1)
        inv2 = pow(2, -1, fine)
        m_class = ((3 * c + 1) * inv2) % fine
        worst = max(worst, abs(cf[m_class] / nO - 1 / mod))
    return worst

def run(kmax, r=1):
    level = {1}
    print(f"exact recursion at r = {r}", flush=True)
    print(f"{'k':>3} {'nodes':>9} {'D_r':>10} {'E_r':>10} {'bound':>10} {'holds':>6} "
          f"{'contracts':>10}", flush=True)
    for k in range(1, kmax + 1):
        O = {m for m in level if m % 3 == 2}
        nxt = set()
        for m in level:
            nxt.update(preds(m))
        we, wo = len(level) / len(nxt), len(O) / len(nxt)
        d, e = D(level, r), E(level, r)
        bound = we * d + wo * e
        dn = D(nxt, r)
        if k >= 12:
            print(f"{k:>3} {len(nxt):>9} {d:>10.6f} {e:>10.6f} {bound:>10.6f} "
                  f"{'yes' if dn <= bound + 1e-12 else 'NO':>6} "
                  f"{'yes' if bound < d else 'no':>10}", flush=True)
        level = nxt
    return level

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 30,
        int(sys.argv[2]) if len(sys.argv) > 2 else 1)
