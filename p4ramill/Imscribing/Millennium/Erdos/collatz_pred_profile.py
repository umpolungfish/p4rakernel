"""The predecessor tree's 3-adic profile, read off the real tree.

Level d+1 is the doubling image of level d together with the odd image of its
2 (mod 3) part -- `predStep`, and `card_predStep` says the count is
|L| + |L filtered to 2 mod 3|, so the branch factor is 1 + p2(d) exactly.

The open piece is p2(d) -> 1/3, i.e. whether the levels equidistribute mod 3.
The transfer is exact but it COSTS A DIGIT: the odd child's class mod 3^r is
fixed by the parent's class mod 3^(r+1), never by its class mod 3^r.  So this
measures the deviation from uniform at each conductor 3^r on the actual tree,
and the rate at which it contracts in the level -- never by building an operator
that spreads uniformly, which would report its own construction.
"""
import sys

def profile(level, mod):
    c = [0] * mod
    for m in level:
        c[m % mod] += 1
    return c

def dev(c):
    """L1 deviation from uniform, normalised: 0 uniform, 1 fully concentrated."""
    n = sum(c); k = len(c)
    return sum(abs(x - n / k) for x in c) / (2 * n * (1 - 1.0 / k))

def run(dmax, root=1):
    level = {root}
    mods = [3, 9, 27, 81]
    print(f"{'d':>3} {'nodes':>10} {'branch':>8} {'p2':>8} " +
          " ".join(f"{'dev%d'%m:>9}" for m in mods), flush=True)
    for d in range(1, dmax + 1):
        nxt = set()
        for m in level:
            nxt.add(2 * m)
            if m % 3 == 2:
                n = 2 * (m // 3) + 1
                if n != 1:
                    nxt.add(n)
        prev = len(level)
        level = nxt
        p2 = sum(1 for m in level if m % 3 == 2) / len(level)
        ds = [dev(profile(level, m)) for m in mods]
        print(f"{d:>3} {len(level):>10} {len(level)/prev:>8.5f} {p2:>8.5f} " +
              " ".join(f"{x:>9.5f}" for x in ds), flush=True)
    return level

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 40)
