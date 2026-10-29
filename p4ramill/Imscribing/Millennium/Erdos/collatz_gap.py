"""How fast the level distribution approaches uniform: the gap, measured.

Uniform is stationary for the level map.  Doubling is a bijection of Z/3^r, and
the odd branch carries the 2 (mod 3) third onto everything, tripling its density,
so uniform in gives uniform out with total mass 1 + 1/3.  What is not settled is
whether the tree CONVERGES to it, so take the deviation off the real tree and read
its decay.
"""
import sys

def preds(m):
    out = [2 * m]
    if m % 3 == 2:
        n = (2 * m - 1) // 3
        if n != 1:
            out.append(n)
    return out

def dev(level, mod):
    n = len(level)
    c = [0] * mod
    for m in level:
        c[m % mod] += 1
    return max(abs(x / n - 1 / mod) for x in c) * mod

def run(kmax):
    level = {1}
    hist = {3: [], 9: [], 27: []}
    print(f"{'k':>3} {'nodes':>9} {'dev3':>9} {'dev9':>9} {'dev27':>9} "
          f"{'r3':>7} {'r9':>7} {'r27':>7}", flush=True)
    for k in range(1, kmax + 1):
        nxt = set()
        for m in level:
            nxt.update(preds(m))
        level = nxt
        ds = {mod: dev(level, mod) for mod in (3, 9, 27)}
        for mod in ds: hist[mod].append(ds[mod])
        def rate(mod):
            h = hist[mod]
            if len(h) < 9 or h[-9] == 0: return float('nan')
            return (h[-1] / h[-9]) ** (1 / 8)
        if k >= 12:
            print(f"{k:>3} {len(level):>9} {ds[3]:>9.5f} {ds[9]:>9.5f} {ds[27]:>9.5f} "
                  f"{rate(3):>7.4f} {rate(9):>7.4f} {rate(27):>7.4f}", flush=True)
    return level

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 38)
