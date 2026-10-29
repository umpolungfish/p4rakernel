"""The residue distribution of the predecessor tree, measured, not assumed.

The branch factor is 1 + (fraction of nodes with m = 2 mod 3), so it is a global
constant exactly when that fraction is stationary.  Take it off the real tree:
count residues mod 3, 9 and 27 at each level and watch the deviation from uniform.
"""
import sys

def preds(m):
    out = [2 * m]
    if m % 3 == 2:
        n = (2 * m - 1) // 3
        if n != 1:
            out.append(n)
    return out

def run(kmax, root=1):
    level = {root}
    print(f"{'k':>3} {'nodes':>10} {'branch':>8} {'p(2 mod 3)':>11} "
          f"{'maxdev mod 9':>13} {'maxdev mod 27':>14}", flush=True)
    prev = 1
    for k in range(1, kmax + 1):
        nxt = set()
        for m in level:
            nxt.update(preds(m))
        level = nxt
        n = len(level)
        p2 = sum(1 for m in level if m % 3 == 2) / n
        d9 = max(abs(sum(1 for m in level if m % 9 == c) / n - 1 / 9) for c in range(9))
        d27 = max(abs(sum(1 for m in level if m % 27 == c) / n - 1 / 27) for c in range(27))
        print(f"{k:>3} {n:>10} {n/prev:>8.5f} {p2:>11.6f} {d9*9:>13.5f} {d27*27:>14.5f}",
              flush=True)
        prev = n
    return level

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 38)
