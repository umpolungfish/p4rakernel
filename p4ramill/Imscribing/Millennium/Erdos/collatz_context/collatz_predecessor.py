"""The inverse reading: open the holder before the computer.

Forward, the branch is free — both parities are always available, so the tree is
all 2^k classes with a survival filter laid over it.  Inverse, the branch is
arithmetic: m always has the predecessor 2m, and has the odd predecessor
(2m-1)/3 exactly when m = 2 (mod 3), in which case that predecessor is odd
automatically (m = 3t+2 gives n = 2t+1).  No filter is needed because every path
is a real trajectory.
"""
import sys

def preds(m):
    """Predecessors of m under the shortcut map, the 1 -> 2 -> 1 cycle cut."""
    out = [2 * m]
    if m % 3 == 2:
        t = (m - 2) // 3
        n = 2 * t + 1
        if n != 1:                # cut the cycle edge back into the root
            out.append(n)
    return out

def tree(kmax, root=1):
    level = {root}
    print(f"{'k':>3} {'nodes':>12} {'branch':>7} {'m=2mod3':>9} {'odd frac':>8} "
          f"{'min n':>10} {'max n':>22}", flush=True)
    prev = 1
    for k in range(1, kmax + 1):
        nxt = set()
        two = 0
        for m in level:
            p = preds(m)
            if len(p) == 2: two += 1
            nxt.update(p)
        frac = two / len(level)
        level = nxt
        odd = sum(1 for x in level if x % 2 == 1)
        print(f"{k:>3} {len(level):>12} {len(level)/prev:>7.4f} {frac:>9.4f} "
              f"{odd/len(level):>8.4f} {min(level):>10} {max(level):>22}", flush=True)
        prev = len(level)
    return level

if __name__ == "__main__":
    lvl = tree(int(sys.argv[1]) if len(sys.argv) > 1 else 25)
