"""Where the rotation count is carried, and where it is not.

For each (k, j) the k rotations of a word of length k with j odd steps contain
some number of survivors.  If that number depends only on (k, j) the count is
CARRIED by the level -- the cycle lemma applies.  This locates the rows where it
is not, against the proved slack coordinate s = j*log2(3) - k.
"""
from math import log2
from itertools import product
L3 = log2(3)

def survives(w):
    j = 0
    for i, c in enumerate(w, 1):
        if c: j += 1
        if 3 ** j < 2 ** i: return False
    return True

def rotations(w):
    k = len(w); return [w[s:] + w[:s] for s in range(k)]

def main(kmax=16):
    print(f"{'k':>3} {'j':>3} {'slack':>8} {'counts':>18}  carried  spread")
    bad = []
    for k in range(1, kmax + 1):
        by_j, seen = {}, set()
        for w in product((0, 1), repeat=k):
            if w in seen: continue
            rots = rotations(w); seen.update(rots)
            by_j.setdefault(sum(w), []).append(sum(1 for r in rots if survives(r)))
        for j in sorted(by_j):
            cs = sorted(set(by_j[j]))
            if cs == [0]: continue
            s = j * L3 - k
            carried = len(cs) == 1
            print(f"{k:>3} {j:>3} {s:>8.4f} {str(cs)[:18]:>18}  {'YES' if carried else 'no':>7}  {max(cs)-min(cs)}")
            if not carried: bad.append((k, j, s))
    print()
    print("word-dependent rows: slack in [%.4f, %.4f]" % (min(s for *_, s in bad), max(s for *_, s in bad)))
    print("count of word-dependent rows:", len(bad))

if __name__ == "__main__":
    main()
