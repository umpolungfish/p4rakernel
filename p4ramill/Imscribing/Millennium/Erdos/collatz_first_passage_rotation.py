"""First passage on the survivor band, read around the ring.

Survival to depth k reads only the running odd-step count:
  a word w in {O,E}^k survives when every prefix of length i with j odd steps
  has 3^j >= 2^i.  Integral, no irrational slope.

First passage is the first prefix that fails.  The cycle lemma prices prefix
conditions by ROTATION, so the question is whether the number of surviving
rotations inside one rotation class is a carried count -- a function of (k,j)
alone -- or whether it depends on the word.  A carried count banks; a
word-dependent one does not.
"""
import sys
from itertools import product

def survives(w):
    """All prefixes clear 3^j >= 2^i."""
    j = 0
    for i, c in enumerate(w, 1):
        if c: j += 1
        if 3 ** j < 2 ** i:
            return False
    return True

def first_passage(w):
    """Least i whose prefix fails, or None."""
    j = 0
    for i, c in enumerate(w, 1):
        if c: j += 1
        if 3 ** j < 2 ** i:
            return i
    return None

def rotations(w):
    k = len(w)
    return [w[s:] + w[:s] for s in range(k)]

def main(kmax):
    print(f"{'k':>3} {'j':>3} {'classes':>8} {'surv/class: distinct counts':>34}  carried?")
    for k in range(1, kmax + 1):
        by_j = {}
        seen = set()
        for w in product((0, 1), repeat=k):
            if w in seen:
                continue
            rots = rotations(w)
            for r in rots:
                seen.add(r)
            j = sum(w)
            n = sum(1 for r in set(rots) if survives(r))
            # weight by how many of the k rotations (with multiplicity) survive
            nmult = sum(1 for r in rots if survives(r))
            by_j.setdefault(j, []).append((nmult, len(set(rots))))
        for j in sorted(by_j):
            counts = sorted({c for c, _ in by_j[j]})
            carried = "YES" if len(counts) == 1 else "no"
            print(f"{k:>3} {j:>3} {len(by_j[j]):>8} {str(counts)[:34]:>34}  {carried}")
        print()

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
