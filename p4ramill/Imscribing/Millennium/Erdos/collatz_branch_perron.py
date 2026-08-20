"""Is the predecessor branch factor a global constant, and what is it exactly?

The frame instrument holds the multiplicity outside the frame, so the branch count
should be a constant of the tree rather than a property of the target.  Test it:
the predecessors of m are 2m always, and (2m-1)/3 when m = 2 (mod 3).  Both are
determined by m mod 3^r for a large enough r, so the level counts obey a linear
recursion whose Perron root IS the branch factor.  Build the substitution matrix
on residues mod 3^r and read its spectral radius.
"""
import sys
from fractions import Fraction

def children(m, mod):
    """residue classes of the predecessors of a class m mod `mod`"""
    out = [(2 * m) % mod]
    if m % 3 == 2:
        out.append(((2 * m - 1) // 3) % mod)   # well defined on m mod 3*mod
    return out

def matrix(r):
    mod = 3 ** r
    M = [[0] * mod for _ in range(mod)]
    # a class m mod 3^r splits into 3 classes mod 3^(r+1); to stay closed we use
    # the coarser action, valid because (2m-1)/3 mod 3^(r-1) is determined by m mod 3^r
    for m in range(mod):
        for c in children(m, 3 ** (r - 1)):
            for lift in range(3):
                M[c + lift * 3 ** (r - 1)][m] += Fraction(1, 3)
    return M

def perron(M, iters=4000):
    n = len(M)
    v = [Fraction(1, n)] * n
    lam = Fraction(0)
    for _ in range(iters):
        w = [sum(M[i][j] * v[j] for j in range(n)) for i in range(n)]
        s = sum(w)
        if s == 0: return 0.0, v
        lam = s / sum(v)
        v = [x / s for x in w]
    return float(lam), v

if __name__ == "__main__":
    for r in (1, 2, 3, 4):
        M = matrix(r)
        lam, v = perron(M, 600)
        print(f"r = {r}  (mod {3**r})  branch factor = {lam:.8f}")
        if r <= 2:
            print("   stationary residue weights mod 3:",
                  [f"{float(sum(v[i] for i in range(len(v)) if i % 3 == c)):.6f}" for c in range(3)])
