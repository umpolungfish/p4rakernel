"""The level operator as an explicit matrix, and its weighted norm.

Indices are the primitive characters: (j,r) with 0 < j < 3^r and 3 does not
divide j, for r = 1..R.  From `level_operator`, normalised by the level counts,

  (L a)(j,r) = rho [ a(2j mod 3^r, r)
                   + e(-j/3^(r+1)) * (1/3) sum_{s<3} omega^s a(2j + s*3^r, r+1) ]

with omega = e(1/3).  The same-conductor term is the doubling permutation; the
feed reaches exactly one conductor up, which is the triangularity.  At r = R the
feed is dropped: that is the truncation.
"""
import numpy as np, cmath, sys

def index(R):
    idx, pos = [], {}
    for r in range(1, R + 1):
        for j in range(1, 3 ** r):
            if j % 3:
                pos[(j, r)] = len(idx); idx.append((j, r))
    return idx, pos

def operator(R, rho=0.75):
    idx, pos = index(R)
    n = len(idx)
    L = np.zeros((n, n), dtype=complex)
    om = cmath.exp(2j * cmath.pi / 3)
    for (j, r) in idx:
        row = pos[(j, r)]
        L[row, pos[(2 * j % 3 ** r, r)]] += rho
        if r < R:
            ph = cmath.exp(-2j * cmath.pi * j / 3 ** (r + 1))
            for s in range(3):
                k = (2 * j + s * 3 ** r) % 3 ** (r + 1)
                L[row, pos[(k, r + 1)]] += rho * ph * om ** s / 3
    return L, idx

def weighted_norm(R, w, rho=0.75):
    L, idx = operator(R, rho)
    d = np.array([w ** r for (j, r) in idx])
    # ||L||_w = || D L D^{-1} ||_2  for the norm ||a||_w = || D a ||_2
    M = (d[:, None]) * L * (1.0 / d[None, :])
    return np.linalg.norm(M, 2), len(idx)

if __name__ == "__main__":
    print("plain 2-norm and spectral radius by truncation:")
    for R in range(1, 7):
        L, idx = operator(R)
        sv = np.linalg.norm(L, 2)
        sr = max(abs(np.linalg.eigvals(L)))
        print(f"  R={R:>2}  dim {len(idx):>5}   ||L||_2 {sv:.4f}   rho(L) {sr:.6f}")
    print("\nweighted norm ||D L D^-1||_2 with weight w^r:")
    hdr = [1.0, 0.8, 0.6, 0.5, 0.4, 0.3, 0.2]
    print("   R  " + "  ".join(f"{w:>7}" for w in hdr))
    for R in range(2, 7):
        row = []
        for w in hdr:
            v, _ = weighted_norm(R, w)
            row.append(f"{v:7.4f}")
        print(f"  {R:>2}  " + "  ".join(row))
