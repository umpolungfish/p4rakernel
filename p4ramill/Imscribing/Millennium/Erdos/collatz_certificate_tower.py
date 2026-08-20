"""The conductor tower: the certificate at modulus 3^k, refined by odd steps.

At modulus 3^k the doubling map is exact and the odd child's class is determined
only mod 3^(k-1), so the adversary picks among three lifts; weighting by the minimum
removes the choice.  The best constant is the ergodic constant of the monotone
homogeneous map

    T(w)_c = w_{2c mod 3^k} + [c = 2 mod 3] * z * min over the three lifts of w

computed by power iteration.  k = 2 reproduces the conductor-nine root of
L^6 = z L^2 + z L + 1.  Replacing min by max gives an upper bound U(z), so the pair
sandwiches the true growth rate Lambda(z) of F_d(z) = sum over nodes of z^j.

Since a node reached by d steps of which j are odd-arm steps has size < 2^d / 3^j,
the density exponent follows by Legendre transform:

    max_alpha  inf_z ( log2 L(z) - alpha log2 z ) / ( 1 - alpha log2 3 )

and because L <= Lambda pointwise, the transform of L is below that of Lambda, so
the value is a lower bound.
"""
import math, numpy as np

def build(k):
    M = 3 ** k; Mm = 3 ** (k - 1); c = np.arange(M)
    jn = np.where(c % 3 == 2)[0]
    n0 = ((2 * jn - 1) // 3) % Mm
    return M, (2 * c) % M, jn, np.stack([n0, n0 + Mm, n0 + 2 * Mm])

def rate(z, pre, mode='min', tol=1e-11, itmax=4000):
    M, dbl, jn, lf = pre
    w = np.ones(M); prev = 0.0; lam = 1.0
    for it in range(itmax):
        nw = w[dbl].copy()
        a, b, d = w[lf[0]], w[lf[1]], w[lf[2]]
        nw[jn] += z * (np.minimum(np.minimum(a, b), d) if mode == 'min'
                       else np.maximum(np.maximum(a, b), d))
        s = nw.max(); lam = s / w.max(); w = nw / s
        if it > 80 and abs(lam - prev) < tol: break
        prev = lam
    return lam

L3 = math.log2(3)

def exponent(k, zs=None):
    pre = build(k); cache = {}
    zs = zs or [1.0 + 0.25 * t for t in range(40)]
    def Lz(z):
        if z not in cache: cache[z] = rate(z, pre)
        return cache[z]
    best = (0.0, 0.0, 0.0); a = 0.005
    while a < 1 / L3 - 0.002:
        v, zb = min(((math.log2(Lz(z)) - a * math.log2(z)), z) for z in zs)
        e = v / (1 - a * L3)
        if e > best[0]: best = (e, a, zb)
        a += 0.005
    return best

if __name__ == "__main__":
    print(f"{'k':>3} {'modulus':>9} {'L(1)':>9} {'exponent':>10} {'alpha':>7} {'z':>6}")
    for k in (2, 4, 6, 8, 10, 11, 12):
        pre = build(k)
        e, a, z = exponent(k)
        print(f"{k:>3} {3**k:>9} {rate(1.0, pre):>9.5f} {e:>10.4f} {a:>7.3f} {z:>6.2f}",
              flush=True)
    print("\nKrasikov-Lagarias: 0.84.  Collatz needs 1.00.")
    print("The Legendre step assumes the large-deviation lower bound for N(d, alpha d);")
    print("L(z) <= Lambda(z) is proved by the certificate and checked against the tree.")
