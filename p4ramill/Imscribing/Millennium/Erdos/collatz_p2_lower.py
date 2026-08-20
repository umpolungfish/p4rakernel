"""p2(d) > 0.1644 for d >= 3.

p2(d) = n2(d)/N(d) where n2 counts level-d vertices = 2 mod 3.  Every vertex has
the child 2v; exactly the 2 mod 3 ones have a second, so N(d+1) = N(d) + n2(d)
and p2(d) = N(d+1)/N(d) - 1 exactly.  The target is a growth rate.

Mod 9 is the right resolution.  Doubling is the 6-cycle 1->2->4->8->7->5->1 on the
units and 3->6->3, 0->0 on the rest.  The odd child n = (2v-1)/3 of a junction has
    v = 2 (mod 9) -> n = 1 (mod 3)
    v = 5 (mod 9) -> n = 0 (mod 3)   dead: 0 mod 3 spawns only a bare chain
    v = 8 (mod 9) -> n = 2 (mod 3)   another junction
Which class mod 9 the child lands in needs v mod 27, so at mod 9 it is adversarial.
This computes the guaranteed growth over every adversary routing.
"""
import sys, itertools
import numpy as np

# ---- the real tree -------------------------------------------------------
def real(dmax):
    level = {1}
    rows = []
    for d in range(1, dmax + 1):
        nxt = set()
        for m in level:
            nxt.add(2 * m)
            if m % 3 == 2:
                n = (2 * m - 1) // 3
                if n != 1:
                    nxt.add(n)
        level = nxt
        N = len(level)
        n2 = sum(1 for x in level if x % 3 == 2)
        rows.append((d, N, n2, n2 / N))
    return rows

# ---- worst case over adversary routings ---------------------------------
UNITS = [1, 2, 4, 8, 7, 5]
def matrix(route2, route8, route5):
    """route2 in {1,4,7}: where a class-2 junction's odd child lands mod 9.
       route8 in {2,5,8}, route5 in {0,3,6}.  A[i][j] = flow from class j to i."""
    A = np.zeros((9, 9))
    for j in range(9):
        A[(2 * j) % 9][j] += 1.0          # the doubling child, always
    A[route2][2] += 1.0
    A[route8][8] += 1.0
    A[route5][5] += 1.0
    return A

def perron(A):
    ev = np.linalg.eigvals(A)
    return max(ev.real)

if __name__ == "__main__":
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    rows = real(dmax)
    print(f"{'d':>3} {'N':>12} {'n2':>12} {'p2':>8} {'N(d)/N(d-1)':>12}")
    prev = 1
    for d, N, n2, p2 in rows:
        print(f"{d:>3} {N:>12} {n2:>12} {p2:>8.4f} {N/prev:>12.4f}")
        prev = N
    tail = [p for d, N, n2, p in rows if d >= 3]
    print(f"\nmin p2 over d>=3 : {min(tail):.4f} at d={[d for d,N,n2,p in rows if p==min(tail)]}")
    print(f"geometric mean of (1+p2) over d>=3: "
          f"{(rows[-1][1]/rows[2][1])**(1/(len(rows)-3)):.6f}")

    print("\nworst case over adversary routings, mod 9:")
    best = None
    for r2, r8, r5 in itertools.product([1, 4, 7], [2, 5, 8], [0, 3, 6]):
        lam = perron(matrix(r2, r8, r5))
        if best is None or lam < best[0]:
            best = (lam, r2, r8, r5)
    print(f"  min Perron root {best[0]:.6f}  at route2->{best[1]} route8->{best[2]} route5->{best[3]}")
    print(f"  target 1.1644 : {'PASS' if best[0] > 1.1644 else 'FAIL'}")
    lams = sorted(perron(matrix(*p)) for p in itertools.product([1,4,7],[2,5,8],[0,3,6]))
    print(f"  all 27 roots: {' '.join(f'{x:.4f}' for x in lams)}")

# ---- a weight certificate ------------------------------------------------
def certificate(lam_target=1.2):
    """Find w > 0 with  g_j >= lam * w_j  for every adversary routing, where
           g_j = w_{2j mod 9} + [j=2] min(w1,w4,w7)
                              + [j=5] min(w0,w3,w6)
                              + [j=8] min(w2,w5,w8).
       Then f = w.u satisfies f(d+1) >= lam f(d) unconditionally."""
    A = matrix(7, 5, 0)                       # the minimising routing
    lam, vecs = None, None
    ev, V = np.linalg.eig(A.T)
    i = int(np.argmax(ev.real)); lam = ev.real[i]
    w = np.abs(V[:, i].real); w = w / w.min()
    return lam, w

def check(w, lam):
    m147 = min(w[1], w[4], w[7]); m036 = min(w[0], w[3], w[6]); m258 = min(w[2], w[5], w[8])
    g = np.array([w[(2 * j) % 9] for j in range(9)], dtype=float)
    g[2] += m147; g[5] += m036; g[8] += m258
    return g, all(g[j] >= lam * w[j] - 1e-12 for j in range(9))

lam, w = certificate()
print(f"\nleft Perron root {lam:.6f}\nweights {np.round(w,4)}")
g, ok = check(w, lam)
print(f"g - lam*w = {np.round(g - lam*w, 9)}   valid: {ok}")

print("\nsearching integer weights with lam = 6/5:")
from fractions import Fraction
best = None
scale = w / w.min()
for S in range(1, 400):
    iw = np.maximum(1, np.round(scale * S)).astype(int)
    g, ok = check(iw.astype(float), 1.2)
    if ok:
        best = iw; break
print(f"  {best}")
if best is not None:
    g, ok = check(best.astype(float), 1.2)
    print(f"  5*g - 6*w = {np.round(5*g - 6*best,6).astype(int)}  all >= 0: {ok}")
