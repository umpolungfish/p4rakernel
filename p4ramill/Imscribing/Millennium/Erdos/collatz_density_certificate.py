"""Counting the predecessor tree by size, not by depth.

Doubling multiplies a node by 2; the odd arm n = (2m-1)/3 by less than 2/3.  So a
node reached by d steps of which j are odd-arm steps has size < 2^d / 3^j, and the
count that matters is the joint one, F_d(z) = sum over nodes of z^j.

The conductor-nine certificate refines to it: put z on the two injections of the
six-cycle (the odd arm is exactly where j increments, since a child is odd iff it
comes from that arm) and the tight chain gives

    L(z)^6 <= z L(z)^2 + z L(z) + 1

Then the density exponent is  max_alpha log2( inf_z L(z) z^-alpha ) / (1 - alpha log2 3).
"""
import math, collections
from scipy.optimize import brentq

L3 = math.log2(3)
Lz = lambda z: brentq(lambda L: L**6 - z*L*L - z*L - 1, 1e-9, 10)

def preds(m):
    out = [2 * m]
    if m % 3 == 2:
        n = (2 * m - 1) // 3
        if n != 1:
            out.append(n)
    return out

D = 30
level = [(1, 0)]
F = collections.defaultdict(collections.Counter)
for d in range(1, D + 1):
    nxt = []
    for (v, j) in level:
        for p in preds(v):
            nxt.append((p, j + (1 if p % 2 == 1 else 0)))
    level = nxt
    for (v, j) in nxt:
        F[d][j] += 1

print(f"{'z':>5} {'L(z) certificate':>17} {'measured growth of F_d(z)':>26}")
for z in (0.5, 0.75, 1.0, 1.5, 2.0):
    Fd = [sum(c * z ** j for j, c in F[d].items()) for d in range(1, D + 1)]
    print(f"{z:>5} {Lz(z):>17.5f} {(Fd[D-1]/Fd[19])**0.1:>26.5f}")

best = (0, 0)
a = 0.01
while a < 1 / L3 - 0.005:
    v = min(math.log2(Lz(z)) - a * math.log2(z) for z in (0.05 * k for k in range(1, 200)))
    e = v / (1 - a * L3)
    if e > best[0]:
        best = (e, a)
    a += 0.005
print(f"\ndensity exponent from the certificate : {best[0]:.4f}  at alpha = {best[1]:.4f}")
print(f"from the depth count alone (6/5)      : {math.log2(6/5):.4f}")
print(f"depth count at the true rate (4/3)    : {math.log2(4/3):.4f}")
print(f"Krasikov-Lagarias                     : 0.84")
print(f"Collatz needs                         : 1.00")
