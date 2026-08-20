"""Check `level_operator` against the tree it claims to describe.

    zeta^j * coeff(predStep L, 3j)
      = zeta^j * coeff(L, 6j) + (1/3) sum_{s<3} omega^s * coeff(L, 2j + s*3^r)

with zeta a 3^(r+1)-th root of unity and omega = zeta^(3^r).  Also checks that
omega^(-2s) and omega^s are the same weight, which is what removes the inverse
from the informal statement.
"""
import cmath

def predStep(L):
    out = set()
    for m in L:
        out.add(2 * m)
        if m % 3 == 2:
            out.add(2 * (m // 3) + 1)
    return out

def coeff(z, L, k):
    return sum(z ** (k * v) for v in L)

worst = 0.0
worst_w = 0.0
L = {1}
for d in range(1, 21):
    L = predStep(L)
    for r in range(1, 5):
        M = 3 ** (r + 1)
        z = cmath.exp(2j * cmath.pi / M)
        w = z ** (3 ** r)
        for j in range(0, 3 ** r):
            lhs = z ** j * coeff(z, predStep(L), 3 * j)
            rhs = z ** j * coeff(z, L, 6 * j) + \
                  sum(w ** s * coeff(z, L, 2 * j + s * 3 ** r) for s in range(3)) / 3
            worst = max(worst, abs(lhs - rhs) / max(1.0, abs(lhs)))
            # the weight identity: omega^(-2s) == omega^s
            for s in range(3):
                worst_w = max(worst_w, abs(w ** (-2 * s) - w ** s))
    if d % 5 == 0:
        print(f"depth {d:>3}  |L| {len(L):>6}   worst relative error {worst:.3e}")
print(f"\nlevels 1..20, conductors 3^1..3^4, every index j")
print(f"worst relative error in the identity : {worst:.3e}")
print(f"worst |omega^(-2s) - omega^s|        : {worst_w:.3e}")
