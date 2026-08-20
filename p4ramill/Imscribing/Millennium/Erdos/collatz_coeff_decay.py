"""Does the level's coefficient vector live in the weighted norm?

The weighted-norm contraction uses  ||a||_w = sup_{j,r} w^{-r} |a(j,r)|, which is
finite only if the coefficients decay like w^r in the conductor.  This measures
whether the tree's do.  They do not: they rise toward one, because once 3^r
exceeds the spread of a level its N_d points cannot occupy 3^r classes.
"""
import cmath

def predStep(L):
    out = set()
    for m in L:
        out.add(2 * m)
        if m % 3 == 2:
            out.add(2 * (m // 3) + 1)
    return out

L, lv = {1}, {}
for d in range(1, 25):
    L = predStep(L); lv[d] = set(L)

print("max over primitive j of |mu_hat_d(j,r)|\n")
print(f"{'d':>3} {'N':>7} " + "".join(f"  r={r:<7}" for r in range(1, 9)))
for d in (8, 12, 16, 20, 24):
    S, row = lv[d], []
    N = len(S)
    for r in range(1, 9):
        M = 3 ** r
        cls = [0] * M
        for v in S:
            cls[v % M] += 1
        best = 0.0
        for j in range(1, M):
            if j % 3 == 0:
                continue
            s = sum(c * cmath.exp(2j * cmath.pi * ((j * i) % M) / M)
                    for i, c in enumerate(cls) if c)
            best = max(best, abs(s) / N)
        row.append(f"  {best:<9.4f}")
    print(f"{d:>3} {N:>7} " + "".join(row))
print("\nthe weight at w = 0.3 demands, for r = 1..8:")
print("      " + "".join(f"  {0.3 ** r:<9.4f}" for r in range(1, 9)))
print("\nSo ||mu_hat_d||_w is infinite and the weighted contraction, though true of")
print("the operator, is not a statement about this tree.")
