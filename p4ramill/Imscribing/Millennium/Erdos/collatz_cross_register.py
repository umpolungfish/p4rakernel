"""Where the contraction actually comes from, in the l2 register.

Writing S_j for the doubling term and F_j for the feed at conductor r, and
Q_r = sum over primitive j of |mu_hat(j,r)|^2, the level map gives exactly

    Q_r(d+1) = rho^2 ( Q_r + Q_F + cross ),   cross = 2 Re sum_j S_j conj(F_j)

so the level contracts precisely when

    Q_F/Q_r + cross/Q_r  <  1/rho^2 - 1   ( ~ 0.79 at rho = 3/4 )

This measures both terms.  Averages are geometric or median throughout: the
arithmetic mean of a ratio is dominated by single levels and says nothing.
"""
import cmath, math, statistics

def predStep(L):
    out = set()
    for m in L:
        out.add(2 * m)
        if m % 3 == 2:
            out.add(2 * (m // 3) + 1)
    return out

def mus(S, N, M):
    cls = [0] * M
    for v in S:
        cls[v % M] += 1
    return [sum(c * cmath.exp(2j * cmath.pi * ((j * i) % M) / M)
                for i, c in enumerate(cls) if c) / N for j in range(M)]

L, lv = {1}, {}
for d in range(1, 31):
    L = predStep(L); lv[d] = set(L)
om = cmath.exp(2j * cmath.pi / 3)

print(f"{'r':>2} {'chars':>6} {'Q_F/Q_r':>9} {'cross/Q_r':>10} {'sum':>8} {'allowed':>8} "
      f"{'Q_F/(Q_{r+1}/3)':>16} {'cross<0':>8} {'geo Q ratio':>12} {'worst':>8}")
for r in (1, 2, 3, 4):
    M, Mp = 3 ** r, 3 ** (r + 1)
    idx = [j for j in range(1, M) if j % 3]
    idxp = [j for j in range(1, Mp) if j % 3]
    A = B = None; A, B, D, Qs = [], [], [], []
    neg = tot = 0; worst = -9.0
    for d in range(6, 30):
        S, N = lv[d], len(lv[d]); Sn, Nn = lv[d + 1], len(lv[d + 1])
        rho = N / Nn
        a = mus(S, N, M); b = mus(S, N, Mp); an = mus(Sn, Nn, M)
        Qr = sum(abs(a[j]) ** 2 for j in idx)
        Qr1 = sum(abs(b[j]) ** 2 for j in idxp)
        QF = cross = 0.0
        for j in idx:
            s_t = a[2 * j % M]
            f_t = cmath.exp(-2j * cmath.pi * j / Mp) * sum(
                om ** s * b[(2 * j + s * M) % Mp] for s in range(3)) / 3
            QF += abs(f_t) ** 2
            cross += 2 * (s_t * f_t.conjugate()).real
        A.append(QF / Qr); B.append(cross / Qr); D.append(QF / (Qr1 / 3))
        Qs.append(sum(abs(an[j]) ** 2 for j in idx) / Qr)
        tot += 1; neg += (cross < 0)
        worst = max(worst, (QF + cross) / Qr - (1 / rho ** 2 - 1))
    m = statistics.median
    print(f"{r:>2} {len(idx):>6} {m(A):>9.4f} {m(B):>10.4f} {m(A) + m(B):>8.4f} "
          f"{0.7918:>8.4f} {m(D):>16.4f} {neg:>4}/{tot:<3} "
          f"{math.exp(sum(map(math.log, Qs)) / len(Qs)):>12.4f} {worst:>+8.3f}")
print("\n'worst' is max over levels of (sum - allowed); negative means every level contracts.")
print("Q_F <= Q_{r+1}/3 is proved (Cauchy-Schwarz on the cube-root vector); the")
print("measured Q_F sits near a third of that bound, which is the cancellation")
print("inside the feed and is the quantity still unproved.")
