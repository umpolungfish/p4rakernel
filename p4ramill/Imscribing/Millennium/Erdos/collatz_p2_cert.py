"""Weight certificate for the growth rate of the Collatz predecessor tree.

Dead classes 0,3,6 mod 9 carry weight zero: doubling fixes 0 and swaps 3,6, and
class 0 mod 3 has no odd predecessor, so each such vertex spawns exactly one
child forever and contributes no growth.  On the six units doubling is the
6-cycle 1->2->4->8->7->5->1, and odd children inject at exactly two places:
class 2 mod 9 has an odd child = 1 mod 3, class 8 mod 9 one = 2 mod 3, class 5
mod 9 one = 0 mod 3 (weight zero).  The six requirements are

    w2            >= L w1        w4 + min(w1,w4,w7) >= L w2
    w8            >= L w4        w7 + min(w2,w5,w8) >= L w8
    w5            >= L w7        w1                 >= L w5

Taking the chain tight with w7 = 1 forces w5 = L, w1 = L^2, w2 = L^3,
w4 = L^4 - 1, w8 = L^5 - L, and the last requirement becomes  L^6 <= L^2+L+1.
"""
from fractions import Fraction as F

L = F(6, 5)
w = {0: F(0), 3: F(0), 6: F(0),
     7: F(3125), 5: F(3750), 1: F(4500), 2: F(5400), 4: F(3355), 8: F(4026)}

m147 = min(w[1], w[4], w[7]); m258 = min(w[2], w[5], w[8])
g = {1: w[2], 2: w[4] + m147, 4: w[8], 8: w[7] + m258, 7: w[5], 5: w[1]}
print(f"L = {L}   w = " + " ".join(f"w{j}={w[j]}" for j in (1,2,4,8,7,5)))
print(f"min(w1,w4,w7) = {m147}   min(w2,w5,w8) = {m258}")
for j in (1, 2, 4, 8, 7, 5):
    print(f"  j={j}: 5*g = {str(5*g[j]):>7}  >=  6*w = {str(6*w[j]):>7}   "
          f"slack {str(5*g[j]-6*w[j]):>7}   {'ok' if 5*g[j] >= 6*w[j] else 'FAIL'}")
print(f"\nL^6 = {L**6} <= L^2+L+1 = {L*L+L+1} : {L**6 <= L*L+L+1}")
t = 1.1644
print(f"at the target {t}: L^6 = {t**6:.5f}   L^2+L+1 = {t*t+t+1:.5f}   room {t*t+t+1-t**6:.5f}")

# --- verified against the real tree ---------------------------------------
level = {1}
print(f"\n{'d':>3} {'N':>8} {'f':>14} {'f(d)/f(d-1)':>12} {'>= 6/5':>7} {'N vs bound':>12}")
prevf = None
for d in range(1, 31):
    nxt = set()
    for m in level:
        nxt.add(2 * m)
        if m % 3 == 2:
            n = (2 * m - 1) // 3
            if n != 1:
                nxt.add(n)
    level = nxt
    f = sum(w[x % 9] for x in level)
    bound = F(4026, 5400) * L ** (d - 3) if d >= 3 else F(0)
    if d >= 3:
        r = f / prevf if prevf else None
        print(f"{d:>3} {len(level):>8} {str(f):>14} "
              f"{float(r) if r else 0:>12.5f} {'ok' if r is None or r >= L else 'FAIL':>7} "
              f"{len(level)} >= {float(bound):>8.2f} {'ok' if len(level) >= bound else 'FAIL'}")
    prevf = f
