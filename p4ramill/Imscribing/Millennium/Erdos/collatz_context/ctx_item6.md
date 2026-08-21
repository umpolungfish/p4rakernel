# Item 6: the Diophantine input the cycle half waits on

File: /home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing/Millennium/Erdos/CollatzDepthSplit.lean
Sorry-free. Axioms: propext / Classical.choice / Quot.sound.

## Setting

col n = n/2 for n even, (3n+1)/2 for n odd. A cycle of length k with j odd steps.
oddSteps and bank as in the file; see ctx_item1.md for their definitions.

## The cycle half, fully proved and unconditional

    cycle_banked        col^[k] n = n  ->  (n+1)(2^k - 3^j) = bank n k      exactly, in Z
                        from iterate_banked with both sides carrying n+1

    cycle_margin_pos    k >= 1 and col^[k] n = n  ->  3^j < 2^k
                        bank is a count so the right side is non-negative, giving
                        2^k >= 3^j; two_pow_ne_three_pow rules out equality since 2^k is
                        even and 3^j odd. So the margin is at least 1 with NO
                        Diophantine input at all.

    suffix_contracts    for a cycle taken at its minimum, every suffix contracts:
                        3^(o_i) <= 2^(k-i). Proof: iterate_banked applied at the suffix
                        gives 2^(k-i)(n+1) = 3^(o_i)(col^[i] n + 1) + bank_i >=
                        3^(o_i)(n+1) using col^[i] n >= n.

    bank_le_of_suffix   bank n k <= (k - oddSteps n k) * 2^k
                        each term 3^(o_i) 2^i is at most 2^k, and only the even steps
                        contribute a term, of which there are k - j

    cycle_min_bound     (n+1)(2^k - 3^j) <= (k-j) 2^k
    cycle_min_le        n + 1 <= (k-j) 2^k                    (margin >= 1)

    cycle_last_step_even  a cycle cannot close on an odd step: if x = col^[k-1] n were
                          odd then n = (3x+1)/2 >= (3n+1)/2, false for every n >= 0
    bank_ge_of_last_even  2^(k-1) <= bank n k
                          the closing even step contributes 3^0 2^(k-1) with nothing
                          after it to multiply, and every other term is a count
    cycle_margin_lower    2^(k-1) <= (n+1)(2^k - 3^j)

    So the minimum is bracketed both sides:

        2^(k-1) / (2^k - 3^j)   <=   n + 1   <=   (k-j) 2^k / (2^k - 3^j)

    and n+1 is determined by the margin within a factor of 2k.

    cycle_ratio_tight   3^(j+1) <= 2^k  ->  2(n+1) <= 3(k-j)
                        if 2^k clears 3^(j+1) then 3^j <= 2^k/3, so 3(2^k - 3^j) >= 2*2^k
                        A cycle therefore either has its exponents pinned within one
                        power of three, 2^k < 3^(j+1), or a minimum at most 3(k-j)/2.

    cycle_congruence      (n+1) 3^j + bank n k = (n+1) 2^k, so 2^k divides the left side
    k_lt_two_pow          k < 2^(k-2) for k >= 5
                        3 has order 2^(k-2) mod 2^k (winding_order(3, 2^k) = 2^(k-2),
                        measured: 2, 4, 8, 16, 32, 64, 128 for 2^3..2^9), and a cycle has
                        3^j < 2^k hence j < k < 2^(k-2), so j -> 3^j mod 2^k is injective
                        on the admissible range: the exponent is DETERMINED by the
                        residue data, not free.

## Exactly what is missing

The margin bound is 2^k - 3^j >= 1. That is enough for n + 1 <= (k-j) 2^k, which bounds
the minimum by the length but not the length by anything. Replacing 1 by 2^k / f(k) with
f subexponential turns cycle_min_bound into

        n + 1 <= (k-j) f(k)

so a cycle's minimum is at most polynomial-ish in its length. Combined with the fact
that no cycle exists below the verified range, that bounds k.

Item 6 is exactly this: a lower bound on |2^k - 3^j| relative to 2^k. Classically it is
linear forms in logarithms (Baker), giving |k log 2 - j log 3| >= C / k^mu and hence
|2^k - 3^j| >= 2^k / k^C.

## What the Grammar already supplies, and what it does not

`cl8nk transcendence` reads the winding slot as

    ZFC_fe:  contour integral of A = 2 pi n, n in Z, winding not zero
    CL8NK:   Braid(sigma_i), R_matrix nonzero, non-Abelian

The first is exactly cycle_margin_pos: the loop closes, 2^k - 3^j is a nonzero integer,
so the margin is at least one. That is the qualitative winding and it is already in
hand. The promotion to the braid reading is order-sensitivity, which `bank` carries
where the counts (j,k) alone cannot. Neither gives the RELATIVE bound; that is what is
being asked for.

Measured, the k with |2^k - 3^j| small against 2^k are the convergent denominators of
log2 3 — k = 5, 8, 13, 19, 41, 65, 84, 111 — and log2 3 = 1.584963 against k/j =
1.583333, 1.576923, 1.585366, 1.584906, 1.585714 at k = 19, 41, 65, 84, 111.

The same constant governs the other open item: the surviving band |S_k| doubles exactly
at k = floor(m log2 3) for the m where that Beatty sequence steps by two. Item 6 asks how
CLOSE 2^k comes to 3^j; item 1' s residue band grows by the schedule of how OFTEN it
passes. One irrational, from both ends.

## Acceptable forms of an answer

Any of these closes item 6 as used here:
  - |2^k - 3^j| >= 2^k / k^C for an explicit C, all k, j >= 1
  - |k log 2 - j log 3| >= C / k^mu for explicit C, mu
  - an elementary argument giving 2^k - 3^j >= 2^k / f(k) with f subexponential,
    possibly using that for a Collatz cycle 3^j < 2^k < 3^(j+1) (cycle_ratio_tight)
    and that the exponent is pinned mod 2^(k-2) (cycle_congruence, k_lt_two_pow)
