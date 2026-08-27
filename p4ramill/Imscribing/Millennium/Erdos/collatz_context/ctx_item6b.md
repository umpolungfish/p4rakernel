# Item 6, re-asked: bound the cycle from inside, not from outside

File: /home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing/Millennium/Erdos/CollatzDepthSplit.lean
*sans* sorry. See ctx_item6.md for the full cycle apparatus; this restates the ask.

## Why the first ask leaked

The previous ob3ect (collatz_item6_margin) asked for an external Diophantine bound
|2^k - 3^j| >= 2^k/f(k) and then applied it. Its banked-count check came back

    banked_ok            false
    weight_lost_in_open  4
    restored             0
    exposed clear        step 10, the reversal that bounds the minimum n+1
    verdict   "4 unit(s) of weight cleared with nothing banked behind them:
               the count was in the open when the reversal came"
    remedy    "open the region that holds the result BEFORE the region that
               computes it, and close them in that order"

Its word fused at step 7 before the clear at step 10, so the deposit was gone when the
reversal arrived. Prove-then-apply is compute-then-clear, and the count is in the open.

## The margin is not external

cycle_banked is an identity, not an estimate:

    col^[k] n = n   ->   (n+1)(2^k - 3^j) = bank n k          exactly, in Z

so the margin IS bank(n,k)/(n+1), determined by the cycle itself. Nothing outside is
needed to know it; what is needed is to work inside the assumption where it is fixed.

## Everything available inside the assumption (all proved, *sans* sorry)

Let n be the minimum of a cycle of length k with j = oddSteps n k odd steps.

    cycle_margin_pos      3^j < 2^k, so the margin is at least 1, with no Diophantine
                          input: bank is a count so 2^k >= 3^j, and two_pow_ne_three_pow
                          rules out equality since 2^k is even and 3^j odd

    cycle_last_step_even  the cycle cannot close on an odd step
    bank_ge_of_last_even  2^(k-1) <= bank n k
    cycle_margin_lower    2^(k-1) <= (n+1)(2^k - 3^j)

    suffix_contracts      every suffix contracts: 3^(o_i) <= 2^(k-i)
    bank_le_of_suffix     bank n k <= (k - j) 2^k
    cycle_min_bound       (n+1)(2^k - 3^j) <= (k-j) 2^k
    cycle_min_le          n + 1 <= (k-j) 2^k

    so                    2^(k-1)/(2^k - 3^j)  <=  n+1  <=  (k-j) 2^k/(2^k - 3^j)
                          n+1 is pinned by the margin within a factor of 2k

    cycle_ratio_tight     3^(j+1) <= 2^k  ->  2(n+1) <= 3(k-j)
                          so either 3^j < 2^k < 3^(j+1), pinning k/j against log2 3
                          within one power of three, or the minimum is at most 3(k-j)/2

    cycle_congruence      (n+1) 3^j + bank n k = (n+1) 2^k, so 2^k divides the left side
    two_three_coprime     3^j is a unit mod 2^k
    k_lt_two_pow          k < 2^(k-2) for k >= 5
                          3 has order 2^(k-2) mod 2^k, and j < k < 2^(k-2), so
                          j -> 3^j mod 2^k is injective on the admissible range: given
                          n mod 2^k and bank mod 2^k the exponent j is DETERMINED

    residue_determined    same oddSteps and banked counts agreeing mod 2^k force the
                          same n mod 2^k

    iterate_banked        2^k (col^[k] n + 1) = 3^j (n+1) + bank n k, every n and k
    descends_iff_banked   col^[k] n < n  <->  bank n k < (2^k - 3^j)(n+1)
                          note a cycle is the equality case: bank = (2^k - 3^j)(n+1)

## The shape asked for

Hold the cycle open as the frame. Inside it the margin, the exponent and the residue are
all determined by each other (cycle_banked, cycle_congruence, k_lt_two_pow). Compute
within that frame and let the clear fall while the count is still held, rather than
deriving a bound and reversing it onto n afterwards.

Two directions that stay inside:

1. The two brackets on n+1 differ by a factor of 2k and both scale as 1/margin, so they
   do not close against each other directly. Something that pins the ratio - for
   instance bank n k relative to (k-j) 2^k, where bank is a sum of k-j terms
   3^(o_i) 2^i with o_i decreasing - would close the gap from inside.

2. The exponent is pinned mod 2^(k-2) by cycle_congruence. A cycle also forces
   3^j < 2^k < 3^(j+1) unless its minimum is at most 3(k-j)/2. Combining the congruence
   with that pinning constrains (j,k) to a thin set; making that set finite, or empty
   above a computable k, closes the cycle half.

## What not to do

Do not seek an external bound on |2^k - 3^j| and apply it afterwards; that is the shape
that leaked. Do not appeal to numerical verification of a range as if it were a proof.
Do not reprove anything in the list above.
