# Item 1': the last open statement of the Collatz chain

File: /home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing/Millennium/Erdos/CollatzDepthSplit.lean
Sorry-free. Axioms: propext / Classical.choice / Quot.sound. Proof-term sweep: 134 T, 243 N, no B, no F.

## The map and the definitions

    col n = n/2        (n even)
    col n = (3n+1)/2   (n odd)                          -- the shortcut map

    oddSteps r 0     = 0
    oddSteps r (k+1) = (if r % 2 = 0 then 0 else 1) + oddSteps (col r) k

    Contracts k r    = 3 ^ oddSteps r k < 2 ^ k

    bank r 0     = 0
    bank r (k+1) = 2 * bank (col r) k
                   + (if r % 2 = 0 then 3 ^ oddSteps (col r) k else 0)

`bank` collects what the even steps contribute. In the coordinate u = n+1 an odd step
is exactly u -> (3/2)u and an even step is 2u' = u + 1; carrying 2^i u_i through the
iteration turns the inequality into an identity.

## What is already proved (do not reprove)

    iterate_banked      2^k * (col^[k] n + 1) = 3^(oddSteps n k) * (n+1) + bank n k
                        exact, for every n and k, by induction on k

    descends_iff_banked col^[k] n < n  <->  bank n k < (2^k - 3^j)(n+1)      in Z
                        an equivalence, no slack; divide iterate_banked by nothing

    descends_iff_quotient / descends_iff_point
                        the same criterion on a class decomposition n = 2^k t + r:
                        col^[k](2^k t + r) < 2^k t + r  <->  col^[k] r - r < (2^k - 3^j) t

    reaches_one_of_banked
                        (forall n > 1, exists k, bank n k < (2^k - 3^j)(n+1))
                          -> forall n >= 1, exists m, col^[m] n = 1
                        strong induction, with col_pos and iterate_col_pos keeping the
                        descent inside the positives

    col_shift           col^[k] (2^k t + r) = 3^(oddSteps r k) * t + col^[k] r
    no_member_descends  not (Contracts k r) -> 2^k t + r <= col^[k](2^k t + r)
    le_iterate_of_not_contracts   not (Contracts k r) -> r <= col^[k] r
    survives_all_never_descends   (forall k, not (Contracts k n)) -> forall k, n <= col^[k] n

    iterate_congruence  2^k divides 3^(oddSteps n k) * (n+1) + bank n k, every n and k
    residue_determined  same oddSteps and banked counts agreeing mod 2^k force the same
                        n mod 2^k; 3^j is a unit there (two_three_coprime)

## The part of item 1' already discharged, unconditionally

    descends_shallow            every n >= 2 with n % 4 != 3 descends within two steps.
                                n even halves at k=1; n = 4m+1 goes to 6m+2 then 3m+1,
                                below 4m+1 for m >= 1. Three quarters of N.

    descends_all_of_class       Contracts k r and col^[k] r < r  ->  every member of
                                r mod 2^k descends, with NO threshold on n. Proof: in
                                descends_iff_quotient the left side is negative and the
                                right is not.

    descends_three_mod_sixteen  every n = 3 mod 16 descends within four steps
                                (orbit 3,5,8,4,2; oddSteps 3 4 = 2; 9 < 16; col^[4] 3 = 2)

    descends_of_contracts_of_large / descends_of_class
                                Contracts k r and col^[k] r < t  ->  descent, for the
                                classes whose image is not below r

## Measured coverage, so the target is exact

Threshold-free coverage of descends_all_of_class by depth:

    k        3       4      5      7      8     10     13     16     20
    cover  0.375  0.5625  0.750 0.8281 0.8789 0.9062 0.9353 0.9542 0.9632

At k = 18, of 262144 residues: 251538 (0.959541) are threshold-free; 3111 (0.011868)
contract but with image not below r, covered above an explicit threshold; 7495
(0.028591) never contract at any depth <= 18. That last band is |S_k|/2^k and IS the
open part.

Surviving-class counts |S_k| for k = 1..24:
1, 1, 2, 3, 4, 8, 13, 19, 38, 64, 128, 226, 367, 734, 1295, 2114, 4228, 7495, 14990,
27328, 46611, 93222, 168807, 286581
|S_k|/2^k: 0.5, 0.25, 0.5, 0.3125, 0.1875, 0.3438, 0.2266, 0.1445, 0.2539, 0.1719,
0.2744, 0.1938, 0.1334, 0.2120, 0.1509, 0.1051, ..., 0.0222 at k = 22.

|S_k| = 2|S_(k-1)| exactly at k = 3, 6, 9, 11, 14, 17, 19, 22 (gaps 3,3,2,3,3,2,3),
which are floor(m log2 3) for the m where that Beatty sequence steps by two. The
mechanism: a class first contracts when 3^j first falls below 2^k, so classes leave
only at depths where 2^k crosses a fresh power of three; between consecutive powers of
three the surviving set doubles, every class taking both lifts.

## Routes already closed by measurement — do not spend on these

1. "No integer survives all depths" as a shortcut. The implication runs
   {survives all depths} SUBSET {counterexamples}, not the other way: descent implies
   Contracts (contrapositive of le_iterate_of_not_contracts), never the reverse, because
   pow_mul_le_iterate bounds col^[k] r from below. So emptying the meet removes one
   shape of counterexample without settling the conjecture. Also |S_k| grows and passes
   Fibonacci at k = 17, so the meet is a positive-dimension Cantor set in Z_2, not the
   point -1.

2. Density / equidistribution / the conductor tower. Delivers almost-all rather than
   all. The chain there is: level operator (level_operator, exact entry by entry),
   weighted norm, coefficient decay, equidistribution (levels_equidistribute). The
   density form reduces to q(3) = 1/3 exactly, where the requirement Lambda(z) >=
   2 sqrt(z/3) is AM-GM with equality at z = 3 and strict elsewhere — zero margin at a
   tangency, so no approximation from below arrives. Conductor tower to 3^16 gives
   density exponent 0.8896 and rising, never reaching 1.

3. Cycle-framed iteration. `ctc` prices nesting a value inside `cycle` as manufactured,
   support {T,F,N,B}, width 4, steps 4, price 3 — no pure fixed point, so any closure
   there is manufactured and carries no information. `meet` is one-shot, width 1,
   steps 0, price 0, which is the framing descends_iff_banked came from.

## What a proof would have to do

Exhibit, for each n > 1, a depth k at which the banked count falls short of the
contraction margin. Equivalently: show that no natural number lies in the intersection
of the surviving classes at every depth, AND that leaving the surviving band forces
descent rather than merely permitting it. The second half is what
descends_all_of_class supplies for 96.3% of residues; the open part is the band.
