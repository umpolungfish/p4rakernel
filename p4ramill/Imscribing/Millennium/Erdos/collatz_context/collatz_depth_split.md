# The depth-k residue split for the shortcut Collatz map

## What it is

The shortcut map is `T(n) = n/2` on evens and `T(n) = (3n+1)/2` on odds. Split
the integers by residue mod `2^k` and iterate `k` times. On each class the
iterate is affine, and its multiplier is a single integer read off the class:

    T^k(2^k t + r) = 3^(j(r,k)) t + T^k(r)

where `j(r,k)` is the number of odd steps taken from `r` in `k` steps. The class
contracts exactly when `3^j < 2^k`, that is when

    j/k < log 2 / log 3 = 0.630930

That ratio is the coordinate. It is graded, it is computed from the class, and
it replaces the per-arm contraction claims that a fixed trace suggests.

Lean: `p4ramill/Imscribing/Millennium/Erdos/CollatzDepthSplit.lean`, sorry-free
on propext / Classical.choice / Quot.sound. `col_shift` is the affine identity,
`col_lt_of_gap` turns the gap `2^k - 3^j` into descent for the whole class.
The census script is `collatz_depth_split.py` beside it.

## What contracts

`col_lt_of_gap` says: if `3^j + m = 2^k` and `T^k(r) < r + m`, then every
`n = 2^k t + r` with `t ≥ 1` descends within `k` steps. Measured over `k ≤ 12`,
the constant clears that bar in every contracting class, so the only members not
covered are the residues themselves at `t = 0`: `r = 1` at every `k`, and
`r ∈ {7, 9, 19, 25}` at `k = 8`. Each is one explicit integer, computed.

At depth four this gives `T^4(16t+3) = 9t+2 < 16t+3` for all `t`, which is
`col4_16t3_contracts`.

## What grows

Three classes that a fixed-depth trace reads as contracting do the opposite, for
every member and not only at a base case:

    T^4(16t+7)  = 27t+13   against 16t+7    j/k = 3/4
    T^5(32s+15) = 81s+40   against 32s+15   j/k = 4/5
    T^6(64u+31) = 243u+121 against 64u+31   j/k = 5/6

`col4_16t7_grows`, `col5_32s15_grows`, `col6_64u31_grows` state the growth in
Lean. The differences are `11t+6`, `49s+25`, `211u+90`, positive at `t, s, u = 0`
and increasing, so there is no threshold above which they turn.

The `31 (mod 32)` class also splits at step six rather than continuing: from
`T^5(32s+31) = 243s+242`, which is even exactly when `s` is even, since
`243s + 242 ≡ s (mod 2)`. The two halves are

    T^6(64u+31) = 243u+121        s even, a halving
    T^6(64u+63) = 729u+728        s odd, a sixth odd step

`col5_32s31`, `col6_64u31`, `col6_64u63`. Reading `243s+242` as even for all `s`
puts `T^6(63) = 364` where the map gives `728`.

## What no depth reaches

The residue `r = 2^k - 1` takes an odd step at every one of the `k` steps, so its
multiplier is `3^k` against `2^k` and its ratio is `1`. That holds at every
depth: `oddSteps_pred_two_pow` proves `j(2^k - 1, k) = k` by induction through
`col(3^i 2^(m+1) - 1) = 3^(i+1) 2^m - 1`, and `not_contracts_pred_two_pow` reads
off `¬ Contracts k (2^k - 1)` for `k ≥ 1`.

So depth is the wrong budget to spend. Refining `k` closes every class whose odd
fraction falls below `0.630930` and leaves the all-odd class standing at every
level. The next rung is a criterion that reads the class rather than the depth:
the surviving classes at depth `k` are those with `j > k log2/log3`, and what
closes them is the arithmetic of the constant `T^k(r)`, not another halving.

## The census

Odd residues mod `2^k`, contracting against surviving, by depth.

| k | odd residues | contract | survive | surviving fraction |
|---|---|---|---|---|
| 4 | 8 | 4 | 4 | 0.5000 |
| 5 | 16 | 11 | 5 | 0.3125 |
| 6 | 32 | 16 | 16 | 0.5000 |
| 7 | 64 | 42 | 22 | 0.3438 |
| 8 | 128 | 99 | 29 | 0.2266 |
| 9 | 256 | 163 | 93 | 0.3633 |
| 10 | 512 | 382 | 130 | 0.2539 |
| 12 | 2048 | 1486 | 562 | 0.2744 |
| 14 | 8192 | 5812 | 2380 | 0.2905 |
| 16 | 32768 | 27824 | 4944 | 0.1509 |
| 18 | 131072 | 109294 | 21778 | 0.1662 |
| 20 | 524288 | 430104 | 94184 | 0.1796 |
| 22 | 2097152 | 1695222 | 401930 | 0.1917 |
| 24 | 8388608 | 7507638 | 880970 | 0.1050 |

The fraction falls with a sawtooth rather than monotonically, because the test
`3^j < 2^k` moves in integer steps: the admissible `j` ceiling advances only when
`k log2/log3` crosses an integer, so a `k` that gains no new `j` loses ground to
the binomial spread. The surviving residues at depth four are `7, 9, 11, 15`
(mod 16) and at depth five `7, 9, 15, 27, 31` (mod 32); `survivors_mod_16` and
`survivors_mod_32` prove both by `decide`.

## The protocol reading

`⊙∈≻≻∋◻` closes as a shape, and the arms are what have to be imscribed onto it.
FSPLIT forks on `r` mod `2^k`, the forward steps are the `k` iterations, and
FFUSE requires each arm to arrive strictly below where it entered. The classes
with `j/k > 0.630930` never reach the fuse, and the all-odd class provably never
reaches it at any depth, so the fork is real and the fusion is partial: a B at
the level of the split, with the surviving fraction as its coordinate.

## The composition census: what survives every depth at once

Fixed depth is one block. Composing blocks means asking for the classes that
contract at no depth up to `k`, which is `Survives k r := ∀ i ≤ k, ¬ Contracts i r`.
The first `k` parities depend only on `r` mod `2^k` (`oddSteps_mod`, and
`contracts_mod_le` carries it to every earlier depth), so these classes form a
tree: a survivor mod `2^k` has two lifts mod `2^(k+1)`, and one new step decides
each.

The tree never dies, and the reason is one line. A survivor has `3^j ≥ 2^k`. An
odd step sends `3^j` to `3^(j+1)` while `2^k` only doubles, so an odd step can
never turn a survivor into a contractor: `survives_succ_of_odd`. Since `3^j` is
odd, the two lifts of a class differ in the parity of their `k`-th step by the
shift identity, so exactly one of them takes the odd step and survives:
`exists_survivor_lift`, and by induction `survivors_nonempty` gives a surviving
class at every depth. That is the bound on the method, proved rather than
observed: no `k` exhausts the split, and the all-odd class is one witness among
many.

When a survivor has slack, `2^(k+1) ≤ 3^j`, both of its lifts survive
(`survives_succ_of_slack`, `both_lifts_survive`). Write `J(k)` for the least `j`
with `3^j ≥ 2^k`. At a depth where `J(k+1) = J(k)` every survivor has slack, so
the count doubles exactly and the density is unchanged; at a depth where `J`
advances, the classes sitting at the old minimum lose their even lift. The census
shows exactly that, with branch factor `2.000` at `k = 3, 6, 9, 11, 14, 17, 19,
22, 25, 28, 30` and the `J` table advancing at every other level.

| k | survivors | density | branch |
|---|---|---|---|
| 4 | 3 | 0.187500 | 1.500 |
| 5 | 4 | 0.125000 | 1.333 |
| 6 | 8 | 0.125000 | 2.000 |
| 8 | 19 | 0.074219 | 1.462 |
| 10 | 64 | 0.062500 | 1.684 |
| 12 | 226 | 0.055176 | 1.766 |
| 14 | 734 | 0.044800 | 2.000 |
| 16 | 2114 | 0.032257 | 1.632 |
| 18 | 7495 | 0.028591 | 1.773 |
| 20 | 27328 | 0.026062 | 1.823 |
| 22 | 93222 | 0.022226 | 2.000 |
| 24 | 286581 | 0.017082 | 1.698 |
| 26 | 1037374 | 0.015458 | 1.810 |
| 28 | 3524586 | 0.013130 | 2.000 |
| 30 | 12771274 | 0.011894 | 2.000 |

The surviving residues are `7, 11, 15` mod 16 and `7, 15, 27, 31` mod 32
(`survivors_survive_mod_16`, `survivors_survive_mod_32`), and by depth seven the
list is `27, 31, 39, 47, 63, 71, 79, 91, 95, 103, 111, 123, 127` mod 128. Over
`k = 20` to `30` the density falls by a factor 2.19 while the survivor count grows
by 1.79 per level; that window is still far from the asymptotic rate, which the
next section reads off directly. Both are true at once
and that is the shape of the object: an ever larger set of ever thinner density,
which is why counting survivors reads as progress and measuring them reads as
decay.

The census is `collatz_survivor_tree.py` with its output in
`collatz_survivor_census.txt`, both beside the Lean file.

## The constant, and why the class criterion is exact

Survival was stated as a condition on the multiplier alone, `3^j ≥ 2^k`, saying
nothing about the constant `col^[k] r`. The constant turns out to be determined
by it. Every odd step sends `n` to `(3n+1)/2 ≥ 3n/2` and every even step to
exactly `n/2`, so the iterate obeys

    3^(oddSteps r k) * r ≤ 2^k * col^[k] r

with no error term, proved by induction as `pow_mul_le_iterate`. A class that has
not contracted has `3^j ≥ 2^k`, and dividing gives `r ≤ col^[k] r`
(`le_iterate_of_not_contracts`). Feeding that back through the shift identity,

    2^k * t + r ≤ col^[k] (2^k * t + r)   for every t

which is `no_member_descends`. So a surviving class contains no member that
descends within `k` steps, at any `t`, and the multiplier test is exact rather
than sufficient-with-exceptions. The census that motivated this measured it
first: over every survivor to `k = 20` there is not one class with `col^[k] r < r`.

Two consequences. The set of `n` with no descent within `k` steps is exactly the
union of the surviving classes, up to the finitely many small members of
contracting classes that `col_lt_of_gap` leaves at `t = 0`, so the densities in
the table above are exact rather than upper bounds. And the direction of the
whole split is settled: what a deeper `k` can buy is entirely governed by the
multiplier `3^j` against `2^k`, since the constant never rescues a class and
never spoils one.

Vox reads the module with no `B` and no `F`: sixteen `T` and forty-seven `N`,
where the `T` set is exactly the theorems that fork on a case — the survivor
lifting, the parity split, the induction on depth — and the `N` set is the linear
computations. The fork the protocol asks for is present where the class analysis
actually forks, and nowhere else.

## The slack coordinate and the decay rate

Write a survivor's coordinate as its slack

    s(r, k) = j * log2 3 - k ,   j = oddSteps r k ,

which survival makes non-negative. One more step moves it by `log2 3 - 1 =
0.5849625` on an odd step and by `-1` on an even one, so the survivor tree is
exactly the two-step walk conditioned to stay non-negative, and the all-odd class
is its upper envelope at `s = 0.5849625 k`. Measured mean slack across survivors
sits near 2.6 and drifts up slowly.

The branching is a dichotomy in that coordinate, both halves proved.
`survives_succ_of_slack` keeps both lifts when `2^(k+1) ≤ 3^j`, that is when
`s ≥ 1`; `contracts_succ_of_even_step` and `not_survives_succ_of_even_step` kill
the even lift when `s < 1`, since an even step leaves the multiplier where it is
while the divisor doubles past it. So with `A_k` the survivors carrying slack and
`B_k` those without,

    S_(k+1) = 2 * A_k + B_k

and the census confirms it level by level: at `k = 20`, `A = 19283` and
`B = 8045` give `46611`, which is the count at `k = 21`.

Because the survival condition reads only `j`, the residue tree can be replaced
by a DP on the odd-step count, `collatz_slack_dp.py`, which reaches `k = 2000`
where the tree stops near 30. That makes the decay rate readable rather than
extrapolated. The walk has step mean `(log2 3 - 2)/2 < 0`, so the probability of
staying non-negative decays at the Chernoff rate

    rho = min over theta of ( e^(theta (log2 3 - 1)) + e^(-theta) ) / 2
        = 0.96590655   at   theta* = ln(1/c) / log2 3 ,  c = log2 3 - 1

which is `log2 rho = -0.05004447`: the surviving density halves every 19.98
levels of depth. The DP agrees and converges to it from below, the per-level
density factor being 0.96400 over `k = 500..1000` and 0.96493 over
`k = 1000..2000`. The shortfall is the polynomial prefactor: fitting
`density ≈ C rho^k k^(-alpha)` gives `alpha = 1.36, 1.41, 1.43, 1.46` on the
windows `200..400`, `400..800`, `500..1000`, `1000..2000`, climbing toward the
`3/2` that a walk conditioned to stay non-negative carries.

That fixes the price of the method. Each level of depth costs a doubling of the
modulus and buys a factor `0.9659` in the density of what is left, so closing the
surviving classes by depth alone would need a modulus growing like `2^(20 b)` for
each further factor `2^(-b)`, while the classes themselves keep growing at
`1.79` per level. The exactness result says none of that can be improved by
attending to the constants, so a further rung has to change the coordinate rather
than the depth.

## What the Grammar says about the split, and the reading it names

The protocol word for the depth split, `⊙∈≻≻∋◻`, imscribes to
⟨𐑨 𐑶 𐑾 𐑹 𐑞 𐑘 𐑔 𐑠 𐑣 𐑫 𐑳 𐑭⟩ at crystal address 7749838. Chirality is 𐑫, wool,
inexhaustible memory; kinetics is 𐑘, yea, untrapped. That pair is exactly what
`InfiniteMemoryNeedsSlowKinetics` refuses: wool admits only egg or on. The word
asks to hold the entire parity vector while reading at the fastest rate, which is
what a depth-`k` split does when it spends one doubling of the modulus per level
and reads all `k` parities at once.

`weight` shows the consequence without reference to the axiom. The word seeds one
register, opens a frame at depth 1, fuses, and ends `surviving: none` — deposits
0, cleared 0, restored 0. Nothing is banked. That is the same fact as the
exactness result above: the constant `col^[k] r` is inert, so the split carries no
content past its own verdict. `banked` reads the word vacuous, and `insert`
reports that no single glyph repairs it, so the repair is a different word rather
than a patch. `cycle` shows the verdict `T` invariant under every rotation, so the
closure is not an artifact of where the reading is cut.

Two repairs are admissible for wool. Dropping to a finite chirality — 𐑖, sure,
with kinetics left at yea — composes to `◻⊞◻⊞⊤≻⋈⊞⊥⋈≺⊤`, which verdicts `N`:
ten inert steps, nothing seeded, no fork at all. A bounded-memory reading of the
trajectory never forks, so it cannot be the closing structure. Keeping wool and
slowing to egg composes to `⊢⋈⊞⊤≺◻⊙∈⊤⊙≺∋`, verdict `T` but again
`surviving: none`. Keeping wool and pairing with on — kinetically trapped by
order — composes to `⊢⋈⊞⊤≺⋈⊙∈⊤⊙≺∋`, verdict `T` with `surviving: T×1`,
deposits 3, restored 1, nothing inert. It is the only one of the three that banks
anything. `insert` then names the missing piece precisely: an `∈` at position 1,
2 or 3, three words holding out of 156 tried, every one of them opening a frame
*before* the region that computes. Trapped by order, holder opened first.

The rotations separate the four words further. The depth split is `T` at every
cut with a single landing, rotation-invariant: a loop that closes carrying neither
phase nor content. The finite-chirality word is `N` at every cut and repairable at
none. The wool-egg word is `T` at every cut with two landings, and the wool-on
word is `T` at every cut with four — `T`, `N`, `tf`, `Ttf` — the most phase any of
them carries.

The repaired words are `B`, and they stay `B`: `insert` reports each already
holds, so the open fork is their state rather than a stage. `banked` reads them
`OK — weight survived 2 live clears by being banked`, with nothing inert. So the
trade is exact. The depth split closes vacuously; the holder-first reading carries
the content and leaves the fork open, which is what an unclosed problem looks like
when the reading is honest about where the arm is.

The three repairs are not equivalent. Stranded in frames never fused is 3, 3 and
1, the last for `⊢⋈⊞∈⊤≺⋈⊙∈⊤⊙≺∋`, where the frame opens after the `⊞` deposit
rather than before it: the multiplicity is held outside the frame and only the
target inside. Read into the tree, that says the branch count belongs to the
level and not to any target in it, which is `card_predStep` below.

Read that back into the map and it is the predecessor tree. Forward, the branch is
free: both parities are available at every class, so the object is all `2^k`
residues with a filter laid over them, and the filter is the whole content.
Backward, the target is fixed before any step is taken and the branch becomes
arithmetic.

## The predecessor tree

Every `m` has the predecessor `2*m`. It has a second, odd predecessor exactly when
`m ≡ 2 (mod 3)`, and then it is `2*t+1` for `m = 3*t+2`, with no division and no
parity side condition to check: `col (2*t+1) = 3*t+2` outright. `col_two_mul`,
`col_odd_pred`, `preimage_cases` and `odd_pred_iff` are those four facts, and
`preimage_cases` shows there is nothing else. Vox verdicts all of them `T`, where
the forward class identities all read `N` — the holder-first reading forks where
the forward one does not.

No filter is needed here, because every path in this tree is a trajectory. The
census, cutting the `1 → 2 → 1` cycle edge at the root, converges cleanly:

| k | nodes | branch | `m ≡ 2 (mod 3)` | odd fraction |
|---|---|---|---|---|
| 20 | 488 | 1.3297 | 0.3297 | 0.2500 |
| 25 | 885 | 1.3308 | 0.3308 | 0.2486 |
| 30 | 3765 | 1.3309 | 0.3309 | 0.2486 |
| 35 | 15844 | 1.3339 | 0.3339 | 0.2503 |
| 40 | 66763 | 1.3335 | 0.3335 | 0.2501 |

The branch factor is `4/3`: one third of the nodes carry the extra predecessor,
and a quarter of all nodes are odd, which is the same third counted one level
down. The tree grows like `(4/3)^k` against the forward `2^k`, and its largest
member at level `k` is exactly `2^k`, the all-doubling path.

So the two readings are exponentially small in complementary ways, and that is the
graded shape of the object. Forward leaves a density `≈ C · 0.9659^k · k^(-3/2)`
of classes unresolved while banking nothing. Backward certifies a set of size
`(4/3)^k` inside `[1, 2^k]`, which is a density `(2/3)^k` of the interval, but
every member of it is a finished trajectory. The forward reading is dense and
inert; the backward one is sparse and load-bearing.

### The level recursion, and the branch factor measured

`predStep L` is one level of the tree: the doubling image of `L` together with the
odd image of its `2 (mod 3)` part. The two are disjoint by parity and both maps
are injective there, so

    (predStep L).card = L.card + (L.filter (· % 3 = 2)).card

which is `card_predStep`, with `mem_predStep_col` confirming every member maps
back into `L` under one step. The branch multiplicity is therefore a property of
the level, exactly as the frame reading said, and the per-level branch factor is
`1 + p₂` where `p₂` is the fraction of the level sitting at `2 (mod 3)`.

Whether that fraction is `1/3` is a measurement, not a definition. Building the
substitution matrix on residues mod `3^r` and reading its Perron root returns
`4/3` at every `r`, but that construction spreads each lift uniformly and so
assumes what it reports. Taken off the real tree instead, `p₂` runs
`0.3412, 0.3346, 0.3327, 0.3334` at `k = 25, 28, 32, 38`, and the deviation from
uniform decays with the modulus refinement: relative maximum deviation `0.010`
mod 9 and `0.031` mod 27 at `k = 38`, both falling. So `4/3` is the measured limit
of an exactly computable per-level rational, and the equidistribution that would
make it exact is the thing still to prove.

### The gap, and why it has to be measured

Both maps that build a level are bijections on residues mod `3^r`. Doubling is,
because 2 is a unit there — `two_coprime_three_pow`, `double_inj_mod` and
`two_inv_mod` give injectivity and the explicit inverse `(3^r+1)/2` — and
`t ↦ 2*t+1` is that map after a shift, `odd_map_inj_mod`. So a level
equidistributed mod `3^(r+1)` yields one equidistributed mod `3^r`, taking `3c`
per class from the doubling image and `c` from the odd image: the `4/3`, exactly.

The cost is one 3-adic digit of resolution per level. Certifying uniformity mod
`3^r` at level `k` that way would need uniformity mod `3^(r+k)` at level 0, and
level 0 is a single point. So uniformity cannot be propagated forward from the
root; it can only arrive by mixing, and the mixing rate is a measurement.

Taken off the tree, the deviation from uniform decays geometrically. Over
`k = 32..40` the eight-level rate runs `0.81` to `0.87` on residues mod 27 and
`0.75` to `0.95` on mod 9 and mod 3, where the counts are small enough to be
noisy. Deviation mod 27 falls from `0.298` at `k = 25` to `0.025` at `k = 40`.
That gap is what makes `4/3` the limit rather than merely the fixed point, and
pinning its value is the open quantity here.
