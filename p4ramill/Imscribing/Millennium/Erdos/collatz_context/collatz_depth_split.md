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

Lean: `p4ramill/Imscribing/Millennium/Erdos/CollatzDepthSplit.lean`, *sans* sorry
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

`⊙∈≻≻∋⊡` closes as a shape, and the arms are what have to be imscribed onto it.
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

The protocol word for the depth split, `⊙∈≻≻∋⊡`, imscribes to
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
with kinetics left at yea — composes to `⊡⊞⊡⊞⊤≻⋈⊞⊥⋈≺⊤`, which verdicts `N`:
ten inert steps, nothing seeded, no fork at all. A bounded-memory reading of the
trajectory never forks, so it cannot be the closing structure. Keeping wool and
slowing to egg composes to `⊢⋈⊞⊤≺⊡⊙∈⊤⊙≺∋`, verdict `T` but again
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

## What the three ob3ects returned

All three ground full and all three verdict `T` at the Frobenius gate.

`collatz_level_contraction` types the level map with the doubling map at ≻, the
odd lift at ≺, the `2 (mod 3)` filter at ∈ and the cardinality sum at ∋, and it
puts the deviation bound at ⊡ as a permanent record chained forward by ⋈. Its
phase 6 prices the cycle at one 3-adic digit of resolution per level, and its B
state is the level simultaneously approaching `4/3` and retaining a non-zero
deviation. `collatz_open_arm` fuses the arm at level cardinality and prices the
same digit as the cost of maintaining `4/3`. `collatz_two_readings` fuses the
dense and sparse readings at a conserved **winding number** with ⊡ = 𐑭, integer
winding, and calls the fused result a scale-free state.

Two of the three ground with chirality 𐑖, sure, and kinetics 𐑧, egg: a descent
through rank at slow kinetics. That is an admissible pair, where the forward
depth-split word was wool with yea and was not.

### The recursion, corrected

Reading the ⊡ record as a one-step bound, the obvious inequality is

    D_r(L') ≤ (3/4) D_r(L) + (1/4) D_(r+1)(L)

for `D_r(L)` the maximum deviation of `L` from uniform on residues mod `3^r`.
That is false: measured against the tree it breaks at `k = 18, 23, 25, 29, 30`,
worst ratio 1.97. The dropped factor is the normalization of the odd branch,
which is fed by the `2 (mod 3)` third of the level and so divides by `|O|`, not
`|L|`. Writing that out gives the exact statement, with `w_e = |L|/|L'|`,
`w_o = |O|/|L'|` and `E_r` the conditional deviation of the parent one digit
finer,

    D_r(L') ≤ w_e D_r(L) + w_o E_r(L),
    E_r(L) ≤ ( D_(r+1)(L) + 3^(-r) D_1(L) ) / p₂

and substituting, since `w_o / p₂ = w_e = 1/(1 + p₂)`,

    D_r(L') ≤ [ D_r(L) + D_(r+1)(L) + 3^(-r) D_1(L) ] / (1 + p₂)

which is closed in the deviation family alone. Measured at `r = 1` and `r = 2`
over `k = 23..28` it holds every time, ratios `0.13` to `0.76`.

### Why it does not close, stated exactly

With `1 + p₂ → 4/3`, contraction from that bound needs
`D_(r+1) + 3^(-r) D_1 < D_r / 3`, so it needs the deviation to fall by more than
a factor three per digit of resolution. It does not: measured, `D_2/D_1` and
`D_3/D_2` sit near 1, the deviation being roughly flat in `r`. So the closed
recursion is valid and non-contracting, and the observed mixing at `0.83` per
level is not produced by it.

What that rules out is the max-norm itself. A maximum over classes discards the
signs, and the mixing has to come from cancellation between classes rather than
from any single worst class. The natural replacement is the character side, where
doubling permutes characters and the odd lift acts on them as a genuine
contraction. Measured at these tree sizes the character sums `|E[e(m/3^r)]|` sit
between `1e-3` and `3e-2` with per-level ratios swinging from `0.06` to `17`, so
the sizes reached here do not yet separate a rate from the noise. Getting that
rate wants either a larger tree or the transfer operator written out on
characters directly.

## The budget, the chain, and the junctions

Bound to the kernel rather than analysed, the object reads differently. The
`nesting` verb answers whether a point is drawn in to a map's answer, and its own
help says Erdős–Straus is the BUDGET on greedy removal rather than its arrival.
Collatz had no map there. The raw shortcut map cannot be one: it is not a
contraction, so two gaps read every point as open and the confirm loop stops at
the first widening, which is the edge that module's doc already names. The action
that nests is the BLOCK, from `n` to the first value below `n`, which strictly
decreases by construction with one held outright. Reading it needed the stopping
condition the doc asked for, so a map may now name the point it arrives AT and
have its gap read there; every existing map reads unchanged.

With that, `nesting collatz` predicts attracted and the run agrees at every point
tried, and the `collatz` verb reports the budget: 27 in seven blocks and seventy
shortcut steps, peak 4616. Over `2..20000` no block is left open, mean budget
17.55, max 25 at 19323. To 3000000 the records climb 1 to 40.

**The records fall into two families, and `merge` separates them.** Of the
consecutive record pairs, eleven have the larger record's trajectory running
straight through the smaller, and twenty are siblings meeting at a junction — and
the junctions are almost no set at all, 20 and 65 carrying twelve of the twenty.

**The ancestor family is exact.** Nine of the eleven are `n ↦ (4n−1)/3`, the two
arms of the split composed once each, one doubling and one odd lift, defined
exactly when `n ≡ 1 (mod 3)`. Without division, `3t+1 ↦ 4t+1`. `col_chain_up` and
`col_chain_down` give `col(4t+1) = 2(3t+1)` and `col(2(3t+1)) = 3t+1`, so
`chain_block` says the block from `4t+1` is exactly two steps, rising above the
seed then landing on `3t+1`: one chain step spends exactly one block, and the
ratio is four thirds. `chain_defined_iff` puts the chain on `1 (mod 3)`, and the
verb shows 26407 at budget 26 climbing through 35209, 46945, 62593 to 83457 at
budget 30, where `0 (mod 3)` ends it because the odd lift has no arm.

So the ratio was never one law. Within-chain steps sit at four thirds and
everything else is a chain switch, which is why the mean sat at 1.42 and neither
`4/3` nor `√2` was the answer.

**The junctions carry a forced ratio.** Every merge happens at a value
`2 (mod 3)`, since that is exactly where a second predecessor exists. Which arm
the traffic uses is forced by `col_odd_pred`: an odd step sends `2t+1` to `3t+2`,
which is `2 (mod 3)` for every `t`, so EVERY odd step lands on a junction, while
an even step lands on one only when its own half does. With the two step kinds
equinumerous that fixes the odd arm's share of all arrivals at

    (1/2) / ( (1/2) + (1/3)(1/2) ) = 3/4

and the census reads `0.7513` over seeds to 20000 and `0.7501` to 60000.
`odd_step_lands_on_junction`, `even_step_junction_iff` and `junction_arms` carry
it.

Measured by traffic from a window of seeds, the junctions look polarized: of
48199 used by seeds to 60000, 37868 sit in the top tenth of odd share and carry
63% of the arrivals. That reading is a fact about the window rather than the
tree, and the intrinsic measure says otherwise — 4616 reads `0.9996` by traffic
and `0.7481` by subtree. Every trajectory ends through the same tail, so low
values collect the traffic whatever their branching is.

New verbs, all in the tool's own help: `collatz`, with `trace`, `merge`, `chain`,
`junctions`, `sweep` and `ceiling`, and `collatz` as a map in `nesting`.


### The intrinsic balance, and an invariant

The quantity that does not move with the window is how much tree feeds each arm.
`collatz balance v d` counts the two subtrees under `2v` and `(2v−1)/3` to a
common depth; `collatz balanced lo hi d` scans for the junctions whose arms feed
within a tenth of each other.

The balanced fraction converges in depth and then does not move with scale. Over
`2..3000` it reads `0.370` at depth 8, then `0.340`, `0.322`, `0.319`, `0.316`,
`0.316` and `0.315` at depths 12, 16, 20, 24, 28, 32. At depth 12 it reads
`0.3400` on `2..3000`, `0.3380` on `100000..103000` and `0.3407` on
`5000000..5003000`. At depth 28 it reads `0.3160` low and `0.3187` at five
million.

The full distribution is the same object at both ends of that range, and it is
discrete rather than smooth. At depth 28, out of a thousand junctions:

    odd share   0.0   0.1   0.2   0.3   0.4   0.5   0.6   0.7   0.8   0.9
    low         333     0     2   117    47   269   107   125     0     0
    5 million   334     0     4   114    50   269   109   121     0     0

Mean odd share `0.3733` low and `0.3727` at five million. A third of all
junctions have a starved odd arm, nothing lands between `0.1` and `0.2`, nothing
above `0.8`, and the largest single cluster sits at `0.5`. Those are the same
numbers six orders of magnitude apart, which is the scale-free state the
two-readings ob3ect named as the fusion of the dense and sparse readings, read
off the tree instead of asserted.

One harness note, since it cost a run: the REPL splits a command line with
`splitn(4, ' ')`, so a fourth argument arrives glued to the third. The `collatz`
arm re-splits its tail before reading it.
### What fixes the share

The spectrum being discrete means something finite sets it, so `collatz classes`
groups junctions by residue and reports the spread inside each class. At modulus
9 the answer is immediate: class `5` sits at mean `0.0041` with a spread of
`0.0014`, while classes `2` and `8` spread over a quarter. At modulus 27 the
pinned classes are `5, 14, 23`; at modulus 81 the spreads elsewhere fall to a few
hundredths. The share is fixed one 3-adic digit at a time, which is the same
digit-per-level accounting the forward reading pays.

The pinned class has an exact cause, and it proves. A junction `v = 9k+5` has odd
arm `6k+3`, which is `0 (mod 3)`. A value `0 (mod 3)` takes only its doubling
predecessor, since the odd one exists exactly on `2 (mod 3)` — `preds_of_barren`
— and every value in its doubling chain stays `0 (mod 3)` — `barren_doubling`. So
that arm never branches at all: it is a bare chain of `d+1` nodes at depth `d`,
against an even arm growing like `(4/3)^d`.

That predicts a share of `(d+1) / ((d+1) + even)`, which at depth 24 is `0.004`.
The verb reads exactly that: `collatz balance 23 24` gives odd arm subtree **25**
against even arm 5666, and `41` gives **25** against 6235, where a junction off
that class — 20 — reads 6266 against 5519 for a share of `0.5317`. Twenty-five is
`d+1` on the nose.

So a third of all junctions are starved for a structural reason rather than a
statistical one, and it is the residue `5 (mod 9)` that starves them.
`col_starved_arm`, `preds_of_barren`, `barren_doubling` and `starved_junction`
carry it, *sans* sorry on the standard three.

### Solving the amplitude equation

At a junction the two arms and the value exhaust the count, so the even arm is
`A(2v) = (4/3)A(v) − A(u)` and the share collapses to a ratio of one function:

    share(v) = (3/4) · A(u) / A(v)

The verb confirms it directly: `(3/4)·A(13)/A(20) = 0.53197` against `0.5317`
measured, and `(3/4)·A(67)/A(101) = 0.46389` against `0.4635`. The finite form
needs no limit at all and is `subtreeCount_junction` with `odd_arm_count`.

Read along a trajectory that solves the equation. An odd `n` IS the odd arm of
`T n`, so `A(n) = (4/3)·share(T n)·A(T n)`; an even `n` is the doubling arm, so
`A(n) = (4/3)·(1 − share(T n))·A(T n)`. Composing over the trajectory,

    A(n) = (4/3)^L · (∏ wᵢ) · A(boundary)
    wᵢ = share(T nᵢ) at an odd step, 1 − share(T nᵢ) at an even one

so `log A` is a Birkhoff sum along the Collatz map. The amplitude is a
multiplicative cocycle whose weights are the shares, and the shares are ratios of
the amplitude along the odd lift: the system closes on itself, which is what this
kind of fixed point looks like rather than a defect in it.

Every step holds to a twentieth of a percent. `A(13)` rebuilt from `A(4)` across
five steps gives `6.275` against `6.287` measured, and the amplitudes verb reports
the recursion within `±0.5%` over a whole range. The single exception is the step
crossing the `1 → 2 → 1` cycle, where the count cuts the edge back into the root:
the recursion reads `+56.34%` at `v = 2` and `+0.05%` at every other value in the
same window. That is the boundary condition, and it is visible rather than hidden.

Vox audits the module at 49 T and 68 N, no B, no F, nothing assumed, no `sorry`.

### The Birkhoff average, and what it closes

The weight reads straight off the counts, `w = (3/4)·S(n,d)/S(T n,d)`, so the sum
of `log w` telescopes and the average is pinned by the two endpoints:

    mean log w = log(3/4) + [ log S(seed) − log S(end) ] / L

The numerator is bounded because the amplitude is, so the prediction is that the
average approaches `log(3/4) = −0.287682` exactly and the gap falls like `1/L`.
`collatz birkhoff` tests it, and the gap times the length is the quantity that
decides:

| seed window | mean length | geometric mean w | gap × length |
|---|---|---|---|
| 2..400 | 31.77 | 0.7215 | −1.2307 |
| 100000..100150 | 80.05 | 0.7379 | −1.3045 |
| 2000000..2000100 | 101.55 | 0.7403 | −1.3266 |

The gap shrinks from `−0.0387` to `−0.0131` while `gap × length` stays at about
`−1.3` across three windows and two orders of magnitude in the seed. That
constant IS the boundedness of the cocycle, and with it the Birkhoff average is
`log(3/4)` exactly rather than approximately. The odd-step fraction falls to
`0.5124` over the same windows.

So the geometric mean of the weights is `3/4`, the reciprocal of the branch
factor `4/3`. The predecessor tree grows at exactly the rate the forward
trajectories thin, and the two readings of the object — the sparse backward one
that banks everything and the dense forward one that banks nothing — are inverse
to each other rather than merely complementary. That is `μ∘δ = id` for this
object, measured: `δ` branches at `4/3` per level and `μ` weights at `3/4` per
step, and the amplitude that carries the composition is bounded.

### Boundedness: what is proved, what is forced, and what is measured

**Proved.** The residue structure forces a Fibonacci ceiling and nothing weaker.
A node `≡ 0 (mod 3)` is a chain, a node `≡ 1` has a single child which is `≡ 2`,
and a node `≡ 2` has a doubling child `≡ 1` plus an odd child. So a branch is
always followed by a non-branching step on the even side, and the pairing

    a(d+1) = 1 + b(d)          -- the `≡ 1` bound
    b(d+1) = 1 + a(d) + b(d)   -- the `≡ 2` bound

gives `1, 3, 6, 11, 19, …` with `b(d) = b(d−1) + b(d−2) + 2`. That is `φ^d`, not
`2^d`, and `subtreeCount_le_classBound` proves every count sits under its class's
entry, with `classBound_fib` showing the recursion is Fibonacci shifted by two.

**Forced.** The mean amplitude is `6`, by conservation rather than by fitting.
Summing the counts over a window counts each `(ancestor, depth)` pair once, so

    Σ_{v ∈ W} S(v,d) = Σ_{k=0}^{d} #{ w : T^k(w) ∈ W }

and with the preimage counts growing at `4/3` the right side is `4·(4/3)^d − 3`
times `|W|`. Dividing by the two thirds of the window that is not a multiple of
three gives `(4 − 3/(4/3)^d) / (2/3)`, which is `5.992` at depth 22. Measured:
`5.9686`, and in depth `5.648, 5.866, 5.950, 5.981, 5.993` at depths 12 to 28,
climbing to 6.

**Measured.** The maximum amplitude does not drift, in either direction that
could break it. Across windows at depth 22 it reads `10.0036` low, then `10.1445`
at a hundred thousand, `10.1659` at five million and `10.1659` at five hundred
million, while the mean holds at `5.968, 5.974, 5.968, 5.972` — eight orders of
magnitude, four digits of agreement. In depth on a fixed window it converges:
`9.8197, 9.9825, 10.0210, 10.0229, 10.0263` at depths 12 to 28.

**Open, and located exactly.** Boundedness does not follow from the residues.
Writing `M₁, M₂` for the suprema on the two live classes, the relations give
`M₁ ≤ (3/4)M₂` and `M₂ ≤ (3/4)(M₁ + M₂)`, which is consistent for every `M₂` and
so bounds nothing. The gap between the proved `φ` ceiling and the measured `4/3`
is exactly the assumption that the odd child's residue equidistributes rather
than landing on `2 (mod 3)` every time: adversarial gives `φ`, uniform gives
`4/3`. So the amplitude is bounded **iff** the odd-lift residues equidistribute,
and that single statement now carries the whole structure — the `4/3` branch
factor, the mean `6`, the `3/4` Birkhoff average, and `μ∘δ = id` between the two
readings.

### The equidistribution, measured at square-root rate

Equidistribution mod `3^r` is the vanishing of every nonprincipal character sum,
so `collatz fourier` measures those directly rather than through a maximum
deviation, which discards the signs the cancellation lives in.

The structure of the flow is fixed and one-way. Doubling permutes the characters
of a given conductor, so it moves no mass between levels; the odd arm sends a
conductor `3^r` character to one of conductor `3^(r+1)`. So the coefficient at
each conductor is fed from the conductor above it and never from below, which is
why nothing propagates outward from the root and why the convergence has to be
cancellation rather than transport.

Measured, the cancellation is square-root. The raw coefficients fall from
`0.25, 0.64, 0.41` at level 9 to `0.0009, 0.0040, 0.0017` at level 34, and the
quantity that decides is the coefficient times `√N`:

| level | nodes | ×√N at 3 | at 9 | at 27 |
|---|---|---|---|---|
| 26 | 1187 | 0.475 | 0.394 | 1.036 |
| 28 | 2122 | 0.095 | 0.365 | 1.377 |
| 30 | 3765 | 0.448 | 0.683 | 0.606 |
| 32 | 6682 | 0.141 | 0.106 | 0.124 |
| 34 | 11878 | 0.103 | 0.433 | 0.186 |

That column stays of order one, mostly under 1.4, while `N` grows tenfold. So
`|μ̂_d(χ)| = O(N_d^{-1/2})`, which is the strongest rate there is, and since
`N_d ≍ (4/3)^d` the coefficients decay like `(4/3)^{-d/2} = 0.866^d` — the same
number the crude deviation census read as `0.83` before the signs were kept.

What is proved around it: the arm map is a bijection on residues, `arm_inj_mod`
with `arm_surj_mod` and `arm_bijection_mod`, so a level uniform one digit finer
produces a level uniform here. Uniform is FIXED by the level map; what is
measured is that the tree converges to it at the square-root rate.

The rung after this is finite linear algebra rather than analysis. Writing the
coefficient vector up to conductor `3^R`, one level of the tree acts on it by a
matrix that is upper-triangular in conductor: same-conductor terms come from the
doubling permutation with modulus one, and the only other term comes from the
conductor above. Proving `|μ̂_{d+1}| ≤ c·|μ̂_d|` therefore reduces to bounding the
feed from `3^(r+1)` against the coefficient at `3^r`, level by level, with every
entry of that matrix explicit. That bound, with `c < 1`, closes the chain:
square-root cancellation gives the equidistribution, the equidistribution bounds
the amplitude, and the bounded amplitude is what makes the Birkhoff average
exactly `log(3/4)` and `μ∘δ = id` between the two readings.

### The level map on coefficients, exactly

Writing `μ̂_d(j,r)` for the coefficient at the character `x ↦ e(jx/3^r)`, one level
of the tree acts as

    μ̂_{d+1}(j,r) = ρ_d [ μ̂_d(2j, r)
                       + e(−j/3^{r+1}) · (1/3) Σ_{s<3} ω^{−2s} μ̂_d(2j + s·3^r, r+1) ]

with `ω` a primitive cube root of unity and `ρ_d = N_d/N_{d+1} → 3/4`. The first
term is the doubling permutation: it moves no mass between conductors and
contracts by exactly `ρ_d`. The second is the odd arm, reaching one conductor
higher.

`collatz flow` verifies it. The computed `|sum|` matches the coefficient the next
level actually carries to five decimals at every level, at conductor 3 and at
conductor 9.

**The feed is a difference, not a sum.** Because `Σ_{s<3} ω^{−2s} = 0`, a
conductor-`3^{r+1}` coefficient that is constant across the three lifts
contributes exactly nothing. The flow between conductors is a difference operator
rather than a transport, which is `cube_roots_sum_zero` with `three_lifts` naming
the three lifts as `c`, `c + 3^r`, `c + 2·3^r`.

**And the decay is phase cancellation, not term-wise contraction.** Measured, the
feed runs comparable to the doubling term — `feed/same` averages about 1.5 — so
the triangle bound gives nothing below one and no term-wise argument can work.
What decays is the sum: the mean of `|sum| / (|same| + |feed|)` is `0.5312` at
conductor 3 over 24 levels and `0.7884` at conductor 9 over 20. The two terms
systematically partly cancel, and that cancellation is the square-root law seen
from the operator side rather than from the sample.

So the remaining statement is sharp and it is about phase: the doubling term and
the odd-arm difference term must decorrelate. Everything else in the chain is
closed — the operator is exact and verified, the cancellation in the feed is
proved, the arm bijection is proved, the Fibonacci ceiling is proved, the mean
amplitude is forced to 6, and the amplitude and Birkhoff average are measured
stable across eight orders of magnitude.

### The cross term: bounded, and anti-correlated

The cross leg has an exact form. With `φ(a) = 3(a − 2⁻¹) + 2` a bijection from
classes mod `3^r` onto the junction classes mod `3^{r+1}`,

    C_cross = 2 · Σ_c n_r(c) · m(φ(c))

so its deviation from the flat value `2·N·Np/3^r` is a correlation between two
mean-zero vectors, and Cauchy–Schwarz bounds it by the product of the two
deviations. Measured, that bound holds in every row with room to spare —
`|cross|/N` against `CS/N` reads `0.063` against `0.585`, `0.594` against `0.719`,
`0.040` against `0.105`.

With the cross leg flat, the three shares are forced to `9/16`, `1/16` and `6/16`
by the two bijections already proved — the doubling leg is exactly the previous
`C(r)`, and the odd leg is the junction population over the `3^r` junction classes
mod `3^{r+1}`. Those are the shares measured, stable to four digits.

In the scale a square-root law lives at, `E = e·N`, the recursion reads

    E_{d+1}(r) = (3/4)·E_d(r) + (1/12)·E_d(r+1) + cross

whose linear part has multiplier exactly `1` when `E(r+1) = 3·E(r)`. So the
square-root law is a **marginal fixed point** of the level map, neither growing
nor decaying, which is why it sits so still across levels and scales. Measured,
`E` stays bounded at both conductors over thirty levels: `0.02`–`0.65` at
conductor 3 and `0.6`–`6.1` at conductor 9.

But the measured ratio `E(r+1)/E(r)` runs `3.5` to `17`, not `3`, so the linear
part alone predicts growth that does not happen. The cross term supplies the
difference, and it is not a negligible remainder: it is **systematically
negative**, eight of eleven rows, mean about `−0.09` per unit `N`. The two arms
are weakly anti-correlated rather than independent.

So the statement that remains is sharper than decorrelation, and it has a sign:
the cross correlation between the doubling image and the odd image is negative on
average, and that negativity is exactly what holds `E` at its marginal fixed
point. Everything else in the chain is closed.

### Where the sign comes from

Doubling is an involution on the live classes mod 3: `2·1 ≡ 2` and `2·2 ≡ 1`, so
the two branching classes are swapped every level and returned every second one,
while the dead class is fixed. `double_swaps_classes` and `double_involution`
carry that. An imbalance between the two live classes therefore tends to
alternate, and a level's correlation with its own image under the arms is
negative for that reason rather than by accident.

The measurement matches, and it matches where the mechanism is purest:

| conductor | levels negative | mean cross deviation | inside CS bound |
|---|---|---|---|
| 3 | 20 of 24 | −0.140 | 24 of 24 |
| 9 | 15 of 22 | −0.063 | 22 of 22 |
| 27 | 12 of 20 | −0.037 | 20 of 20 |

The bias is strongest at conductor 3, where the junction condition *is* the mod-3
condition and the swap is exact, and it weakens toward a coin flip as the
conductor rises and the swap dilutes. The Cauchy–Schwarz bound holds in every row
at every conductor, so the bound is structural while the sign is dynamical.

Reading the signed imbalance directly at conductor 3, it changes sign every two to
three levels rather than every level — the involution perturbed by the odd arm's
feed, which is exactly the term that reaches one conductor higher.

So the chain now reads: `μ∘δ = id` between the two readings rests on the bounded
amplitude, the bounded amplitude on the square-root law, the square-root law on
its being a marginal fixed point of the excess recursion, and that fixed point on
the cross correlation's negative sign — which the doubling involution supplies and
the odd arm perturbs. That last perturbation is the whole of what is left.

### The perturbation, exactly

At conductor three the even children swap the two live classes, so their entire
contribution to the imbalance `I = n₁ − n₂` is its negation. The odd children come
only from the junctions, and which class each lands in is fixed by its parent's
residue mod 9: `2 ↦ 1`, `5 ↦ 0`, `8 ↦ 2`. Only two of those three touch the
imbalance, so

    I_{d+1} = −I_d + (m₂ − m₈)

with `m_c` the level's counts mod 9. The involution is the minus sign; the
perturbation is one difference of two mod-9 classes and nothing else.
`odd_child_class_two`, `_five`, `_eight` and `junction_classes_split` carry the
pointwise content.

Checked in exact integers to depth 30 the identity holds at every level, with a
single exception at level 2 where the tree cuts its own `1 → 2 → 1` edge: the
prediction of 2 meets an actual 1, short by exactly the omitted node. Boundary,
not law.

The perturbation is not a small correction. Its mean size is `1.79` times the
imbalance it perturbs, so the odd arm carries the level rather than nudging it —
while the imbalance itself stays tiny, running between `−13` and `+11` at level 30
where `N = 3765` and `√N = 61`. Both terms are `O(√N)` and they trade the level
between them, which is why the sign alternates in runs of two and three rather
than every level.

So the structure recurses: the conductor-3 imbalance is driven exactly by a
conductor-9 difference, which is in turn driven by conductor-27 differences by the
same argument one digit up. That tower, with the involution supplying the minus
sign at every rung, is the whole mechanism.

### The tower is finite, and the norm it closes in

The regress has a floor. A level of `N` nodes leaves classes empty once `3^r > N`,
so the tower has about `0.262·d` rungs rather than infinitely many, and the top
rung saturates at `e(r) ≈ 3^r/N` for free. That is the base case, and it was there
all along.

With the finer term carrying coefficient `1/16`, the object that closes is the
weighted norm `‖e‖ = sup_r 3^{-r}·e(r)`:

    3^{-r}·e_{d+1}(r) ≤ (9/16)·3^{-r}e_d(r) + (3/16)·3^{-(r+1)}e_d(r+1) ≤ (12/16)·‖e_d‖

a contraction at `3/4` per level, because the weight pays exactly the `3` the
digit costs. And `(3/4)^d = 1/N_d`, so the fixed point of that contraction IS the
square-root law — derived from the two bijections rather than fitted to the
census.

Measured over sixteen levels, including every term and with no modelling: the
per-level ratio runs `0.583, 1.006, 0.926, 0.610, 0.834, 0.852, 0.744, 0.772,
0.719, 0.662, 0.816, 0.734, 0.768, 0.692, 0.818, 0.709`, mean `0.76` against the
predicted `0.75`. And `‖e‖ × N` runs `0.59` to `1.04`, sitting at one.

The norm is attained at the top rung every time, so it reads the saturation end,
and the quantity that matters below it is bounded by it: `e(1) ≤ 3‖e‖ ≈ 3/N`,
against a measured `e(1)·N` of `0.02` to `0.65`. Comfortably inside.

So the linear half of the contraction is proved — it is the two bijections and the
weight — and the measurement says the full map contracts at `0.76` with the cross
term included. What is not yet proved is the cross term's bound in this norm.
Cauchy–Schwarz gives `|cross| ≤ 2√(δ_even · δ_odd)` structurally, and it holds in
every measured row; what is needed is that bound carried through the `3^{-r}`
weighting with a constant small enough to leave `3/4 + c < 1`. That is one
inequality, and everything else is in place beneath it.

### What the ob3ect returned, and the fold it named

`collatz_cross_bound` grounds full at ⟨𐑦𐑰𐑽𐑿𐑐𐑧𐑚𐑝⊙𐑖𐑳𐑭⟩, Lean-verifies at `O₂dag`,
and passes the Frobenius gate `T`. Its phase 1 names the pieces the way the
measurements had them: `≻` the doubling map, `≺` the odd lift reaching one
conductor higher, `⊥` the marginal fixed point, `⊞` the phase cancellation, `⊡`
the Cauchy–Schwarz bound as the permanent record. Its phase 3 `both` reads
"the linear part has multiplier one, but the cross term is negative and provides
the decay" — which is the measurement, arrived at independently.

The usable content is in `banked_count_check`, which passes and still flags a
loss:

> 1 further unit(s) flattened by a fold between sibling regions and not
> restored … the fold keeps the larger rather than the sum. Put them in one
> region to keep both.

That is about the norm. `sup_r 3^{-r}e(r)` is a fold that keeps the larger and
drops the rest. Replacing it with the sum keeps every rung, and it still
contracts: over levels 17 to 28 the sum-fold ratio runs `1.334, 0.694, 0.760,
0.866, 0.978, 0.840, 0.762, 0.605, 1.106, 0.613, 0.725, 0.635`, mean about `0.82`
against the max-fold's `0.76`, with `sum × N` bounded between `2.0` and `4.2`.
Keeping every rung costs a slightly larger constant and discards nothing.

`weight` on the ob3ect's own word then shows the same fault structurally: four
units **stranded in frames never fused**. The movement stops dead at step 8 —
`⊞` deposits `t+f`, the register fixes at `Ftf`, and `⊡ ⋈ ∋ ⊤` all read inert, so
the fuse never collects what the split put in. The cancellation is asserted before
the fusion.

Reordering to fuse first fixes it. `⊢⊙∈≻⊤≺⋈∋⊥⊞⊡⊤⊣` and `⊢⊙∈≻⊤≺⊥⊞⋈∋⊡⊤⊣` both
verdict `T`, bank clean, need no repair, land on `A` with all four values held,
`restored 1`, and **nothing stranded**. Moving `⊞` after `∋` alone takes the
stranding from four to two; putting the whole fusion ahead of both evaluations
takes it to zero.

Read into the mathematics that is one instruction: **sum the legs before
asserting the fixed point**. Collect the three collision legs into the excess
first, and only then invoke the marginal fixed point and the phase cancellation.
Evaluating the fixed point before collecting the legs is precisely what the
max-fold does when it drops rungs before summing them, and it is why that norm
reads a smaller constant than it has earned.

### Summing before evaluating, and what it costs

Following the instruction, the ℓ¹ fold `‖e‖₁ = Σ_r 3^{-r} e(r)` sums the recursion
exactly:

    ‖e_{d+1}‖₁ ≤ (9/16)‖e_d‖₁ + (3/16)‖e_d‖₁ + C = (3/4)‖e_d‖₁ + C,
    C = Σ_r 3^{-r}·cross(r)

with the `3/16` arising because the `r+1` terms are a sub-sum of the same norm.
Nothing is discarded, and the only free quantity is `c = C/‖e‖₁`, which must sit
under `1/4`.

Measured over 23 levels: `c < 1/4` holds in 18, mean `+0.197`, and it fails at
five with a worst of `+3.25`. At the worst ordinary level the ratio is `1.106`,
so `3/4 + c = 1.107` and that level expands rather than contracting. The
two-step map does not repair it either — the involution has period two, so pairs
were the natural place for an excursion to meet its partner, but the two-step
ratio sits under `(3/4)² = 0.5625` in only 7 of 23, mean `0.745`, worst `1.778`.

What is true is weaker and still real: the norm decays. The per-level ratios have
geometric mean about `0.78`, and the two-step mean of `0.745` is `0.863` per
level, which is `√(3/4) = 0.866` — the square-root rate the coefficients were
already measured at. So the ℓ¹ fold decays at the square-root rate rather than at
the linear part's `3/4`, and the difference is exactly what the cross term costs.

So summing rather than maxing is the honest fold and it does not close the
constant. The linear part gives `3/4` and is proved; the measured constant is
`0.78` to `0.86`; and a uniform bound on `c` below `1/4` is false as stated,
because five levels in twenty-three exceed it. What a proof needs is not that
bound but a bound on the excursions — the levels where `c` spikes — or a norm
that averages them out. That is the open item, stated at the size it actually is.

### The excursions were the instrument, not the object

The five levels where `c` exceeded `1/4` were not the dynamics. Two things were
moving underneath them. A rung opens whenever `3^r` crosses `N`, so the sum gains
a term the level below never had and the ratio jumps once; and at small `N` the
histogram is a handful of nodes and the excess is noise. Holding the rung count
fixed removes the first, and reading only levels with enough nodes removes the
second.

With rungs held at four, every failure sits at `N ≤ 91` — levels 10, 13, 16 and
17, with 12, 31, 68 and 91 nodes. From level 18 onward:

| level | nodes | ratio | c |
|---|---|---|---|
| 18 | 120 | 0.694 | −0.056 |
| 22 | 381 | 0.872 | +0.122 |
| 26 | 1187 | 0.530 | −0.220 |
| 30 | 3765 | 0.992 | +0.242 |
| 34 | 11878 | 0.813 | +0.063 |

`c < 1/4` at **every one of seventeen consecutive levels**, `N` running from 120
to 11878, and the ratio never reaches one, the worst being `0.992`. Mean `c` is
`+0.145`.

So the contraction `3/4 + c < 1` holds at every level large enough for its own
histogram to mean anything, and the earlier failures were the measurement rather
than the map. What is still missing is the same thing it always was, now stated
at its real size: an a priori bound on `c` for levels above a threshold, coming
from the residue structure rather than from the census.

### The second ob3ect, and a reading the measurement refuses

`collatz_cross_bound_2` grounds full at ⟨𐑦𐑰𐑑𐑿𐑐𐑧𐑲𐑜⊙𐑖𐑳𐑴⟩, Lean-verifies at
`O₂dag`, and its banked check comes back with **nothing lost** — `surplus_total 0`,
`restored 1`, landing on `A`. Its word `⊢⊙∈≻⊤≺⊥⊞⋈∋⊡⊣` puts the fuse after the
paradox, which is the same reordering the `weight` verb had forced by hand, found
independently.

Two of its assignments carry claims about the mathematics.

`⊡ = 𐑴`, a ℤ₂ invariant protecting the bound against deformation. That is the
involution: `2·1 ≡ 2` and `2·2 ≡ 1` mod 3, already proved as
`double_swaps_classes` and `double_involution`, and already the source of the
cross term's negative sign.

`∋ = 𐑜`, disjunction — *one sufficient residue satisfies the bound rather than all
partners simultaneously*. Read into the sum, that says the weighted cross sum is
carried by a single rung, so bounding it would need that rung and not every rung
at once. **The measurement refuses it.** Taking the ratio of the whole sum to its
largest single rung across 22 levels, the value swings from `0.16` to `4.33`:
sometimes one rung exceeds the entire sum, because the rungs cancel against each
other, and sometimes the sum is four times any single term, because they add.
Mean share `1.18`, no domination in either direction.

So the ℤ₂ reading is already in hand and the disjunctive one does not survive
contact with the census. The bound still has to hold the whole sum at once, and
the open item is unchanged: an a priori bound on `c` above a stated level size,
where the measurement says `c < 1/4` at every one of seventeen consecutive levels
from `N = 120` upward.

### The oracle's hunt

Pointed at the claim rather than at the object, the adversarial discipline pays
immediately. `collatz attack` walks every level to a given depth, computes `c`,
and stops at the first level past the threshold that breaks `c < 1/4`.

It broke on the first serious attempt: **level 25, `N = 885`, `c = +0.3565`** at
six rungs. And it broke exactly where the sixth rung first opens — `3^6 = 729`
sits above the previous level's 665 and below this level's 885. So capping the
rung count never prevented an opening, it only delayed it, and the earlier repair
was incomplete. The counterexample is a fact about comparing two levels whose
norms have different numbers of terms.

Stated properly — the rung count required live at *both* levels — the hunt
survives everywhere tried:

| rungs | min N | levels tested | worst c |
|---|---|---|---|
| 5 | 120 | 27 to depth 48 | +0.1767 |
| 6 | 500 | 19 to depth 44 | +0.1060 |
| 7 | 2500 | 15 to depth 44 | +0.0806 |

The margin widens as the tower deepens, though part of that is definitional:
`c = C/‖e‖` and a deeper tower has more terms in the denominator, so the same
absolute cross term reads as a smaller fraction. What is not definitional is that
no level anywhere in that range reaches `1/4`.

Surviving is not proof, and the verb says so in its own output. What it reports is
what was exhausted: the contraction `3/4 + c < 1` stands unrefuted across every
comparable level from `N = 120` to depth 48, at three different tower depths, with
the worst case at `0.18` and falling.

### Proving the bound: what comes out, and what does not

Write each histogram as flat plus deviation. Both deviations sum to zero, so the
flat parts contribute exactly the product of the totals over the modulus and
nothing else survives — the cross term **is** the correlation of the two
deviations, with no remainder. `cross_decompose` proves that over any finite index
type with any reindexing of the second factor, and it is *sans* sorry.

From there Cauchy–Schwarz, with the arm proportions `3/4` and `1/4`:

    |cross(r)| ≤ (3/8)·√( e_even(r) · e_odd(r) )

where `e_even(r)` is the level's own excess *exactly*, by the doubling bijection,
and `e_odd(r)` is the arm image's. Summing against the weight,

    c ≤ (3/8)√3 · √( ‖e_arm‖ / ‖e‖ )

so the route closes precisely when that ratio sits under `0.1482`.

It does not. Measured over 24 levels, the ratio runs `3.7` to `5.7` — the arm
image is as uniform as its quarter share allows, `4` being what population alone
would give — so the bound lands at `1.25` to `1.55`. The measured `c` is about
`0.1`. Cauchy–Schwarz is loose here by a factor of roughly fourteen.

That is not a fixable slack. Cauchy–Schwarz takes absolute values, and the sign is
exactly what carries the contraction: the cross term is systematically negative,
20 of 24 levels at conductor 3, because doubling is an involution on the two live
classes. Any bound that discards the sign is bounding a quantity four times larger
than the one that decides.

So the state after the attempt: the decomposition is proved, the inequality it
supports is proved, and that inequality gives `1.30` where `0.25` is needed. The
missing factor is not analytic slack to be tightened — it is the ℤ₂ the second
ob3ect named, and a proof of the bound has to carry the sign through rather than
around it.

### Why the low conductors are the hard ones

The doubling permutation on residues mod `3^r` has order `2·3^(r-1)`. The kernel
reads it directly — `winding order 2 3, 9, 27, 81, 243` gives `2, 6, 18, 54, 162`
— and that one fact organises the whole sign question.

At `r = 1` the order is **two**. The permutation is the involution, so a deviation
alternates every level and the cancellation is complete and per-level. That is why
the conductor-3 identity `I_{d+1} = −I_d + (m₂ − m₈)` carries a bare minus sign,
and why the cross term comes back negative in 20 of 24 levels there.

At `r ≥ 2` the order is `6, 18, 54, …`, and there is no per-level sign at all. The
deviation returns to itself only after a full cycle, so what survives each level
is dilution rather than cancellation. Measured, the cross term sits at `0.349` of
the Cauchy–Schwarz bound at conductor 9 and `0.189` at conductor 27, against
`3^(-r/2)` of `0.333` and `0.192` — square-root cancellation over the classes,
with the cycle length proportional to that count.

`two_order_mod_three`, `two_order_mod_nine`, `two_order_mod_twentyseven` and
`doubling_involutive_only_at_three` carry it, the last saying exactly that
doubling is its own inverse at conductor three and at no conductor above it.

So the two regimes are structurally different and the proof splits where the order
splits: the low rungs get exact identities because they have a sign to carry, and
the high rungs get the generic square-root bound because they have length to
average over. That is the shape of the remaining work, and it is finite — the
identities needed are at `r = 1`, which is done, and `r = 2`, which is not.

### The identity at conductor nine

At `r = 1` the doubling permutation is an involution and the recursion closes in a
single alternating step. At `r = 2` it is a six-cycle, so there is no per-level
sign — but the recursion is still exact, only now it reads the level at two
resolutions at once.

Both arms are determined. The even child `2m` has class `2·(m mod 9)`, and
doubling is a bijection there with inverse `5`, since `2·5 = 10 ≡ 1 (mod 9)`. The
odd child `2t+1` of a junction `3t+2` has class `2·(t mod 9)+1`, fixed by `t mod
9`, which is `m mod 27`. So

    n'(c) = n(5c mod 9) + m₂₇( 3·((5(c−1)) mod 9) + 2 )

each class of the next level fed by exactly one class mod 9 through the doubling
arm and exactly one class mod 27 through the odd arm. `even_child_mod_nine`,
`odd_child_mod_nine`, `inv_two_mod_nine`, `doubling_onto_mod_nine`,
`odd_source_mod_nine`, `oddSource_is_junction` and `oddSource_feeds` carry it.

Checked in exact integers by `collatz perturb9`, all nine classes at every level
to depth 30: **one mismatch in the entire walk**, at level 2, where the tree cuts
its own `1 → 2 → 1` edge — the same boundary the conductor-3 identity meets and no
other.

So both low rungs now have their exact identities, `r = 1` alternating and `r = 2`
not, and above them the generic square-root bound applies with the cycle length to
average over. What is not yet done is using them: the identities say what the low
rungs *are*, and the bound on `c` needs what they *contribute* to the weighted
sum. That is the next rung, and it is the first one in a while that needs no new
structure — only the two identities already in hand.

### Using the identities: where the difficulty actually sits

With both low identities in hand the `r = 1` contribution can be written out. The
even arm's deviation is the level's own with classes 1 and 2 transposed — `σ(d)`,
by the involution — and the odd arm's is the mod-9 deviation read on the three
junction classes `2, 5, 8`, which sums to zero because those are exactly the
junctions. So the contribution is `2⟨σ(d), h⟩`, an inner product of two zero-sum
vectors in three dimensions, both factors known exactly.

Everything therefore turns on the cosine, and measured it is close to one:
`|actual|/CS` at conductor 3 runs `0.204, 0.614, 1.000, 0.982, 0.968, 0.997,
0.962, 0.993, 0.300, 0.876, 0.843, 0.998`, mean `0.72`. **Cauchy–Schwarz is tight
at the lowest conductor.** In three dimensions with a zero-sum constraint the
space is two-dimensional, so two such vectors are nearly parallel or nearly
antiparallel, and they are.

That inverts the picture I had. The high conductors are where cancellation lives —
`0.349` at 9, `0.189` at 27, falling like `3^(-r/2)` over a growing cycle. The
lowest conductor has no cancellation at all; what saves it is the **sign**. The
inner product is negative in most levels, so the largest term in the weighted sum
is usually subtracting from the norm rather than adding to it.

The risk is therefore entirely the positive excursions at `r = 1`: `+0.968`,
`+0.997`, `+0.300` in the window above. And they do not alternate cleanly — the
signs run in blocks of one to four rather than flipping every level, because the
involution's alternation is perturbed by the odd arm exactly as the conductor-3
identity says.

So the whole difficulty is now localised to one explicit object: the sign of
`⟨σ(d), h⟩` at conductor 3, where `d` is the level's mod-3 deviation and `h` its
mod-9 deviation on the junction classes. Both factors are given by identities
already proved. That is a much smaller thing than "bound the cross term", and it
is what the next rung has to characterise.

### The proportionality, and the honest end of this thread

Since the two vectors are nearly parallel, `b ≈ λa`, and the whole sign question is
the sign of one scalar. Measured over 22 levels, `λ` is negative in **18**, mean
**−0.6417**, with the exceptions at `+2.474`, `+0.785`, `+0.135` and one earlier.

So the odd arm opposes the even arm about four times in five, with a
proportionality near `−2/3`, and that opposition is exactly what makes the largest
term of the weighted sum subtract from the norm rather than add to it. Written
out, with `x, y, z` the level's mod-3 imbalances and `p, q, r` the junctions'
mod-9 split, both zero-sum,

    S = xq + yr + zp = q(x − y) − p(x + 2y)

an explicit form in four integers, every one of them supplied by an identity
already proved.

And the sign is not deterministic. Four levels in twenty-two come out positive,
they do not alternate, and they do not line up with the rung openings that
explained the earlier excursions. That is the same shape of obstruction met three
times now at three different resolutions — the tower, then the excess, now the
inner product — each time smaller and more explicit, and each time not closing.

What this thread has established, and it is not nothing: the contraction reduces
to the sign of `q(x−y) − p(x+2y)` at conductor three, where the two identities fix
every term; the high conductors contribute `3^(-r/2)` by cancellation over the
doubling cycle and need no argument; and Cauchy–Schwarz is tight at the bottom and
loose at the top, which is why no single bound covers both. What it has not
established is any reason the four exceptional levels cannot recur, and without
that the contraction remains measured rather than proved.

### Reading the exceptional levels

Printing the six integers at each level makes the exceptions readable. The pairing
is `(n0 ↔ m5)`, `(n1 ↔ m8)`, `(n2 ↔ m2)`, and `m2, m5, m8` are the three mod-9
parts of `n2` itself. I expected that to split the terms in two — the first two
pairing disjoint sets, which anti-correlate at fixed total, and the third pairing a
part with its whole, which should correlate positively — two against one giving
the sign.

**That is wrong, and the census says so.** The part-whole term is positive in only
`5` of `24` levels, mean `−15.6`. It anti-correlates like the others. All three
pairings oppose; there is no competition between them.

What is exact in the measured window is simpler: `sign(λ) = sign(x·q + y·r)` at
every one of the 24 levels, with both negative in the same 20. The part-whole term
never flips the outcome, so the sign question reduces once more — to two terms and
four integers,

    x·q + y·r  =  (n₀ − N/3)(m₅ − N_o/3) + (n₁ − N/3)(m₈ − N_o/3)

where `n₀, n₁` are the level's non-junction classes mod 3 and `m₅, m₈` are two of
the three mod-9 parts of the junction class.

So the odd arm's mod-9 split systematically opposes the mod-3 imbalance in every
pairing, four times in five, and the four exceptions are levels where a disjoint
pair fluctuates into alignment. That is a statement about a fluctuation, not about
a rule, and it is why three successive descents have sharpened the object without
closing it: at the bottom the quantity is stochastic in character. Any proof of the
contraction has to be a concentration statement about `x·q + y·r`, not a
deterministic bound — which is a different kind of theorem than the one I have been
trying to write.

### The concentration statement

The contraction never needed `c < 1/4` at every level. The norm decays iff the
*product* of the per-level ratios decays, which is the mean of `log(3/4 + c)`
being negative. A level may expand as long as the running average does not. That
is a concentration statement, and it is a far weaker demand than the supremum
bound I spent several rungs failing to prove.

Measured, it holds with room that is not close:

| rungs | levels | mean c | worst running mean | geometric ratio |
|---|---|---|---|---|
| 3 | 27 | −0.0067 | +0.0076 | 0.71141 |
| 4 | 27 | −0.0115 | +0.0232 | 0.72645 |
| 5 | 23 | −0.0119 | +0.0897 | 0.73048 |
| 6 | 17 | −0.0094 | −0.0094 | 0.73600 |

The mean of `c` is **negative** at every tower depth — the cross term helps on
average rather than costing — and the geometric mean of the ratio comes in *below*
the linear part's `3/4` in all four runs. The worst running mean anywhere is
`+0.0897`, against `0.25` needed. With a per-level variance of `0.0175`, so a
standard deviation near `0.13` over 27 levels, the threshold sits about ten
standard errors away.

That reframes the whole difficulty. The four exceptional levels, the positive
excursions, the fluctuating sign of `x·q + y·r` — none of them bear on this. They
are per-level events, and the contraction is an average. What has to be proved is
`E[c] < 1/4`, and what is measured is `E[c] ≈ −0.01`.

So the target has moved from a supremum that is false to an average with a
ten-sigma margin. Everything under it is unchanged: the linear part is proved at
`3/4` from the two bijections, the cross term is exactly the correlation of two
deviations by `cross_decompose`, its negativity has its source in the lag sum rule
`autocorr_sum_zero`, and the low conductors have their exact identities. What
remains is an a priori bound on the *average* of the cross term — a different
theorem than the one I was writing, and by every measurement a much easier one.

### Correction: the concentration statement is not a reduction

The averaged form telescopes. Summing `log` of the per-level ratios gives
`log‖e_{K+1}‖ − log‖e_1‖`, so the geometric mean over a window is
`(‖e_{K+1}‖/‖e_1‖)^{1/K}` — a function of the two endpoints and nothing else.
Checked against the run: the endpoints give `0.72761` where the level-by-level
average gave `0.72645`, the same number.

So "the geometric mean of the ratio is below one" is not a weaker target than the
decay. **It is the decay**, written differently. Proving `E[c] < 1/4` is proving
the contraction, not reducing it, and the ten-standard-error margin I reported is
a measurement of the conclusion rather than of a lemma leading to it. That
paragraph as I wrote it last turn was wrong and this one replaces it.

What survives the correction is the decomposition, which is real:

* the linear part contracts at `3/4` deterministically, from the two bijections —
  `double_collide_iff` and `arm_collide_iff`, with the weight paying the digit;
* the cross term is exactly the correlation of two deviations, `cross_decompose`,
  with no remainder;
* its systematic negativity has a proved source, `autocorr_sum_zero`, and a proved
  mechanism at the conductor where it is strongest, the involution;
* the low conductors have exact identities, `r = 1` alternating and `r = 2` not.

And what does not survive is any route from those to the bound. `sup c < 1/4` is
false, the oracle broke it. `E[c] < 1/4` is true and is the thing itself. The
Cauchy–Schwarz bound is tight at the bottom conductor and loose at the top, giving
`1.30` where `0.25` is needed. Each of the three descents named the object more
precisely and none of them supplied an inequality that was not either false or
circular.

That is the state, and it is worth stating without decoration: the apparatus is
proved, the measurements are stable across eight orders of magnitude, and the
contraction is not proved. What is missing is an a priori input about the cross
term that does not come from the structure already used — the structure has been
enumerated, and it is not sufficient.
