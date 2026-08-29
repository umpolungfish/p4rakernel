import Mathlib
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.Base
import Imscribing.Classical.Szemeredi

/-!
# Erdős problem 3 at k = 3

If `Σ 1/a` over `A` diverges, does `A` contain a three-term arithmetic
progression?

The difficulty is that divergence does not give density. The primes witness the
gap: `ErdosTuran.primes_reciprocal_diverges` gives `Σ 1/p = ∞` while `π(N)/N → 0`,
so no `ε` satisfies `ε·N ≤ #(A ∩ [0,N))` for every `N`. Any argument routed
through positive lower density is therefore not merely unproved but unavailable.

What this file proves outright:

* `three_ap_of_dense` — one window dense enough for the corners bound already
  forces a progression, via Roth.
* `block_card_le` — a progression-free set meets the dyadic block `[2^j, 2^(j+1))`
  in at most `rothNumberNat (2^j)` points, since progression-freeness is
  translation invariant.
* `summable_of_blocks` — if `Σ_j r₃(2^j)/2^j` converges then a progression-free
  set has convergent reciprocal sum, and hence divergence forces a progression.

* `summable_blocks_of_log_bound` — a Roth bound past exponent one makes those
  block terms sum. The exponent is the whole content: at `ε = 0` the comparison
  series is harmonic.
* `erdos_problem_3_k3_of_roth_bound` — the conclusion from that bound alone.

What it assumes: one axiom, `Szemeredi.bloom_sisask_upper_bound`
(arXiv:2007.03528), `r₃(N) ≤ C·N/(log N)^(1+c)` on Mathlib's `rothNumberNat`.
`erdos_problem_3_k3_unconditional` rests on it and on nothing else; every other
theorem here rests on `propext`, `Classical.choice` and `Quot.sound` alone.
-/

open scoped BigOperators Classical
open Finset