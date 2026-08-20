# The gap, enumerated

Everything named here is proved and sorry-free in `CollatzDepthSplit.lean`, or
measured by the verb named, with the outputs in `closing_measurements.txt`.

**The object.** One level of the Collatz predecessor tree maps to the next by two
arms: doubling `m ↦ 2m`, always, and the odd lift `m ↦ 2t+1` for `m = 3t+2`. The
collision excess `e(r) = 3^r C(r)/N² − 1` measures a level's distance from uniform
on residues mod `3^r`, and `‖e‖ = Σ_r 3^(-r) e(r)` over the finite tower `3^r ≤ N`.

**Proved.**
- The level map contracts its linear part at exactly `3/4`: the doubling leg is
  the previous `C(r)` by `double_collide_iff`, the odd leg is the arm image by
  `arm_collide_iff` and `arm_bijection_mod`, and the weight `3^(-r)` pays the digit
  the odd arm costs.
- The cross leg is exactly the correlation of the two deviations, no remainder:
  `cross_decompose`.
- Its negativity has a source: a mean-zero function's autocorrelations sum to zero
  over all lags, `autocorr_sum_zero`, so the nonzero lags cannot all be positive.
- At conductor 3 the doubling permutation is an involution — `double_swaps_classes`,
  `double_involution`, `two_order_mod_three` — and the identity is exact:
  `I_{d+1} = −I_d + (m₂ − m₈)`, verified in integers at every level to depth 30.
- At conductor 9 the permutation is a six-cycle, `two_order_mod_nine`, and the
  identity is exact there too: `even_child_mod_nine`, `odd_child_mod_nine`,
  `oddSource_feeds`, verified over all nine classes to depth 30.
- The residue structure forces a Fibonacci ceiling and not `2^d`:
  `subtreeCount_le_classBound`.

**Measured, stable across eight orders of magnitude.** Branch factor `4/3`; mean
amplitude `6`; Birkhoff weight `3/4`; character sums at `N^(-1/2)`; collision legs
at `9/16, 1/16, 6/16`; cross term negative in 20 of 24 levels at conductor 3; mean
`c` negative at every tower depth.

**The gap, and why the enumerated structure does not close it.**
- `sup c < 1/4` is FALSE — the oracle found level 25, `N = 885`, `c = +0.3565`.
- `E[c] < 1/4` is TRUE and is the decay itself: the log-ratios telescope, so the
  geometric mean over a window is the endpoint ratio, `0.72761` against a measured
  `0.72645`. Proving it is not a reduction.
- Cauchy–Schwarz gives `|cross(r)| ≤ (3/8)√(e_even e_odd)`, hence `c ≤ 1.30`,
  where `0.25` is needed. It is TIGHT at conductor 3 — `|cos|` reaching `0.998` —
  and loose at conductor 27, so no single constant covers both regimes.

So what is wanted is an input to the *average* of the cross correlation which the
residue bijections, the involution, the lag sum rule and the two low identities do
not already supply, and which is not a restatement of the decay.
