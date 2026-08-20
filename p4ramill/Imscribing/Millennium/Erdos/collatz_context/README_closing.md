# The one inequality left

Everything below is proved and sorry-free in `CollatzDepthSplit.lean`, or measured
in `closing_measurements.txt` by the verbs named.

The level map on the predecessor tree contracts the collision excess in the
weighted norm `‖e‖ = sup_r 3^(-r) e(r)`, where `e(r) = 3^r C(r)/N^2 − 1` and
`C(r)` counts level pairs sharing a residue mod `3^r`.

Three legs, two of them forced:

- doubling with doubling — exactly the previous level's `C(r)`, since `2a ≡ 2b`
  iff `a ≡ b` mod `3^r` (`double_collide_iff`);
- odd with odd — the junction population over the `3^r` junction classes mod
  `3^(r+1)`, since the arm map is a bijection on residues (`arm_collide_iff`,
  `arm_bijection_mod`);
- mixed — `2 Σ_c n_r(c) m(φ(c))` with `φ(a) = 3(a − 2⁻¹) + 2` a bijection from
  classes mod `3^r` onto junction classes mod `3^(r+1)`.

The first two give `(9/16) e(r) + (1/16) e(r+1)`, and the weight pays the 3 the
digit costs, so they contract at `3/4` per level. The tower is finite: classes go
empty once `3^r > N`, about `0.262 d` rungs, and the top saturates at `3^r/N`.

**What is missing.** A bound on the mixed leg in the same weighted norm, with a
constant `c` leaving `3/4 + c < 1`. Cauchy–Schwarz gives `|cross| ≤ 2√(δ_even
δ_odd)` and that holds in every measured row at every conductor; what is not
established is that bound carried through the `3^(-r)` weighting.

Measured, the full map including the mixed leg contracts at mean `0.76` over
sixteen levels, and `‖e‖ × N` sits at one. The mixed leg's deviation is
systematically negative — 20 of 24 levels at conductor 3, mean `−0.140` — which
the doubling involution explains: `2` has order two mod 3, so the two live classes
swap every level (`double_swaps_classes`), and the imbalance obeys the exact
integer identity `I_(d+1) = −I_d + (m₂ − m₈)` (`junction_classes_split`), verified
at every level to depth 30 except where the tree cuts its own cycle edge.
