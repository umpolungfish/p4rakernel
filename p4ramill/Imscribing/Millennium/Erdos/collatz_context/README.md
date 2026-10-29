# Collatz context

What is proved and measured, for grounding an ob3ect.

The map is the shortcut Collatz map, `col n = n/2` on evens and `(3n+1)/2` on odds.

Proved, *sans* sorry on propext / Classical.choice / Quot.sound, in
`CollatzDepthSplit.lean`:

- `col_shift`: over a residue class `r` mod `2^k` the k-fold iterate is affine,
  `3^j * t + col^[k] r`, with `j` the odd-step count read off the class.
- `pow_mul_le_iterate`, `le_iterate_of_not_contracts`, `no_member_descends`: the
  class criterion `3^j < 2^k` is exact, and the constant never decides anything.
- `survives_succ_of_odd`, `exists_survivor_lift`, `survivors_nonempty`: the set of
  classes that contract at no depth is non-empty at every depth.
- `survives_succ_of_slack`, `contracts_succ_of_even_step`: the branch dichotomy in
  the slack coordinate `s = j*log2 3 - k`.
- `col_two_mul`, `col_odd_pred`, `preimage_cases`, `odd_pred_iff`: the
  predecessors of `m` are `2m` always, and `2t+1` exactly when `m = 3t+2`.
- `card_predStep`: one level of the predecessor tree has count
  `L.card + (L.filter (· % 3 = 2)).card`.
- `two_coprime_three_pow`, `double_inj_mod`, `odd_map_inj_mod`, `two_inv_mod`:
  both maps building a level are bijections on residues mod `3^r`.

Measured, in the census files here:

- Forward survivor density decays at `0.96590655` per level with a `k^(-3/2)`
  prefactor, read to `k = 2000`.
- Predecessor tree branch factor converges to `4/3`, a quarter of nodes odd.
- Deviation of a level from uniform on residues mod `3^r` decays geometrically,
  eight-level rate `0.81`–`0.87` mod 27, deviation `0.298` at `k = 25` down to
  `0.025` at `k = 40`.

Vox verdicts on every declaration are in `vox_verdicts.txt`: no B, no F.
