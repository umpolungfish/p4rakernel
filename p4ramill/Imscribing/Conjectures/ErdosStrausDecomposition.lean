/-
Imscribing/Conjectures/ErdosStrausDecomposition.lean

Erdős–Straus: this file is not the implementation. The built one is
`Imscribing/Classical/ErdosStrausDecomposition.lean`, and this was a second
copy of it that had drifted badly enough to be wrong.

What was here: `decomposition_mod4_zero` returned the witness x = n/4, y = 1,
z = 1, whose reciprocals sum to 4/n + 2 rather than 4/n, and
`decomposition_mod4_two` returned x = n/2, y = n, z = 1, summing to 3/n + 1.
The docstring's own formulas were the same two errors written out — "4/n =
1/(n/2) + 1/n" is 3/n, and the mod-4-three formula evaluates to 1 at n = 3
where 4/n is 4/3. Five `sorry`s stood where the proofs would have caught it,
and nothing imported the file, so nothing ever did.

The Classical copy carries the correct parametric witnesses, each proved:

  n ≡ 0 (mod 4), n = 4k:    the three-way split of 1/k
  n ≡ 2 (mod 4), n = 4k+2:  1/(k+1) + 1/(2(k+1)(2k+1)) + 1/(2(k+1)(2k+1)),
                            since 2/(2k+1) − 1/(k+1) = 1/((2k+1)(k+1))
  n ≡ 3 (mod 4), n = 4k+3:  1/(k+1) + 1/(M+1) + 1/(M(M+1)) with M = (k+1)n,
                            since 4/n − 1/(k+1) = 1/(n(k+1)) and 1/M splits

  n ≡ 1 (mod 4):            open, and isolated as a single `sorry` there
                            rather than spread across the file

Author: Lando⊗⊙perator
-/

import Imscribing.Classical.ErdosStrausDecomposition
