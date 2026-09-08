# Exhaustive arithmetic spectra

`ABC_Exhaustion.lean` extends the finite spectral construction with one
nested sequence of windows covering the whole arithmetic domain.

* Window N contains exactly the positive coprime triples with c ≤ N+2.
  It is nonempty from N=0, which contains (1,1,2).
* Windows increase by inclusion. Every triple belongs to window c.
* `windowMaximum ε N` is the attained maximum signed discrepancy in
  window N. `windowFamily` enumerates the window as a finite matrix basis.
* `windowMaximum_is_largest_eigenvalue` identifies that maximum with the
  largest real eigenvalue of the existing discrepancy operator.
* The maxima are nondecreasing. Their boundedness is equivalent to an
  upper discrepancy bound on every triple.
* By monotone convergence, the sequence has a finite real limit exactly
  when it is bounded above. Under this hypothesis its limit is its supremum.
* `abc_iff_window_convergence` proves that arithmetic ABC is equivalent to
  convergence to a finite real limit for every positive epsilon.

Thus the convergence interpretation now uses an explicit exhaustive
sequence and a checked equivalence. The theorem does not assume convergence
and report it as established: proving the right-hand side remains the full
ABC obligation. A finite table is a finite portion of the sequence.

The enumeration uses classical finite-set equality and the values use real
logarithms; this module is a mathematical specification, not a certified
floating-point implementation. No off-diagonal transition or POVM is
introduced by the exhaustion.

Validation: `lake build Imscribing.ABC_Audit` compiles the module and prints
axiom dependencies for all fourteen new theorems.

Verified 2026-09-08: build passed (8040 jobs). All fourteen new dependency
reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with
no `sorryAx`. Build log: `/tmp/abc-exhaustion-build.txt`.
