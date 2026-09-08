# Arithmetic operator readings

The exhaustive sequence and convergence equivalence are developed in
`ABC_Exhaustion.lean` and documented in [ABC_Exhaustion.md](ABC_Exhaustion.md).

`ABC_Spectral.lean` formalizes the operator interpretation of arithmetic
discrepancy without replacing the underlying arithmetic definitions.

For a finite family `family : Fin n → Triple`, define the real matrix

    Dε(i,j) = if i=j then log(c_i) - (1+ε) log(rad(a_i b_i c_i)) else 0.

The development proves its coordinate action and characterizes every real
eigenvalue using the explicit nonzero-eigenvector equation. Its eigenvalues
are exactly the discrepancies of the family. Every nonempty finite family
has an attained largest eigenvalue. The empty family has no eigenvalues.

`UniformSpectralUpperBound` chooses C after ε but before the family size,
the triples, and the eigenvalue. `uniform_spectral_iff_abc` proves this
condition equivalent to the arithmetic ABC statement. Singleton families
supply the reverse implication; no exhaustion or convergence assumption
is hidden in that direction.

For squarefree-c families all eigenvalues are nonpositive, by the previously
proved arithmetic estimate. `spectralClosure` holds the arithmetic result
and uniform spectral evidence together, with a checked B classification.

## Retained and separated claims

The computational object, its finite readings, and the uniform arithmetic
statement now have an explicit mathematical connection. A largest
eigenvalue supplies the relevant one-sided bound. Spectral radius would
also bound negative eigenvalues in absolute value, a different condition.

Repeated prime powers affect diagonal entries in this construction. An
off-diagonal ladder requires separately specified transitions and a theorem
connecting its readings to these discrepancies. This signed matrix is not
declared to be a positive operator-valued measure. No claim that proof is
impossible, that B encodes matrix entries, or that finite numerical readings
alone establish a uniform bound is used as an assumption.

The existence of a maximum for each finite family and one constant valid
for all families are separately quantified statements. The latter is the
full scale-Closure datum, expressed here in operator language.

## Validation

The module is registered in Lake and imported by `ABC_Audit.lean`, which
prints dependencies for its six theorems and its Witness constructor.
Build command: `lake build Imscribing.ABC_Audit`.

Verified 2026-09-08: build passed (8039 jobs). All seven new audited
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`;
none depends on `sorryAx`. Log: `/tmp/abc-spectral-build.txt`.
