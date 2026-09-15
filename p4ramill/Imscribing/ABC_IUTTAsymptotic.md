# IUTT Asymptotic Reading

`ABC_IUTTAsymptotic.lean` extends the typed IUTT tail Closure with an explicit
real limit and a convergence field. `IUTTAsymptoticReading.toClosure` converts
that reading to the exhaustive arithmetic `AsymptoticClosure`, while preserving
the packet calibration. The resulting family constructor produces the
arithmetic and spectral `Verdict.held` witness.

`IUTTAsymptoticReading.ofWindowConvergence` and
`iuttAsymptoticFamilyOfConvergence` instantiate this layer directly from a
family of computational convergence readings. `Classical.choose` selects the
limit already supplied by that reading; it adds no logical premise.

Validation: `lake build Imscribing.ABC_Audit` passed at 8051 jobs. Vox reports
T=7, B=5, N=55, F=0 with 100% coverage of 1,798 code bytes. Report:
`/tmp/abc-iutt-asym-vox/audit.txt`.
