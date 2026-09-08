# Tail Regime Closure

`ABC_TailRegime.lean` packages the exhaustive arithmetic trajectory as a
closed computational regime at a fixed `ε`. `exactTailRegime ε` reads the
window maximum at every scale, proves that the readout is monotone, records a
maximizing triple at each finite scale, and gives every triple a cofinal scale
at which its discrepancy is below the readout.

`tailClosureWitness ε` keeps finite attainment and cofinal coverage as the two
fields of a `Verdict.held` value. Its classifier is therefore mechanically
`(true, true)`, while the readout remains the actual window trajectory. This
is the computational Closure object; a separate asymptotic scalar can consume
the trajectory when that scalar is part of the selected regime.

Validation: `lake build Imscribing.ABC_Audit` passed at 8049 jobs. The compiled
tail regime was audited by Vox with T=8, B=5, N=62, F=0 and 100% coverage of
1,974 code bytes. Report: `/tmp/abc-tail-vox/audit.txt`.
