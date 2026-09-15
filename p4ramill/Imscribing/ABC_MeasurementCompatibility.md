# Measurement Compatibility

`ABC_MeasurementCompatibility.lean` proves that every finite measurement in a
`MeasurementChain` lies below any supplied IUTT asymptotic limit. It also
retains the exact packet calibrations and packages the finite-to-asymptotic
relationship as a held Witness.

Validation: `lake build Imscribing.ABC_Audit` passed at 8054 jobs. Vox reports
T=8, B=5, N=65, F=0 with 100% coverage of 2,086 code bytes. Report:
`/tmp/abc-compat-vox/audit.txt`.
