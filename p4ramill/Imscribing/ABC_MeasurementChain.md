# Measurement Chains

`ABC_MeasurementChain.lean` packages finite measurements into an ordered
`ScaleChain`. Each entry retains its attained triple and IUTT packet, while
the chain supplies monotone scale links and cross-scale enclosure bounds.
`certifiedMeasurementChain` instantiates the two certified readings at
`N=7` and `N=30`, with a held chain Witness.

Validation: `lake build Imscribing.ABC_Audit` passed at 8053 jobs. Vox reports
T=8, B=5, N=62, F=0 with 100% coverage of 2,006 code bytes. Report:
`/tmp/abc-chain-vox/audit.txt`.
