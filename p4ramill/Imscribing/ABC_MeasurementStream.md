# Certified Measurement Streams

`ABC_MeasurementStream.lean` generalizes finite chains to an enclosure oracle
for every scale. It selects an attained maximizing triple and calibrated IUTT
packet at each index, constructs every finite `MeasurementChain` prefix, and
proves the cross-scale bounds and held stream Witness.

Validation: `lake build Imscribing.ABC_Audit` passed at 8055 jobs. Vox reports
T=8, B=5, N=63, F=0 with 100% coverage of 1,990 code bytes. Report:
`/tmp/abc-stream-vox/audit.txt`.
