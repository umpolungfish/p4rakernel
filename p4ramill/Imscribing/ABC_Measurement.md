# Finite ABC Measurement

`ABC_Measurement.lean` makes a finite reading executable as a typed record.
`FiniteMeasurement.ofEnclosure` selects an attained maximizing triple from a
certified window, attaches its calibrated IUTT packet, and exposes the exact
height/radical coordinates. Its `witness` retains the enclosure lower reading
and upper reading as a `Verdict.held` measurement.

Concrete measurements are instantiated at the certified scales `N=7` and
`N=30` for `ε=1/10`.

Validation: `lake build Imscribing.ABC_Audit` passed at 8052 jobs. Vox reports
T=8, B=5, N=65, F=0 with 100% coverage of 2,070 code bytes. Report:
`/tmp/abc-measure-vox/audit.txt`.
