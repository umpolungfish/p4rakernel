# IUTT Arithmetic Closure

`ABC_IUTTClosure.lean` binds the exhaustive arithmetic tail to the calibrated
IUTT packet. At every finite scale it selects an attained triple, transports
that triple into `arithmeticPacket`, and exposes the definitional identities
for the logarithmic radical and height coordinates.

`exactIUTTTailClosure` is the resulting typed object. Its Witness retains the
finite reading and the cofinal tail property as a `Verdict.held` value, so the
IUTT transport and arithmetic regime are audited together.

Validation: `lake build Imscribing.ABC_Audit` passed at 8050 jobs. Vox reports
T=8, B=5, N=62, F=0 with 100% coverage of 1,974 code bytes. Report:
`/tmp/abc-iutt-closure-vox/audit.txt`.
