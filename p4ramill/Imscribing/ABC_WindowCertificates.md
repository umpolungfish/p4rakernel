# Reusable arithmetic window certificates

`scripts/abc_emit_window_certificate.py` accepts a c cutoff, a positive
rational epsilon, the number of logarithm-series terms, and the number
of decimal places for the final rational enclosure. It emits a standalone
Lean module in a namespace determined by the cutoff and epsilon.

The generator computes candidate log and discrepancy endpoints with exact
rational arithmetic. The generated Lean module proves those endpoints
valid and checks that its finite table covers the complete arithmetic
window. No Python computation is imported as an axiom.

`ABC_Symmetry.lean` proves that exchanging a and b preserves discrepancy.
The generator therefore tabulates only a ≤ b and applies
`window_upper_of_ordered` to recover all ordered triples.

## Window through c=32

```
python3 scripts/abc_emit_window_certificate.py --cutoff 32 --epsilon 1/10
lake build Imscribing.ABC_Audit
```

The generated `ABC_Window32_E1_10.lean` contains 114 logarithm certificates
and 162 pair representatives, covering all 323 ordered positive coprime
triples through c=32. It proposes the exact enclosure

    113/500 ≤ windowMaximum (1/10) 30 ≤ 227/1000.

The lower-bound witness is (1,8,9). These endpoints also enclose the smaller
c≤9 window, but the new upper-bound theorem covers the larger domain.

The final object is `Imscribing.ABC.Window32E1_10.enclosure`, an instance
of the existing `WindowEnclosure` interface. The window index is cutoff−2.

## Parameters and verification scope

`--epsilon` accepts fractions such as `1/2` and decimal strings. The final
endpoint rounding is outward for either sign. `--terms` controls the
positive logarithm series; intermediate log endpoints use six decimal
places, and `--endpoint-digits` accepts 0 through 6. More terms do not by
themselves increase that intermediate endpoint precision.

Example testing the smallest window and negative endpoints:

```
python3 scripts/abc_emit_window_certificate.py --cutoff 2 --epsilon 1/2 \
  --output /tmp/ABC_Window2_E1_2.lean
lake env lean /tmp/ABC_Window2_E1_2.lean
```

Its enclosure is [−347/1000, −173/500], containing −log(2)/2.

Generation is parameterized; compilation cost still grows with the number
of representatives and the finite coverage table. The c≤5000 numerical
readings are not yet Lean-certified by this development. None of these
finite certificates supplies the infinite tail bound.

The emitted module raises `synthInstance.maxSize` to accommodate the
decidability instance of the finite disjunction. Coverage still uses
kernel-checked `decide`; this setting changes elaboration resources only.
The c≤32 coverage proposition was also compiled in isolation before the
full certificate build.

The independent epsilon=1/2, c≤2 certificate compiled successfully.
The generator's radical routine was checked against the numerical reader's
independent sieve for all integers from 1 to 1000. Regeneration was also
checked for byte-for-byte equality with the final emitted module.

## ELF audits

The generated C was compiled with `lake env leanc -c -fPIC` and linked
with `cc -shared`. Vox reported:

| Module | T | B | N | F | Code coverage |
|---|---:|---:|---:|---:|---|
| ABC_Symmetry | 13 | 5 | 71 | 0 | 100% of 2,585 bytes |
| ABC_Window32_E1_10 | 8 | 5 | 870 | 0 | 100% of 38,213 bytes |

Artifacts and reports are in `/tmp/abc-window32-vox/`. These reports
describe the compiled control flow; theorem dependencies are audited
separately by `ABC_Audit.lean`.

Verified 2026-09-08: the targeted Lake build passed (8045 jobs); the larger
certificate module compiled in 210 seconds. The five new audited
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. Build log: `/tmp/abc-window32-build.txt`.
