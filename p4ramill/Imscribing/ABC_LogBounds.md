# Proof-carrying finite logarithm readings

`ABC_LogBounds.lean` connects finite rational approximations to Lean's real
logarithm. For x ≥ 1, write z=(x-1)/(x+1). It proves

    S_m(x) ≤ log x ≤ S_m(x) + 2 z^(2m+1)/(1-z²),
    S_m(x) = 2 Σ_{i<m} z^(2i+1)/(2i+1).

The proof uses Mathlib's `Real.sum_range_le_log_div` and
`Real.log_div_le_sum_range_add`. The displayed remainder is deliberately
looser than the original numerical reader's remainder by a factor 2m+1,
so the certificate follows the existing library theorem directly.

`log_binary_enclosure` proves the range-reduction rule for n=2^k x.
`LogEnclosure n` contains rational endpoints and proofs that they enclose
log n. `discrepancy_enclosure` propagates height and radical log enclosures,
reversing support endpoints when subtracting (1+ε) times the radical log.

## First complete window certificate

`scripts/abc_emit_small_certificate.py` emits `ABC_SmallCertificate.lean`.
It proposes endpoints from exact rational arithmetic, then emits Lean
proofs using the above lemmas and `norm_num`. The generated file contains:

* 13 integer-log certificates, using six series terms and binary reduction;
* an arithmetic discrepancy enclosure for each of the 27 ordered positive
  coprime triples with c ≤ 9;
* an exhaustive proof by bounded cases that every such triple is covered;
* a lower-bound witness (1,8,9);
* `certifiedWindowNine : WindowEnclosure (1/10) 7` with endpoints 226/1000
  and 227/1000. Window index 7 means c ≤ 9, by the exhaustive-window definition.

Python is a proof generator here: an incorrect proposal must still pass
the Lean proofs. The generated module does not use `native_decide`, new
axioms, or admitted proof terms. Its exact arithmetic and analytic bounds
are checked as part of the ordinary Lean build.

This certificate covers the small window. The existing c ≤ 5000 JSON
readings remain numerical interval results; they have not been converted
into Lean certificates. Neither a finite enclosure nor this generator
supplies the unobserved tail bound.

Regenerate and build from p4ramill:

```
python3 scripts/abc_emit_small_certificate.py
lake build Imscribing.ABC_Audit
```

Verified 2026-09-08: build passed (8043 jobs); the generated certificate
module built in 15 seconds. All six new audited declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Log: `/tmp/abc-small-certificate-build.txt`.

A negative check replaced the proposed lower endpoint for log(2) by 7/10
in a temporary copy. Lean rejected that certificate, as expected.
Log: `/tmp/abc-rejected-log.txt`. No failing test source is imported by Lake.
