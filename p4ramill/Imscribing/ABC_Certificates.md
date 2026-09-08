# From finite readings to tail certificates

The subsequent [ABC_LogBounds.md](ABC_LogBounds.md) development provides
checked logarithm bounds and a Lean certificate generator for the complete
c ≤ 9 window. The larger numerical readings below use the original reader.

`ABC_Certificates.lean` adds three checked interfaces:

* `WindowEnclosure` carries real lower and upper bounds and proofs that
  they enclose the exact window maximum.
* `TailCertificate` combines such a finite enclosure with a bound for
  every triple beyond the cutoff. The global bound is the maximum of
  the two upper bounds.
* Bounds at epsilon = 1/(n+1) suffice for all positive epsilon. Discrepancy
  and the window maximum are antitone in epsilon, and these reciprocal
  values approach zero. A family of tail certificates at these values
  constructs a held Witness containing arithmetic and spectral evidence.

No tail certificate for the general arithmetic family is instantiated.

## Rational interval reader

`scripts/abc_spectral_readings.py` enumerates all ordered positive coprime
triples up to the requested c cutoff. Prime-support logs are accumulated
by a prime sieve. Pairwise coprimality makes the log-radical of abc the sum
of the three separate support logs.

For x in [1,2], put z=(x-1)/(x+1). The reader uses

    log x = 2 Σ_{j=0}^{m-1} z^(2j+1)/(2j+1) + R
    0 ≤ R ≤ 2 z^(2m+1)/((2m+1)(1-z²)).

This follows by integrating the geometric series for 2/(1-z²); the positive
tail is bounded by replacing its denominators by the first tail denominator.
Integer arguments are reduced as n=2^k x. The script uses exact fractions
for the series and rounds outward to a fixed-point denominator of 10^30.
All subsequent discrepancy and maximum calculations use integer arithmetic.
JSON includes exact rational bounds, outward-rounded decimal bounds, and
the triples attaining the largest lower and upper endpoints.

This is an analytic interval implementation, not a Lean certificate
generator. The log-series remainder argument and Python execution are not
yet connected by proof terms to `WindowEnclosure`. The script does not
claim to certify the infinite tail or produce a `TailCertificate`.

## Readings

Command:

```
python3 scripts/abc_spectral_readings.py --cutoffs 100 1000 5000
```

Results are saved in `ABC_Spectral_readings.json`. Values below abbreviate
the enclosed largest discrepancy; exact endpoints are in that file.

| c cutoff | Ordered triples | ε=0.01 | ε=0.1 | ε=1 |
|---|---:|---:|---:|---:|
| 100 | 3,043 | 0.959240 | 0.653132 | -0.693147 |
| 1,000 | 304,191 | 1.456715 | 1.110713 | -0.693147 |
| 5,000 | 7,600,457 | 2.983083 | 2.501844 | -0.693147 |

At cutoff 5,000, the lower-bound witness for both small epsilons is
(1,4374,4375). At epsilon=1 it is (1,1,2). These are finite readings;
the increase at the small epsilons establishes neither divergence nor
convergence of the exhaustive sequence.

## Validation

The reader's `--self-test` checks 200 integer-log enclosures against
90-digit Decimal logarithms, its radical sieve against independent trial
division, and six finite-window maxima and counts against a separate
high-precision enumeration. All checks passed. The Decimal checks are
regression tests, not proofs of interval soundness.

Lean build: `lake build Imscribing.ABC_Audit`. The audit includes the seven
new theorems and the Witness constructor.

Verified 2026-09-08: build passed (8041 jobs). All eight new audited
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. Log: `/tmp/abc-certificates-build.txt`.
