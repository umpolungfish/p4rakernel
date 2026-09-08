# abc: formal statement and arithmetic bridge

`ABC.lean`, namespace `Imscribing.ABC`, continues `IUTT.lean` with actual
natural-number arithmetic. `ABC_Audit.lean` audits 44 arithmetic and Witness
declarations, including every theorem in both modules.

## The conjecture

For every real ε>0 there exists a real K>0, independent of the triple,
such that c ≤ K rad(abc)^(1+ε) for positive coprime a,b with a+b=c.
`Triple` packages these hypotheses; its pairwise-coprimality theorem also
establishes coprimality with c. `StandardStatement` spells out the quantifiers
without the structure, and `conjecture_iff_standard` proves equivalence.

The radical is Mathlib's `UniqueFactorizationMonoid.radical`. The theorem
`radical_eq_primeFactors` identifies it with the product of distinct natural
prime factors. Mathlib sets rad(0)=1; zero never occurs in admissible abc
products, so this convention does not affect the statement. The proofs
include positivity, prime and prime-power behavior, and rad(216)=6.

For (a,b,c)=(1,8,9), rad(abc)=rad(72)=6. The checked example rejects the
stronger, false bound c ≤ rad(abc).

## What is proved

`conjecture_iff_log_estimate` establishes the exact equivalence with

    ∀ ε>0, ∃ C, ∀ t,
      log(c_t) ≤ (1+ε) log(rad(a_t b_t c_t)) + C.

The reverse implication constructs K=exp(C); the forward uses C=log(K).
Positivity needed for every logarithm and real power is proved.

`conjecture_iff_uniform_discrepancy` rewrites this as a bound on

    discrepancy ε t = log(c_t) − (1+ε) log(rad(a_t b_t c_t)).

For a concrete connection to `IUTT`, `arithmeticPacket t` is the packet

    (log(rad(abc)), 0, log(c)/4).

Its j²-weighted evaluation is exactly log(c); coordinate zero retains
log(rad(abc)). `arithmeticRecord` retains the full Ftf carrier beside this
packet. These calibration identities are proved. This is a deliberately
explicit encoding, not a derivation of arithmetic data from a Hodge theater.

`abc_of_filtered_estimate` proves that a uniform estimate on these calibrated
packets implies abc. `abc_of_calibrated_filtered_bound` provides the same
interface for any filtered space with calibrated height and conductor
observables. The final exponentiation argument needs the calibration and
bound, not the filtration itself: the filtration must do its work upstream,
in a proof of the bound. Merely supplying a filtration cannot supply it.

## Witness and Closure

`ABC_Witness.lean` uses the existing
`Imscribing.Paraconsistent.DialetheicWitness.Verdict`:

* `primeSupportWitness` holds rad(1·8·9)=6 together with 9>6.
* `filteredRepresentationWitness` holds exact log-height calibration
  together with the weighted evaluator's non-factorization through the
  position-blind scalar map.
* `arithmeticClosure estimate` holds the abc conclusion supplied by a
  `FilteredEstimate` together with tensor non-factorization.

All three classify as B. The input to `arithmeticClosure` is an explicit
proof argument; its B tag does not supply that argument. The concrete
Witness tags compile as data, while their proof fields are erased.

The integrated filtered/log Witness is `abcVerdict h_filtered`:
its first field is `LogEstimate`, obtained by the checked equivalence,
and its second is the supplied `FilteredEstimate`. `abcVerdict_is_B`
verifies the tag. `iutt_abc_dialetheia` exposes the same construction.

`abc_of_verdict` consumes positive support (T or B) and extracts the
log-estimate proof. `abc_from_filtered_via_verdict` supplies that support
from the constructed Witness, completing the filtered → held → abc chain.
`abc_of_verdict_refined` returns `Option (PLift Conjecture)`: T and B
produce a proof-bearing value; F and N produce none. The theorem
`verdict_extraction_tracks_positive` checks all four branches.

`PLift` is required because `Option` stores Type-valued data, whereas
`Conjecture` is Prop-valued. A Type-valued Witness is declared with `def`.
The supplied sketch's incomplete branches are replaced by total, checked
definitions; no admission is converted into positive support.

## Quality bound

`quality t = log(c)/log(rad(abc))`. The arithmetic proves rad(abc) ≥ 2,
hence log(rad(abc)) ≥ log 2 > 0 for every admissible triple.
Given `LogEstimate`, choose its ε=1 constant C. The proved uniform bound is

    quality t ≤ 2 + max C 0 / log 2.

The coefficient is 2 because 1+ε=2. The maximum handles a negative C
without reversing a denominator comparison. `quality_bounded_of_log_estimate`
proves the bound once. `quality_bounded_of_held_verdict` extracts it from
T/B support; `quality_bound_or_nonpositive` gives the total alternative:
a bound, an F verdict, or an N verdict.

## Uniform estimate

`FilteredEstimate` and `UniformDiscrepancyBound` are defined propositions,
not axioms and not proved theorems. The missing result is a constant C_ε
uniform over all admissible triples. The current packet construction proves
representation and calibration only. `IUTT`'s information-retention theorem
does not bound this arithmetic discrepancy.

There is no unconditional `theorem abc_proved` in this module.

## Existing file not reused

`Millennium/GoldbachABC.lean` is not imported or modified. Its local radical
returns 1 for all n>1, and its abc declaration depends on an additional
Goldbach/abc equivalence axiom and an unfinished Goldbach proof. Those cannot
serve as the arithmetic basis or proof of the statement defined here.

## Reproduction

```sh
lake build Imscribing.ABC Imscribing.ABC_Audit
lake env lean Imscribing/ABC_Audit.lean
```

The new files contain no added axioms, sorry placeholders, or native_decide
proofs. Their dependency audit is kept separate from compiled control-flow
auditing, which cannot recover erased proof terms.

Verified 2026-09-08: targeted Lake build passed (8033 jobs including
dependencies). All 22 axiom reports were checked and contain no sorryAx.
The compiled linked ELF `/tmp/abc-vox/ABC.so` was audited with Vox:
T=8, B=5, N=67, F=0, with 100% reported coverage of 2229 code bytes.
The report is `/tmp/abc-vox/audit.txt`.

After the Witness/quality integration: the combined Lake build passed
(8036 jobs), and all 44 declaration reports contain no sorryAx.
The compiled Witness ELF `/tmp/abc-witness-vox/ABC_Witness.so` reports
T=8, B=7, N=104, F=0, with 100% coverage of 3491 code bytes.
Its report is `/tmp/abc-witness-vox/audit.txt`.
