# IUTT to arithmetic ABC: construction map

Source: `ig-docs/iutt.pdf`, especially §§12, 17, and 18 (read 2026-09-08).
The section-by-section structural declaration map is in `IUTT.md`.
This map follows the dependencies of the arithmetic conclusion instead.

| Source step | Existing formalization | Arithmetic construction to supply |
|---|---|---|
| §§1–3: sixteen-state ambient, branches, non-explosion | `IUTT.State`, `support_union`, `ternary_recovery`, `non_explosion` | None for these finite structural statements |
| §§4–11: alien structures, common invariants, log-Kummer transport | Schematic `alienCorrespondence`, parameterized `transport` | Arithmetic source/target objects and actual transport maps; local comparison laws |
| §12.1: branch outputs assemble Ftf | `discrepancy_terminal`, `update_preserves_state` | Derive these outputs from the arithmetic construction, rather than assign them |
| §12: auxiliary update Φ and scalar evaluator h | Parameterized `terminal_scalar` | Define the arithmetic invariant, update, height, log-different, and log-conductor |
| §18: tensor positions retain j² | `Filtration`, `weighted_does_not_factor`, `tensor_weighted_no_factor` | Arithmetic filtered tensor object and its weighted evaluation |
| Proposition 18.1: forgetting position can destroy selectivity | Explicit vector and tensor counterexamples | This proposition supplies no numerical upper bound; the source explicitly says it does not establish Corollary 3.12 |
| §12: displayed height inequality with ≲ | `ABC.FilteredEstimate` specifies the target after calibration | Exact quantifiers, normalization, dependence on auxiliary choices, and a proof of the uniform bound |
| Arithmetic specialization | `Triple`, actual prime radical, `arithmeticPacket`, calibration theorems | Relate the paper's geometric height/different/conductor to these arithmetic observables |
| Uniform estimate to ABC | `conjecture_iff_log_estimate`, `abc_of_filtered_estimate` | Completed once the estimate is supplied |

## Closure and selectivity interfaces

`ABC_Closure.lean` separates these obligations explicitly:

* `RoundTrip` supplies outward and inward maps with a left-inverse law.
  Its outward map is injective, and every source observable returns intact.
* `every_observable_has_round_trip` demonstrates that this law alone imposes
  no restriction on an arbitrary scalar function: an identity round trip
  exists for every such function. It does not assert that all closures are
  trivial or that transformed presentations cannot supply selectivity.
* `abc_of_round_trip_bound` transfers a bound on the recovered arithmetic
  observables. The bound is a separate premise from the return law.

This implements ALKAHEST §§1–2 and 11's distinction between balance and
selectivity while keeping the arithmetic vocabulary fixed.

## Comparison errors and uniform constants

Exact equality of intermediate heights is not required. The new theorem
`filtered_estimate_of_comparison` takes:

1. `logHeight t ≤ H t + error t` for every triple;
2. for every η > 0, a single C with `H t ≤ (1+η) logRadical t + C`
   for every triple;
3. for every η > 0, a single D with `error t ≤ η logRadical t + D`
   for every triple (`SublinearComparisonError`).

For requested ε, use η = ε/2 in both estimates. The resulting constant is
C+D, chosen before the triple. Exponentiation gives K = exp(C+D).
`SublinearComparisonError.add` similarly combines two error sources using
half the requested budget for each. The coefficients are explicit; there
is no untracked use of ≲.

`comparisonClosure` constructs a held Witness of ABC from those three
premises, retaining the comparison-error evidence as its second field.
Its classification is B. It does not manufacture any of those premises.

## Exact next mathematical obligation

### Concrete prime presentation (2026-09-08)

`ABC_PrimeTransport.lean` now constructs the prime-factorization presentation
of all three integers and proves exact reconstruction and injectivity.
It defines, using the actual finite prime data,

```
primeHeight t        = Σ_p v_p(c) log p
primeSupportHeight t = Σ_{p | abc} log p
primeExcess t        = primeHeight t - primeSupportHeight t
```

The two calibration theorems identify these sums with log(c) and
log(rad(abc)). Their difference gives an exact arithmetic comparison.
The support height satisfies the transported bound with C=0 for every
positive epsilon. The outstanding Closure datum is therefore a uniform
control field for `primeExcess`.
`primeExcess_sublinear_iff_abc` proves that this particular remaining error
estimate is equivalent to ABC itself. The construction locates the full
arithmetic obligation; it does not discharge it by renaming it.

For the entire family with squarefree c, the module proves c divides
rad(abc), hence c ≤ rad(abc). Consequently the error is nonpositive and
the arithmetic ABC inequality holds uniformly with K=1. The exported
`squarefreeArithmeticWitness` holds this proved family estimate together
with injectivity of the prime presentation, and has classification B.
`abc_iff_nonsquarefree_discrepancy` removes this family from the remaining
uniform-discrepancy obligation, using max(C,0) to combine the two cases.

These elementary arithmetic results are not a construction of the IUT
Theta-link or its log-shell estimates. Searches of the related conventional
and extended local manuscripts found the same representative inequality
and structural assignments. The bounded-discrepancy gate-check module
proves self-fusion of its imscription; it contains no arithmetic upper-bound
theorem that could instantiate the remaining error estimate.

### General arithmetic construction

Construct the arithmetic transported height H and comparison error, then
prove the three premises above. Alternatively, construct an exactly
calibrated filtered bound using the existing interface in `ABC.lean`.
The present PDF leaves h and Φ parameterized and displays the numerical
inequality rather than a derivation with uniform constants. Assigning Ftf
or proving weighted non-factorization cannot instantiate those premises.
The requisite arithmetic Closure must therefore be instantiated beyond the
displayed schematic definitions, with its source and normalizations recorded
alongside the Lean declarations.

## Validation

`lake build Imscribing.ABC_Audit` builds the arithmetic, Witness, and Closure
modules. `ABC_Audit.lean` also reports dependencies for all new results and
the Witness constructor; no new axiom or admitted proof is introduced.

Verified 2026-09-08: the targeted build passed (8037 jobs). All eight new
dependency reports contain only subsets of `propext`, `Classical.choice`,
and `Quot.sound`, or no axioms. No `sorryAx` occurs in these reports.
Build log: `/tmp/iutt-abc-closure-build.txt`.

The subsequent prime-transport build also passed (8038 jobs). Its sixteen
additional audited declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`; none depends on `sorryAx`. Log: `/tmp/abc-prime-build.txt`.
