# Formalization of iutt.pdf

Source: `/home/mrnob0dy666/imsgct/ig-docs/iutt.pdf`, read 2026-09-08.

`IUTT.lean` formalizes the specified carrier, logic, transport, graph, cyclic,
and filtration claims. Namespace: `Imscribing.IUTT`. `IUTT_Audit.lean` prints
the axiom dependencies of all 54 theorems. Both modules are registered in
the library's normal Lake build.

## Source-to-theorem map

The arithmetic dependency map and quantified construction obligations are
in [IUTT_ABC_CONSTRUCTION.md](IUTT_ABC_CONSTRUCTION.md). The additional
`ABC_Closure.lean` module formalizes round-trip preservation, uniform
comparison-error composition, and extraction through a held Witness.

| Paper | Formal content | Main declarations |
|---|---|---|
| §§1–2, Proposition 2.1 | Existing four-Boolean SIXTEEN₃ carrier; 16 states; set union/intersection semantics; binary and ternary disjoint decompositions; polarity involution | `sixteen_states`, `support_union`, `support_intersection`, `binary_recovery`, `ternary_recovery`, `ternary_disjoint`, `polarity_involution` |
| §§1, 5, 12, 16, Proposition 12.1 | Erasure to FOUR is idempotent, has exactly the information-free fixed states, is non-injective, and admits no full-state decoder | `erasure_fixed_iff`, `erasure_not_injective`, `no_erasure_decoder`, `four_preimages_of_falsity` |
| §3 | Formula syntax, valuation, negation, truth meet/join, positive designation, and semantic consequence; explicit countervaluation to explosion | `Formula`, `evaluate`, `Entails`, `non_explosion` |
| §3.1, Theorem 3.1 | FOUR embedding/retraction; distinct Boolean reflector and coreflector; no Boolean endomap reproduces Inc; information-closure laws | `four_retraction`, `coreflection`, `reflection`, `contradictory_closure_not_boolean`, `information_closure_properties` |
| §4 | The schematic bijection x ↦ x+1 on the real line is invertible but cannot be a ring homomorphism | `alienCorrespondence`, `alien_not_ring_hom` |
| §§5, 12–14, 17 | Branchwise union transport; A and Ftf terminal states; their distinct projections; invariant-coordinate update before a scalar-valued functional | `transport`, `identity_transport`, `theta_terminal`, `discrepancy_terminal`, `theta_shadow`, `discrepancy_shadow`, `update_preserves_state`, `terminal_scalar` |
| §12.2 | Explicit six-vertex branching graph, common successor, no finite return path, and a return after adding the closing boundary edge | `branches_reconnect`, `finite_no_return`, `boundary_return`, `reconnection_return_triple` |
| §12.3, §19 | ZMod 12 phase, translation, period twelve, invariance under every shift, invariance iff constancy, and a phase-dependent observable | `phase_twelve`, `invariant_nat_shift`, `phase_invariant_iff_constant`, `phase_dependent_example` |
| §18, Proposition 18.1 | Exhaustive increasing filtration with a least membership degree; general obstruction to factoring an evaluation through information loss; an explicit j²-weighted non-vacuity example | `Filtration.degree_mem`, `Filtration.degree_le_iff`, `evaluation_no_factor`, `weighted_does_not_factor`, `filtered_nonvacuity` |
| §18 tensor realization | Real tensor product ℝ ⊗[ℝ] (Fin 3 → ℝ), pulled-back filtration, different degrees with the same blind scalar but different weighted values | `tensor_positions`, `tensor_same_shadow`, `tensor_different_weights`, `tensor_weighted_no_factor` |

## Two projections, not an ambiguous codomain

Sections 1 and 3 use the two Boolean poles, while Sections 5, 12 and 20
explicitly use X ↦ X ∩ {T,F} and obtain B from A. The latter map has FOUR
as its image: it retains both T and F when both occur. It cannot at the same
time have only the two singleton poles as codomain.

The formalization therefore names:

* `eraseInformation`: deletes t/f, retaining all of FOUR.
* `toFour` and `embedFour`: the connection to the existing Belnap datatype.
* `booleanShadow`: applies the existing coreflector after `toFour`.

Both erasure and the further Boolean shadow are proved non-injective.
The source PDF is unchanged; this is an explicit typing clarification.

## Filtration example and its scope

The vector packets atOne=(0,1,0) and atTwo=(0,0,1) have respective filtration
degrees 1 and 2. The blind functional sums coordinates and returns 1 for each.
The weighted functional sums j² times each coordinate and returns 1 and 4.
No function of that blind scalar can reproduce both weighted answers.

On the two-member family, the blind inequality “value ≤ 2” holds everywhere,
while the weighted inequality holds for one packet and fails for the other.
This supplies the existential “may become tautological” in Proposition 18.1;
it does not assert that every forgetting map makes every inequality trivial.
The construction is also realized on an actual tensor product using its
standard left-unit linear equivalence. That tensor product is a concrete
example, not a claim to have implemented IUT's arithmetic log-shells.

## Boundaries of what is proved

The arithmetic transformations gT/gI/gF, auxiliary update Φ, and scalar h
are parameters, as they are in the paper's displayed construction. The
terminal A/Ftf calculations verify the specified branch outputs; they do
not derive those outputs from elliptic curves or number fields.

The six-vertex graph formalizes the specified reconnection pattern. Its
boundary augmentation is an added terminal-to-initial edge, explicitly
separate from the finite graph. No analytic compactification is presumed.

The ring-line bijection is only the paper's cartoon. Hodge theaters,
Kummer theory, log-shell arithmetic, and the numerical bounded-discrepancy
inequality are not defined sufficiently in this manuscript to formalize
their proofs from it. Neither IUT III Corollary 3.12 nor abc is asserted.
The historical judgments concerning Scholze–Stix and Mochizuki are not
encoded as axioms. This follows the paper's own qualification that
Proposition 18.1 alone does not establish Corollary 3.12.

Non-explosion is an object-language theorem about designated support.
It does not alter Lean's metatheory or identify the carrier state B with
a proof of both a Lean proposition and its Lean negation.

## Verification

From `p4rakernel/p4ramill`:

```sh
lake build Imscribing.IUTT Imscribing.IUTT_Audit
lake env lean Imscribing/IUTT_Audit.lean
```

The finite proofs use kernel-checked `decide`, not `native_decide`.
There are no added axioms, sorry placeholders, or admitted conclusions.

Verified 2026-09-08: the targeted Lake build completed successfully (8032
jobs, including dependencies). All 54 axiom reports contain only subsets
of `propext`, `Classical.choice`, and `Quot.sound`, or no axioms.

The generated C was also compiled with `lake env leanc -c -fPIC`, linked
with `cc -shared`, and audited by `Vox/target/release/vox`. The linked ELF
at `/tmp/iutt-vox/IUTT.so` reported T=21, B=13, N=357, F=0 and 100% coverage
of its 15,677 code bytes. `/tmp/iutt-vox/audit.txt` records the result.
This is a compiled control-flow audit; theorem proofs are erased from the
runtime artifact and their dependency audit is the Lean report above.
