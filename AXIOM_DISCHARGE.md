# Axiom discharge — where this stands

## Done

`SIC_D16_Moduli.lean` 27 → 0 and `SIC_D20_Moduli.lean` 35 → 0, both building,
committed as `250bd46`. Repository total 435 → 373.

Verified by `#print axioms`, not by counting: `omega_trivial_at_d20`,
`statement_B_confirmed_by_coinvariant_count` and `wideRayDegree_6` depend on no
axioms at all; the rest carry only `propext` and `Quot.sound`. The tower
theorems use `decide` rather than `native_decide`, so the compiler is outside
the trusted base.

## The method, which is mechanical

Almost every axiom in these files came in pairs: an opaque constant, then a
second axiom giving its value. A value is a value — the pair becomes a `def` and
a `theorem … := rfl`. Per-level tower assertions become one recursion carrying
the growth law, and each level a `decide`. `Type 0` placeholders become the
twelve-slot imscription the object occupies, following `SIC_D2048_Moduli.lean`.

## Next, in order

**Fifteen axioms of `True`.** `True` is provable, so each carries its name and
its claim is still to be written. Sorted by what each one needs.

*Ready now.* `Collatz.lean:929 drift_theorem_axiom` — its own doc gives the
arithmetic, (1/2)log(1/2) + (1/2)log(3/2) = (1/2)log(3/4) < 0, and calls it
elementary. Write it as a theorem.

*Needs its statement carried in.* `modularity_axiom`, `functional_equation_axiom`,
`hodgeDecomposition`, `hardLefschetz`, `lefschetzDecomposition`,
`grothendieckRiemannRoch`, `energy_inequality`, `initialCriticalNormFinite`,
`frobenius_g2_cancellation` name theorems that are established in the
literature and reachable through the ob3ect pipeline or a direct development;
each closes given the work.

*Needs a reading first.* 
`sigma_one_to_one_limit`, `grammar_is_sic_povm`, `joint_dual_is_sic`,
`grothendieck_AD_join_contains_A`, and the classical placeholders in
`MatchingSDR`, `UnitDistanceDiameterOne`, `DifferenceSetSyndetic`,
`UnitDistancePhaseTransition`, `TriangleTiling`, `ErdosLaxDivergence`,
`HajnalSpecker`. Each needs reading before it can be sorted into the two above.

Reference check done: of the fifteen only `hardLefschetz` (4 uses) and
`hodgeDecomposition` (1) are referenced anywhere.

**Six remaining opaque constants** in `Cramer.lean` (3), `Goldbach.lean` (2) and
`YM_Mathematical_Witness.lean` (1) — same `def` + `rfl` treatment as above.

**Then the work changes kind.** Roughly 340 propositions remain, about 53 of
them deep structure — manifolds, measures, cohomology, L-functions. These are
the frontier: each is an actual claim rather than a recorded computation, so
each closes through its own development rather than through the pattern above.
The number to watch from here is how many carry a statement worth proving, not
how far the count falls.

## Census, for re-running

    command grep -rn '^\s*axiom ' p4ramill --include='*.lean' | command grep -v '/\.lake/' | wc -l

Bare `grep` honours .gitignore in this shell, so a census must use `command grep`.
