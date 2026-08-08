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

**Fifteen axioms of `True`.** These assert nothing: `True` is provable, so they
record a name and no claim, and nothing can be derived from them. Two classes,
and they need different treatment.

*Provable here.* `Collatz.lean:929 drift_theorem_axiom` — its own doc gives the
arithmetic, (1/2)log(1/2) + (1/2)log(3/2) = (1/2)log(3/4) < 0, and says it is
elementary. It is; prove it.

*MathlibGap stand-ins for real published theorems* — `modularity_axiom` and
`functional_equation_axiom` (BSD, and again in `BSD_MathBridge.lean`),
`hodgeDecomposition`, `hardLefschetz`, `lefschetzDecomposition`,
`grothendieckRiemannRoch`, `energy_inequality`, `initialCriticalNormFinite`,
`frobenius_g2_cancellation`. Stating these as `: True` is the worst of both: it
looks like an assumption and carries none. Restate each as the proposition it
actually assumes, so the axiom says what is being taken. The count will not
fall; the honesty rises, and `verify_sic_moduli.sh`-style axiom reports become
meaningful.

*Grammar claims with stated content* — `sigma_one_to_one_limit`,
`grammar_is_sic_povm`, `joint_dual_is_sic`, `grothendieck_AD_join_contains_A`,
plus the classical placeholders in `MatchingSDR`, `UnitDistanceDiameterOne`,
`DifferenceSetSyndetic`, `UnitDistancePhaseTransition`, `TriangleTiling`,
`ErdosLaxDivergence`, `HajnalSpecker`. Each has its content in the surrounding
prose; state it.

Reference check already done: of these only `hardLefschetz` (4 uses) and
`hodgeDecomposition` (1) are referenced anywhere, so the rest can be restated
without touching another file.

**Six remaining opaque constants** in `Cramer.lean` (3), `Goldbach.lean` (2) and
`YM_Mathematical_Witness.lean` (1) — same `def` + `rfl` treatment as above.

**Then it stops being mechanical.** What is left after that is roughly 340
propositions, of which about 53 are deep structure — manifolds, measures,
cohomology, L-functions — and those stay axioms until they are proved. The
Millennium files are where an axiom is an actual claim rather than a recorded
computation, and the census should not be pushed past that line for the sake of
a number.

## Census, for re-running

    command grep -rn '^\s*axiom ' p4ramill --include='*.lean' | command grep -v '/\.lake/' | wc -l

Bare `grep` honours .gitignore in this shell, so a census must use `command grep`.
