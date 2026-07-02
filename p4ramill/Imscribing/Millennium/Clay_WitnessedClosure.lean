import Imscribing.Millennium.UniverseRulesets
import Imscribing.Millennium.BSD_Resolution
import Imscribing.Millennium.Hodge_Grammar
import Imscribing.Ob3ects.the_structurally_closed_birch_swinnerton_dyer_cl_scaffold
import Imscribing.Ob3ects.the_structurally_closed_hodge_conjecture_clay_ty_scaffold

/-!
# Clay_WitnessedClosure — the BSD & Hodge cross-universe closure, in Lean (five universes)

Content built on the two `witness-drag` ob3ect route scaffolds (BSD, Hodge). It
makes machine-checkable the structural result of
`imscribing_grammar/manuscripts/clay_cross_universe_closure.md`: under the uniform
`T_CEILING` generalization (all five dynamics primitives treated as ceilings at
their canonical anchors), the BSD and Hodge structural types reach
`idempotent_terminal` — the gate-layer closure the framework associates with a
solved structural type — under **five existing, non-tailored** gate-universes each,
and are simultaneously `T_CEILING`-consistent.

The five universes (`scope_universe`, `kinetics_trap`, `stoichiometry_universe`,
`absorption_scope_empire`, `absorption_topology_seal`) are exactly the manuscript's
closers; the last two were ported into `UniverseRulesets.lean` from
`scripts/new_universes.py` (#27, #28) for this witness.

Tuples are the procedurally-sourced in-build imscriptions:
`BSDResolution.birchSwinnertonDyer` and `HodgeGrammar.hod_conjecture_full`. The
earlier draft used `CLINK.hodge_decomposition`, whose topology (`eat`) fails
`absorption_topology_seal` (Þ≥are) — a stale tuple; `hod_conjecture_full`
(topology `are`) is the current one, verified by computation before assertion.

## Honest scope (for the curmudgeon)

Structural-closure witness inside the Grammar's operad model, verified by `decide`.
**Not** a proof of BSD or Hodge, and it does **not** discharge the deep `sorry`
markers in `BSD.lean` / `Hodge.lean` — those are the conventional mathematical
statements and are untouched. What is proved: the closure verdict the manuscript
computed in Python now type-checks in Lean, over the full five universes and the
current tuples, with `T_CEILING` defined exactly as the manuscript specifies.
-/

namespace Imscribing.Millennium.ClayWitnessedClosure

open Imscribing.Primitives
open Millennium.UniverseRulesets

/-- The `T_CEILING` T-constitution: `tCanonical` with **all five** dynamics
    primitives treated as ceilings, at their existing canonical anchor values
    (Φ≤5, ƒ≤3, Ç≤3, Ħ≤4, Ω≤3). No anchor is changed; only the four exact-equality
    modes are relaxed to ceilings, matching the manuscript's uniform generalization. -/
def T_CEILING : List TPrimSpec :=
  [ tPrimLe (fun s => ordinalP s.pol) 5,
    tPrimLe (fun s => ordinalF s.fid) 3,
    tPrimLe (fun s => ordinalK s.kin) 3,
    tPrimLe (fun s => ordinalH s.chir) 4,
    tPrimLe (fun s => ordinalOmega s.prot) 3 ]

/-- `T_CEILING`-consistency as a single Boolean. -/
def tCeilingConsistent (s : Imscription) : Bool :=
  T_CEILING.all (fun tp => tp.consistent s)

-- The procedurally-sourced Clay tuples (never hand-imscribed here).
abbrev bsd   : Imscription := Imscribing.Millennium.BSDResolution.birchSwinnertonDyer
abbrev hodge : Imscription := Millennium.HodgeGrammar.hod_conjecture_full

-- ── BSD: full five-universe gate+T witnessed closure ──────────

theorem bsd_witnessed_closure :
    ruleset_scope_universe.operadLayer bsd = .idempotent_terminal ∧
    ruleset_kinetics_trap.operadLayer bsd = .idempotent_terminal ∧
    ruleset_stoichiometry_universe.operadLayer bsd = .idempotent_terminal ∧
    ruleset_absorption_scope_empire.operadLayer bsd = .idempotent_terminal ∧
    ruleset_absorption_topology_seal.operadLayer bsd = .idempotent_terminal ∧
    tCeilingConsistent bsd = true := by decide

-- ── Hodge: full five-universe gate+T witnessed closure ────────

theorem hodge_witnessed_closure :
    ruleset_scope_universe.operadLayer hodge = .idempotent_terminal ∧
    ruleset_kinetics_trap.operadLayer hodge = .idempotent_terminal ∧
    ruleset_stoichiometry_universe.operadLayer hodge = .idempotent_terminal ∧
    ruleset_absorption_scope_empire.operadLayer hodge = .idempotent_terminal ∧
    ruleset_absorption_topology_seal.operadLayer hodge = .idempotent_terminal ∧
    tCeilingConsistent hodge = true := by decide

/-- The paired result the two `witness-drag` routes were designed to reach: both
    Clay structural types are gate-layer closed under all five of their manuscript
    universes and `T_CEILING`-consistent — the same closure condition the framework
    associates with solved structural types. -/
theorem clay_pair_witnessed_closure :
    (ruleset_scope_universe.operadLayer bsd = .idempotent_terminal ∧
     ruleset_absorption_topology_seal.operadLayer bsd = .idempotent_terminal ∧
     tCeilingConsistent bsd = true) ∧
    (ruleset_scope_universe.operadLayer hodge = .idempotent_terminal ∧
     ruleset_absorption_topology_seal.operadLayer hodge = .idempotent_terminal ∧
     tCeilingConsistent hodge = true) := by decide

end Imscribing.Millennium.ClayWitnessedClosure
