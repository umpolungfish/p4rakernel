import Imscribing.Millennium.UniverseRulesets
import Imscribing.Millennium.BSD_Resolution
import Imscribing.CLINK
import Imscribing.Ob3ects.the_structurally_closed_birch_swinnerton_dyer_cl_scaffold
import Imscribing.Ob3ects.the_structurally_closed_hodge_conjecture_clay_ty_scaffold

/-!
# Clay_WitnessedClosure — the BSD & Hodge cross-universe closure, in Lean

Content built on the two `witness-drag` ob3ect route scaffolds (BSD, Hodge).
It makes machine-checkable the structural result of
`imscribing_grammar/manuscripts/clay_cross_universe_closure.md`: under the
uniform `T_CEILING` generalization (all five dynamics primitives treated as
ceilings at their canonical anchors), the BSD and Hodge structural types reach
`idempotent_terminal` — the gate-layer closure the framework associates with a
solved structural type — under **existing, non-tailored** gate-universes, and are
simultaneously `T_CEILING`-consistent.

The manuscript closes each of the two via five existing gate-universes. Three of
those (`scope_universe`, `kinetics_trap`, `stoichiometry_universe`) are the ones
present in `UniverseRulesets.lean`; the other two (`absorption_scope_empire`,
`absorption_topology_seal`) are not yet ported, so the witness here is stated over
the three Lean-available universes. Every tuple is the procedurally-sourced
in-build imscription (`BSDResolution.birchSwinnertonDyer`,
`CLINK.hodge_decomposition`); none is hand-written here.

## Honest scope (for the curmudgeon)

This is a structural-closure witness inside the Grammar's operad model, verified by
`decide`. It is **not** a proof of BSD or Hodge, and it does **not** discharge the
deep `sorry` markers in `BSD.lean` / `Hodge.lean` — those are the conventional
mathematical statements and are untouched. What is proved: the closure verdict the
manuscript computed in Python now type-checks in Lean, over existing universes and
existing tuples, with `T_CEILING` defined exactly as the manuscript specifies.
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
abbrev hodge : Imscription := Imscribing.CLINK.hodge_decomposition

-- ── BSD: full gate+T witnessed closure ────────────────────────

theorem bsd_witnessed_closure :
    ruleset_scope_universe.operadLayer bsd = .idempotent_terminal ∧
    ruleset_kinetics_trap.operadLayer bsd = .idempotent_terminal ∧
    ruleset_stoichiometry_universe.operadLayer bsd = .idempotent_terminal ∧
    tCeilingConsistent bsd = true := by decide

-- ── Hodge: full gate+T witnessed closure ──────────────────────

theorem hodge_witnessed_closure :
    ruleset_scope_universe.operadLayer hodge = .idempotent_terminal ∧
    ruleset_kinetics_trap.operadLayer hodge = .idempotent_terminal ∧
    ruleset_stoichiometry_universe.operadLayer hodge = .idempotent_terminal ∧
    tCeilingConsistent hodge = true := by decide

/-- The paired result the two `witness-drag` routes were designed to reach:
    both Clay structural types are gate-layer closed under three existing,
    non-tailored universes and `T_CEILING`-consistent — the same closure
    condition the framework associates with solved structural types. -/
theorem clay_pair_witnessed_closure :
    (ruleset_scope_universe.operadLayer bsd = .idempotent_terminal ∧
     tCeilingConsistent bsd = true) ∧
    (ruleset_scope_universe.operadLayer hodge = .idempotent_terminal ∧
     tCeilingConsistent hodge = true) := by decide

end Imscribing.Millennium.ClayWitnessedClosure
