import Imscribing.Millennium.UniverseRulesets
import Imscribing.Millennium.ClayCanonicalTuples
import Imscribing.Ob3ects.the_navier_stokes_criticality_type_gate_blocked_scaffold
import Imscribing.Ob3ects.the_p_versus_np_separation_gate_blocked_under_al_scaffold

/-!
# Clay_UnclosedResistance — Navier–Stokes and P-vs-NP resist closure everywhere

Content built on the NS and P-vs-NP `witness-drag`/`furnace` scaffolds. Where
`Clay_WitnessedClosure` shows BSD/Hodge closing and YM one-bump-short, this module
proves the honest negative for the two that stay open: neither the canonical
Navier–Stokes nor the canonical P-vs-NP structural type reaches
`idempotent_terminal` under **any** of the 23 gate-universes currently in the Lean
tree (the 20 in `allRulesets` plus the three ported `absorption_*` universes). This
is the machine-checked form of the manuscript's "fail at the gate layer under all
29, with or without T_CEILING."

The structural reason is the winding gate: both tuples carry Ω (protection/winding)
below the terminal anchor `ah` (ord 3) — NS Ω=`awe` (1), PNP Ω=`awe` (1) — and every
closure-bearing universe requires Ω≥3 at its terminal gate. Low winding ⇒ no
idempotent-terminal closure.

## A caveat on the Riemann Hypothesis (deliberately excluded)

RH is NOT included here. The canonical catalog RH tuple carries ⊙=`𐑮` (roar); the
source-of-truth ordinal table (`imscrbgrmr/canonical_primitives.py`) ranks `𐑮` at
2.33 — below super-critical `𐑣` (3), so under canonical ordinals RH also fails
`triple_criticality` and closes nowhere, matching the manuscript. But the Lean port
`UniverseRulesets.ordinalPhi` flattens Criticality to integers (`roar`=3), and
`triple_criticality.g3` gates at `gatePhi 3`, so in Lean RH spuriously reaches
`idempotent_terminal` there. That is a Lean-port ⊙-scale discrepancy, not a real
closure; rather than assert a verdict that disagrees with canonical, RH is left out
pending an `ordinalPhi`/`gatePhi` fix. NS and PNP are unaffected (they fail on Ω,
independent of the ⊙ scale).

## Honest scope

Structural-resistance result in the operad model, verified by `decide`. It says
these two structural types do not reach the framework's closure condition under any
current universe — it is not a claim about the conventional mathematical problems.
-/

namespace Imscribing.Millennium.ClayUnclosedResistance

open Imscribing.Primitives
open Millennium.UniverseRulesets

/-- The 23 gate-universes currently in the Lean tree. -/
def universes : List Ruleset :=
  allRulesets ++
    [ ruleset_absorption_chirality_first,
      ruleset_absorption_scope_empire,
      ruleset_absorption_topology_seal ]

abbrev ns  : Imscription := ClayCanonicalTuples.navierStokes
abbrev pnp : Imscription := ClayCanonicalTuples.pVsNP

/-- Navier–Stokes reaches `idempotent_terminal` under none of the 23 universes. -/
theorem ns_closes_nowhere :
    universes.any (fun r => decide (r.operadLayer ns = .idempotent_terminal)) = false := by
  native_decide

/-- P-vs-NP reaches `idempotent_terminal` under none of the 23 universes. -/
theorem pnp_closes_nowhere :
    universes.any (fun r => decide (r.operadLayer pnp = .idempotent_terminal)) = false := by
  native_decide

/-- The shared blocker: both carry winding Ω below the terminal anchor `ah` (3). -/
theorem ns_pnp_low_winding :
    (ordinalOmega ns.prot < 3) ∧ (ordinalOmega pnp.prot < 3) := by decide

/-- Combined resistance verdict. -/
theorem clay_resistance :
    (universes.any (fun r => decide (r.operadLayer ns = .idempotent_terminal)) = false) ∧
    (universes.any (fun r => decide (r.operadLayer pnp = .idempotent_terminal)) = false) := by
  native_decide

end Imscribing.Millennium.ClayUnclosedResistance
