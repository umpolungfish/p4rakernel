import Imscribing.Millennium.Erdos.CollatzDepthSplit
import Imscribing.Vox.ProofLift
/-!
The cycle theorems, lifted past the sweep's default cap so the closure condition can
be read as a word rather than argued about.
-/
open Lean Meta in
#eval show MetaM Unit from do
  for nm in [`CollatzDepthSplit.cycle_equation,
             `CollatzDepthSplit.iterate_le_pow,
             `CollatzDepthSplit.cycle_excursion,
             `CollatzDepthSplit.two_pow_ne_three_pow,
             `CollatzDepthSplit.col_succ_odd,
             `CollatzDepthSplit.cycle_bound,
             `CollatzDepthSplit.iterate_banked,
             `CollatzDepthSplit.cycle_banked] do
    let some (.thmInfo ti) := (← getEnv).find? nm | IO.println s!"{nm}: not found"
    let w ← ProofLift.lift ti.value
    let ax ← ProofLift.assumedAxioms nm
    let axs := if ax.isEmpty then "clean" else String.intercalate "," (ax.map toString)
    IO.println s!"{nm}\t⊢{w}⊣\t{axs}"
