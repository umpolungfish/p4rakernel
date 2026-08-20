import Imscribing.Millennium.Erdos.CollatzDepthSplit
import Imscribing.Vox.ProofLift
/-!
The bridge and level-operator theorems lift past the sweep's default 60000-mark cap, so they get
their own pass at a cap that admits them.
-/
open Lean Meta in
#eval show MetaM Unit from do
  for nm in [`CollatzDepthSplit.equidist_of_dft_small,
             `CollatzDepthSplit.tendsto_density_of_dft_tendsto_zero,
             `CollatzDepthSplit.levels_equidistribute,
             `CollatzDepthSplit.census_mass,
             `CollatzDepthSplit.level_operator,
             `CollatzDepthSplit.cube_indicator,
             `CollatzDepthSplit.feed_is_odd_image] do
    let some (.thmInfo ti) := (← getEnv).find? nm | IO.println s!"{nm}: not found"
    let w ← ProofLift.lift ti.value
    let ax ← ProofLift.assumedAxioms nm
    let axs := if ax.isEmpty then "clean" else String.intercalate "," (ax.map toString)
    IO.println s!"{nm}\t⊢{w}⊣\t{axs}"
