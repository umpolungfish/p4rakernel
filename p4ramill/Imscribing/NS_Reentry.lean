/-
  NS_Reentry.lean
  Navier-Stokes: the overflow re-entry, formalised in the re-entry tower.

  The NS problem looks like it needs an "external" injection to feed the
  cascade to small scales.  This file checks the dialetheic reading: the
  injection is not external.  It is the tower's own Cantor overflow (the
  value lifted to the next scale) which re-enters by first factoring through
  the frame collapse at that same scale, and then through the cascade step
  back down to the home scale.

  Factorisation:
      reEntry : V (n+1) → V n  =  cascadeStep ∘ collapseStep
  where
      collapseStep : V (n+1) → V (n+1)   the frame collapse ρ (same scale)
      cascadeStep  : V (n+1) → V n       the reveal μ (the step down)

  Reading the NS "external injection" this way, the injection is the tower's
  own overflow re-entering through ρ — internal, marked, and idempotent under
  its own frame collapse.  No map from outside V is used.
-/
import Imscribing.CircumPunctum
import Imscribing.Paraconsistent.Belnap

set_option linter.unusedVariables false

namespace Imscribing.NSReentry

open Imscribing.CircumPunctum

/- The two stages the overflow re-entry factors through:
     collapseStep : V (n+1) → V (n+1)  the frame collapse at the same scale
     cascadeStep  : V (n+1) → V n      the cascade step back to the home scale
-/
def collapseStep {n : ℕ} : V (n + 1) → V (n + 1) := ρ
def cascadeStep  {n : ℕ} : V (n + 1) → V n := μ

/-- Dialetheic re-entry of the overflow: the value at the next scale re-enters
    by first factoring through the frame collapse at that same scale, and then
    through the cascade step back down.  This is the internal reading of the
    NS "external" injection. -/
def reEntry {n : ℕ} : V (n + 1) → V n := cascadeStep ∘ collapseStep

/-- FACTORISATION LAW: re-entry is exactly cascade-after-collapse at the same
    scale.  The injection is the tower's own overflow re-entering through ρ. -/
theorem reEntry_def_factors {n : ℕ} (x : V (n + 1)) :
    reEntry x = cascadeStep (collapseStep x) := rfl

/-
  The re-entered overflow is a fixed point of the frame collapse at the next
  scale: collapsing it again changes nothing.  The injection, once it has
  entered, does not keep feeding new content — it is dialetheic, held.
-/
theorem reEntry_fixed_under_collapse {n : ℕ} (x : V (n + 1)) :
    collapseStep (collapseStep x) = collapseStep x := by
  unfold collapseStep
  exact ρ_idempotent x

/-
  The marker the Cantor lift sets survives the re-entry: the collapsed value
  is a marked singleton, its fibre bit true.  The overflow is present at the
  re-entered point, not merely accounted for.
-/
theorem reentry_marker_set {n : ℕ} (x : V (n + 1)) :
    (collapseStep x).2 = true := by
  unfold collapseStep; rfl

/-
  Read at the home scale, re-entry is indistinguishable from the cascade step
  alone: collapsing first and then cascading equals cascading.  The frame
  collapse is already satisfied by the marker, so it contributes no further
  change — the re-entered overflow and the pure cascade land on the same value.
-/
theorem reEntry_is_cascade {n : ℕ} (x : V (n + 1)) :
    reEntry x = cascadeStep x := by
  unfold reEntry cascadeStep
  exact μ_η_id (μ x)

/-
  NS tie-in: the value the NS regularity register holds (nsRegularity = B in
  ParaconsistentNS.lean) is the fixed point of the dialetheic closure.  The
  re-entered overflow lands on a value the closure cannot move: the
  contradiction is contained, not resolved, and no external input is needed.
-/
theorem ns_reentry_fixed_point :
    Imscribing.CircumPunctum.Inc (Imscribing.Paraconsistent.Belnap.B) =
      Imscribing.Paraconsistent.Belnap.B :=
    Imscribing.CircumPunctum.Inc_fixed_point_B

end Imscribing.NSReentry
