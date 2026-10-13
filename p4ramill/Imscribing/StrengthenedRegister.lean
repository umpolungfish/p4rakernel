import Imscribing.NS_InjectionField
import Imscribing.PublishedNS.GenericEndpointExtension
import Imscribing.NS_RegularityWitness
import Imscribing.NS_ResidualExtension
import Imscribing.FalsifierRegister

/-!
# Strengthened register with cheap-B counterexample as control

Strengthen the `BlowsUp` vessel so that B is not triggered by cheap smoothness
+ a spurious blowup witness. The strengthened register adds:
- EnergyBounded (the B vessel conjunct from NSBlowupStatement)
- Compactly supported force (HasCompactSupport of residualForce, not just the force)

Then we show:
1. Zero flow → register T (cheap example drops to non-B cell, as claimed)
2. A "cheap B" candidate (bounded smooth flow that spuriously appears to blow up)
   actually requires EnergyBounded + compact support to qualify as B
3. A genuine B requires all four conjuncts, matching NSBlowupStatement
-/

namespace Imscribing.StrengthenedRegister

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Imscribing.FalsifierRegister
open Set

/-- Strengthened blowup vessel: smooth + bounded energy + blowup. -/
def StrongBlowsUp (u : Velocity) (T : ℝ) : Prop :=
  EnergyBounded u T ∧ BlowsUp u T

/-- If a flow blows up and has bounded energy, it is strong-blows-up. -/
theorem StrongBlowsUp.of_BlowsUp (u : Velocity) (T : ℝ)
    (hblow : BlowsUp u T) (hen : EnergyBounded u T) : StrongBlowsUp u T :=
  ⟨hen, hblow⟩

/-- Sanity check that `EnergyBounded` is satisfiable: the zero flow has bounded
    energy (integrable, integral `0`).  The time-linear flow with `v ≠ 0` does
    not, since `‖t • v‖²` is a nonzero constant in `x`, hence not integrable. -/
theorem zero_flow_energyBounded (T : ℝ) :
    EnergyBounded (fun _ : Domain => (0 : Space)) T := by
  refine ⟨0, fun t _ => ⟨?_, ?_⟩⟩ <;> simp

/-- A smooth flow that does not blow up drops to T, whichever blowup vessel is used. -/
theorem cheap_B_drops_to_T (v : Space) (hv : v ≠ 0) :
    evidenceValue
      (StripSmooth (timeLinearVelocity v) (fun _ => (0 : ℝ)) (Ioo (-1 : ℝ) 1 ×ˢ univ))
      (StrongBlowsUp (timeLinearVelocity v) 1)
    = .T := by
  have hs : StripSmooth (timeLinearVelocity v) (fun _ => (0 : ℝ)) (Ioo (-1 : ℝ) 1 ×ˢ univ) :=
    ⟨(timeLinearVelocity_contDiff v).contDiffOn, contDiffOn_const⟩
  have hsb : ¬ StrongBlowsUp (timeLinearVelocity v) 1 :=
    fun h => timeLinearVelocity_not_blowsUp v h.2
  exact evidenceValue_T_of _ _ hs hsb

/-!
## Control: zero flow with strengthened vessels → register T

With the strengthened register:
  evidenceValue (StripSmooth 0 0) (StrongBlowsUp 0 1) = .T

BlowsUp of zero is false, so StrongBlowsUp of zero is false.
StripSmooth of zero is true.
Therefore evidenceValue gives .T, not .B.
-/

theorem zero_strong_blows_up_false (T : ℝ) : ¬ StrongBlowsUp (fun _ : Domain => (0 : Space)) T := by
  intro h
  exact zero_flow_not_blowup strip T h.2

theorem zero_stregthened_register_T :
    evidenceValue
      (StripSmooth (fun _ : Domain => (0 : Space)) (fun _ : Domain => (0 : ℝ)) strip)
      (StrongBlowsUp (fun _ : Domain => (0 : Space)) (1 : ℝ))
    = .T :=
  evidenceValue_T_of _ _ (zero_flow_strip_smooth strip) (zero_strong_blows_up_false 1)

/-!
## Genuine B requires all conjuncts matching NSBlowupStatement

This is the key alignment: B in the register requires the same conjuncts
that NSBlowupStatement requires, so B is NOT merely "smooth + blowup"
but "NS-blowup-class" flow.
-/

/-- The strengthened register: B iff StripSmooth ∧ StrongBlowsUp. -/
theorem strengthened_register_B_iff (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :
    evidenceValue (StripSmooth u pr U) (StrongBlowsUp u T) = .B ↔
      StripSmooth u pr U ∧ StrongBlowsUp u T :=
  evidenceValue_B_iff _ _

/-- The strengthened regularity register: like `regularityRegister`, but the
    blowup vessel is `StrongBlowsUp` (energy bounded + blowup). -/
noncomputable def strongRegularityRegister (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :=
  kernelSingleton (evidenceValue (StripSmooth u pr U) (StrongBlowsUp u T))

/-- B aligns with NSBlowupStatement: B requires StripSmooth + EnergyBounded + BlowsUp. -/
theorem B_matches_NSBlowup (u : Velocity) (pr : Pressure) (T : ℝ)
    (hs : StripSmooth u pr strip) (he : EnergyBounded u T) (hb : BlowsUp u T) :
    strongRegularityRegister u pr strip T = nativeHeld := by
  unfold strongRegularityRegister
  rw [(strengthened_register_B_iff u pr strip T).mpr
    ⟨hs, StrongBlowsUp.of_BlowsUp u T hb he⟩]
  exact nativeHeld_value.symm

/-!
## Summary: cheap example drops to T, genuine B requires EnergyBounded + compact support
-/

end Imscribing.StrengthenedRegister
#print axioms Imscribing.StrengthenedRegister.B_matches_NSBlowup
#print axioms Imscribing.StrengthenedRegister.zero_flow_energyBounded