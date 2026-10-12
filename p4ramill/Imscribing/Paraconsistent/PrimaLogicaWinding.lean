import Imscribing.NS_KernelReentry

/-!
# Prima Logica: ordered Inclosure over native SIXTEEN_3

C. Lando Mills — supplementary formalization.

The existing native `heldClosure` adjoins the singleton B immediately.
`wind` instead adjoins the *first missing* member in the order N, T, F, B.
Both operators act on the actual native SIXTEEN_3 carrier. They are distinct;
this module never conflates the fixed singleton `{B}` with the full register
`{N,T,F,B}`.

No new axiom is introduced. The finite-state properties are proven by
exhausting the four Boolean coordinates of the native carrier.
-/

namespace Imscribing.PrimaLogica

open Lean Imscribing.NSReentry

/-- The unmarked register. -/
def unmarked : Sixteen3 := Sixteen3.ofBelnap false false false false

/-- The four singleton evidence registers, in winding order. -/
def onlyN : Sixteen3 := Sixteen3.ofBelnap true false false false
def onlyT : Sixteen3 := Sixteen3.ofBelnap false true false false
def onlyF : Sixteen3 := Sixteen3.ofBelnap false false true false
def onlyB : Sixteen3 := Sixteen3.ofBelnap false false false true

/-- The full register is the terminal winding state, not the singleton B. -/
def complete : Sixteen3 := Sixteen3.ofBelnap true true true true

/-- Unified B: the whole native FOUR-register, not the singleton Belnap B. -/
def unifiedB : Sixteen3 := complete

/-- L5 LP: the BNTF native-register carrier, with Inclosure given by `lpInclosure`.
    The five successive states form `stage 0` through `stage 4` below. -/
abbrev L5_LP := Sixteen3

/-- In the information lattice, unified B absorbs every 16-state register. -/
theorem unifiedB_join_left (s : Sixteen3) :
    Sixteen3.join_i unifiedB s = unifiedB := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

theorem unifiedB_join_right (s : Sixteen3) :
    Sixteen3.join_i s unifiedB = unifiedB := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

/-- The specified five-stage chain. Values at indices >= 4 are terminal. -/
def stage : Nat → Sixteen3
  | 0 => unmarked
  | 1 => Sixteen3.ofBelnap true false false false
  | 2 => Sixteen3.ofBelnap true true false false
  | 3 => Sixteen3.ofBelnap true true true false
  | _ => complete

/-- Advance one step, retaining all existing information and adjoining the
first missing member of N, T, F, B. Acts on every native 16-state register. -/
def wind (s : Sixteen3) : Sixteen3 :=
  if s.hasN = false then Sixteen3.join_i s onlyN
  else if s.hasT = false then Sixteen3.join_i s onlyT
  else if s.hasF = false then Sixteen3.join_i s onlyF
  else if s.hasB = false then Sixteen3.join_i s onlyB
  else s

/-- Inclosure is the motion of L5 LP through BNTF, not a fifth static truth value. -/
def lpInclosure : L5_LP → L5_LP := wind

/-- The authored L5 LP chain begins at the unmarked state. -/
theorem lpInclosure_unmarked : lpInclosure unmarked = stage 1 := rfl

-- The trajectory from the unmarked register is exactly the stated chain.
theorem wind_unmarked : wind unmarked = stage 1 := rfl
theorem wind_stage_one : wind (stage 1) = stage 2 := rfl
theorem wind_stage_two : wind (stage 2) = stage 3 := rfl
theorem wind_stage_three : wind (stage 3) = stage 4 := rfl
theorem wind_stage_four : wind (stage 4) = stage 4 := rfl

theorem wind_four_from_unmarked :
    wind (wind (wind (wind unmarked))) = complete := rfl

/-- Every initial register reaches the full register within four winding steps. -/
theorem wind_four_from_any (s : Sixteen3) :
    wind (wind (wind (wind s))) = complete := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

/-- L5 LP reaches the unified B register after four Inclosure steps. -/
theorem L5_LP_inclosure_four_from_any (s : L5_LP) :
    lpInclosure (lpInclosure (lpInclosure (lpInclosure s))) = unifiedB := by
  simpa [lpInclosure, unifiedB] using (wind_four_from_any s)

/-- A winding step never deletes information. -/
theorem wind_extensive (s : Sixteen3) :
    Sixteen3.le_i s (wind s) = true := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Winding respects the native information order on all 16 states. -/
theorem wind_monotone (s t : Sixteen3) :
    Sixteen3.le_i s t = true →
      Sixteen3.le_i (wind s) (wind t) = true := by
  rcases s with ⟨sn, st, sf, sb⟩
  rcases t with ⟨tn, tt, tf, tb⟩
  cases sn <;> cases st <;> cases sf <;> cases sb <;>
    cases tn <;> cases tt <;> cases tf <;> cases tb <;> decide

/-- The completed register is the *only* fixed point of ordered winding. -/
theorem wind_fixed_iff_complete (s : Sixteen3) :
    wind s = s ↔ s = complete := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Every stage is below its successor in the information order. -/
theorem stage_zero_le_one : Sixteen3.le_i (stage 0) (stage 1) = true := rfl
theorem stage_one_le_two : Sixteen3.le_i (stage 1) (stage 2) = true := rfl
theorem stage_two_le_three : Sixteen3.le_i (stage 2) (stage 3) = true := rfl
theorem stage_three_le_four : Sixteen3.le_i (stage 3) (stage 4) = true := rfl

/-- None of the four proper stages has the same carrier as the next one. -/
theorem proper_stages_distinct :
    stage 0 ≠ stage 1 ∧ stage 1 ≠ stage 2 ∧
    stage 2 ≠ stage 3 ∧ stage 3 ≠ stage 4 := by
  decide

/-- Native B-adjunction commutes with winding across every one of the 16 states. -/
theorem winding_commutes_with_native_closure (s : Sixteen3) :
    wind (heldClosure s) = heldClosure (wind s) := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Winding and immediate B-adjunction agree precisely after N,T,F are held. -/
theorem winding_eq_native_closure_iff (s : Sixteen3) :
    wind s = heldClosure s ↔
      (s.hasN = true ∧ s.hasT = true ∧ s.hasF = true) := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- At the three-member register, winding and B-adjunction agree. -/
theorem winding_agrees_with_native_closure_at_stage_three :
    wind (stage 3) = heldClosure (stage 3) := rfl

/-- From the unmarked register, the two distinct dynamics do not agree. -/
theorem winding_differs_from_B_closure_at_unmarked :
    wind unmarked ≠ heldClosure unmarked := by
  decide

/-- The native closure's fixed singleton B is distinct from full Inclosure. -/
theorem singleton_B_is_not_complete : onlyB ≠ complete := by decide

/-- The terminal winding register is stable under native B-closure. -/
theorem terminal_stable_under_B_closure : heldClosure complete = complete := rfl

end Imscribing.PrimaLogica
