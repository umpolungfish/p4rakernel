import Imscribing.NS_InjectionField
import Init.Paraconsistent

/-!
Native SIXTEEN_3 closure carried through the Navier–Stokes re-entry tower.
The differential field and its information register travel together. Feedback
normalizes the register while preserving every value of the carried field.
-/

namespace Imscribing.NSReentry

open Lean Imscribing.CircumPunctum

enable_trilattice

/-- Native least fixed point of information feedback retaining the B member. -/
reentry nativeHeld (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i f (Sixteen3.ofBelnap false false false true)

disable_trilattice

theorem nativeHeld_value :
    nativeHeld = Sixteen3.ofBelnap false false false true := rfl

/-- Each FOUR member enters the native powerset as its singleton. -/
def kernelSingleton : Imscribing.Paraconsistent.Belnap → Sixteen3
  | .N => Sixteen3.ofBelnap true false false false
  | .T => Sixteen3.ofBelnap false true false false
  | .F => Sixteen3.ofBelnap false false true false
  | .B => Sixteen3.ofBelnap false false false true

/-- The NS tower's held FOUR value agrees with the computed native fixed point. -/
theorem nativeHeld_eq_ns_fixed_point :
    nativeHeld = kernelSingleton (Inc Imscribing.Paraconsistent.Belnap.B) := rfl

/-- Preserve the input memberships and adjoin the native held value. -/
def heldClosure (state : Sixteen3) : Sixteen3 := Sixteen3.join_i state nativeHeld

theorem heldClosure_extensive (state : Sixteen3) :
    Sixteen3.le_i state (heldClosure state) = true := by
  rcases state with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

theorem heldClosure_idempotent (state : Sixteen3) :
    heldClosure (heldClosure state) = heldClosure state := by
  rcases state with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

/-- Fixed registers are exactly those retaining the B membership. -/
theorem heldClosure_fixed_iff (state : Sixteen3) :
    heldClosure state = state ↔ state.hasB = true := by
  rcases state with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

theorem nativeHeld_fixed : heldClosure nativeHeld = nativeHeld := rfl

/-- The native result is below every fixed register in the information order. -/
theorem nativeHeld_least_fixed (candidate : Sixteen3)
    (hfixed : heldClosure candidate = candidate) :
    Sixteen3.le_i nativeHeld candidate = true := by
  have hheld := (heldClosure_fixed_iff candidate).mp hfixed
  simp [Sixteen3.le_i, hheld]

/-- Universal property: closure is the least held register above the input. -/
theorem heldClosure_least (state candidate : Sixteen3)
    (hstate : Sixteen3.le_i state candidate = true)
    (hheld : candidate.hasB = true) :
    Sixteen3.le_i (heldClosure state) candidate = true := by
  simpa [Sixteen3.le_i, heldClosure, nativeHeld_value, Sixteen3.join_i, hheld]
    using hstate

theorem heldClosure_monotone (state candidate : Sixteen3)
    (hstate : Sixteen3.le_i state candidate = true) :
    Sixteen3.le_i (heldClosure state) (heldClosure candidate) = true := by
  simp [Sixteen3.le_i, heldClosure, Sixteen3.join_i] at hstate ⊢
  exact hstate.1

/-- A scale value carries a field and the full sixteen-value register. -/
abbrev RegisteredScale (Carrier : Type*) (n : ℕ) :=
  CarriedScale (Carrier × Sixteen3) n

/-- Feedback through the upper frame preserves its field and closes its register. -/
def registeredCollapse {Carrier : Type*} {n : ℕ}
    (overflow : RegisteredScale Carrier (n + 1)) : RegisteredScale Carrier (n + 1) :=
  (collapseStep overflow.1, overflow.2.1, heldClosure overflow.2.2)

def registeredReEntry {Carrier : Type*} {n : ℕ}
    (overflow : RegisteredScale Carrier (n + 1)) : RegisteredScale Carrier n :=
  carriedCascade (registeredCollapse overflow)

/-- Both frame and information feedback stabilize after normalization. -/
theorem registeredCollapse_idempotent {Carrier : Type*} {n : ℕ}
    (overflow : RegisteredScale Carrier (n + 1)) :
    registeredCollapse (registeredCollapse overflow) = registeredCollapse overflow := by
  apply Prod.ext
  · exact reEntry_fixed_under_collapse overflow.1
  · exact congrArg (fun state => (overflow.2.1, state))
      (heldClosure_idempotent overflow.2.2)

theorem registeredReEntry_field {Carrier : Type*} {n : ℕ}
    (overflow : RegisteredScale Carrier (n + 1)) :
    (registeredReEntry overflow).2.1 = overflow.2.1 := rfl

theorem registeredReEntry_register {Carrier : Type*} {n : ℕ}
    (overflow : RegisteredScale Carrier (n + 1)) :
    (registeredReEntry overflow).2.2 = heldClosure overflow.2.2 := rfl

/-- The complete return preserves the scale source and field, closing the register. -/
theorem registered_round_trip {Carrier : Type*} {n : ℕ}
    (source : RegisteredScale Carrier n) :
    registeredReEntry (carriedLift source) =
      (source.1, source.2.1, heldClosure source.2.2) := rfl

theorem registered_round_trip_fixed {Carrier : Type*} {n : ℕ}
    (source : RegisteredScale Carrier n) (hheld : source.2.2.hasB = true) :
    registeredReEntry (carriedLift source) = source := by
  rw [registered_round_trip, (heldClosure_fixed_iff source.2.2).mpr hheld]

/-- Any field predicate survives feedback because the field itself is preserved. -/
theorem registered_field_property {Carrier : Type*} {n : ℕ}
    (overflow : RegisteredScale Carrier (n + 1)) (property : Carrier → Prop)
    (hproperty : property overflow.2.1) :
    property (registeredReEntry overflow).2.1 := hproperty

def MomentumTerms.registeredOverflow {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) (state : Sixteen3) :
    RegisteredScale (Domain → Value) (n + 1) :=
  carriedLift (p n, terms.residual, state)

def MomentumTerms.registeredInjection {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) (state : Sixteen3) : Domain → Value :=
  (registeredReEntry (terms.registeredOverflow n state)).2.1

/-- The actual residual returns for every input register and every scale. -/
theorem MomentumTerms.registered_injection_eq_residual {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) (state : Sixteen3) :
    terms.registeredInjection n state = terms.residual := rfl

end Imscribing.NSReentry

namespace Imscribing.NSInjectionField

open Imscribing.NSReentry Lean
open scoped ContDiff

noncomputable section

def registeredInjectionForce (ν : ℝ) (u : Velocity) (pressure : Pressure)
    (n : ℕ) (state : Sixteen3) : Velocity :=
  (momentumTerms ν u pressure).registeredInjection n state

theorem registered_injection_connection (ν : ℝ) (u : Velocity) (pressure : Pressure)
    (n : ℕ) (state : Sixteen3) (z : Domain) :
    timeDerivative u z + transport u z + (-ν) • spatialLaplacian u z +
      pressureGradient pressure z = registeredInjectionForce ν u pressure n state z := rfl

theorem registered_injection_eq_injection (ν : ℝ) (u : Velocity) (pressure : Pressure)
    (n : ℕ) (state : Sixteen3) :
    registeredInjectionForce ν u pressure n state = injectionForce ν u pressure n := rfl

theorem registered_injection_smooth (ν : ℝ) (u : Velocity) (pressure : Pressure)
    (n : ℕ) (state : Sixteen3) (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ pressure) :
    ContDiff ℝ ∞ (registeredInjectionForce ν u pressure n state) :=
  injection_smooth ν u pressure n hu hp

theorem registered_zero_field (ν : ℝ) (n : ℕ) (state : Sixteen3) (z : Domain) :
    registeredInjectionForce ν (fun _ => 0) (fun _ => 0) n state z = 0 :=
  zero_field_injection ν n z

theorem registered_time_linear (ν : ℝ) (v : Space) (n : ℕ)
    (state : Sixteen3) (z : Domain) :
    registeredInjectionForce ν (timeLinearVelocity v) (fun _ => 0) n state z = v :=
  time_linear_injection ν v n z

end
end Imscribing.NSInjectionField
