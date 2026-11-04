import Mathlib
import Imscribing.PrimeWhorlCore

/-!
# Prime Whorl: independent arithmetic witness certification

The defect is generated elsewhere (phase, horn fibre, reduced determinant,
trace, or cross-frame calculation). Only the *exact GCD* is certified here.
This file makes no claim that a particular walk will find a proper divisor.
-/

namespace Imscribing.PrimeWhorl

/-- A proper divisor of the input source N. -/
def ProperDivisor (N d : Nat) : Prop :=
  1 < d ∧ d < N ∧ d ∣ N

/-- A tagged evidence channel. Tags preserve provenance without implying that
    all defect-generating mechanisms are mathematically equivalent. -/
inductive WitnessKind where
  | hornFibre
  | livePhaseInterior
  | livePhaseExterior
  | reducedDetInterior
  | reducedDetExterior
  | traceInterior
  | traceExterior
  | crossFrame
  deriving Repr, DecidableEq

/-- Each certificate retains its source and original (possibly large) defect. -/
structure ExactWitness (N : Nat) where
  kind : WitnessKind
  defect : Nat
  divisor : Nat
  eqGcd : divisor = Nat.gcd N defect
  proper : ProperDivisor N divisor

/-- A GCD is a proper-divisor certificate *if* it lies strictly between 1 and N. -/
theorem gcd_certifies (N defect : Nat)
    (hlo : 1 < Nat.gcd N defect)
    (hhi : Nat.gcd N defect < N) :
    ProperDivisor N (Nat.gcd N defect) := by
  exact ⟨hlo, hhi, Nat.gcd_dvd_left N defect⟩

/-- Make a proof-carrying witness or return `none`. All checks are exact and
    executable for arbitrary-precision natural numbers. -/
def certify (N : Nat) (kind : WitnessKind) (defect : Nat) :
    Option (ExactWitness N) := by
  let d := Nat.gcd N defect
  if hlo : 1 < d then
    if hhi : d < N then
      exact some {
        kind := kind
        defect := defect
        divisor := d
        eqGcd := rfl
        proper := gcd_certifies N defect hlo hhi
      }
    else
      exact none
  else
    exact none

/-- A successful certification always includes the exact proper-divisor proof. -/
theorem certified_is_proper {N : Nat} (w : ExactWitness N) :
    1 < w.divisor ∧ w.divisor < N ∧ w.divisor ∣ N := w.proper

/-- A successful certification always records the exact GCD it tested. -/
theorem certified_matches_gcd {N : Nat} (w : ExactWitness N) :
    w.divisor = Nat.gcd N w.defect := w.eqGcd

/-- Native small arithmetic regression checks; they check extraction only,
    not a purported derivation of the defect from a braid. -/
example : Nat.gcd 299 23 = 23 := by decide
example : Nat.gcd 299 260 = 13 := by decide
example : Nat.gcd 5917 3721 = 61 := by decide
example : Nat.gcd 5917 1098 = 61 := by decide
example : Nat.gcd 5917 4559 = 97 := by decide
example : Nat.gcd 5917 4085 = 1 := by decide

end Imscribing.PrimeWhorl
