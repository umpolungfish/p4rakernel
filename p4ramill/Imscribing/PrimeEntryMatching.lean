import Mathlib
import Imscribing.FractionalHall

open scoped BigOperators

namespace Imscribing

/-- The low source vertices `1, ..., m`, represented as a subtype of `Fin`. -/
abbrev PrimeLowSource (m : ℕ) := {i : Fin (m + 1) // i.val ≠ 0}

/-- Destinations in the low-index interval `(n*q, upper]`. -/
abbrev PrimeEntryDestination (n q upper : ℕ) :=
  {x : Fin (upper + 1) // n * q < x.val}

/-- A low source is adjacent to a destination when the latter is obtained
by multiplying it by one prime. -/
def PrimeEntryAdj (m n q upper : ℕ)
    (i : PrimeLowSource m) (x : PrimeEntryDestination n q upper) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x.val.val = i.val.val * p

/--
A fractional flow supported on prime-entry edges, with every low-source row
summing to one and every destination column having capacity at most one,
produces an injective prime-entry matching.

The analytic number theory enters only through the four hypotheses on `w`.
-/
theorem primeEntryFlow_matching
    (m n q upper : ℕ)
    (w : PrimeLowSource m → PrimeEntryDestination n q upper → ℝ)
    (hw_nonneg : ∀ i x, 0 ≤ w i x)
    (hw_supported : ∀ i x, ¬ PrimeEntryAdj m n q upper i x → w i x = 0)
    (hw_row : ∀ i, (∑ x : PrimeEntryDestination n q upper, w i x) = 1)
    (hw_col : ∀ x, (∑ i : PrimeLowSource m, w i x) ≤ 1) :
    ∃ f : PrimeLowSource m → PrimeEntryDestination n q upper,
      Function.Injective f ∧
      ∀ i, ∃ p : ℕ, Nat.Prime p ∧ (f i).val.val = i.val.val * p := by
  classical
  obtain ⟨f, hf_inj, hf_adj⟩ :=
    _root_.fractionalFlow_matching
      (PrimeEntryAdj m n q upper) w hw_nonneg hw_supported hw_row hw_col
  exact ⟨f, hf_inj, hf_adj⟩

/-- Every value selected by the low-index matching lies in `(n*q, upper]`. -/
theorem primeEntryDestination_bounds
    (n q upper : ℕ) (x : PrimeEntryDestination n q upper) :
    n * q < x.val.val ∧ x.val.val ≤ upper := by
  constructor
  · exact x.property
  · exact Nat.le_of_lt_succ x.val.isLt

end Imscribing
