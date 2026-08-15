import Mathlib
open Finset

example (A : Finset ℕ) (j : ℕ) (hsub : A ⊆ Finset.Ico (2^j) (2^(j+1)))
    (hA : ThreeAPFree (A : Set ℕ)) :
    A.card ≤ rothNumberNat (2^j) := by
  have h1 : A.card ≤ addRothNumber (Finset.Ico (2^j) (2^(j+1))) :=
    hA.le_addRothNumber hsub
  have h2 : addRothNumber (Finset.Ico (2^j) (2^(j+1))) = rothNumberNat (2^(j+1) - 2^j) :=
    addRothNumber_Ico _ _
  have h3 : 2^(j+1) - 2^j = 2^j := by
    have : 2^(j+1) = 2 * 2^j := by ring
    omega
  rw [h2, h3] at h1
  exact h1
