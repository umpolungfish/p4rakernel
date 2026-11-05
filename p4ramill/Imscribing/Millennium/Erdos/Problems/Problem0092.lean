import Mathlib

/-!
# Erdős problem #92

Reference: https://www.erdosproblems.com/92
The quantity counts equidistant neighbours, rather than distinct distances.
The disproof below is specified as a proposition; no disproof is assumed.
-/

open Filter
open scoped Topology
noncomputable section
namespace Erdos92

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Largest number of other points on one circle centred at `x`. -/
def maxEquidistantPointsAt (x : Plane) (A : Finset Plane) : ℕ :=
  ((A.erase x).image (dist x)).sup fun d =>
    ((A.erase x).filter fun y => dist x y = d).card

/-- Every centre in a nonempty configuration has at least `k` equidistant neighbours. -/
def HasMinEquidistantProperty (k : ℕ) (A : Finset Plane) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPointsAt x A

def possibleValues (n : ℕ) : Set ℕ :=
  {k | ∃ A : Finset Plane, A.card = n ∧ HasMinEquidistantProperty k A}

lemma possibleValues_bddAbove (n : ℕ) : BddAbove (possibleValues n) := by
  refine ⟨n, ?_⟩
  rintro k ⟨A, hcard, ⟨x, hx⟩, hall⟩
  apply (hall x hx).trans
  unfold maxEquidistantPointsAt
  apply Finset.sup_le
  intro d hd
  exact (Finset.card_filter_le _ _).trans ((Finset.card_erase_le).trans hcard.le)

/-- Maximum possible minimum equidistant-neighbour count for `n` points. -/
def f (n : ℕ) : ℕ := sSup (possibleValues n)

/-- The strong bound asked for in #92, including its free constant. -/
def StrongBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    (f n : ℝ) ≤ (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)))

/-- A counterexample family must violate each constant at arbitrarily large sizes. -/
def CounterexampleFamily : Prop :=
  ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ))) < (f n : ℝ)

/-- Equivalent formulations of the disproof obligation, without assuming it. -/
theorem erdos_problem_92 : ¬ StrongBound ↔ CounterexampleFamily := by
  simp only [StrongBound, CounterexampleFamily, eventually_atTop, not_exists,
    not_and, not_forall, not_le, exists_prop]

end Erdos92
