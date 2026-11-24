import Imscribing.ABC_LogBounds

namespace Imscribing.ABC

/-- Exchange the two summands, retaining the arithmetic constraints. -/
def Triple.swap (t : Triple) : Triple :=
  ⟨t.b, t.a, t.c, t.b_pos, t.a_pos, by rw [Nat.add_comm, t.sum_eq], t.coprime.symm⟩

theorem discrepancy_swap (ε : ℝ) (t : Triple) :
    discrepancy ε t.swap = discrepancy ε t := by
  unfold discrepancy logHeight logRadical rad Triple.swap
  rw [Nat.mul_comm t.b t.a]

/-- Exhaustive numerical certificates only need one ordering of each pair. -/
theorem window_upper_of_ordered (ε U : ℝ) (B : ℕ)
    (ordered : ∀ t : Triple, t.c ≤ B → t.a ≤ t.b → discrepancy ε t ≤ U) :
    ∀ t : Triple, t.c ≤ B → discrepancy ε t ≤ U := by
  intro t hc
  by_cases hab : t.a ≤ t.b
  · exact ordered t hc hab
  · have h := ordered t.swap hc (by dsimp [Triple.swap]; omega)
    simpa only [discrepancy_swap] using h

end Imscribing.ABC
