import Imscribing.ABC_AsymptoticClosure

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

/-- The closed computational tail regime at one epsilon. Its readout is the
    exact exhaustive trajectory, with finite attainment and cofinal coverage.
    No limiting scalar is part of this object. -/
structure TailRegime (ε : ℝ) where
  read : ℕ → ℝ
  read_is_window : ∀ N, read N = windowMaximum ε N
  step_closed : Monotone read
  finite_attained : ∀ N, ∃ t ∈ arithmeticWindow N, discrepancy ε t = read N
  cofinal : ∀ t : Triple, ∃ N, discrepancy ε t ≤ read N

noncomputable def exactTailRegime (ε : ℝ) : TailRegime ε where
  read := windowMaximum ε
  read_is_window := fun _ => rfl
  step_closed := windowMaximum_monotone ε
  finite_attained := windowMaximum_attained ε
  cofinal := fun t =>
    ⟨t.c, discrepancy_le_windowMaximum ε t.c t (arithmeticWindow_exhaustive t)⟩

theorem TailRegime.read_monotone {ε : ℝ} (r : TailRegime ε) :
    Monotone r.read := r.step_closed

theorem TailRegime.read_attained {ε : ℝ} (r : TailRegime ε) (N : ℕ) :
    ∃ t ∈ arithmeticWindow N, discrepancy ε t = r.read N := by
  rw [r.read_is_window]
  exact windowMaximum_attained ε N

theorem TailRegime.read_dominates {ε : ℝ} (r : TailRegime ε) (t : Triple) :
    ∃ N, discrepancy ε t ≤ r.read N := r.cofinal t

/-- A Witness for tail Closure retains attainment and cofinality as separate
    evidence fields. Both are properties of the trajectory itself. -/
def tailClosureWitness (ε : ℝ) :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict
      (∀ N : ℕ, ∃ t ∈ arithmeticWindow N, discrepancy ε t =
      (exactTailRegime ε).read N) :=
  Verdict.held (Q := ∀ t : Triple, ∃ N,
    discrepancy ε t ≤ (exactTailRegime ε).read N)
    (exactTailRegime ε).finite_attained
    (exactTailRegime ε).cofinal

theorem tailClosureWitness_is_B (ε : ℝ) :
    (tailClosureWitness ε).classify = (true, true) := by
  simp [tailClosureWitness, Verdict.classify]

theorem tailClosure_preserves_finite_reading (ε : ℝ) (N : ℕ) :
    (exactTailRegime ε).read N = windowMaximum ε N := rfl

theorem tailClosure_preserves_triple (ε : ℝ) (t : Triple) :
    ∃ N, discrepancy ε t ≤ (exactTailRegime ε).read N :=
  (exactTailRegime ε).cofinal t

end Imscribing.ABC
