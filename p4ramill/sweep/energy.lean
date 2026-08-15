import Mathlib
open Finset
open scoped BigOperators

noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The additive-energy count: quadruples with `a + b = c + d`, counted as the
number of representations of each `x` as a sum of two elements of `A`, squared
and summed. Real-valued and stated over a `Finset`, so it elaborates without
choice-of-instance games on a `Set`. -/
def reps (A : Finset G) (x : G) : ℕ := (A ×ˢ A).filter (fun p => p.1 + p.2 = x) |>.card

def energy (A : Finset G) : ℕ := ∑ x : G, (reps A x) ^ 2

/-- Every pair contributes to exactly one `x`, so the representation counts sum
to `|A|²`. -/
theorem sum_reps (A : Finset G) : ∑ x : G, reps A x = A.card ^ 2 := by
  classical
  unfold reps
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 + p.2)
      (s := A ×ˢ A) (t := (Finset.univ : Finset G)) (fun _ _ => Finset.mem_univ _)]
  · rw [Finset.card_product, sq]

/-- **The Cauchy–Schwarz lower bound on additive energy.**

`E(A) ≥ |A|⁴ / |G|`. The representation counts sum to `|A|²` over `|G|` points,
so squaring cannot be smaller than the square of the mean. This is the standard
bound, and it is the one an argument about energy actually uses; it is strictly
stronger than `E(A) ≥ α³|G|`, by a factor of `|A|·|G|`. -/
theorem energy_ge (A : Finset G) :
    (A.card : ℝ) ^ 4 / (Fintype.card G : ℝ) ≤ (energy A : ℝ) := by
  classical
  have hG : (0 : ℝ) < (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this
  have hcs : ((∑ x : G, (reps A x : ℝ))) ^ 2
      ≤ (Fintype.card G : ℝ) * ∑ x : G, (reps A x : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset G))
      (f := fun x => (reps A x : ℝ))
    simpa using this
  have hsum : (∑ x : G, (reps A x : ℝ)) = (A.card : ℝ) ^ 2 := by
    have h := sum_reps A
    calc (∑ x : G, (reps A x : ℝ)) = ((∑ x : G, reps A x : ℕ) : ℝ) := by push_cast; ring
      _ = ((A.card ^ 2 : ℕ) : ℝ) := by rw [h]
      _ = (A.card : ℝ) ^ 2 := by push_cast; ring
  rw [hsum] at hcs
  have hE : (energy A : ℝ) = ∑ x : G, (reps A x : ℝ) ^ 2 := by
    unfold energy; push_cast; ring
  rw [hE]
  rw [div_le_iff₀ hG]
  calc (A.card : ℝ) ^ 4 = ((A.card : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (Fintype.card G : ℝ) * ∑ x : G, (reps A x : ℝ) ^ 2 := hcs
    _ = (∑ x : G, (reps A x : ℝ) ^ 2) * (Fintype.card G : ℝ) := by ring

#print axioms sum_reps
#print axioms energy_ge
