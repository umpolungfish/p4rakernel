import Mathlib

/-! One shared proton in a concrete mixed contact Gram realization.
The donor and acceptor remain coordinates of the containing conformation.
The mechanical potential and executing root map are defined together.
This local model does not assert whole-protein closure or a universal bond law.
-/
namespace Imscribing.Biochem.MixedContactGram

def stiffness (pd pa c : ℝ) : ℝ := pd + pa + 2*c
def weight (pd pa c d a : ℝ) : ℝ := (pd+c)*d + (pa+c)*a
def potential (pd pa c d a x : ℝ) : ℝ :=
  pd*(x-d)^2 + pa*(x-a)^2 + 2*c*(x-d)*(x-a)
def forceResidual (pd pa c d a x : ℝ) : ℝ :=
  2*(stiffness pd pa c*x - weight pd pa c d a)
noncomputable def root (pd pa c d a : ℝ) : ℝ := weight pd pa c d a / stiffness pd pa c

theorem mixed_stiffness_positive {pd pa c im : ℝ}
    (trace : pd+pa=1) (mixed : c*c+im*im < pd*pa) :
    0 < stiffness pd pa c := by
  have hb : 4*c*c < 1 := by nlinarith [sq_nonneg (pd-pa),sq_nonneg im]
  have hc : -(1/2:ℝ) < c := by nlinarith [sq_nonneg (c+(1/2:ℝ))]
  unfold stiffness
  linarith

theorem root_has_zero_force (pd pa c d a : ℝ) (h : stiffness pd pa c ≠ 0) :
    forceResidual pd pa c d a (root pd pa c d a) = 0 := by
  unfold forceResidual root
  field_simp [h]
  <;> ring

theorem complete_gram_square (pd pa c d a x : ℝ) (h : stiffness pd pa c ≠ 0) :
    potential pd pa c d a x - potential pd pa c d a (root pd pa c d a) =
      stiffness pd pa c * (x-root pd pa c d a)^2 := by
  unfold potential root
  field_simp
  dsimp [stiffness,weight] at *
  nlinarith [h]

theorem root_is_stable_minimum (pd pa c d a x : ℝ) (h : 0 < stiffness pd pa c) :
    potential pd pa c d a (root pd pa c d a) ≤ potential pd pa c d a x := by
  have equality := complete_gram_square pd pa c d a x (ne_of_gt h)
  have nonnegative := mul_nonneg (le_of_lt h) (sq_nonneg (x-root pd pa c d a))
  linarith

theorem root_is_unique_minimum (pd pa c d a x : ℝ) (h : 0 < stiffness pd pa c)
    (same : potential pd pa c d a x = potential pd pa c d a (root pd pa c d a)) :
    x = root pd pa c d a := by
  have equality := complete_gram_square pd pa c d a x (ne_of_gt h)
  have square_zero : (x-root pd pa c d a)^2=0 := by nlinarith
  have difference : x-root pd pa c d a=0 := by nlinarith [sq_nonneg (x-root pd pa c d a)]
  linarith

/-- Eliminating the shared proton retains a donor/acceptor coupling.
Its rest displacement is zero in this model; chemical and steric guards
must remain in the containing conformation. -/
theorem retained_pair_potential (pd pa c d a : ℝ) (h : stiffness pd pa c ≠ 0) :
    potential pd pa c d a (root pd pa c d a) =
      (pd*pa-c*c)/stiffness pd pa c*(d-a)^2 := by
  unfold potential root weight
  field_simp [h]
  dsimp [stiffness]
  ring

#print axioms retained_pair_potential
#print axioms mixed_stiffness_positive
#print axioms root_has_zero_force
#print axioms complete_gram_square
#print axioms root_is_stable_minimum
#print axioms root_is_unique_minimum
end Imscribing.Biochem.MixedContactGram
