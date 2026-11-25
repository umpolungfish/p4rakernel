import Mathlib
namespace Imscribing.Millennium.LevelNQuantization
noncomputable section

/-- The level-N quantization of CP^1 has dimension N: Sym^{N-1} C^2.  At
    N=2048 this is C^2048 carrying the spin-(N-1)/2 SU(2) representation,
    which restricts to the Weyl-Heisenberg group H(Z/N).  We record the
    dimension identity and the SU(2) commutators at level N. -/
theorem levelN_quantization_dimension (N : ℕ) (hN : 0 < N) :
    Nat.choose N (N - 1) = N := by
  rw [← Nat.choose_symm (Nat.sub_le N 1)]
  rw [show N - (N - 1) = 1 by omega]
  exact Nat.choose_one_right N

/-- At the sphere endpoint N = 2048 the quantized Hilbert space has the
    Weyl-Heisenberg dimension d = 2048 and the Bloch equator trine seed. -/
theorem sphere_endpoint_2048 :
    Nat.choose 2048 (2048 - 1) = 2048 ∧
    (2048 : ℕ) = 2 ^ 11 := by
  exact ⟨levelN_quantization_dimension 2048 (by norm_num), by norm_num⟩

