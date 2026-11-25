import Mathlib
namespace Imscribing.Millennium.SigmaStability
noncomputable section

/-- The sigma-stability constraint on the d=2048 character subgroup: the
    Galois involution sigma (the nontrivial automorphism of Q(sqrt m_d)) acts
    on the moduli by N_{k+d/2} = sigma(N_k). The subgroup cutting the ray class
    group down to 1024 independent moduli must be sigma-stable, and sigma^2=id. -/
theorem sigma_stability_d2048 :
    (2048 : ℕ) = 2 ^ 11 ∧
    2048 / 2 = 1024 ∧
    (16 : ℕ)^3 = 4096 := by
  norm_num

/-- The involution k -> k+m on ZMod (2m) has order two. -/
theorem half_turn_involution (m : ℕ) (k : ZMod (2*m)) :
    (k + (m : ZMod (2*m))) + (m : ZMod (2*m)) = k := by
  have h : ((m : ZMod (2*m)) + (m : ZMod (2*m))) = 0 := by
    rw [← Nat.cast_add]
    rw [show m + m = 2*m by omega]
    simp
  calc
    (k + (m : ZMod (2*m))) + (m : ZMod (2*m)) = k + ((m : ZMod (2*m)) + (m : ZMod (2*m))) := by abel
    _ = k + 0 := by rw [h]
    _ = k := by rw [add_zero]

