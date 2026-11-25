import Mathlib
namespace Imscribing.Millennium.SaturationHorizon
noncomputable section

/-- The Diophantine saturation horizon: n=4 is the unique nontrivial integer
    with 2^n = n^2 = 16 (n=2 is the trivial one). At n=4 the internal dyadic
    reflection S×S is isomorphic to the external powerset P(S). -/
theorem saturation_horizon_four :
    (2 : ℕ)^4 = 4^2 ∧ 4^2 = 16 ∧
    (2 : ℕ)^2 = 2^2 ∧
    (∀ n : ℕ, (2 : ℕ)^n = n^2 → n = 2 ∨ n = 4) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · intro n h
    -- verified by exhaustive bound: 2^n = n^2 only for n=2,4
    have hbound : n ≤ 4 := by
      by_contra hn
      have hn5 : 5 ≤ n := by omega
      -- for n >= 5, 2^n > n^2
      have hg : ∀ m ≥ 5, (2 : ℕ)^m > m^2 := by
        intro m hm
        induction' m with m ih
        · omega
        · by_cases hm5 : 5 ≤ m
          · have ih' := ih hm5
            calc (2:ℕ)^(m+1) = 2 * 2^m := by rw [pow_succ]; ring
                 _ > 2 * m^2 := by nlinarith
                 _ ≥ (m+1)^2 := by nlinarith [hm5]
          · have hm4 : m = 4 := by omega
            subst m
            norm_num
      have hgt := hg n hn5
      omega
    interval_cases n
    · norm_num at h
    · norm_num at h
    · exact Or.inl rfl
    · norm_num at h
    · exact Or.inr rfl

/-- The 1024 reduced moduli at d=2048: 4·16^2 = 1024 = d/2, and the
    conductor 16^3 = 4·1024. -/
theorem reduced_moduli_saturation :
    (4 : ℕ) * 16^2 = 1024 ∧
    1024 = 2048 / 2 ∧
    (16 : ℕ)^3 = 4 * 1024 := by
  norm_num

