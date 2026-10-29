import Imscribing.ABC_Closure

/-!
# Prime multiplicities and arithmetic comparison

This is an arithmetic change of presentation, with exact reconstruction.
It is not an identification of prime factorization with the IUT Θ-link.
The remaining error estimate is stated and related exactly to ABC.
-/
namespace Imscribing.ABC

def primePresentation (t : Triple) : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) × (ℕ →₀ ℕ) :=
  (t.a.factorization, t.b.factorization, t.c.factorization)

def reconstructPrimeData (f : ℕ →₀ ℕ) : ℕ := f.prod (fun p k => p ^ k)

theorem reconstruct_factorization (n : ℕ) (hn : 0 < n) :
    reconstructPrimeData n.factorization = n :=
  Nat.factorization_prod_pow_eq_self (ne_of_gt hn)

theorem primePresentation_recovers (t : Triple) :
    (reconstructPrimeData (primePresentation t).1,
      reconstructPrimeData (primePresentation t).2.1,
      reconstructPrimeData (primePresentation t).2.2) = (t.a, t.b, t.c) := by
  simp only [primePresentation, reconstruct_factorization _ t.a_pos,
    reconstruct_factorization _ t.b_pos, reconstruct_factorization _ t.c_pos]

theorem primePresentation_injective : Function.Injective primePresentation := by
  intro s t h
  have hdata := congrArg (fun p : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) × (ℕ →₀ ℕ) =>
    (reconstructPrimeData p.1, reconstructPrimeData p.2.1,
      reconstructPrimeData p.2.2)) h
  dsimp only at hdata
  rw [primePresentation_recovers, primePresentation_recovers] at hdata
  cases s
  cases t
  simp only [Prod.mk.injEq] at hdata
  rcases hdata with ⟨rfl, rfl, rfl⟩
  rfl

noncomputable def primeHeight (t : Triple) : ℝ :=
  t.c.factorization.sum (fun p k => (k : ℝ) * Real.log p)

noncomputable def primeSupportHeight (t : Triple) : ℝ :=
  ∑ p ∈ (t.a * t.b * t.c).primeFactors, Real.log (p : ℝ)

theorem primeHeight_calibration (t : Triple) : primeHeight t = logHeight t :=
  (Real.log_nat_eq_sum_factorization t.c).symm

theorem primeSupportHeight_calibration (t : Triple) :
    primeSupportHeight t = logRadical t := by
  unfold logRadical rad
  rw [radical_eq_primeFactors, Nat.cast_prod]
  symm
  apply Real.log_prod
  intro p hp
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- The signed excess of multiplicity-weighted height over total prime
    support. Both terms are computed from the actual prime data. -/
noncomputable def primeExcess (t : Triple) : ℝ :=
  primeHeight t - primeSupportHeight t

theorem primeExcess_calibration (t : Triple) :
    primeExcess t = logHeight t - logRadical t := by
  simp only [primeExcess, primeHeight_calibration, primeSupportHeight_calibration]

theorem prime_height_comparison (t : Triple) :
    logHeight t = primeSupportHeight t + primeExcess t := by
  rw [primeExcess, primeHeight_calibration]
  ring

/-- The transported support height has its uniform estimate with C = 0. -/
theorem prime_support_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∀ t : Triple, primeSupportHeight t ≤ (1 + η) * logRadical t + 0 := by
  intro t
  rw [primeSupportHeight_calibration]
  have := mul_nonneg hη.le (logRadical_pos t).le
  nlinarith

/-- This equivalence prevents relabeling the remaining ABC estimate as
    an already proved error lemma. -/
theorem primeExcess_sublinear_iff_abc : SublinearComparisonError primeExcess ↔ Conjecture := by
  constructor
  · intro h
    apply abc_of_filtered_estimate
    apply filtered_estimate_of_comparison primeSupportHeight primeExcess
    · intro t
      exact (prime_height_comparison t).le
    · intro η hη
      exact ⟨0, prime_support_uniform_bound η hη⟩
    · exact h
  · intro h η hη
    obtain ⟨C, hC⟩ := conjecture_iff_log_estimate.mp h η hη
    refine ⟨C, fun t => ?_⟩
    rw [primeExcess_calibration]
    have := hC t
    nlinarith

/-- On squarefree c, its entire height already occurs in prime support. -/
theorem height_le_rad_of_squarefree (t : Triple) (hc : Squarefree t.c) :
    (t.c : ℝ) ≤ rad t := by
  have hprod : t.a * t.b * t.c ≠ 0 :=
    ne_of_gt (Nat.mul_pos (Nat.mul_pos t.a_pos t.b_pos) t.c_pos)
  have hdiv : t.c ∣ radical (t.a * t.b * t.c) :=
    (UniqueFactorizationMonoid.dvd_radical_iff hc.isRadical hprod).mpr (dvd_mul_left _ _)
  have hle := Nat.le_of_dvd (radical_pos (t.a * t.b * t.c)) hdiv
  unfold rad
  exact_mod_cast hle

theorem primeExcess_nonpos_of_squarefree (t : Triple) (hc : Squarefree t.c) :
    primeExcess t ≤ 0 := by
  rw [primeExcess_calibration, sub_nonpos]
  exact Real.log_le_log (by exact_mod_cast t.c_pos) (height_le_rad_of_squarefree t hc)

/-- A genuine uniform arithmetic estimate on the squarefree-c family. -/
theorem squarefree_discrepancy_bound (ε : ℝ) (hε : 0 < ε) (t : Triple)
    (hc : Squarefree t.c) : discrepancy ε t ≤ 0 := by
  have he := primeExcess_nonpos_of_squarefree t hc
  rw [primeExcess_calibration] at he
  have := mul_nonneg hε.le (logRadical_pos t).le
  unfold discrepancy
  nlinarith

/-- The squarefree-c family has the same multiplicative constant K=1
    for every triple and every positive epsilon. -/
theorem squarefree_abc_bound (ε : ℝ) (hε : 0 < ε) (t : Triple)
    (hc : Squarefree t.c) : (t.c : ℝ) ≤ (rad t) ^ (1 + ε) := by
  have hd := squarefree_discrepancy_bound ε hε t hc
  have hl : logHeight t ≤ (1 + ε) * logRadical t + Real.log 1 := by
    simp only [Real.log_one, add_zero]
    exact sub_nonpos.mp hd
  have hb := (bound_iff_log_bound t ε 1 (by norm_num)).mpr hl
  simpa only [one_mul] using hb

def squarefreeArithmeticWitness :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict
      (∀ ε : ℝ, 0 < ε → ∀ t : Triple, Squarefree t.c →
        (t.c : ℝ) ≤ (rad t) ^ (1 + ε)) :=
  .held squarefree_abc_bound primePresentation_injective

theorem squarefreeArithmeticWitness_is_B :
    squarefreeArithmeticWitness.classify = (true, true) := rfl

/-- The proved family can be removed from the outstanding estimate.
    The remaining constant is uniform over all non-squarefree-c triples. -/
theorem abc_iff_nonsquarefree_discrepancy : Conjecture ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : Triple,
      ¬ Squarefree t.c → discrepancy ε t ≤ C := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := conjecture_iff_uniform_discrepancy.mp h ε hε
    exact ⟨C, fun t _ => hC t⟩
  · intro h
    apply conjecture_iff_uniform_discrepancy.mpr
    intro ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨max C 0, fun t => ?_⟩
    by_cases hc : Squarefree t.c
    · exact (squarefree_discrepancy_bound ε hε t hc).trans (le_max_right C 0)
    · exact (hC t hc).trans (le_max_left C 0)

end Imscribing.ABC
