import Imscribing.ABC_IUTTClosure

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

/-! A scalar limit reading attached to the typed IUTT tail regime. -/

structure IUTTAsymptoticReading (ε : ℝ) where
  tail : IUTTTailClosure ε
  limit : ℝ
  converges : Filter.Tendsto tail.regime.read Filter.atTop (nhds limit)

noncomputable def IUTTAsymptoticReading.ofWindowConvergence
    (ε : ℝ) (h : ∃ L : ℝ,
      Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds L)) :
    IUTTAsymptoticReading ε := by
  exact
    { tail := exactIUTTTailClosure ε
      limit := Classical.choose h
      converges := by
        have heq : (exactIUTTTailClosure ε).regime.read = windowMaximum ε :=
          funext (exactIUTTTailClosure ε).regime.read_is_window
        rw [heq]
        exact Classical.choose_spec h }

theorem IUTTAsymptoticReading.read_is_window
    (reading : IUTTAsymptoticReading ε) :
    reading.tail.regime.read = windowMaximum ε := by
  funext N
  exact reading.tail.regime.read_is_window N

noncomputable def IUTTAsymptoticReading.toClosure
    (reading : IUTTAsymptoticReading ε) : AsymptoticClosure ε :=
  { limit := reading.limit
    converges := by
      rw [← reading.read_is_window]
      exact reading.converges }

theorem IUTTAsymptoticReading.maximum_le_limit
    (reading : IUTTAsymptoticReading ε) (N : ℕ) :
    windowMaximum ε N ≤ reading.limit :=
  reading.toClosure.maximum_le_limit N

theorem IUTTAsymptoticReading.triple_below_limit
    (reading : IUTTAsymptoticReading ε) (t : Triple) :
    discrepancy ε t ≤ reading.limit := by
  obtain ⟨N, hN⟩ := reading.tail.regime.cofinal t
  exact hN.trans (by
    rw [reading.tail.regime.read_is_window] at hN ⊢
    exact reading.maximum_le_limit N)

theorem iutt_asymptotic_to_conjecture
    (readings : ∀ ε : ℝ, 0 < ε → IUTTAsymptoticReading ε) :
    Conjecture := by
  apply AsymptoticClosure.to_conjecture
  intro ε hε
  exact (readings ε hε).toClosure

noncomputable def iuttAsymptoticWitness
    (readings : ∀ ε : ℝ, 0 < ε → IUTTAsymptoticReading ε) :
    Verdict Conjecture :=
  .held (iutt_asymptotic_to_conjecture readings)
    (uniform_spectral_iff_abc.mpr (iutt_asymptotic_to_conjecture readings))

theorem iuttAsymptoticWitness_is_B
    (readings : ∀ ε : ℝ, 0 < ε → IUTTAsymptoticReading ε) :
    (iuttAsymptoticWitness readings).classify = (true, true) := rfl

noncomputable def iuttAsymptoticFamilyOfConvergence
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds L)) :
    ∀ ε : ℝ, 0 < ε → IUTTAsymptoticReading ε :=
  fun ε hε => IUTTAsymptoticReading.ofWindowConvergence ε (h ε hε)

theorem iuttAsymptoticFamilyOfConvergence_to_conjecture
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds L)) :
    Conjecture :=
  iutt_asymptotic_to_conjecture (iuttAsymptoticFamilyOfConvergence h)

noncomputable def iuttAsymptoticWitnessOfConvergence
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds L)) :
    Verdict Conjecture :=
  iuttAsymptoticWitness (iuttAsymptoticFamilyOfConvergence h)

theorem iuttAsymptoticWitnessOfConvergence_is_B
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds L)) :
    (iuttAsymptoticWitnessOfConvergence h).classify = (true, true) := by
  simp [iuttAsymptoticWitnessOfConvergence, iuttAsymptoticFamilyOfConvergence,
    iuttAsymptoticWitness, Verdict.classify]

end Imscribing.ABC
