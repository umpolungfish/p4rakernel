import Imscribing.ABC_ScaleChain

namespace Imscribing.ABC

/-- An asymptotic Closure record for one epsilon. The trajectory is the
    exact exhaustive window maximum; convergence is the Closure field. -/
structure AsymptoticClosure (ε : ℝ) where
  limit : ℝ
  converges : Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds limit)

theorem AsymptoticClosure.bounded (closure : AsymptoticClosure ε) :
    ∃ C : ℝ, ∀ t : Triple, discrepancy ε t ≤ C := by
  have hb : BddAbove (Set.range (windowMaximum ε)) :=
    closure.converges.bddAbove_range
  exact (window_bounded_iff_discrepancy ε).mp hb

theorem AsymptoticClosure.maximum_le_limit (closure : AsymptoticClosure ε)
    (N : ℕ) : windowMaximum ε N ≤ closure.limit := by
  have hm := windowMaximum_monotone ε
  have hb := closure.converges.bddAbove_range
  have hs : (⨆ n, windowMaximum ε n) = closure.limit := by
    exact tendsto_nhds_unique (tendsto_atTop_ciSup hm hb) closure.converges
  rw [← hs]
  exact le_ciSup hb N

theorem AsymptoticClosure.to_conjecture
    (closures : ∀ ε : ℝ, 0 < ε → AsymptoticClosure ε) : Conjecture := by
  apply abc_iff_window_convergence.mpr
  intro ε hε
  exact ⟨(closures ε hε).limit, (closures ε hε).converges⟩

def asymptoticWitness
    (closures : ∀ ε : ℝ, 0 < ε → AsymptoticClosure ε) :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict Conjecture :=
  .held (AsymptoticClosure.to_conjecture closures)
    (uniform_spectral_iff_abc.mpr (AsymptoticClosure.to_conjecture closures))

theorem asymptoticWitness_is_B
    (closures : ∀ ε : ℝ, 0 < ε → AsymptoticClosure ε) :
    (asymptoticWitness closures).classify = (true, true) := rfl

/-- A finite chain is compatible with the asymptotic trajectory at every
    later index. -/
theorem chain_reading_below_asymptotic
    (closure : AsymptoticClosure ε) (N : ℕ) :
    windowMaximum ε N ≤ closure.limit := closure.maximum_le_limit N

theorem asymptotic_lower_contains_finite
    (closure : AsymptoticClosure ε) (N : ℕ)
    (e : WindowEnclosure ε N) : e.lower ≤ closure.limit :=
  e.lower_le.trans (closure.maximum_le_limit N)

end Imscribing.ABC
