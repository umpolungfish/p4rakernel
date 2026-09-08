import Imscribing.ABC_ScaleClosure

namespace Imscribing.ABC

/-- A finite ordered family of certified spectral readings. -/
structure ScaleChain (ε : ℝ) (k : ℕ) where
  index : Fin k → ℕ
  reading : ∀ i, WindowEnclosure ε (index i)
  index_mono : Monotone index

theorem scaleLink_trans {ε : ℝ} {N M P : ℕ}
    (hNM : ScaleLink ε N M) (hMP : ScaleLink ε M P) : ScaleLink ε N P :=
  ⟨hNM.index_le.trans hMP.index_le, hNM.maximum_le.trans hMP.maximum_le⟩

theorem ScaleChain.link {ε : ℝ} {k : ℕ} (chain : ScaleChain ε k)
    {i j : Fin k} (hij : i ≤ j) : ScaleLink ε (chain.index i) (chain.index j) :=
  scaleLink_of_le _ (chain.index_mono hij)

theorem ScaleChain.cross_bound {ε : ℝ} {k : ℕ} (chain : ScaleChain ε k)
    {i j : Fin k} (hij : i ≤ j) :
    (chain.reading i).lower ≤ (chain.reading j).upper :=
  enclosure_cross_bound (chain.link hij) (chain.reading i) (chain.reading j)

theorem ScaleChain.lower_or_cross {ε : ℝ} {k : ℕ} (chain : ScaleChain ε k)
    {i j : Fin k} (hij : i ≤ j) :
    (chain.reading i).lower ≤ (chain.reading j).lower ∨
      (chain.reading i).lower ≤ (chain.reading j).upper :=
  enclosure_lower_monotone (chain.link hij) (chain.reading i) (chain.reading j)

noncomputable def certifiedTwoScale : ScaleChain (1/10 : ℝ) 2 where
  index i := if i.val = 0 then 7 else 30
  reading i := by
    by_cases h : i.val = 0
    · simpa [h] using certifiedWindowNine
    · have hi : i.val = 1 := by omega
      simpa [h, hi] using Imscribing.ABC.Window32E1_10.enclosure
  index_mono := by
    intro i j hij
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · simp [hi, hj]
      · have hj' : j.val = 1 := by omega
        simp [hi, hj']
    · have hi' : i.val = 1 := by omega
      have hj' : j.val = 1 := by omega
      simp [hi', hj']

theorem certifiedTwoScale_cross :
    (certifiedTwoScale.reading ⟨0, by decide⟩).lower ≤
      (certifiedTwoScale.reading ⟨1, by decide⟩).upper :=
  certifiedTwoScale.cross_bound (by decide)

def certifiedTwoScaleWitness :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict
      ((226/1000 : ℝ) ≤ windowMaximum (1/10) 30) :=
  .held (by
    exact certifiedWindowNine.lower_le.trans
      certifiedNineToThirty.maximum_le) certifiedTwoScale_cross

theorem certifiedTwoScaleWitness_is_B :
    certifiedTwoScaleWitness.classify = (true, true) := rfl

end Imscribing.ABC
