import Imscribing.ABC_Measurement

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

structure MeasurementChain (ε : ℝ) (k : ℕ) where
  scales : ScaleChain ε k
  measurement : ∀ i : Fin k, FiniteMeasurement ε (scales.index i)
  enclosure_consistent : ∀ i, (measurement i).enclosure = scales.reading i

noncomputable def MeasurementChain.fromScaleChain
    (scales : ScaleChain ε k) : MeasurementChain ε k where
  scales := scales
  measurement := fun i => FiniteMeasurement.ofEnclosure (scales.reading i)
  enclosure_consistent := fun _ => rfl

theorem MeasurementChain.link {ε : ℝ} {k : ℕ}
    (chain : MeasurementChain ε k) {i j : Fin k} (hij : i ≤ j) :
    ScaleLink ε (chain.scales.index i) (chain.scales.index j) :=
  chain.scales.link hij

theorem MeasurementChain.cross_bound {ε : ℝ} {k : ℕ}
    (chain : MeasurementChain ε k) {i j : Fin k} (hij : i ≤ j) :
    (chain.measurement i).enclosure.lower ≤
      (chain.measurement j).enclosure.upper := by
  rw [chain.enclosure_consistent, chain.enclosure_consistent]
  exact chain.scales.cross_bound hij

def MeasurementChain.witness {ε : ℝ} {k : ℕ}
    (chain : MeasurementChain ε k) :
    Verdict (∀ i : Fin k,
      discrepancy ε (chain.measurement i).triple =
        windowMaximum ε (chain.scales.index i)) :=
  .held (fun i => (chain.measurement i).attains)
    (fun i => chain.enclosure_consistent i)

theorem MeasurementChain.witness_is_B {ε : ℝ} {k : ℕ}
    (chain : MeasurementChain ε k) :
    chain.witness.classify = (true, true) := by
  simp [MeasurementChain.witness, Verdict.classify]

noncomputable def certifiedMeasurementChain :
    MeasurementChain (1/10 : ℝ) 2 :=
  MeasurementChain.fromScaleChain certifiedTwoScale

theorem certifiedMeasurementChain_cross :
    (certifiedMeasurementChain.measurement ⟨0, by decide⟩).enclosure.lower ≤
      (certifiedMeasurementChain.measurement ⟨1, by decide⟩).enclosure.upper :=
  certifiedMeasurementChain.cross_bound (by decide)

theorem certifiedMeasurementChain_witness_is_B :
    certifiedMeasurementChain.witness.classify = (true, true) := by
  simp [MeasurementChain.witness, Verdict.classify]

end Imscribing.ABC
