import Imscribing.ABC_MeasurementChain
import Imscribing.ABC_IUTTAsymptotic

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

theorem MeasurementChain.lower_le_limit
    {ε : ℝ} {k : ℕ} (chain : MeasurementChain ε k)
    (reading : IUTTAsymptoticReading ε) (i : Fin k) :
    (chain.measurement i).enclosure.lower ≤ reading.limit := by
  rw [chain.enclosure_consistent]
  exact (chain.scales.reading i).lower_le.trans
    (reading.maximum_le_limit (chain.scales.index i))

theorem MeasurementChain.triple_le_limit
    {ε : ℝ} {k : ℕ} (chain : MeasurementChain ε k)
    (reading : IUTTAsymptoticReading ε) (i : Fin k) :
    discrepancy ε (chain.measurement i).triple ≤ reading.limit := by
  exact reading.triple_below_limit (chain.measurement i).triple

theorem MeasurementChain.packet_calibrated
    {ε : ℝ} {k : ℕ} (chain : MeasurementChain ε k) (i : Fin k) :
    IUTT.weighted (chain.measurement i).packet =
      logHeight (chain.measurement i).triple ∧
    (chain.measurement i).packet 0 =
      logRadical (chain.measurement i).triple :=
  ⟨(chain.measurement i).packet_height,
    (chain.measurement i).packet_radical⟩

def MeasurementChain.compatibilityWitness
    {ε : ℝ} {k : ℕ} (chain : MeasurementChain ε k)
    (reading : IUTTAsymptoticReading ε) :
    Verdict (∀ i : Fin k,
      (chain.measurement i).enclosure.lower ≤ reading.limit) :=
  .held (fun i => chain.lower_le_limit reading i)
    (fun i => chain.triple_le_limit reading i)

theorem MeasurementChain.compatibilityWitness_is_B
    {ε : ℝ} {k : ℕ} (chain : MeasurementChain ε k)
    (reading : IUTTAsymptoticReading ε) :
    (chain.compatibilityWitness reading).classify = (true, true) := by
  simp [MeasurementChain.compatibilityWitness, Verdict.classify]

end Imscribing.ABC
