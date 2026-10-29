import Imscribing.ABC_IUTTClosure
import Imscribing.ABC_Certificates

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

structure FiniteMeasurement (ε : ℝ) (N : ℕ) where
  enclosure : WindowEnclosure ε N
  triple : Triple
  member : triple ∈ arithmeticWindow N
  attains : discrepancy ε triple = windowMaximum ε N

noncomputable def FiniteMeasurement.ofEnclosure
    (e : WindowEnclosure ε N) : FiniteMeasurement ε N := by
  let h := windowMaximum_attained ε N
  exact ⟨e, Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

noncomputable def FiniteMeasurement.packet
    (m : FiniteMeasurement ε N) : IUTT.Packet := arithmeticPacket m.triple

theorem FiniteMeasurement.packet_height (m : FiniteMeasurement ε N) :
    IUTT.weighted m.packet = logHeight m.triple :=
  packet_height_calibration m.triple

theorem FiniteMeasurement.packet_radical (m : FiniteMeasurement ε N) :
    m.packet 0 = logRadical m.triple :=
  packet_radical_calibration m.triple

theorem FiniteMeasurement.readout (m : FiniteMeasurement ε N) :
    discrepancy ε m.triple = windowMaximum ε N := m.attains

def FiniteMeasurement.witness (m : FiniteMeasurement ε N) :
    Verdict (m.enclosure.lower ≤ discrepancy ε m.triple) :=
  .held (m.enclosure.lower_le.trans m.attains.symm.le) m.enclosure.le_upper

theorem FiniteMeasurement.witness_is_B (m : FiniteMeasurement ε N) :
    m.witness.classify = (true, true) := rfl

noncomputable def certifiedMeasurementNine :
    FiniteMeasurement (1/10 : ℝ) 7 :=
  FiniteMeasurement.ofEnclosure certifiedWindowNine

noncomputable def certifiedMeasurementThirty :
    FiniteMeasurement (1/10 : ℝ) 30 :=
  FiniteMeasurement.ofEnclosure Window32E1_10.enclosure

theorem certifiedMeasurementNine_readout :
    discrepancy (1/10 : ℝ) certifiedMeasurementNine.triple =
      windowMaximum (1/10 : ℝ) 7 := certifiedMeasurementNine.attains

theorem certifiedMeasurementThirty_readout :
    discrepancy (1/10 : ℝ) certifiedMeasurementThirty.triple =
      windowMaximum (1/10 : ℝ) 30 := certifiedMeasurementThirty.attains

end Imscribing.ABC
