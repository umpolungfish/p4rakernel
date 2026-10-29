import Imscribing.ABC_MeasurementCompatibility

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

structure CertifiedMeasurementStream (ε : ℝ) where
  enclosure : ∀ N : ℕ, WindowEnclosure ε N

noncomputable def CertifiedMeasurementStream.measurement
    (stream : CertifiedMeasurementStream ε) (N : ℕ) :
    FiniteMeasurement ε N :=
  FiniteMeasurement.ofEnclosure (stream.enclosure N)

theorem CertifiedMeasurementStream.measurement_readout
    (stream : CertifiedMeasurementStream ε) (N : ℕ) :
    discrepancy ε (stream.measurement N).triple = windowMaximum ε N :=
  (stream.measurement N).attains

noncomputable def CertifiedMeasurementStream.prefix
    (stream : CertifiedMeasurementStream ε) (k : ℕ) :
    MeasurementChain ε k :=
  MeasurementChain.fromScaleChain
    { index := fun i => i.val
      reading := fun i => stream.enclosure i.val
      index_mono := by
        intro i j hij
        exact hij }

theorem CertifiedMeasurementStream.prefix_measurement
    (stream : CertifiedMeasurementStream ε) (k : ℕ) (i : Fin k) :
    ((stream.prefix k).measurement i).enclosure = stream.enclosure i.val := rfl

theorem CertifiedMeasurementStream.prefix_cross_bound
    (stream : CertifiedMeasurementStream ε) (k : ℕ)
    {i j : Fin k} (hij : i ≤ j) :
    (stream.enclosure i.val).lower ≤ (stream.enclosure j.val).upper := by
  exact (stream.prefix k).cross_bound hij

def CertifiedMeasurementStream.witness
    (stream : CertifiedMeasurementStream ε) :
    Verdict (∀ N : ℕ,
      discrepancy ε (stream.measurement N).triple = windowMaximum ε N) :=
  .held stream.measurement_readout
    (fun N => (stream.enclosure N).lower_le)

theorem CertifiedMeasurementStream.witness_is_B
    (stream : CertifiedMeasurementStream ε) :
    stream.witness.classify = (true, true) := by
  simp [CertifiedMeasurementStream.witness, Verdict.classify]

end Imscribing.ABC
