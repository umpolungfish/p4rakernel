import Imscribing.ABC_TailRegime

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

/-! The arithmetic tail and the IUTT packet are one typed reading. -/

structure IUTTTailReading (ε : ℝ) (r : TailRegime ε) (N : ℕ) where
  triple : Triple
  member : triple ∈ arithmeticWindow N
  attains : discrepancy ε triple = r.read N

noncomputable def IUTTTailReading.select (ε : ℝ) (r : TailRegime ε) (N : ℕ) :
    IUTTTailReading ε r N :=
  let h := r.finite_attained N
  ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

noncomputable def IUTTTailReading.packet
    (reading : IUTTTailReading ε r N) : IUTT.Packet :=
  arithmeticPacket reading.triple

theorem IUTTTailReading.packet_radical
    (reading : IUTTTailReading ε r N) :
    reading.packet 0 = logRadical reading.triple :=
  packet_radical_calibration reading.triple

theorem IUTTTailReading.packet_height
    (reading : IUTTTailReading ε r N) :
    IUTT.weighted reading.packet = logHeight reading.triple :=
  packet_height_calibration reading.triple

theorem IUTTTailReading.readout
    (reading : IUTTTailReading ε r N) :
    discrepancy ε reading.triple = r.read N :=
  reading.attains

structure IUTTTailClosure (ε : ℝ) where
  regime : TailRegime ε
  reading : ∀ N : ℕ, IUTTTailReading ε regime N
  packet_is_arithmetic : ∀ N, (reading N).packet =
    arithmeticPacket (reading N).triple
  packet_height_is_log : ∀ N,
    IUTT.weighted (reading N).packet = logHeight (reading N).triple
  packet_radical_is_log : ∀ N,
    (reading N).packet 0 = logRadical (reading N).triple

noncomputable def exactIUTTTailClosure (ε : ℝ) : IUTTTailClosure ε where
  regime := exactTailRegime ε
  reading := fun N => IUTTTailReading.select ε (exactTailRegime ε) N
  packet_is_arithmetic := fun _ => rfl
  packet_height_is_log := fun N =>
    packet_height_calibration ((IUTTTailReading.select ε (exactTailRegime ε) N).triple)
  packet_radical_is_log := fun N =>
    packet_radical_calibration ((IUTTTailReading.select ε (exactTailRegime ε) N).triple)

theorem exactIUTTTailClosure_readout (ε : ℝ) (N : ℕ) :
    discrepancy ε ((exactIUTTTailClosure ε).reading N).triple =
      (exactIUTTTailClosure ε).regime.read N :=
  (exactIUTTTailClosure ε).reading N |>.readout

def iuttTailClosureWitness (ε : ℝ) :
    Verdict (∀ N : ℕ, ∃ t ∈ arithmeticWindow N,
      discrepancy ε t = (exactIUTTTailClosure ε).regime.read N) :=
  .held (fun N =>
    ⟨((exactIUTTTailClosure ε).reading N).triple,
      ((exactIUTTTailClosure ε).reading N).member,
      ((exactIUTTTailClosure ε).reading N).attains⟩)
    (exactIUTTTailClosure ε).regime.cofinal

theorem iuttTailClosureWitness_is_B (ε : ℝ) :
    (iuttTailClosureWitness ε).classify = (true, true) := by
  simp [iuttTailClosureWitness, Verdict.classify]

end Imscribing.ABC
