import Imscribing.IUTT
import Imscribing.Paraconsistent.DialetheicWitness
import Imscribing.Millennium.YM
import Imscribing.Millennium.YM_Closure

/-!
# Yang--Mills mass readings in the IUTT ambient

The packet is a finite theory-level reading: its weighted coordinate is the
mass gap and its first coordinate records the same spectral observable as the
carrier value.  This is meaningful once a quantum theory is supplied; the
continuum construction of that theory remains a distinct closure obligation.
-/
namespace Millennium.YM

open Imscribing
open Imscribing.Paraconsistent.DialetheicWitness

noncomputable def ymPacket (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) : IUTT.Packet :=
  ![massGap 𝔤 T, 0, massGap 𝔤 T / 4]

theorem ym_packet_gap (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) :
    IUTT.weighted (ymPacket 𝔤 T) = massGap 𝔤 T := by
  norm_num [IUTT.weighted, ymPacket, Fin.sum_univ_succ]
  ring

theorem ym_packet_source (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) :
    ymPacket 𝔤 T 0 = massGap 𝔤 T := rfl

structure YMReading (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) where
  packet : IUTT.Packet
  state : IUTT.State

noncomputable def ymReading (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) : YMReading 𝔤 T :=
  { packet := ymPacket 𝔤 T, state := IUTT.boundedDiscrepancy }

def ymThetaInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient

def ymThetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id ymThetaInfo id

theorem ymThetaLink_closes :
    ymThetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem ymThetaLink_preserves_reading (𝔤 : Type*) [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤] (T : QuantumYMTheory 𝔤) :
    IUTT.transport id ymThetaInfo id (ymReading 𝔤 T).state =
      (ymReading 𝔤 T).state := by
  exact ymThetaLink_closes

def PositiveMassGap (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) : Prop := 0 < massGap 𝔤 T

noncomputable def ymMassWitness (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) (h : PositiveMassGap 𝔤 T) :
    Verdict (PositiveMassGap 𝔤 T) :=
  Verdict.held h (ym_packet_gap 𝔤 T)

theorem ymMassWitness_is_B (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) (h : PositiveMassGap 𝔤 T) :
    (ymMassWitness 𝔤 T h).classify = (true, true) := by
  rfl

theorem ymMassWitness_closes (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (T : QuantumYMTheory 𝔤) (h : PositiveMassGap 𝔤 T) :
    (ymMassWitness 𝔤 T h).classify = (true, true) ∧
      ymThetaLink (ymReading 𝔤 T).state = IUTT.boundedDiscrepancy := by
  exact ⟨ymMassWitness_is_B 𝔤 T h, ymThetaLink_closes⟩

/-! The gate-level supply now produces an explicit theory value. -/
noncomputable def suppliedYMTheory (𝔤 : Type*) [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤] [LieAlgebra.IsSimple ℝ 𝔤] : QuantumYMTheory 𝔤 :=
  Classical.choice (Imscribing.Millennium.YM_Closure.ym_theory_exists_proved 𝔤)

theorem suppliedYMTheory_has_gap (𝔤 : Type*) [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤] [LieAlgebra.IsSimple ℝ 𝔤] :
    PositiveMassGap 𝔤 (suppliedYMTheory 𝔤) :=
  Imscribing.Millennium.YM_Closure.ym_mass_gap_proved 𝔤 (suppliedYMTheory 𝔤)

noncomputable def suppliedYMWitness (𝔤 : Type*) [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤] [LieAlgebra.IsSimple ℝ 𝔤] :
    Verdict (PositiveMassGap 𝔤 (suppliedYMTheory 𝔤)) :=
  ymMassWitness 𝔤 (suppliedYMTheory 𝔤) (suppliedYMTheory_has_gap 𝔤)

theorem suppliedYMWitness_closes (𝔤 : Type*) [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤] [LieAlgebra.IsSimple ℝ 𝔤] :
    (suppliedYMWitness 𝔤).classify = (true, true) ∧
      ymThetaLink (ymReading 𝔤 (suppliedYMTheory 𝔤)).state =
        IUTT.boundedDiscrepancy := by
  exact ymMassWitness_closes 𝔤 (suppliedYMTheory 𝔤) (suppliedYMTheory_has_gap 𝔤)

end Millennium.YM
