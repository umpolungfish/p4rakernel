import Imscribing.IUTT
import Imscribing.Paraconsistent.DialetheicWitness
import Imscribing.Millennium.NS

/-!
# Navier--Stokes critical readings in the IUTT ambient

This bridge records the energy and critical Sobolev observables for one
initial datum.  A supplied finite critical bound becomes a B-valued local
Witness; the universal global regularity assertion remains a separate
closure obligation.
-/
namespace Millennium.NS

open Imscribing
open Imscribing.Paraconsistent.DialetheicWitness

noncomputable def nsPacket (u₀ : NSInitialDatum) : IUTT.Packet :=
  ![initialEnergyNorm u₀, 0, initialCriticalNorm u₀ / 4]

theorem ns_packet_energy (u₀ : NSInitialDatum) :
    nsPacket u₀ 0 = initialEnergyNorm u₀ := rfl

theorem ns_packet_critical (u₀ : NSInitialDatum) :
    IUTT.weighted (nsPacket u₀) = initialCriticalNorm u₀ := by
  norm_num [IUTT.weighted, nsPacket, Fin.sum_univ_succ]
  ring

noncomputable def nsExcess (u₀ : NSInitialDatum) : ℝ :=
  IUTT.weighted (nsPacket u₀) - nsPacket u₀ 0

theorem ns_excess_formula (u₀ : NSInitialDatum) :
    nsExcess u₀ = initialCriticalNorm u₀ - initialEnergyNorm u₀ := by
  simp [nsExcess, ns_packet_critical, ns_packet_energy]

structure NSReading (u₀ : NSInitialDatum) where
  packet : IUTT.Packet
  state : IUTT.State

noncomputable def nsReading (u₀ : NSInitialDatum) : NSReading u₀ :=
  { packet := nsPacket u₀, state := IUTT.boundedDiscrepancy }

def nsThetaInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient

def nsThetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id nsThetaInfo id

theorem nsThetaLink_closes :
    nsThetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem nsThetaLink_preserves_reading (u₀ : NSInitialDatum) :
    IUTT.transport id nsThetaInfo id (nsReading u₀).state =
      (nsReading u₀).state := by
  exact nsThetaLink_closes

def CriticalBound (u₀ : NSInitialDatum) : Prop :=
  ∃ C : ℝ, 0 < C ∧ initialCriticalNorm u₀ ≤ C

noncomputable def nsCriticalWitness (u₀ : NSInitialDatum)
    (h : CriticalBound u₀) : Verdict (CriticalBound u₀) :=
  Verdict.held h (ns_packet_critical u₀)

theorem nsCriticalWitness_is_B (u₀ : NSInitialDatum)
    (h : CriticalBound u₀) :
    (nsCriticalWitness u₀ h).classify = (true, true) := by
  rfl

theorem nsCriticalWitness_closes (u₀ : NSInitialDatum)
    (h : CriticalBound u₀) :
    (nsCriticalWitness u₀ h).classify = (true, true) ∧
      nsThetaLink (nsReading u₀).state = IUTT.boundedDiscrepancy := by
  exact ⟨nsCriticalWitness_is_B u₀ h, nsThetaLink_closes⟩

end Millennium.NS
