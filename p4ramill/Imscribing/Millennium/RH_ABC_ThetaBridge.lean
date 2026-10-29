import Imscribing.IUTT
import Imscribing.Paraconsistent.DialetheicWitness
import Imscribing.Millennium.RH

/-!
# RH symmetry readings in the IUTT ambient

This bridge records the functional-equation reflection itself.  A critical
zero supplies the native complex datum; a supplied critical-line reading is
held together with the reflection law in a B-valued Witness.  The universal
zero-location assertion is deliberately not manufactured by this packet.
-/
namespace Millennium.RH

open Imscribing
open Imscribing.Paraconsistent.DialetheicWitness

noncomputable def rhPacket (s : ℂ) : IUTT.Packet :=
  ![s.re, 0, (1 - s).re / 4]

theorem rh_packet_source (s : ℂ) : rhPacket s 0 = s.re := rfl

theorem rh_packet_reflection (s : ℂ) :
    IUTT.weighted (rhPacket s) = (1 - s).re := by
  norm_num [IUTT.weighted, rhPacket, Fin.sum_univ_succ]
  ring

structure RHReading (s : ℂ) where
  packet : IUTT.Packet
  state : IUTT.State

noncomputable def rhReading (s : ℂ) : RHReading s :=
  { packet := rhPacket s, state := IUTT.boundedDiscrepancy }

def rhThetaInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient

def rhThetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id rhThetaInfo id

theorem rhThetaLink_closes :
    rhThetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem rhThetaLink_preserves_reading (s : ℂ) :
    IUTT.transport id rhThetaInfo id (rhReading s).state =
      (rhReading s).state := by
  exact rhThetaLink_closes

def CriticalLineReading (s : ℂ) : Prop := s.re = 1 / 2

noncomputable def rhSymmetryWitness (s : ℂ)
    (h : CriticalLineReading s) : Verdict (CriticalLineReading s) :=
  Verdict.held h (critical_line_symmetric s)

theorem rhSymmetryWitness_is_B (s : ℂ) (h : CriticalLineReading s) :
    (rhSymmetryWitness s h).classify = (true, true) := by
  rfl

theorem rhSymmetryWitness_closes (s : ℂ) (h : CriticalLineReading s) :
    (rhSymmetryWitness s h).classify = (true, true) ∧
      rhThetaLink (rhReading s).state = IUTT.boundedDiscrepancy := by
  exact ⟨rhSymmetryWitness_is_B s h, rhThetaLink_closes⟩

end Millennium.RH
