import Init.Paraconsistent
import Imscribing.MillenniumParaconsistent.ParaconsistentRH
import Imscribing.MillenniumParaconsistent.ParaconsistentYM
import Imscribing.MillenniumParaconsistent.ParaconsistentHodge
import Imscribing.MillenniumParaconsistent.ParaconsistentNS
import Imscribing.MillenniumParaconsistent.ParaconsistentPvsNP
import Imscribing.MillenniumParaconsistent.ParaconsistentBSD
import Imscribing.MillenniumParaconsistent.ParaconsistentOPN

/-!
  ParaconsistentMaster.lean
  Master audit of Belnap-valued dialetheic containment.

  The imported problem-specific modules assign Belnap B to their structural
  barrier predicates. This module proves facts about those assignments and
  the ENGAGR/FSPLIT/FFUSE operation; it does not establish classical solutions
  to the Millennium Prize Problems.
-/

open Paraconsistent
open Paraconsistent.Belnap

namespace Millennium.Paraconsistent.Master

/-- Join in Belnap's information order. -/
def join (a b : Belnap) : Belnap :=
  match a, b with
  | .B, _ | _, .B => .B
  | .N, x | x, .N => x
  | .T, .F | .F, .T => .B
  | .T, .T => .T
  | .F, .F => .F

theorem fundamental_dialetheic_identity :
    band .B (bnot .B) = .B := by decide

theorem fundamental_non_explosion :
    band .B (bnot .B) ≠ .F := by decide

def engager (r : Belnap) : Belnap := band r (bnot r)

def fsplit (r : Belnap) : Belnap × Belnap :=
  match r with
  | .B => (.T, .F)
  | r => (r, r)

def ffuse (r1 r2 : Belnap) : Belnap := join r1 r2

/-- One complete ENGAGR → FSPLIT → FFUSE iteration. -/
def cycle (r : Belnap) : Belnap :=
  ffuse (fsplit (engager r)).1 (fsplit (engager r)).2

theorem frobenius_on_B : cycle .B = .B := by decide

/-- Correct idempotence statement (cycle ∘ cycle = cycle). -/
theorem cycle_idempotent_all (r : Belnap) :
    cycle (cycle r) = cycle r := by
  cases r <;> decide

/-- The cycle is not the identity: in particular T maps to F. -/
theorem cycle_collapses_T : cycle .T = .F := by decide

theorem cycle_all_values :
    cycle .N = .N ∧ cycle .T = .F ∧
    cycle .F = .F ∧ cycle .B = .B := by decide

/-- The six formalized barrier values, plus optional OPN, are B by definition. -/
theorem encoded_barriers_are_B :
    RH.rhValue = .B ∧
    YM.ymExistence = .B ∧
    Hodge.hodgeConjectureValue = .B ∧
    NS.nsRegularity = .B ∧
    PvsNP.pEqualsNP = .B ∧
    BSD.twoAdicBarrier = .B ∧
    OPN.opnExistence = .B := by
  decide

/-- Frobenius cycle fixes each of the encoded barrier values. -/
theorem frobenius_closed_resolution :
    cycle RH.rhValue = RH.rhValue ∧
    cycle YM.ymExistence = YM.ymExistence ∧
    cycle Hodge.hodgeConjectureValue = Hodge.hodgeConjectureValue ∧
    cycle NS.nsRegularity = NS.nsRegularity ∧
    cycle PvsNP.pEqualsNP = PvsNP.pEqualsNP ∧
    cycle BSD.twoAdicBarrier = BSD.twoAdicBarrier ∧
    cycle OPN.opnExistence = OPN.opnExistence := by
  decide

/-- This is a report of the modeled containment, not an external proof claim. -/
def resolutionSummary : String :=
  "The modeled barriers carry Belnap B and are fixed by the " ++
  "ENGAGR/FSPLIT/FFUSE cycle. This certifies the encoded " ++
  "dialetheic containment identities, not the underlying prize conjectures."

end Millennium.Paraconsistent.Master
