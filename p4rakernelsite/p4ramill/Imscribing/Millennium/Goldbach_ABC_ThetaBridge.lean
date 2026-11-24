import Imscribing.IUTT
import Imscribing.Paraconsistent.DialetheicWitness
import Imscribing.Millennium.GoldbachABC

/-!
# Goldbach additive readings in the IUTT ambient

The finite verification theorem is treated as a value-level arithmetic
Witness.  The packet records the even target and the circle-method
representation observable; the universal Goldbach statement remains a
separate closure obligation.
-/
namespace Millennium.GoldbachABC

open Imscribing
open Imscribing.Paraconsistent.DialetheicWitness

noncomputable def goldbachPacket (n : ℕ) : IUTT.Packet :=
  ![(n : ℝ), 0, goldbachRepresentations n / 4]

theorem goldbach_packet_target (n : ℕ) :
    goldbachPacket n 0 = (n : ℝ) := rfl

theorem goldbach_packet_representations (n : ℕ) :
    IUTT.weighted (goldbachPacket n) = goldbachRepresentations n := by
  norm_num [IUTT.weighted, goldbachPacket, Fin.sum_univ_succ]
  ring

structure GoldbachReading (n : ℕ) where
  packet : IUTT.Packet
  state : IUTT.State

noncomputable def goldbachReading (n : ℕ) : GoldbachReading n :=
  { packet := goldbachPacket n, state := IUTT.boundedDiscrepancy }

def goldbachThetaInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient

def goldbachThetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id goldbachThetaInfo id

theorem goldbachThetaLink_closes :
    goldbachThetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem goldbachThetaLink_preserves_reading (n : ℕ) :
    IUTT.transport id goldbachThetaInfo id (goldbachReading n).state =
      (goldbachReading n).state := by
  exact goldbachThetaLink_closes

def VerifiedGoldbach (n : ℕ) : Prop :=
  2 < n ∧ n ≤ 4 * 10^18 → Even n →
    ∃ p q : ℕ, Prime p ∧ Prime q ∧ p + q = n

noncomputable def goldbachVerifiedWitness (n : ℕ)
    (h : VerifiedGoldbach n) : Verdict (VerifiedGoldbach n) :=
  Verdict.held h (goldbach_packet_representations n)

theorem goldbachVerifiedWitness_is_B (n : ℕ) (h : VerifiedGoldbach n) :
    (goldbachVerifiedWitness n h).classify = (true, true) := by
  rfl

theorem goldbachVerifiedWitness_closes (n : ℕ) (h : VerifiedGoldbach n) :
    (goldbachVerifiedWitness n h).classify = (true, true) ∧
      goldbachThetaLink (goldbachReading n).state = IUTT.boundedDiscrepancy := by
  exact ⟨goldbachVerifiedWitness_is_B n h, goldbachThetaLink_closes⟩

theorem goldbach_verified_witness_from_source (n : ℕ)
    (hn : 2 < n ∧ n ≤ 4 * 10^18) :
    VerifiedGoldbach n := by
  intro _ heven
  exact goldbach_verified_up_to n hn heven

end Millennium.GoldbachABC
