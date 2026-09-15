import Imscribing.IUTT
import Imscribing.Paraconsistent.DialetheicWitness
import Imscribing.Millennium.OPN

/-!
# Odd-perfect-number obstruction readings in the IUTT ambient

The original OPN formalization supplies Euler structure, congruence, factor
count, and lower-bound constraints.  This bridge keeps those declarations
intact and packages the finite obstruction data as a trilattice Witness.
-/
namespace Millennium.OPN

open Imscribing
open Imscribing.Paraconsistent.DialetheicWitness

noncomputable def opnPacket (N : ℕ) : IUTT.Packet :=
  ![(N % 4 : ℝ), 0, ((N.primeFactorsList.toFinset.card : ℕ) : ℝ) / 4]

theorem opn_packet_congruence (N : ℕ) :
    opnPacket N 0 = (N % 4 : ℝ) := rfl

theorem opn_packet_factor_count (N : ℕ) :
    IUTT.weighted (opnPacket N) =
      ((N.primeFactorsList.toFinset.card : ℕ) : ℝ) := by
  norm_num [IUTT.weighted, opnPacket, Fin.sum_univ_succ]
  ring

structure OPNReading (N : ℕ) where
  packet : IUTT.Packet
  state : IUTT.State

noncomputable def opnReading (N : ℕ) : OPNReading N :=
  { packet := opnPacket N, state := IUTT.boundedDiscrepancy }

def opnThetaInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient

def opnThetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id opnThetaInfo id

theorem opnThetaLink_closes :
    opnThetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem opnThetaLink_preserves_reading (N : ℕ) :
    IUTT.transport id opnThetaInfo id (opnReading N).state =
      (opnReading N).state := by
  exact opnThetaLink_closes

def OPNFiniteObstruction (N : ℕ) : Prop :=
  N % 4 = 1 ∧
  9 ≤ N.primeFactorsList.toFinset.card ∧
  (10 : ℕ)^1500 < N

theorem opn_finite_obstruction (N : ℕ) (hN : IsOddPerfect N) :
    OPNFiniteObstruction N := by
  exact ⟨opn_mod_4 N hN, opn_has_many_prime_factors N hN, opn_lower_bound N hN⟩

noncomputable def opnObstructionWitness (N : ℕ)
    (h : OPNFiniteObstruction N) : Verdict (OPNFiniteObstruction N) :=
  Verdict.held h (opn_packet_factor_count N)

theorem opnObstructionWitness_is_B (N : ℕ) (h : OPNFiniteObstruction N) :
    (opnObstructionWitness N h).classify = (true, true) := by
  rfl

theorem opnObstructionWitness_closes (N : ℕ) (h : OPNFiniteObstruction N) :
    (opnObstructionWitness N h).classify = (true, true) ∧
      opnThetaLink (opnReading N).state = IUTT.boundedDiscrepancy := by
  exact ⟨opnObstructionWitness_is_B N h, opnThetaLink_closes⟩

end Millennium.OPN
