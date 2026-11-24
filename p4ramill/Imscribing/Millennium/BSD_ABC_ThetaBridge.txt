import Imscribing.IUTT
import Imscribing.Paraconsistent.DialetheicWitness
import Imscribing.Millennium.BSD

/-!
# BSD rank readings in the IUTT ambient

The packet below is a calibrated value-level reading of the two BSD rank
observables.  Its weighted coordinate is the analytic rank and its first
coordinate is the Mordell--Weil rank.  The rank-one theorem therefore gives a
genuine finite Witness; no universal BSD claim is smuggled into the packet.
-/
namespace Millennium.BSD

open Imscribing
open Imscribing.Paraconsistent.DialetheicWitness

noncomputable def bsdPacket (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    IUTT.Packet :=
  ![(ellipticRank W : ℝ), 0, (analyticRank W : ℝ) / 4]

theorem bsd_packet_rank (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    bsdPacket W 0 = (ellipticRank W : ℝ) := rfl

theorem bsd_packet_analytic (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    IUTT.weighted (bsdPacket W) = (analyticRank W : ℝ) := by
  norm_num [IUTT.weighted, bsdPacket, Fin.sum_univ_succ]
  ring

noncomputable def bsdDiscrepancy (W : WeierstrassCurve ℚ) [W.IsElliptic] : ℝ :=
  IUTT.weighted (bsdPacket W) - bsdPacket W 0

theorem bsd_discrepancy_formula (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    bsdDiscrepancy W = (analyticRank W : ℝ) - (ellipticRank W : ℝ) := by
  simp [bsdDiscrepancy, bsd_packet_analytic, bsd_packet_rank]

structure BSDReading (W : WeierstrassCurve ℚ) [W.IsElliptic] where
  packet : IUTT.Packet
  state : IUTT.State

noncomputable def bsdReading (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    BSDReading W :=
  { packet := bsdPacket W, state := IUTT.boundedDiscrepancy }

theorem bsd_reading_endpoint (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    (bsdReading W).state = IUTT.boundedDiscrepancy := rfl

def bsdThetaInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient

def bsdThetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id bsdThetaInfo id

theorem bsdThetaLink_closes :
    bsdThetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem bsdThetaLink_preserves_reading (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    IUTT.transport id bsdThetaInfo id (bsdReading W).state =
      (bsdReading W).state := by
  exact bsdThetaLink_closes

def BSDRankReading (W : WeierstrassCurve ℚ) [W.IsElliptic] : Prop :=
  ellipticRank W = analyticRank W

noncomputable def bsdRankWitness (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (h : analyticRank W ≤ 1) : Verdict (BSDRankReading W) :=
  Verdict.held (bsd_rank_at_most_one W h) (bsd_packet_analytic W)

theorem bsdRankWitness_is_B (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (h : analyticRank W ≤ 1) :
    (bsdRankWitness W h).classify = (true, true) := by
  rfl

theorem bsdRankWitness_closes (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (h : analyticRank W ≤ 1) :
    (bsdRankWitness W h).classify = (true, true) ∧
      bsdThetaLink (bsdReading W).state = IUTT.boundedDiscrepancy := by
  exact ⟨bsdRankWitness_is_B W h, bsdThetaLink_closes⟩

end Millennium.BSD
