import Imscribing.ABC
import Imscribing.IUTT

/-!
# ABC packets through the Θ-link

This module fixes the transport interface used by the executable GPU reader:
the arithmetic packet is carried through IUTT's ternary transport, while the
full trilattice state remains available at the endpoint. The identity action is
the calibrated reference path; nontrivial Θ-links can be supplied later as the
three component maps.
-/
namespace Imscribing.ABC

structure ThetaReading where
  packet : IUTT.Packet
  state : IUTT.State

def thetaTransport (gT gI gF : IUTT.State → IUTT.State)
    (r : ThetaReading) : ThetaReading :=
  { packet := r.packet, state := IUTT.transport gT gI gF r.state }

theorem thetaTransport_preserves_packet
    (gT gI gF : IUTT.State → IUTT.State) (r : ThetaReading) :
    (thetaTransport gT gI gF r).packet = r.packet := rfl

noncomputable def arithmeticThetaReading (t : Triple) : ThetaReading :=
  { packet := arithmeticPacket t, state := IUTT.boundedDiscrepancy }

theorem identity_theta_closes (r : ThetaReading) :
    (thetaTransport id id id r).state = r.state := by
  exact IUTT.identity_transport r.state

theorem arithmetic_theta_calibration (t : Triple) :
    IUTT.weighted (arithmeticThetaReading t).packet = logHeight t := by
  exact packet_height_calibration t

theorem arithmetic_theta_endpoint (t : Triple) :
    (arithmeticThetaReading t).state = IUTT.boundedDiscrepancy := rfl

/-! A concrete horizontal Θ-link: the information branch is saturated with
the ambient lane, while truth and falsity branches pass through unchanged. -/
def thetaLinkInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient
def thetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id thetaLinkInfo id

theorem thetaLink_endpoint :
    thetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem thetaLink_is_not_identity :
    thetaLink IUTT.truth ≠ IUTT.truth := by
  decide

theorem thetaLink_preserves_arithmetic_endpoint (t : Triple) :
    (thetaTransport id thetaLinkInfo id (arithmeticThetaReading t)).state =
      IUTT.boundedDiscrepancy := by
  change thetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy
  exact thetaLink_endpoint

end Imscribing.ABC
