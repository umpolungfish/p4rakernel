import Imscribing.IUTT
import Imscribing.Paraconsistent.DialetheicWitness
import Imscribing.Millennium.Hodge

/-!
# Hodge cycle readings in the IUTT ambient

The packet records codimension and its reflected degree observable.  The
Witnesses below use the two established special cases (degree zero and
Lefschetz (1,1)); the universal cycle-class surjectivity statement remains a
separate closure obligation.
-/
namespace Millennium.Hodge

open Imscribing
open Imscribing.Paraconsistent.DialetheicWitness

noncomputable def hodgePacket (p : ℕ) : IUTT.Packet :=
  ![(p : ℝ), 0, (p : ℝ) / 4]

theorem hodge_packet_codimension (p : ℕ) :
    hodgePacket p 0 = (p : ℝ) := rfl

theorem hodge_packet_degree (p : ℕ) :
    IUTT.weighted (hodgePacket p) = (p : ℝ) := by
  norm_num [IUTT.weighted, hodgePacket, Fin.sum_univ_succ]
  ring

structure HodgeReading (X : SmoothProjectiveVariety) (p : ℕ)
    (α : HodgeCohomology X p) where
  packet : IUTT.Packet
  state : IUTT.State

noncomputable def hodgeReading (X : SmoothProjectiveVariety) (p : ℕ)
    (α : HodgeCohomology X p) : HodgeReading X p α :=
  { packet := hodgePacket p, state := IUTT.boundedDiscrepancy }

def hodgeThetaInfo (x : IUTT.State) : IUTT.State := x.union IUTT.ambient

def hodgeThetaLink : IUTT.State → IUTT.State :=
  IUTT.transport id hodgeThetaInfo id

theorem hodgeThetaLink_closes :
    hodgeThetaLink IUTT.boundedDiscrepancy = IUTT.boundedDiscrepancy := by
  decide

theorem hodgeThetaLink_preserves_reading
    (X : SmoothProjectiveVariety) (p : ℕ) (α : HodgeCohomology X p) :
    IUTT.transport id hodgeThetaInfo id (hodgeReading X p α).state =
      (hodgeReading X p α).state := by
  exact hodgeThetaLink_closes

noncomputable def hodgeDegreeZeroWitness
    (X : SmoothProjectiveVariety) (α : HodgeCohomology X 0) :
    Verdict (IsAlgebraicClass X 0 α) :=
  Verdict.held (hodge_degree_zero_axiom X α) (hodge_packet_degree 0)

noncomputable def hodgeLefschetzWitness
    (X : SmoothProjectiveVariety) (α : HodgeCohomology X 1) :
    Verdict (IsAlgebraicClass X 1 α) :=
  Verdict.held (lefschetz_11_axiom X α) (hodge_packet_degree 1)

theorem hodgeDegreeZeroWitness_is_B
    (X : SmoothProjectiveVariety) (α : HodgeCohomology X 0) :
    (hodgeDegreeZeroWitness X α).classify = (true, true) := by
  rfl

theorem hodgeLefschetzWitness_is_B
    (X : SmoothProjectiveVariety) (α : HodgeCohomology X 1) :
    (hodgeLefschetzWitness X α).classify = (true, true) := by
  rfl

theorem hodgeLefschetzWitness_closes
    (X : SmoothProjectiveVariety) (α : HodgeCohomology X 1) :
    (hodgeLefschetzWitness X α).classify = (true, true) ∧
      hodgeThetaLink (hodgeReading X 1 α).state = IUTT.boundedDiscrepancy := by
  exact ⟨hodgeLefschetzWitness_is_B X α, hodgeThetaLink_closes⟩

end Millennium.Hodge
