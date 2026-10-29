-- FourClaimsSameClosure.lean
-- Four unrelated concepts, imscribed separately, close on the identical
-- Imscription.
--
-- KastrupConformalGroup, GlattfelderSelfContainmentPrinciple,
-- IUTClosedWalkAtOInfinity, and ScholzeStixBooleanProjectionAtO2 were
-- auto-designed from four different prompts about four different subjects
-- -- a symmetry group, an information-theoretic principle, a number-
-- theoretic proof technique, and a logical objection to it. Read directly
-- off each file's own definition, not copied literals trusted to agree,
-- their closing states are the same term.

import Imscribing.Ob3ects.GateCheck.kastrupconformalgroup_gate_check
import Imscribing.Ob3ects.GateCheck.glattfelderselfcontainmentprinciple_gate_check
import Imscribing.Ob3ects.GateCheck.iutclosedwalkatoinfinity_gate_check
import Imscribing.Ob3ects.GateCheck.scholzestixbooleanprojectionato2_gate_check

namespace Imscribing

/-- The four gate-checks in this directory close on the literal same
    Imscription, checked against each file's own definition directly. -/
theorem all_four_close_on_the_same_state :
    kastrupconformalgroup_s13 = glattfelderselfcontainmentprinciple_s14 ∧
    glattfelderselfcontainmentprinciple_s14 = iutclosedwalkatoinfinity_s14 ∧
    iutclosedwalkatoinfinity_s14 = scholzestixbooleanprojectionato2_s12 :=
  ⟨rfl, rfl, rfl⟩

/-- Because the four states are the same term, they necessarily share a
    tier -- not by coincidence of four separate `by decide` calls landing
    on the same value, but because they are one value computed once. -/
theorem all_four_share_one_tier :
    TierFunctor.obj kastrupconformalgroup_s13 = TierFunctor.obj glattfelderselfcontainmentprinciple_s14 ∧
    TierFunctor.obj glattfelderselfcontainmentprinciple_s14 = TierFunctor.obj iutclosedwalkatoinfinity_s14 ∧
    TierFunctor.obj iutclosedwalkatoinfinity_s14 = TierFunctor.obj scholzestixbooleanprojectionato2_s12 := by
  obtain ⟨h1, h2, h3⟩ := all_four_close_on_the_same_state
  exact ⟨congrArg TierFunctor.obj h1, congrArg TierFunctor.obj h2, congrArg TierFunctor.obj h3⟩

/-- Named precisely: that shared tier is O₂dag, checked directly. -/
theorem all_four_close_at_O2dag :
    TierFunctor.obj kastrupconformalgroup_s13 = .O₂dag := by decide

end Imscribing
