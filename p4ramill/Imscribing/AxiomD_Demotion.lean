/-
  Imscribing/AxiomD_Demotion.lean

  AXIOM D, DEMOTED — and the regression test that keeps it demoted.

  Axiom D used to read:

      axiom holographic_closure_forces_frobenius (d) (t) (p) (pol) :
        d = if' → t = are → p ≥ ah → pol = or'

  with `pol` universally quantified and unconstrained by the hypotheses. It was
  intended to say that a holographically closed system carries or'. It said
  something else: that EVERY polarity is or'. Instantiating at pol := yew and
  discharging the three hypotheses by rfl and le_refl gives `yew = or'`, and
  Polarity.noConfusion turns that into False — so the axiom proved everything,
  and every theorem resting on it said nothing.

  It is now `HolographicClosure`, a predicate on an imscription that reads the
  polarity off the structure instead of quantifying over it. Every field of a
  concrete imscription is a constructor, so the predicate is decidable: what
  needed an axiom now needs no axiom at all, only computation.

  This file is the guard. It checks three things:
    (1) the theorems that used to invoke Axiom D now depend on no axiom;
    (2) the predicate HOLDS where it should;
    (3) the predicate FAILS where it should — which is what makes it a claim
        rather than a tautology, and is precisely what the axiom form could not
        express.
-/

import Imscribing.Millennium.BSD_Complete_Witness
import Imscribing.Millennium.PrimitiveBridge

namespace Imscribing.AxiomDDemotion

open Imscribing.Primitives Millennium.BSDCompleteWitness

-- (1) No axiom is involved in any of the former Axiom D consequences.
#print axioms bsd_axiom_D_forces_frobenius
#print axioms bsd_frobenius_identity_is_structural
#print axioms Millennium.PrimitiveBridge.hodge_corrected_polarity_forced

-- (2) The constraint holds for the BSD imscription, by computation.
theorem bsd_satisfies_holographic_closure : HolographicClosure bsdResolved := by
  decide

-- (3) The constraint is falsifiable. Take the BSD imscription and change only
-- its polarity: the closure signature is untouched, so the hypotheses still
-- fire, and the conclusion is now false. The predicate reports that.
def polarityBrokenWitness : Imscription :=
  { bsdResolved with pol := Polarity.yew }

theorem broken_witness_fails_closure :
    ¬ HolographicClosure polarityBrokenWitness := by
  decide

-- The signature really is intact in the counterexample — it is the polarity
-- alone that breaks it, so this is a test of the conclusion and not of the
-- hypotheses.
theorem broken_witness_keeps_the_signature :
    polarityBrokenWitness.dim = Dimensionality.if' ∧
    polarityBrokenWitness.top = Topology.are ∧
    polarityBrokenWitness.prot ≥ Protection.ah := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The demotion in one line: the constraint is decidable, so every instance of
    it is established by computation and Axiom D is needed for none of them.
    `Decidable` is data rather than a proposition, so this is an example of the
    instance rather than a theorem about it. -/
example (i : Imscription) : Decidable (HolographicClosure i) := inferInstance

/-- And the consequence, as a proposition: for any imscription, either the
    constraint holds or it fails, and which one is settled by evaluation. No
    imscription needs an axiom to decide it. -/
theorem holographic_closure_decided (i : Imscription) :
    HolographicClosure i ∨ ¬ HolographicClosure i :=
  Decidable.em _

end Imscribing.AxiomDDemotion
