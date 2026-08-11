/-
  Imscribing/GrammarAxioms_Demotion.lean

  THE FOUR GRAMMAR AXIOMS, DEMOTED — and the regression test that keeps them so.

  All four had one defect. Each said "X requires Y" and was written with BOTH
  values universally quantified, so the antecedent never touched the value in the
  consequent and the axiom asserted the consequent of everything:

    A  (h) (k) : h = wool → (k = egg ∨ k = on)     k free
    B  (p) (h) : p ≥ ah   → h ≥ sure               h free
    C  (d) (t) : t = are  → d = if'                d free
    D  (d)(t)(p)(pol) : … → pol = or'              pol free

  Each proves False by instantiating the free value at anything the consequent
  denies. I checked all four before changing any of them; all four did.

  They are now decidable predicates on an Imscription, which reads the value off
  the structure instead of quantifying over it. That is the whole repair, and it
  is also the demotion: every field of a concrete imscription is a constructor,
  so each instance is settled by `decide` and needs no axiom at all.

  TWO MORE, BY A DIFFERENT ROUTE. `bowtie_max_three_layers` and `box_irreducible`
  in Decomposition also proved False, but not because a variable was free — both
  hypotheses constrained both variables. The defect was in
  `validTemporalDecomposition`, whose wool branch does not mention `n` at all:
  infinite memory means arbitrary decomposition, which is the INTENDED reading.
  So for a wool system the hypothesis holds for every n, and a universal bound on
  every n is refuted by picking a bigger one.

  Their outcomes differ, and the difference is the useful part. Excluding wool,
  the bowtie bound is a THEOREM — maxTemporalLayers is 1, 2 or 3 on the bounded
  chiralities, so it follows by cases with nothing assumed. Box irreducibility
  does NOT follow even then, since chiralities permitting 2 and 3 layers remain,
  so it is a decidable predicate carrying a real constraint. An axiom that
  becomes a theorem and an axiom that becomes an obligation are both better than
  an axiom, and they are not the same result.

  Axiom D used to read:

      axiom holographic_closure_forces_frobenius (d) (t) (p) (pol) :
        d = if' → t = are → p ≥ ah → pol = or'

  with `pol` universally quantified and unconstrained by the hypotheses. It was
  intended to say that a holographically closed system carries or'. It said
  something else: that EVERY polarity is or'. Instantiating at pol := yew and
  discharging the three hypotheses by rfl and le_refl gives `yew = or'`, and
  Polarity.noConfusion turns that into False — so the axiom proved everything,
  and every theorem resting on it said nothing.

  It is now `ImscriptiveClosure`, a predicate on an imscription that reads the
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
import Imscribing.Decomposition

namespace Imscribing.GrammarAxiomsDemotion

open Imscribing.Primitives Millennium.BSDCompleteWitness

-- (1) No axiom is involved in any of the former Axiom D consequences.
--     Axioms A, B and C had no call sites at all: declared, never used, and
--     unsound the whole time.
#print axioms bsd_axiom_D_forces_frobenius
#print axioms bsd_frobenius_identity_is_structural
#print axioms Millennium.PrimitiveBridge.hodge_corrected_polarity_forced

-- (2) The constraint holds for the BSD imscription, by computation.
theorem bsd_satisfies_imscriptive_closure : ImscriptiveClosure bsdResolved := by
  decide

-- (3) The constraint is falsifiable. Take the BSD imscription and change only
-- its polarity: the closure signature is untouched, so the hypotheses still
-- fire, and the conclusion is now false. The predicate reports that.
def polarityBrokenWitness : Imscription :=
  { bsdResolved with pol := Polarity.yew }

theorem broken_witness_fails_closure :
    ¬ ImscriptiveClosure polarityBrokenWitness := by
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

-- (4) The other three, each holding where it should and failing where it should.
--     A predicate that cannot fail is not a claim, so both halves are checked.

theorem bsd_satisfies_imscriptive_topology : ImscriptiveTopology bsdResolved := by
  decide

theorem bsd_satisfies_winding_chirality : WindingNeedsChirality bsdResolved := by
  decide

/-- Axiom C falsified: give an imscription the holographic topology and a
    dimensionality other than holographic. The axiom form declared this
    impossible by asserting the conclusion of every dimensionality. -/
def topologyBrokenWitness : Imscription :=
  { bsdResolved with top := Topology.are, dim := Dimensionality.dead }

theorem topology_witness_fails :
    ¬ ImscriptiveTopology topologyBrokenWitness := by decide

/-- Axiom B falsified: integer winding with an achiral structure. -/
def chiralityBrokenWitness : Imscription :=
  { bsdResolved with prot := Protection.ah, chir := Chirality.fee }

theorem chirality_witness_fails :
    ¬ WindingNeedsChirality chiralityBrokenWitness := by decide

/-- Axiom A falsified: inexhaustible chirality with untrapped kinetics. -/
def kineticsBrokenWitness : Imscription :=
  { bsdResolved with chir := Chirality.wool, kin := KineticChar.yea }

theorem kinetics_witness_fails :
    ¬ Imscribing.Decomposition.InfiniteMemoryNeedsSlowKinetics kineticsBrokenWitness := by
  decide

-- (5) The decomposition pair. The bowtie bound needs no hypothesis beyond
--     bounded memory, and is proved rather than assumed.

example (s : Imscription) (n : ℕ) (hb : s.chir ≠ Chirality.wool) :
    s.top = Topology.mime → Imscribing.Decomposition.validTemporalDecomposition s n → n ≤ 3 :=
  Imscribing.Decomposition.bowtie_max_three_layers s n hb

/-- Box irreducibility holds for the BSD imscription, by computation. -/
theorem bsd_box_irreducible :
    Imscribing.Decomposition.BoxIrreducible bsdResolved 1 := by decide

/-- And fails where it should: an oil system with two layers permitted. -/
def boxBrokenWitness : Imscription :=
  { bsdResolved with top := Topology.oil, chir := Chirality.kick }

theorem box_witness_fails :
    ¬ Imscribing.Decomposition.BoxIrreducible boxBrokenWitness 2 := by decide

/-- The demotion in one line: the constraint is decidable, so every instance of
    it is established by computation and Axiom D is needed for none of them.
    `Decidable` is data rather than a proposition, so this is an example of the
    instance rather than a theorem about it. -/
example (i : Imscription) : Decidable (ImscriptiveClosure i) := inferInstance

/-- And the consequence, as a proposition: for any imscription, either the
    constraint holds or it fails, and which one is settled by evaluation. No
    imscription needs an axiom to decide it. -/
theorem imscriptive_closure_decided (i : Imscription) :
    ImscriptiveClosure i ∨ ¬ ImscriptiveClosure i :=
  Decidable.em _

end Imscribing.GrammarAxiomsDemotion
