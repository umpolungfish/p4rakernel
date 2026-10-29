import Imscribing.Paraconsistent.TemporalSemantics

open Imscribing.Paraconsistent.Temporal.Semantics

#print axioms FDE.negationClosure_fixed
#print axioms FDE.negationClosure_idempotent
#print axioms FDE.negationClosure_extensive
#print axioms FDE.negationClosure_monotone
#print axioms FDE.negationClosure_le_iff
#print axioms FDE.negationSeededStep_closure_fixed
#print axioms FDE.negationSeededStep_fixed_iff
#print axioms FDE.negationSeededStep_least
#print axioms NegationSignals.orbit_period_two
#print axioms NegationSignals.adjacent_ticks_hold_closure
#print axioms NegationSignals.seededFeedback_settled
#print axioms KernelReentry.truthNegationReentry_is_closure
#print axioms KernelReentry.unknownNegationReentry_is_closure
#print axioms KernelReentry.dialetheicNegationReentry_is_closure

-- A T seed alternates in the raw trace and settles under retained-seed feedback.
#eval (List.range 5).map (NegationSignals.orbit (FDE.singleton .T))
#eval (List.range 5).map (NegationSignals.seededFeedback (FDE.singleton .T))

-- Native declarations exercise the T, N, and B seeds through the kernel solver.
#eval KernelReentry.truthNegationReentry
#eval KernelReentry.unknownNegationReentry
#eval KernelReentry.dialetheicNegationReentry

example : NegationSignals.orbit (FDE.singleton .T) 0 ≠
    NegationSignals.orbit (FDE.singleton .T) 1 := by decide

-- Separate T/F membership and singleton B remain distinct, incomparable sets.
example : KernelReentry.truthNegationReentry ≠
    KernelReentry.dialetheicNegationReentry := by decide

example : Lean.Sixteen3.le_i KernelReentry.truthNegationReentry
      KernelReentry.dialetheicNegationReentry = false ∧
    Lean.Sixteen3.le_i KernelReentry.dialetheicNegationReentry
      KernelReentry.truthNegationReentry = false := by decide
