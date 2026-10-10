import Imscribing.Paraconsistent.CombinatoryReentry

open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.Temporal.Semantics

local infixl:70 " @@ " => Term.app

#print axioms abstract_apply
#print axioms duplicate_apply
#print axioms SKK_identity
#print axioms Y_fixedpoint
#print axioms Y_constant
#print axioms hold_apply
#print axioms seededOperator_apply
#print axioms run_reduces
#print axioms run_add
#print axioms executionSignal_tick

-- Open terms participate in combinator reduction without a closedness condition.
example : run 2 (.s @@ .k @@ .k @@ .var 37) = .var 37 := by decide
example : run 3 (duplicate @@ .var 37) = .var 37 @@ .var 37 := by decide
example : Conversion (Y @@ .var 37) (.var 37 @@ (Y @@ .var 37)) :=
  Y_fixedpoint (.var 37)

-- Holding T computes the native T/F re-entry value in three contractions.
#eval (List.range 5).map (executionSignal (hold @@ .datum (FDE.singleton .T)))
example : run 3 (hold @@ .datum (FDE.singleton .T)) =
    .datum KernelReentry.truthNegationReentry := by decide
example : run 3 (hold @@ .datum (FDE.singleton .N)) =
    .datum KernelReentry.unknownNegationReentry := by decide
example : run 3 (hold @@ .datum (FDE.singleton .B)) =
    .datum KernelReentry.dialetheicNegationReentry := by decide

-- Every native membership pattern is a concrete compiler/reducer control.
private def carrier : List Lean.Sixteen3 := do
  let n ← [false, true]
  let t ← [false, true]
  let f ← [false, true]
  let b ← [false, true]
  pure ⟨n, t, f, b⟩

example : carrier.length = 16 := by decide
example : carrier.all (fun x =>
    run 3 (hold @@ .datum x) == .datum (FDE.negationClosure x)) = true := by decide
example : carrier.all (fun seed => carrier.all (fun x =>
    run 32 (seededOperator seed @@ .datum x) ==
      .datum (FDE.negationSeededStep seed x))) = true := by decide

-- The compiled feedback operator advances the retained seed through two ticks.
private def seededTick (seed x : Lean.Sixteen3) : Term :=
  run 32 (seededOperator seed @@ .datum x)

#eval seededTick (FDE.singleton .T) Lean.Sixteen3.none
#eval seededTick (FDE.singleton .T) (FDE.singleton .T)
example : seededTick (FDE.singleton .T) Lean.Sixteen3.none =
    .datum (FDE.singleton .T) := by decide
example : seededTick (FDE.singleton .T) (FDE.singleton .T) =
    .datum KernelReentry.truthNegationReentry := by decide

-- Recursive self-application computes an ordinary result for a constant functional.
#eval run 100 (Y @@ (.k @@ .datum (FDE.singleton .B)))
example : run 100 (Y @@ (.k @@ .datum (FDE.singleton .B))) =
    .datum (FDE.singleton .B) := by decide

-- T/F membership and singleton B remain different after combinator execution.
example : run 3 (hold @@ .datum (FDE.singleton .T)) ≠
    run 3 (hold @@ .datum (FDE.singleton .B)) := by decide

-- No contraction is available for a bare symbolic variable.
example : reduceOnce (.var 37) = none := by decide
example (fuel : Nat) : run fuel (.var 37) = .var 37 :=
  run_halted fuel (.var 37) (by decide)
