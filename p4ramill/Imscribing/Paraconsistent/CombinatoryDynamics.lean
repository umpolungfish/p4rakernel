import Imscribing.Paraconsistent.CombinatoryFixedPoint

/-!
Feedback from any native carrier state, with certified transient and cycle.
Each tick retains the original program's reduction evidence. Returned cycles
have a positive primitive period and distinct states before the first repeat.
-/

namespace Imscribing.Paraconsistent.CombinatoryDynamics

open CombinatoryReentry CombinatoryFixedPoint
open Temporal.Semantics
local infixl:70 " @@ " => Term.app

theorem feedback_restart {α : Type} (step : α → α) (seed : α) (start tick : Nat) :
    feedback step (feedback step seed start) tick = feedback step seed (start + tick) := by
  induction tick with
  | zero => rfl
  | succ tick ih =>
      change step (feedback step (feedback step seed start) tick) =
        step (feedback step seed (start + tick))
      exact congrArg step ih

theorem feedback_equal_future {α : Type} (step : α → α) (seed : α)
    (left right : Nat) (h : feedback step seed left = feedback step seed right)
    (tick : Nat) :
    feedback step seed (left + tick) = feedback step seed (right + tick) := by
  induction tick with
  | zero => exact h
  | succ tick ih =>
      change step (feedback step seed (left + tick)) =
        step (feedback step seed (right + tick))
      exact congrArg step ih

def DistinctBefore {program : Term} (table : ProgramTable program)
    (seed : Lean.Sixteen3) (stop : Nat) : Prop :=
  ∀ i j : Fin stop, feedback table.interpret seed i.val =
    feedback table.interpret seed j.val → i = j

instance {program : Term} (table : ProgramTable program) (seed : Lean.Sixteen3)
    (stop : Nat) : Decidable (DistinctBefore table seed stop) :=
  inferInstanceAs (Decidable (∀ i j : Fin stop,
    feedback table.interpret seed i.val = feedback table.interpret seed j.val → i = j))

/-- A first repeated state, with the complete program table and closure proof. -/
structure Cycle (program : Term) (seed : Lean.Sixteen3) where
  table : ProgramTable program
  entry : Nat
  period : Nat
  positive : 0 < period
  bounded : entry + period ≤ 16
  closes : feedback table.interpret seed (entry + period) =
    feedback table.interpret seed entry
  distinct : DistinctBefore table seed (entry + period)

def certifyCycle {program : Term} (table : ProgramTable program) (seed : Lean.Sixteen3)
    (entry period : Nat) : Option (Cycle program seed) :=
  if hpositive : 0 < period then
    if hbounded : entry + period ≤ 16 then
      if hcloses : feedback table.interpret seed (entry + period) =
          feedback table.interpret seed entry then
        if hdistinct : DistinctBefore table seed (entry + period) then
          some ⟨table, entry, period, hpositive, hbounded, hcloses, hdistinct⟩
        else none
      else none
    else none
  else none

/-- Search the seventeen observations from tick zero through tick sixteen. -/
def findCycle {program : Term} (table : ProgramTable program) (seed : Lean.Sixteen3) :
    Option (Cycle program seed) := Id.run do
  for stop in [1:17] do
    for entry in [0:stop] do
      if feedback table.interpret seed stop == feedback table.interpret seed entry then
        if let some cycle := certifyCycle table seed entry (stop - entry) then
          return some cycle
  return none

def analyzeOrbit (fuel : Nat) (program : Term) (seed : Lean.Sixteen3) :
    Option (Cycle program seed) := do
  let table ← tabulate fuel program
  findCycle table seed

def Cycle.orbit {program : Term} {seed : Lean.Sixteen3} (cycle : Cycle program seed) :
    Signal Lean.Sixteen3 := feedback cycle.table.interpret seed

theorem Cycle.program_tick {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) (tick : Nat) :
    Steps (program @@ .datum (cycle.orbit tick)) (.datum (cycle.orbit (tick + 1))) :=
  cycle.table.reduces_at (cycle.orbit tick)

theorem Cycle.periodic {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) (tick : Nat) :
    cycle.orbit (cycle.entry + tick + cycle.period) = cycle.orbit (cycle.entry + tick) := by
  calc
    cycle.orbit (cycle.entry + tick + cycle.period) =
        cycle.orbit (cycle.entry + cycle.period + tick) := by rw [Nat.add_right_comm]
    _ = cycle.orbit (cycle.entry + tick) :=
      feedback_equal_future cycle.table.interpret seed _ _ cycle.closes tick

theorem Cycle.no_earlier_return {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) (phase : Fin cycle.period) (hphase : 0 < phase.val) :
    cycle.orbit (cycle.entry + phase.val) ≠ cycle.orbit cycle.entry := by
  intro heq
  have hindices := cycle.distinct
    ⟨cycle.entry + phase.val, Nat.add_lt_add_left phase.isLt cycle.entry⟩
    ⟨cycle.entry, Nat.lt_add_of_pos_right cycle.positive⟩ heq
  exact (Nat.ne_of_gt (Nat.lt_add_of_pos_right hphase)) (congrArg Fin.val hindices)

theorem Cycle.fixed_of_period_one {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) (hperiod : cycle.period = 1) :
    cycle.table.interpret (cycle.orbit cycle.entry) = cycle.orbit cycle.entry := by
  change cycle.orbit (cycle.entry + 1) = cycle.orbit cycle.entry
  rw [← hperiod]
  exact cycle.closes

theorem Cycle.moves_of_period_gt_one {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) (hperiod : 1 < cycle.period) :
    cycle.table.interpret (cycle.orbit cycle.entry) ≠ cycle.orbit cycle.entry :=
  cycle.no_earlier_return ⟨1, hperiod⟩ Nat.zero_lt_one

def Cycle.transient {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) : List Lean.Sixteen3 :=
  (List.range cycle.entry).map cycle.orbit

def Cycle.loop {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) : List Lean.Sixteen3 :=
  (List.range cycle.period).map fun phase => cycle.orbit (cycle.entry + phase)

def Cycle.isStationary {program : Term} {seed : Lean.Sixteen3}
    (cycle : Cycle program seed) : Bool := cycle.period == 1

end Imscribing.Paraconsistent.CombinatoryDynamics
