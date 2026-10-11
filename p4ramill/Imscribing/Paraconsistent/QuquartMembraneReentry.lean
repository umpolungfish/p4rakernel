import Imscribing.Paraconsistent.TensorFiltration
import Imscribing.Paraconsistent.CombinatoryDynamics
import Imscribing.Millennium.ZetaSICDualFrame

/-! The existing lane/native equivalence transports ququart outcome labels and
certified feedback ticks. Coordinate recovery retains complex coordinates. -/
namespace Imscribing.Paraconsistent.QuquartMembraneReentry

open CombinatoryReentry CombinatoryDynamics
open Temporal.Semantics
open Imscribing.Millennium.ZetaSICDualFrame
local infixl:70 " @@ " => Term.app

/-- Runtime bit weights are t=1, f=2, T=4, F=8. -/
def runtimeLane (index : Fin 16) : Imscribing.IUTT.State :=
  (index.val.testBit 2, index.val.testBit 3,
   index.val.testBit 0, index.val.testBit 1)

/-- Reuse the corpus equivalence: T→B, F→F, t→T, f→N. -/
def nativeOutcome (index : Fin 16) : Lean.Sixteen3 :=
  TensorFiltration.nativeCarrier (runtimeLane index)

def runtimeOutcome (x : Lean.Sixteen3) : Fin 16 :=
  ⟨(if x.hasT then 1 else 0) + (if x.hasN then 2 else 0) +
    (if x.hasB then 4 else 0) + (if x.hasF then 8 else 0), by
    rcases x with ⟨n, t, f, b⟩
    cases n <;> cases t <;> cases f <;> cases b <;> decide⟩

theorem runtime_native_roundtrip : ∀ index : Fin 16,
    runtimeOutcome (nativeOutcome index) = index := by decide

theorem native_runtime_roundtrip (x : Lean.Sixteen3) :
    nativeOutcome (runtimeOutcome x) = x := by
  rcases x with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

def outcomeEquivalence : Fin 16 ≃ Lean.Sixteen3 where
  toFun := nativeOutcome
  invFun := runtimeOutcome
  left_inv := runtime_native_roundtrip
  right_inv := native_runtime_roundtrip

/-- Runtime negation swaps the t and F bits under the existing equivalence.
The measured retained evidence is joined after each negation. -/
def retainedRuntimeStep (retained state : Fin 16) : Fin 16 :=
  runtimeOutcome (Lean.Sixteen3.join_i
    (FDE.liftNegation (nativeOutcome state)) (nativeOutcome retained))

theorem retained_runtime_program (retained state : Fin 16) :
    Steps (seededOperator (nativeOutcome retained) @@ .datum (nativeOutcome state))
      (.datum (nativeOutcome (retainedRuntimeStep retained state))) := by
  rw [retainedRuntimeStep, native_runtime_roundtrip]
  exact seededOperator_apply _ _

/-- Integer implementation used by the native membrane clock leaf. -/
theorem retained_runtime_bits : ∀ retained state : Fin 16,
    (retainedRuntimeStep retained state).val =
      (state.val &&& 6) ||| ((state.val &&& 1) <<< 3) |||
        ((state.val &&& 8) >>> 3) ||| retained.val := by decide

/-- The runtime label of a certified native clock observation. -/
def runtimeTick {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (tick : Nat) : Fin 16 :=
  runtimeOutcome (clock.read tick)

theorem runtime_tick_agrees {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (tick : Nat) :
    nativeOutcome (runtimeTick clock tick) = clock.cycle.orbit tick := by
  rw [runtimeTick, native_runtime_roundtrip, clock.read_eq_orbit]

theorem runtime_program_tick {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (tick : Nat) :
    Steps (program @@ .datum (nativeOutcome (runtimeTick clock tick)))
      (.datum (nativeOutcome (runtimeTick clock (tick + 1)))) := by
  simp only [runtimeTick, native_runtime_roundtrip]
  exact clock.program_tick tick

/-- A membrane observation keeps its logical label and complex coordinate
vector together; neither is replaced by the other. -/
structure Observation where
  outcome : Fin 16
  coordinates : Fin 16 → ℂ

noncomputable def observe {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (coordinates : Nat → Fin 16 → ℂ)
    (tick : Nat) : Observation :=
  ⟨runtimeTick clock tick,
   ququartDualGram.mulVec (ququartGram.mulVec (coordinates tick))⟩

theorem observation_coordinates {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (coordinates : Nat → Fin 16 → ℂ) (tick : Nat) :
    (observe clock coordinates tick).coordinates = coordinates tick :=
  ququart_coordinate_reconstruction (coordinates tick)

theorem observation_control {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (coordinates : Nat → Fin 16 → ℂ) (tick : Nat) :
    nativeOutcome (observe clock coordinates tick).outcome = clock.cycle.orbit tick :=
  runtime_tick_agrees clock tick

end Imscribing.Paraconsistent.QuquartMembraneReentry
