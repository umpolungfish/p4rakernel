import Mathlib.Logic.Function.Iterate
import Imscribing.Paraconsistent.TemporalSemantics
import Imscribing.Paraconsistent.IMASM16_3Machine

enable_trilattice

/-! A criterion for discarding distinctions in a carried ensemble.

`State` denotes the whole bounded ensemble, including its correlated alternatives,
not an isolated constituent. `step` must act on that same ensemble. The observation
type retains the required folding, coherence, work and enabled-action readouts.
The results quantify over every finite continuation of the supplied machine.
They do not assert that a particular machine already characterizes protein folding.
-/
namespace Imscribing.Biochem.FoldingDistinctions

universe u v w z

/-- A repeated two-state future can be skipped only with its terminal parity.
The two states are not identified, and a cycle is not declared a fixed point. -/
theorem two_step_return {State : Type u} (step : State → State) (s : State)
    (cycle : step (step s) = s) (k : ℕ) : (step^[2*k]) s = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply]
    have closed : (step^[2]) s = s := by
      simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using cycle
    rw [closed, ih]

theorem two_step_odd_return {State : Type u} (step : State → State) (s : State)
    (cycle : step (step s) = s) (k : ℕ) : (step^[2*k+1]) s = step s := by
  rw [Function.iterate_succ_apply', two_step_return step s cycle k]

#print axioms two_step_return
#print axioms two_step_odd_return

def runFrom {State : Type u} {Action : Type v}
    (step : State → Action → State) : List Action → State → State
  | [], s => s
  | a :: rest, s => runFrom step rest (step s a)

def SameFuture {State : Type u} {Action : Type v} {Observation : Type w}
    (step : State → Action → State) (observe : State → Observation)
    (s t : State) : Prop :=
  ∀ continuation, observe (runFrom step continuation s) = observe (runFrom step continuation t)

theorem sameFuture_now {State : Type u} {Action : Type v} {Observation : Type w}
    {step : State → Action → State} {observe : State → Observation} {s t : State}
    (h : SameFuture step observe s t) : observe s = observe t := h []

theorem sameFuture_step {State : Type u} {Action : Type v} {Observation : Type w}
    {step : State → Action → State} {observe : State → Observation} {s t : State}
    (h : SameFuture step observe s t) (a : Action) :
    SameFuture step observe (step s a) (step t a) := by
  intro rest
  exact h (a :: rest)

/-- An identification is adequate when it preserves the current observations
and remains adequate after every generating action on the carried ensemble. -/
def Adequate {State : Type u} {Action : Type v} {Observation : Type w} {Code : Type z}
    (step : State → Action → State) (observe : State → Observation)
    (encode : State → Code) : Prop :=
  ∀ ⦃s t⦄, encode s = encode t →
    observe s = observe t ∧ ∀ a, encode (step s a) = encode (step t a)

/-- Sufficiency propagates through arbitrary recursive continuation length. -/
theorem adequate_preserves_every_future
    {State : Type u} {Action : Type v} {Observation : Type w} {Code : Type z}
    {step : State → Action → State} {observe : State → Observation} {encode : State → Code}
    (adequate : Adequate step observe encode) {s t : State} (same : encode s = encode t) :
    SameFuture step observe s t := by
  intro continuation
  induction continuation generalizing s t with
  | nil => exact (adequate same).1
  | cons a rest ih => exact ih ((adequate same).2 a)

/-- A positive witness to a different future prevents any adequate encoding
from erasing that distinction. This is the necessity half of the criterion. -/
theorem different_future_requires_distinction
    {State : Type u} {Action : Type v} {Observation : Type w} {Code : Type z}
    {step : State → Action → State} {observe : State → Observation} {encode : State → Code}
    (adequate : Adequate step observe encode) {s t : State} (continuation : List Action)
    (different : observe (runFrom step continuation s) ≠ observe (runFrom step continuation t)) :
    encode s ≠ encode t := by
  intro same
  exact different (adequate_preserves_every_future adequate same continuation)

/-- Future agreement is the coarsest observation-preserving, successor-stable
identification: every other such identification is contained in it. -/
theorem stable_identification_is_contained_in_sameFuture
    {State : Type u} {Action : Type v} {Observation : Type w}
    {step : State → Action → State} {observe : State → Observation}
    (related : State → State → Prop)
    (stable : ∀ ⦃s t⦄, related s t → observe s = observe t ∧ ∀ a, related (step s a) (step t a))
    {s t : State} (h : related s t) : SameFuture step observe s t := by
  intro continuation
  induction continuation generalizing s t with
  | nil => exact (stable h).1
  | cons a rest ih => exact ih ((stable h).2 a)

namespace NativeBankWitness
open Imscribing.Paraconsistent.IMASM16_3Machine

def truthBank : MachineState := run [.FSPLIT3, .EVALT, .AREV]
def falsityBank : MachineState := run [.FSPLIT3, .EVALF, .AREV]

theorem equal_landing_registers : truthBank.reg = falsityBank.reg := by decide

theorem distinct_fuse_returns :
    (step truthBank .FFUSE3).reg ≠ (step falsityBank .FFUSE3).reg := by decide

theorem landing_register_is_insufficient :
    ¬ Adequate step MachineState.reg MachineState.reg := by
  intro adequate
  have same := (adequate equal_landing_registers).2 Mark16_3.FFUSE3
  exact distinct_fuse_returns same

end NativeBankWitness

namespace NativeReverseBridge

/-- Constant and three nonconstant characters of the four named native lanes.
The constant coordinate retains support cardinality; no lane is discarded. -/
def affine (r : Reg16_3) : Int × Int × Int × Int :=
  let a : Int := if Reg16_3.bigT r then 1 else 0
  let b : Int := if Reg16_3.bigF r then 1 else 0
  let c : Int := if Reg16_3.smallT r then 1 else 0
  let d : Int := if Reg16_3.smallF r then 1 else 0
  (a+b+c+d, a-b+c-d, a+b-c-d, a-b-c+d)

def reverseAffine (p : Int × Int × Int × Int) : Int × Int × Int × Int :=
  (p.1, -p.2.1, p.2.2.1, -p.2.2.2)

theorem affine_retains_every_native_distinction :
    ∀ r s : Reg16_3, affine r = affine s → r = s := by decide

theorem affine_transports_actual_reverse :
    ∀ r : Reg16_3, affine (Reg16_3.invol r) = reverseAffine (affine r) := by decide

/-- The third arm emitted by the source's internal native ternary split.
Its two small lanes are retained together. -/
def smallPair : Reg16_3 := Reg16_3.mk false false true true

theorem smallPair_fixed : Reg16_3.invol smallPair = smallPair := rfl

/-- Any domain action transported from AREV must fix the image of its fixed
register. Extra geometric motion requires additional carried state and a
bridge on that state; a slot label alone does not supply that bridge. -/
theorem transported_reverse_fixes_smallPair {Domain : Type u}
    (realize : Reg16_3 → Domain) (reverse : Domain → Domain)
    (commutes : ∀ r, realize (Reg16_3.invol r) = reverse (realize r)) :
    reverse (realize smallPair) = realize smallPair := by
  simpa only [smallPair_fixed] using (commutes smallPair).symm

theorem no_fixed_free_reverse_bridge {Domain : Type u}
    (realize : Reg16_3 → Domain) (reverse : Domain → Domain)
    (no_fixed_point : ∀ d, reverse d ≠ d) :
    ¬ (∀ r, realize (Reg16_3.invol r) = reverse (realize r)) := by
  intro commutes
  exact no_fixed_point _ (transported_reverse_fixes_smallPair realize reverse commutes)

end NativeReverseBridge

#print axioms adequate_preserves_every_future
#print axioms different_future_requires_distinction
#print axioms stable_identification_is_contained_in_sameFuture
#print axioms NativeBankWitness.landing_register_is_insufficient
#print axioms NativeReverseBridge.no_fixed_free_reverse_bridge
#print axioms NativeReverseBridge.affine_retains_every_native_distinction
#print axioms NativeReverseBridge.affine_transports_actual_reverse
end Imscribing.Biochem.FoldingDistinctions
