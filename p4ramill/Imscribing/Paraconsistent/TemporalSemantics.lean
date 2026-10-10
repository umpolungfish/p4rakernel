import Imscribing.Paraconsistent.Belnap

/-!
# Tick-indexed semantics for paraconsistent observations

This module models a recursive observation as a signal indexed by natural
ticks. It does not change Lean's kernel or make unguarded recursion logically
transparent. `feedback` is guarded by one tick: each value depends only on the
previous value.
-/

namespace Imscribing.Paraconsistent.Temporal.Semantics

open Imscribing.Paraconsistent

/-- A discrete-time stream of four-valued observations. -/
abbrev Signal := Nat → Belnap

/-- Read the next tick. -/
def next (s : Signal) : Signal := fun n => s (n + 1)

/-- Apply a truth-value operation at every tick. -/
def map (f : Belnap → Belnap) (s : Signal) : Signal := fun n => f (s n)

/-- A one-tick delay with an explicit initial observation. -/
def delay (initial : Belnap) (s : Signal) : Signal
  | 0 => initial
  | n + 1 => s n

/-- Compose signal transformers. -/
def compose (f g : Signal → Signal) : Signal → Signal := fun s => f (g s)

/-- Guarded feedback: the next output is computed from the previous tick. -/
def feedback (step : Belnap → Belnap) (initial : Belnap) : Signal
  | 0 => initial
  | n + 1 => step (feedback step initial n)

/-- The guarded fixed-point equation: expose the seed now and feed the
    transformed trace back only after one tick of delay. -/
theorem feedback_unfold (step : Belnap → Belnap) (initial : Belnap) :
    feedback step initial = delay initial (map step (feedback step initial)) := by
  funext n
  cases n <;> rfl

theorem next_delay (initial : Belnap) (s : Signal) :
    next (delay initial s) = s := by
  funext n
  rfl

theorem map_compose (f g : Belnap → Belnap) (s : Signal) :
    map f (map g s) = map (f ∘ g) s := by
  rfl

theorem compose_assoc (f g h : Signal → Signal) :
    compose (compose f g) h = compose f (compose g h) := rfl

/-- An oscillator started at true and negated once on every tick. -/
def liarOscillator : Signal := feedback bnot Belnap.T

theorem liarOscillator_step (n : Nat) :
    liarOscillator (n + 1) = bnot (liarOscillator n) := rfl

theorem bnot_involutive (v : Belnap) : bnot (bnot v) = v := by
  cases v <;> rfl

theorem liarOscillator_period_two (n : Nat) :
    liarOscillator (n + 2) = liarOscillator n := by
  change bnot (bnot (liarOscillator n)) = liarOscillator n
  exact bnot_involutive _

/-- The liar trace stays on the classical true/false slice while it oscillates. -/
def Oscillating (s : Signal) : Prop :=
  ∀ n, (s n = .T ∨ s n = .F) ∧ s (n + 1) = bnot (s n)

theorem liarOscillator_values (n : Nat) :
    liarOscillator n = .T ∨ liarOscillator n = .F := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      change bnot (liarOscillator n) = .T ∨ bnot (liarOscillator n) = .F
      rcases ih with h | h
      · rw [h]
        exact Or.inr rfl
      · rw [h]
        exact Or.inl rfl

theorem liarOscillator_oscillates : Oscillating liarOscillator := by
  intro n
  exact ⟨liarOscillator_values n, liarOscillator_step n⟩

def Stable (s : Signal) : Prop := ∃ v, ∀ n, s n = v

theorem liarOscillator_not_stable : ¬ Stable liarOscillator := by
  rintro ⟨v, hv⟩
  have h0 : liarOscillator 0 = .T := rfl
  have h1 : liarOscillator 1 = .F := rfl
  have ht : v = .T := (hv 0).symm.trans h0
  have hf : v = .F := (hv 1).symm.trans h1
  have : Belnap.T = Belnap.F := ht.symm.trans hf
  exact (by decide : Belnap.T ≠ Belnap.F) this

/-- Stable unknown evidence is distinct from an alternating classical trace. -/
def undetermined : Signal := fun _ => .N

theorem undetermined_stable : Stable undetermined :=
  ⟨.N, fun _ => rfl⟩

theorem undetermined_negation_fixed (n : Nat) :
    bnot (undetermined n) = undetermined n := rfl

/-- Belnap's glut is a stable, self-negating observation. -/
def glut : Signal := fun _ => .B

theorem glut_stable : Stable glut := ⟨.B, fun _ => rfl⟩

theorem glut_negation_fixed (n : Nat) : bnot (glut n) = glut n := rfl

/-- A relation is a tick bisimulation when it matches the current readout and
    remains related after both signals advance by one tick. -/
def IsBisimulation (R : Signal → Signal → Prop) : Prop :=
  ∀ ⦃s t⦄, R s t → s 0 = t 0 ∧ R (next s) (next t)

theorem bisimilar_signals_agree (R : Signal → Signal → Prop)
    (hstep : IsBisimulation R) {s t : Signal} (hrel : R s t) :
    ∀ n, s n = t n := by
  intro n
  induction n generalizing s t hrel with
  | zero => exact (hstep hrel).1
  | succ n ih =>
      have hnext : R (next s) (next t) := (hstep hrel).2
      exact ih hnext

end Imscribing.Paraconsistent.Temporal.Semantics
