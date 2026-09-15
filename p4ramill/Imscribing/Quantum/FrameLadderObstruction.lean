import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! A precise obstruction to interpreting frame push/pop as the unnormalized
two-coordinate incidence ladder. The state readout is arbitrary: it may inspect
the entire machine state and need not be linear or injective. The hypotheses
require literal equality of operators, not equality up to a scalar.
-/
namespace Imscribing.Quantum.FrameLadderObstruction

abbrev Sector := ℂ × ℂ × ℂ

/-- In the unnormalized sector sums u0=FF, u1=TF+FT, u2=TT. -/
def raise (v : Sector) : Sector := (0, v.1, 2 * v.2.1)
def lower (v : Sector) : Sector := (2 * v.2.1, v.2.2, 0)

theorem lower_raise_fixed_only_zero (v : Sector)
    (h : lower (raise v) = v) : v = (0, 0, 0) := by
  rcases v with ⟨a, b, c⟩
  have ha := congrArg (fun w : Sector => w.1) h
  have hb := congrArg (fun w : Sector => w.2.1) h
  have hc := congrArg (fun w : Sector => w.2.2) h
  simp [raise, lower] at ha hb hc
  have a0 : a = 0 := by linear_combination ha
  have b0 : b = 0 := by linear_combination hb
  simp [a0, b0, ← hc]

/-- A push/pop identity cannot intertwine with this ladder through any nonzero
    state readout. This is conditional on the explicitly stated state equations;
    it does not claim that Rust operational semantics were imported into Lean. -/
theorem any_exact_frame_readout_is_zero {State : Type*}
    (push pop : State → State) (readout : State → Sector)
    (roundtrip : ∀ s, pop (push s) = s)
    (reads_push : ∀ s, readout (push s) = raise (readout s))
    (reads_pop : ∀ s, readout (pop s) = lower (readout s)) :
    ∀ s, readout s = (0, 0, 0) := by
  intro s
  apply lower_raise_fixed_only_zero
  calc
    lower (raise (readout s)) = lower (readout (push s)) := by rw [reads_push]
    _ = readout (pop (push s)) := (reads_pop (push s)).symm
    _ = readout s := by rw [roundtrip]

end Imscribing.Quantum.FrameLadderObstruction
