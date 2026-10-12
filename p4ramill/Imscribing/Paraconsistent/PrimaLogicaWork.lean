import Imscribing.Paraconsistent.PrimaLogicaWinding

/-!
# Prima Logica: the Work

"The balance is not the work."

`work s` counts the members of {N,T,F,B} that the register `s` still lacks.
The balance (the fixed point of `wind`) is where `work = 0`. Every other
register has work to do, and each winding step does exactly one unit of it.

Same method as PrimaLogicaWinding: exhaust the four Boolean coordinates of
the native Sixteen3 carrier. No new axiom.

NOTE: written without access to a Lean toolchain. Build before relying on it.
-/

namespace Imscribing.PrimaLogica

open Lean Imscribing.NSReentry

/-- Distance from the balance: the number of N,T,F,B members not yet held. -/
def work (s : Sixteen3) : Nat :=
  (if s.hasN then 0 else 1) + (if s.hasT then 0 else 1) +
  (if s.hasF then 0 else 1) + (if s.hasB then 0 else 1)

/-- The unmarked register carries the full Work. -/
theorem work_unmarked : work unmarked = 4 := by decide

/-- At the completed register there is no Work left. -/
theorem work_complete : work complete = 0 := by decide

/-- No register has more than four units of Work. -/
theorem work_le_four (s : Sixteen3) : work s ≤ 4 := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Balance iff no Work: the fixed point is exactly where work vanishes. -/
theorem work_eq_zero_iff_complete (s : Sixteen3) :
    work s = 0 ↔ s = complete := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Away from the balance there is Work to do. -/
theorem work_pos_of_ne_complete (s : Sixteen3) (h : s ≠ complete) :
    0 < work s := by
  rcases Nat.eq_zero_or_pos (work s) with h0 | hpos
  · exact absurd ((work_eq_zero_iff_complete s).mp h0) h
  · exact hpos

/-- Each winding step does exactly one unit of Work, except at the balance. -/
theorem work_wind_step (s : Sixteen3) (h : s ≠ complete) :
    work (wind s) + 1 = work s := by
  revert h
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- At the balance, winding does no Work. -/
theorem work_wind_complete : work (wind complete) = work complete := by decide

/-- Winding never increases the Work. -/
theorem work_wind_le (s : Sixteen3) : work (wind s) ≤ work s := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Exactly `work s` winding steps reach the balance. -/
theorem wind_reaches_in_work_steps (s : Sixteen3) :
    Nat.iterate wind (work s) s = complete := by
  rcases s with ⟨n, t, f, b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Four is tight: three winding steps from the unmarked register fall short. -/
theorem three_steps_fall_short :
    Nat.iterate wind 3 unmarked ≠ complete := by decide

end Imscribing.PrimaLogica
