import Mathlib

namespace Probe

noncomputable def m_d_real (d : ℕ) : ℝ := ((d : ℝ) - 3) * ((d : ℝ) + 1)

lemma m_d_real_pos (d : ℕ) (hd : 4 ≤ d) : 0 < m_d_real d := by
  unfold m_d_real
  have hd' : (3 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 3 < d)
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by nlinarith
  nlinarith

noncomputable def se (d : ℕ) : ℝ := (((d : ℝ) - 1) + Real.sqrt (m_d_real d)) / 2
noncomputable def sec' (d : ℕ) : ℝ := (((d : ℝ) - 1) - Real.sqrt (m_d_real d)) / 2

-- FIX A: linear_combination against the sqrt-square identity
theorem norm_one (d : ℕ) (hd : 4 ≤ d) : se d * sec' d = 1 := by
  have hsq : Real.sqrt (m_d_real d) ^ 2 = m_d_real d :=
    Real.sq_sqrt (m_d_real_pos d hd).le
  unfold se sec' m_d_real at *
  linear_combination (-(1 : ℝ) / 4) * hsq

def m_d (d : ℕ) : ℤ := ((d : ℤ) - 3) * ((d : ℤ) + 1)

def isFibQC (d : ℕ) : Prop := ∃ k : ℕ, (m_d d : ℤ) = (5 : ℤ) * ((k : ℤ) ^ 2)

-- FIX B: carry the witness, so the check is decidable and native_decide is honest
def fibQCWitnesses : List (ℕ × ℕ) :=
  [(4, 1), (8, 3), (19, 8), (48, 21), (124, 55), (323, 144), (844, 377),
   (2208, 987), (5779, 2584)]

def witnessOK (p : ℕ × ℕ) : Bool := decide (m_d p.1 = (5 : ℤ) * ((p.2 : ℤ) ^ 2))

theorem all_nine_witnessed : (fibQCWitnesses.filter witnessOK).length = 9 := by
  native_decide

theorem all_nine_prop : ∀ p ∈ fibQCWitnesses, isFibQC p.1 := by
  intro p hp
  fin_cases hp <;> exact ⟨_, by native_decide⟩

end Probe
