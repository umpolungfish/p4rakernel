import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable def fluxTube (a s : ℝ) (r : ℝ) : ℝ := -a / r + s * r

#print fluxTube
#check deriv

theorem probe_eq (a s r : ℝ) :
    deriv (fluxTube a s) r = deriv (fun r => -a / r + s * r) r := by
  rfl
