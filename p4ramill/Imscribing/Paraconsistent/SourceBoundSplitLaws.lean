import Imscribing.Paraconsistent.SourceBoundSplit

namespace Imscribing.Paraconsistent.SourceBoundSplit

/-- Algebraic holonomy of N half-turns, with its retained Z2 class. -/
theorem phase_holonomy (N : Nat) : phaseUnit N = (-1 : G)^N := by
  have decomposition : N = N%2 + 2*(N/2) := by omega
  conv_rhs => rw [decomposition, pow_add, pow_mul]
  simp only [neg_one_sq, one_pow, mul_one]
  have bound := Nat.mod_lt N (by decide : 0 < 2)
  have alternatives : N%2 = 0 ∨ N%2 = 1 := by omega
  rcases alternatives with h | h <;> simp [phaseUnit, h]

theorem get_split (a : Amp) (coordinate : Nat) :
    a.truth.get coordinate+a.falsity.get coordinate = a.get coordinate := by
  unfold Amp.get Amp.truth Amp.falsity
  split_ifs <;> simp

theorem chart_split_recovery {N} (c : Chart N) (e r : ZMod N) (coordinate : Nat) :
    Chart.amplitudeAt {c with amplitude:=c.amplitude.truth,ancestry:=some false} e r coordinate+
    Chart.amplitudeAt {c with amplitude:=c.amplitude.falsity,ancestry:=some true} e r coordinate =
    c.amplitudeAt e r coordinate := by
  simp only [Chart.amplitudeAt]
  split_ifs <;> simp [get_split]

theorem amplitudeAt_acc {N} (charts : List (Chart N)) (e r : ZMod N) (coordinate : Nat) (seed : G) :
    charts.foldl (fun total c => total+c.amplitudeAt e r coordinate) seed =
      seed+amplitudeAt charts e r coordinate := by
  unfold amplitudeAt
  induction charts generalizing seed with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons]
    simp only [zero_add]
    conv_lhs => rw [ih (seed+c.amplitudeAt e r coordinate)]
    conv_rhs => rw [ih (c.amplitudeAt e r coordinate)]
    simp only [add_assoc]

theorem amplitudeAt_cons {N} (c : Chart N) (cs : List (Chart N)) (e r : ZMod N) (coordinate : Nat) :
    amplitudeAt (c::cs) e r coordinate = c.amplitudeAt e r coordinate+amplitudeAt cs e r coordinate := by
  change cs.foldl (fun total c => total+c.amplitudeAt e r coordinate)
    (0+c.amplitudeAt e r coordinate) = _
  rw [zero_add]
  exact amplitudeAt_acc cs e r coordinate (c.amplitudeAt e r coordinate)

theorem amplitudeAt_append {N} (left right : List (Chart N)) (e r : ZMod N) (coordinate : Nat) :
    amplitudeAt (left++right) e r coordinate =
      amplitudeAt left e r coordinate+amplitudeAt right e r coordinate := by
  induction left with
  | nil => simp [amplitudeAt]
  | cons c cs ih => simp [amplitudeAt_cons, ih, add_assoc]

/-- The actual tagged sector split and history-erasing fuse recover every
complex coordinate of the complete source family before intervening actions. -/
theorem source_frobenius {N} (charts : List (Chart N)) (e r : ZMod N) (coordinate : Nat) :
    amplitudeAt
      (((charts.map fun (c : Chart N) => {c with amplitude:=c.amplitude.truth,ancestry:=some false}) ++
        (charts.map fun (c : Chart N) => {c with amplitude:=c.amplitude.falsity,ancestry:=some true})).map
          (fun (c : Chart N) => {c with ancestry:=none})) e r coordinate = amplitudeAt charts e r coordinate := by
  simp only [List.map_append, List.map_map, amplitudeAt_append]
  induction charts with
  | nil => simp [amplitudeAt]
  | cons c cs ih =>
    simp only [List.map_cons, amplitudeAt_cons]
    have recovered := chart_split_recovery c e r coordinate
    simp only [Chart.amplitudeAt] at recovered
    change Chart.amplitudeAt {c with amplitude:=c.amplitude.truth} e r coordinate + _ +
      (Chart.amplitudeAt {c with amplitude:=c.amplitude.falsity} e r coordinate + _) = _
    have local_recovery :
        Chart.amplitudeAt {c with amplitude:=c.amplitude.truth} e r coordinate+
        Chart.amplitudeAt {c with amplitude:=c.amplitude.falsity} e r coordinate =
        c.amplitudeAt e r coordinate := by
      simpa only [Chart.amplitudeAt] using recovered
    rw [←ih, ←local_recovery]
    abel

theorem phase_charts_involution {N} (charts : List (Chart N)) :
    scaleCharts (phaseUnit N) (scaleCharts (phaseUnit N) charts) = charts := by
  induction charts with
  | nil => rfl
  | cons c cs ih =>
    simp only [scaleCharts, List.map_cons] at *
    have restored : {c with amplitude:=(c.amplitude.scale (phaseUnit N)).scale (phaseUnit N)} = c := by
      rw [phase_involution]
    exact congrArg₂ List.cons restored ih

end Imscribing.Paraconsistent.SourceBoundSplit
