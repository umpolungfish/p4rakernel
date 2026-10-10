import Lean
import Init.Paraconsistent

open Lean

enable_trilattice

/-- Adding the truth singleton at every information-order iteration converges to it. -/
reentry injectedTruth (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i f (Sixteen3.ofBelnap false true false false)

example : injectedTruth = Sixteen3.ofBelnap false true false false := rfl
example : injectedTruth.hasT = true := rfl

-- Runtime use goes through the same stored membership value.
#eval show IO Unit from do
  unless injectedTruth.hasT && !injectedTruth.hasB do
    throw <| IO.userError "compiled re-entry payload mismatch"

reentry mask0 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false false false false)
example : mask0 = (Sixteen3.ofBelnap false false false false) := rfl
reentry mask1 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true false false false)
example : mask1 = (Sixteen3.ofBelnap true false false false) := rfl
reentry mask2 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false true false false)
example : mask2 = (Sixteen3.ofBelnap false true false false) := rfl
reentry mask3 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true true false false)
example : mask3 = (Sixteen3.ofBelnap true true false false) := rfl
reentry mask4 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false false true false)
example : mask4 = (Sixteen3.ofBelnap false false true false) := rfl
reentry mask5 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true false true false)
example : mask5 = (Sixteen3.ofBelnap true false true false) := rfl
reentry mask6 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false true true false)
example : mask6 = (Sixteen3.ofBelnap false true true false) := rfl
reentry mask7 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true true true false)
example : mask7 = (Sixteen3.ofBelnap true true true false) := rfl
reentry mask8 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false false false true)
example : mask8 = (Sixteen3.ofBelnap false false false true) := rfl
reentry mask9 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true false false true)
example : mask9 = (Sixteen3.ofBelnap true false false true) := rfl
reentry mask10 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false true false true)
example : mask10 = (Sixteen3.ofBelnap false true false true) := rfl
reentry mask11 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true true false true)
example : mask11 = (Sixteen3.ofBelnap true true false true) := rfl
reentry mask12 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false false true true)
example : mask12 = (Sixteen3.ofBelnap false false true true) := rfl
reentry mask13 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true false true true)
example : mask13 = (Sixteen3.ofBelnap true false true true) := rfl
reentry mask14 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap false true true true)
example : mask14 = (Sixteen3.ofBelnap false true true true) := rfl
reentry mask15 (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.meet_i f Sixteen3.all) (Sixteen3.ofBelnap true true true true)
example : mask15 = (Sixteen3.ofBelnap true true true true) := rfl

reentry identity (f : Sixteen3) : Sixteen3 := f
example : identity = Sixteen3.none := rfl
reentry intersect (f : Sixteen3) : Sixteen3 := Sixteen3.meet_i f Sixteen3.all
example : intersect = Sixteen3.none := rfl

#eval show IO Unit from do
  let values := #[mask0, mask1, mask2, mask3, mask4, mask5, mask6, mask7, mask8, mask9, mask10, mask11, mask12, mask13, mask14, mask15]
  for i in [:16] do
    unless values[i]! == Sixteen3.ofMask i do
      throw <| IO.userError s!"compiled re-entry mask mismatch: {i}"
