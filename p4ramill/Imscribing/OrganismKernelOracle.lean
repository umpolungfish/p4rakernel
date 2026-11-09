import Init.Paraconsistent
import Lean.Sixteen3

open Lean Paraconsistent

/-! Organism Kernel Oracle: Belnap lattice operations over Sixteen3 masks,
providing the dialetheic truth-value machinery for the organism's decision
procedures. All operations run on Four-valued Belnap logic (N, T, F, B). -/

def maskToSixteen3 (m : Nat) : Lean.Sixteen3 :=
  ⟨m % 2 == 1, m / 2 % 2 == 1, m / 4 % 2 == 1, m / 8 % 2 == 1⟩

def sixteen3ToMask (s : Lean.Sixteen3) : Nat :=
  (if s.hasN then 1 else 0) +
  (if s.hasT then 2 else 0) +
  (if s.hasF then 4 else 0) +
  (if s.hasB then 8 else 0)

def main : IO Unit := do
  -- Lattice rows: all 256 pairs (x,y) in 0..15×0..15
  for x in List.range 16 do
    for y in List.range 16 do
      let a := maskToSixteen3 x
      let b := maskToSixteen3 y
      let join_i := a.join_i b
      let meet_i := a.meet_i b
      let join_t := a.join_t b
      let meet_t := a.meet_t b
      let join_f := a.join_f b
      let meet_f := a.meet_f b
      let leq_t := a.le_t b
      let leq_f := a.le_f b
      let leq_i := a.le_i b
      IO.println ("lattice " ++ toString x ++ " " ++ toString y ++ " " ++
                  toString (sixteen3ToMask join_i) ++ " " ++
                  toString (sixteen3ToMask meet_i) ++ " " ++
                  toString (sixteen3ToMask join_t) ++ " " ++
                  toString (sixteen3ToMask meet_t) ++ " " ++
                  toString (sixteen3ToMask join_f) ++ " " ++
                  toString (sixteen3ToMask meet_f) ++ " " ++
                  (if leq_t then "true" else "false") ++ " " ++
                  (if leq_f then "true" else "false") ++ " " ++
                  (if leq_i then "true" else "false"))
  -- Evidence rows: FDE conjunction/disjunction for x,y in 0..3
  for x in List.range 4 do
    for y in List.range 4 do
      let aT := (x % 2 == 1)
      let aF := (x / 2 % 2 == 1)
      let bT := (y % 2 == 1)
      let bF := (y / 2 % 2 == 1)
      let andT := aT && bT
      let andF := aF || bF
      let orT := aT || bT
      let orF := aF && bF
      let band := (if andT then 1 else 0) + 2 * (if andF then 1 else 0)
      let bor := (if orT then 1 else 0) + 2 * (if orF then 1 else 0)
      IO.println ("evidence " ++ toString x ++ " " ++ toString y ++ " " ++
                  toString band ++ " " ++ toString bor)