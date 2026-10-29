import Init.Paraconsistent
import Lean.Sixteen3

open Lean Paraconsistent

private def atoms : Array Belnap := #[.N, .T, .F, .B]
private def code : Belnap → Nat
  | .N => 0 | .T => 1 | .F => 2 | .B => 3
private def mask (x : Lean.Sixteen3) : Nat :=
  (if x.hasN then 1 else 0) + (if x.hasT then 2 else 0) +
  (if x.hasF then 4 else 0) + (if x.hasB then 8 else 0)

def main : IO Unit := do
  for x in [:16] do
    for y in [:16] do
      let a := Lean.Sixteen3.ofMask x
      let b := Lean.Sixteen3.ofMask y
      IO.println s!"lattice {x} {y} {mask (a.join_i b)} {mask (a.meet_i b)} {mask (a.join_t b)} {mask (a.meet_t b)} {mask (a.join_f b)} {mask (a.meet_f b)} {a.le_t b} {a.le_f b} {a.le_i b}"
  for x in [:4] do
    for y in [:4] do
      IO.println s!"evidence {x} {y} {code (Belnap.band atoms[x]! atoms[y]!)} {code (Belnap.bor atoms[x]! atoms[y]!)}"
