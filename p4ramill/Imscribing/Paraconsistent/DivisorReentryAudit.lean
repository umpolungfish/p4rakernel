import Imscribing.Paraconsistent.DivisorReentry
open Imscribing.Paraconsistent.DivisorReentry
open Imscribing.Paraconsistent.CombinatoryReentry

#print axioms designation_iff
#print axioms contradictory_divisor_retains_both
#print axioms falsity_join_preserves_truth
#print axioms factor_fixedpoint
#print axioms seeded_reduces
#print axioms terminal_reduces

#eval factor 91
#eval factor 97
#eval factors 36
#eval factorFrom 91 13
#eval factor 91 true
#eval factors 36 true

example : run 300 (factorProgram 91 2) = .number 7 := by decide
example : run 100 (factorProgram 91 13 true) = .number 13 := by decide
example : run 100 (factorProgram 0 2) = .number 0 := by decide
example : run 100 (factorProgram 1 2) = .number 1 := by decide

/-- Execute every requested API and compare its exact arithmetic result. -/
def verify : IO Unit := do
  for N in List.range 101 do
    let expected := (List.range N).filter (fun k => 1 < k && N % k == 0)
    for contradictory in [false, true] do
      let got := factors N contradictory
      unless got.reverse == expected do
        throw (IO.userError s!"divisors mismatch N={N}, contradictory={contradictory}: {got}")
      let first := factor N contradictory
      unless first == expected.headD N do
        throw (IO.userError s!"first factor mismatch N={N}: {first}")
      for d in expected do
        unless factorFrom N d contradictory == d do
          throw (IO.userError s!"seed mismatch N={N}, d={d}")
      if N ≤ 36 then
        for seed in List.range (N + 2) do
          let wanted := (expected.filter (fun k => seed ≤ k)).headD N
          unless factorFrom N seed contradictory == wanted do
            throw (IO.userError s!"advancing seed mismatch N={N}, seed={seed}")
  IO.println "Y/SIXTEEN_3 re-entry: first factor, all divisors, prime sentinel, seeded return, and contradictory evidence pass for N=0..100"


def main (args : List String) : IO Unit := do
  let parse (text : String) : IO Nat :=
    match text.toNat? with
    | some n => pure n
    | none => throw (IO.userError s!"invalid natural numeral: {text}")
  let report (N k : Nat) (both : Bool) : IO Unit := do
    if 1 < k && k < N then
      unless N % k == 0 do
        throw (IO.userError s!"extracted numeral {k} does not divide {N}")
      IO.println s!"factor={k} cofactor={N / k} product={k * (N / k)} evidence={repr (δ N k both)}"
    else IO.println s!"sentinel={k}"
  match args with
  | [] => verify
  | ["factor", n] =>
      let N ← parse n
      report N (factor N) false
  | ["factor", n, "both"] =>
      let N ← parse n
      report N (factor N true) true
  | ["from", n, d] =>
      let N ← parse n
      let seed ← parse d
      report N (factorFrom N seed) false
  | ["from", n, d, "both"] =>
      let N ← parse n
      let seed ← parse d
      report N (factorFrom N seed true) true
  | ["factors", n] => IO.println s!"{factors (← parse n)}"
  | ["factors", n, "both"] => IO.println s!"{factors (← parse n) true}"
  | _ => throw (IO.userError "usage: divisor_reentry [factor N [both] | factors N [both] | from N d [both]]")
