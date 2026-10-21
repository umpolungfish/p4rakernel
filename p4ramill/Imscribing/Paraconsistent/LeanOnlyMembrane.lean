import Imscribing.Paraconsistent.DivisorReentry
import Imscribing.ReEntryConstructions
import Imscribing.Paraconsistent.DialecticResident

namespace Imscribing.Paraconsistent.LeanOnlyMembrane

open CombinatoryReentry DivisorReentry

def squareMask : Nat :=
  (List.finRange 256).foldl (fun mask residue =>
    if DialecticResident.squareSupport256 residue then mask + 2^residue.val else mask) 0

/-- The production term is the corpus Y program, starting from N alone. -/
def prepared (N : Nat) : Term :=
  .app (.app Y (.multiplicativeSplit N)) (.productFamily 1 (MultiplicativeReentry.unit (0, 0)))

/-- A held membrane keeps the source, its binary well and its actual Y return.
The reduction witness belongs to this returned term, including unfinished runs. -/
structure Membrane (N : Nat) where
  sourceWell : BinaryWell
  sourceBound : binEval sourceWell = N
  continuation : Term
  reduced : Steps (prepared N) continuation
  budget : Nat

def prepare (N : Nat) : Membrane N where
  sourceWell := Nat.digits 2 N
  sourceBound := Nat.ofDigits_digits 2 N
  continuation := prepared N
  reduced := .refl _
  budget := 0

/-- All computation is delegated to the existing proof-producing Lean reducer. -/
def trigger {N : Nat} (fuel : Nat) (membrane : Membrane N) : Membrane N where
  sourceWell := membrane.sourceWell
  sourceBound := membrane.sourceBound
  continuation := run fuel membrane.continuation
  reduced := membrane.reduced.trans (run_reduces fuel membrane.continuation)
  budget := membrane.budget + fuel

theorem trigger_resume {N : Nat} (first second : Nat) (m : Membrane N) :
    (trigger second (trigger first m)).continuation =
      (trigger (first + second) m).continuation := by
  exact (run_add first second m.continuation).symm

theorem trigger_source {N : Nat} (fuel : Nat) (m : Membrane N) :
    binEval (trigger fuel m).sourceWell = N := m.sourceBound

def readFactor {N : Nat} (m : Membrane N) : Option Nat :=
  match m.continuation with
  | .number d => if 1 < d && d < N && N % d == 0 then some d else none
  | _ => none

def report {N : Nat} (m : Membrane N) : IO Unit := do
  unless binEval m.sourceWell == N do
    throw (IO.userError "source bank did not return")
  match m.continuation with
  | .residentFactorScan sourceN mask k source a residual cell =>
    unless sourceN == N && mask == squareMask &&
        source == (if k == 0 then N else 4*k*N) &&
        a*a == source+residual &&
        a == FullyNestedFactorMachine.initialNat source + cell do
      throw (IO.userError "source-bound residual relation did not return")
    IO.println s!"source_residual_return=true multiplier={k} cell={cell}"
  | _ => pure ()
  IO.println s!"source={N} budget={m.budget} source_bank_return=true"
  match readFactor m with
  | some d =>
    let q := N / d
    unless d * q == N do throw (IO.userError "product did not close")
    IO.println s!"factor={d} quotient={q} remainder={N % d} product={d*q} evidence={repr (divisorEvidence N d true)}"
  | none => IO.println s!"held_continuation={repr m.continuation}"

end Imscribing.Paraconsistent.LeanOnlyMembrane
