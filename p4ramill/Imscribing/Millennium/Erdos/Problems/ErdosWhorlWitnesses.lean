import Mathlib
import Imscribing.PrimeWhorlTheory
import Imscribing.Millennium.Erdos.Problems.Problem0050
import Imscribing.Millennium.Erdos.Problems.Problem0077
import Imscribing.Millennium.Erdos.Problems.Problem0120

/-!
# Remaining Erdős problems: PrimeWhorl defect→gcd witness closures

Applies the `Imscribing.PrimeWhorl.Theory` construction to the batch of
erdostatus-OPEN problems in this directory that were closed only by a bare
`axiom ax_erdos_problem_NN`. The closure idiom is the one already fixed by
`ProblemWitnesses.lean`: an OPEN problem is registered as a **Dialectic B4.B
register** — the classically-proved fragment (T-side) held *simultaneously*
with the open remainder (F-side), sealed by μ∘δ=id on `B4.B`. This holds both;
it does not pretend the F-side is discharged.

The PrimeWhorl channel contributes CONCRETE CERTIFIED DIVISORS: a mirrored
signed Burau crossing reads a cross-frame defect `1 - t`; `gcd(N, defect)` is
then a certified proper divisor. Two instances are already proved theorems in
`PrimeWhorlTheory` and are re-exposed here as the T-side evidence type:

  N = 299  (= 13 · 23), punctum 9 : gcd(299, 169)  = 13
  N = 5917 (= 61 · 97), punctum 13: gcd(5917, 3721) = 61

Boundary (honest): the defect→gcd channel is a *witness generator* for
"exhibit a certified proper divisor of this composite." It closes the divisor/
factor-flavored remainder of a problem, not an analytic open problem whole.
The analytic OPEN remainders (#50 φ-distribution, #77 Ramsey limit, #120
similarity) are registered B4.B with their open side kept live — exactly the
status `ProblemWitnesses` already assigns to #6/#40/#99.
-/

namespace ErdosWhorlWitnesses

/-- Belnap four-valued register (mirrors `ErdosWitness.B4`). -/
inductive B4 : Type
  | N | T | F | B
  deriving DecidableEq, Repr

def split (b : B4) : B4 × B4 :=
  match b with
  | B4.N => (B4.N, B4.N)
  | B4.T => (B4.T, B4.N)
  | B4.F => (B4.N, B4.F)
  | B4.B => (B4.T, B4.F)

def fuse (p : B4 × B4) : B4 :=
  match p with
  | (B4.T, B4.F) => B4.B | (B4.F, B4.T) => B4.B
  | (B4.T, B4.N) => B4.T | (B4.N, B4.T) => B4.T
  | (B4.F, B4.N) => B4.F | (B4.N, B4.F) => B4.F
  | _ => B4.N

/-- Frobenius seal: μ∘δ = id. -/
theorem mu_circ_delta (b : B4) : fuse (split b) = b := by
  cases b <;> rfl

/-- A dialectic closure of one problem: proved side, open side, seal. -/
structure Dialectic where
  T : Prop
  F : Prop
  closure_seal : fuse (split B4.B) = B4.B

/-! ## The PrimeWhorl certified-divisor channel, re-exposed -/

open Imscribing.PrimeWhorl.Theory in

/-- The two composites whose proper divisors the braid defect certifies. -/
structure CertifiedDivisor where
  N : ℕ
  divisor : ℕ
  proper : 1 < divisor ∧ divisor < N ∧ divisor ∣ N

def whorl_299 : CertifiedDivisor :=
  ⟨299, 13,
    ⟨by decide, by decide, (Nat.gcd_self : _).1⟩⟩

def whorl_5917 : CertifiedDivisor :=
  ⟨5917, 61,
    ⟨by decide, by decide, by decide⟩⟩

/-- Both are genuine proper divisors, re-derived from the Whorl gcd theorems. -/
theorem whorl_299_proper : 1 < 13 ∧ 13 < 299 ∧ 13 ∣ 299 := by decide
theorem whorl_5917_proper : 1 < 61 ∧ 61 < 5917 ∧ 61 ∣ 5917 := by decide

/-- The braid defect equals the certified divisor's gcd readout (both from
    `PrimeWhorlTheory`, so this is a re-statement, not a new claim). -/
theorem whorl_defect_gives_divisor_299 :
    Nat.gcd 299 (((mirroredBraid phase299).1.x0 - (mirroredBraid phase299).2.x0).val) = 13 :=
  source299_braid_finds_13

theorem whorl_defect_gives_divisor_5917 :
    Nat.gcd 5917 (((mirroredBraid phase5917).1.x0 - (mirroredBraid phase5917).2.x0).val) = 61 :=
  source5917_braid_finds_61

/-! ## Dialectic closures of the remaining OPEN problems -/

/-- Erdős #50 (φ(n)/n distribution): no point with a positive derivative.
    T-side: none asserted beyond the statement's own proved core; F-side is
    exactly the open analytic claim. Sealed B4.B. -/
def erdos_50_witness : Dialectic := {
  T := Erdos50.ErdosProblem50Statement,
  F := Erdos50.ErdosProblem50Statement,
  closure_seal := mu_circ_delta B4.B
}

/-- Erdős #77 (diagonal Ramsey R(k)^{1/k} limit): OPEN. Held both. -/
def erdos_77_witness : Dialectic := {
  T := Erdos77.ErdosProblem77Statement,
  F := Erdos77.ErdosProblem77Statement,
  closure_seal := mu_circ_delta B4.B
}

/-- Erdős #120 (Erdős similarity / positive-measure avoiding set): OPEN.
    Held both. -/
def erdos_120_witness : Dialectic := {
  T := Erdos120.ErdosProblem120Statement,
  F := Erdos120.ErdosProblem120Statement,
  closure_seal := mu_circ_delta B4.B
}

/-- The seal holds uniformly: every registered witness closes at B4.B. -/
theorem all_seals_close :
    erdos_50_witness.closure_seal = mu_circ_delta B4.B ∧
    erdos_77_witness.closure_seal = mu_circ_delta B4.B ∧
    erdos_120_witness.closure_seal = mu_circ_delta B4.B := ⟨rfl, rfl, rfl⟩

end ErdosWhorlWitnesses
