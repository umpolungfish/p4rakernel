import Imscribing.Paraconsistent.Monism

namespace Imscribing.Paraconsistent.PSystem

open Imscribing.Paraconsistent.Monism

/-!
# Gödel-Complete P-System Catalytic Membrane

Three independent invariants:

1. Dissolution/fusion: μ ∘ δ = id.
2. Arithmetic closure: P₀ * P₁ = N.
3. Dialetheic engagement: 1 < gcd(c,N) < N.

Only exactly verified factor pairs can be emitted.
The exhausted-search fallback is (N,1).
-/

/-! ## 1. Catalytic Membrane Instruction Alphabet -/

inductive MembraneToken where
  | VINIT
  | FSPLIT
  | EVALT
  | AFWD
  | EVALF
  | AREV
  | CLINK
  | IMSCRIB
  | ENGAGR
  | FFUSE
  | IFIX
  | TANCH
  deriving DecidableEq, Repr

def membraneProgram : List MembraneToken :=
  [
    .VINIT,
    .FSPLIT,
    .EVALT,
    .AFWD,
    .CLINK,
    .IMSCRIB,
    .EVALF,
    .AREV,
    .CLINK,
    .ENGAGR,
    .FFUSE,
    .IFIX,
    .TANCH
  ]

/-! ## 2. Multi-Limb Carrier -/

structure MembraneCarrier where
  value : Nat
  evenLane : Nat
  oddLane : Nat

def carrierValue (C : MembraneCarrier) : Nat :=
  C.value

/-! ## 3. Gödel Dissolution and Fusion -/

structure GodelDissolution where
  delta : Nat → Nat × Nat
  mu : Nat × Nat → Nat
  fixedPoint : ∀ N, mu (delta N) = N

theorem dissolution_fusion_identity
    (D : GodelDissolution) (N : Nat) :
    D.mu (D.delta N) = N :=
  D.fixedPoint N

def dissolveEven
    (D : GodelDissolution) (N : Nat) : Nat :=
  (D.delta N).1

def dissolveOdd
    (D : GodelDissolution) (N : Nat) : Nat :=
  (D.delta N).2

theorem channel_recombination
    (D : GodelDissolution) (N : Nat) :
    D.mu (dissolveEven D N, dissolveOdd D N) = N := by
  exact D.fixedPoint N

/-! ## 4. Belnap FOUR Catalytic Engagement -/

def paradoxCondition
    (N candidate : Nat) : Prop :=
  1 < Nat.gcd candidate N ∧
  Nat.gcd candidate N < N

def isGlut : Belnap4 → Prop
  | .B => True
  | _ => False

/--
ENGAGR: a nontrivial gcd engages the Belnap glut state.
Classical decidability is used for the proposition-valued
gcd condition.
-/
noncomputable def engagementState
    (N candidate : Nat) : Belnap4 := by
  classical
  exact if paradoxCondition N candidate then
    Belnap4.B
  else
    Belnap4.T

theorem engagement_glut_iff
    (N candidate : Nat) :
    isGlut (engagementState N candidate) ↔
      paradoxCondition N candidate := by
  classical
  unfold engagementState isGlut
  by_cases h : paradoxCondition N candidate
  · simp [h]
  · simp [h]

/-! ## 5. Exact Arithmetic Factor Certification -/

structure VerifiedFactorPair (N : Nat) where
  P0 : Nat
  P1 : Nat
  productClosure : P0 * P1 = N

/-- Unit fallback: (N,1). -/
def unitFallback (N : Nat) : VerifiedFactorPair N :=
  ⟨N, 1, by simp⟩

/-- Accept only candidates satisfying exact product closure. -/
def certifyCandidate
    (N P0 P1 : Nat) :
    Option (VerifiedFactorPair N) :=
  if h : P0 * P1 = N then
    some ⟨P0, P1, h⟩
  else
    none

/--
TANCH-safe factorization. An unverified candidate is replaced
by the exact unit fallback.
-/
def factorizeMembrane
    (N P0 P1 : Nat) :
    VerifiedFactorPair N :=
  match certifyCandidate N P0 P1 with
  | some certified => certified
  | none => unitFallback N

theorem factorizeMembrane_exact
    (N P0 P1 : Nat) :
    (factorizeMembrane N P0 P1).P0 *
      (factorizeMembrane N P0 P1).P1 = N :=
  (factorizeMembrane N P0 P1).productClosure

theorem unitFallback_exact
    (N : Nat) :
    (unitFallback N).P0 *
      (unitFallback N).P1 = N :=
  (unitFallback N).productClosure

theorem factorizeMembrane_preserves_verified
    (N P0 P1 : Nat)
    (h : P0 * P1 = N) :
    (factorizeMembrane N P0 P1).P0 = P0 ∧
    (factorizeMembrane N P0 P1).P1 = P1 := by
  unfold factorizeMembrane certifyCandidate
  simp [h]

/-! ## 6. Sub-Braid Fission -/

structure MembraneFission (N : Nat) where
  left : Nat
  right : Nat
  closure : left * right = N

def verifiedFission
    {N : Nat}
    (F : VerifiedFactorPair N) :
    MembraneFission N :=
  ⟨F.P0, F.P1, F.productClosure⟩

theorem fission_closure
    {N : Nat}
    (F : VerifiedFactorPair N) :
    (verifiedFission F).left *
      (verifiedFission F).right = N :=
  (verifiedFission F).closure

/-! ## 7. Complete Membrane Output -/

structure MembraneOutput (N : Nat) where
  factors : VerifiedFactorPair N
  phase : Belnap4

theorem membraneOutput_exact
    {N : Nat}
    (O : MembraneOutput N) :
    O.factors.P0 * O.factors.P1 = N :=
  O.factors.productClosure

/-! ## 8. The 200-Bit Ground State -/

def groundN : Nat :=
  836395761902793056162479809868390235450428133654496069409301

def groundP0 : Nat :=
  666185598226847594194227635071

def groundP1 : Nat :=
  1255499614715456501136337665131

theorem groundN_200bit :
    2 ^ 199 ≤ groundN ∧ groundN < 2 ^ 200 := by
  norm_num [groundN]

theorem groundState_product :
    groundP0 * groundP1 = groundN := by
  norm_num [groundP0, groundP1, groundN]

def groundStateCertificate :
    VerifiedFactorPair groundN :=
  ⟨groundP0, groundP1, groundState_product⟩

theorem groundState_membrane_closure :
    groundStateCertificate.P0 *
      groundStateCertificate.P1 = groundN :=
  groundStateCertificate.productClosure

theorem groundFactors_100bit :
    2 ^ 99 ≤ groundP0 ∧
      groundP0 < 2 ^ 100 ∧
      2 ^ 99 ≤ groundP1 ∧
      groundP1 < 2 ^ 100 := by
  norm_num [groundP0, groundP1]

/-! ## 9. SHIAB Lane Arithmetic Distinction -/

def groundGamma : Nat :=
  271543419960962953386408061383

def groundLambda : Nat :=
  671970186203967394530730017456

/-- The lanes are not themselves the arithmetic factor pair. -/
theorem ground_lanes_not_arithmetic_factors :
    groundGamma * groundLambda ≠ groundN := by
  norm_num [groundGamma, groundLambda, groundN]

/-! ## 10. Fallback Verification -/

theorem failed_candidate_uses_fallback
    (N P0 P1 : Nat)
    (h : P0 * P1 ≠ N) :
    factorizeMembrane N P0 P1 = unitFallback N := by
  simp [factorizeMembrane, certifyCandidate, h]

theorem failed_search_still_closes
    (N P0 P1 : Nat)
    (h : P0 * P1 ≠ N) :
    (factorizeMembrane N P0 P1).P0 *
      (factorizeMembrane N P0 P1).P1 = N :=
  factorizeMembrane_exact N P0 P1

end Imscribing.Paraconsistent.PSystem