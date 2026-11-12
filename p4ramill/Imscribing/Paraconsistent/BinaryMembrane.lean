import Imscribing.Paraconsistent.PSystem

namespace Imscribing.Paraconsistent.BinaryMembrane

open Imscribing.Paraconsistent.Monism
open Imscribing.Paraconsistent.PSystem

/-!
# Binary Catalytic Membrane Integration

FSPLIT:
  δ(N) = (N mod 2, N / 2)

FFUSE:
  μ(b,q) = 2q + b

IMSCRIB:
  μ ∘ δ = id

ENGAGR:
  1 < gcd(candidate,N) < N

IFIX:
  Produce exact arithmetic factor certificates.

TANCH:
  Every emitted pair satisfies P0 * P1 = N.

No sorry, admit, or placeholder axioms.
-/

/-! ## 1. Binary Dissolution and Fusion -/

def binarySplit (N : Nat) : Nat × Nat :=
  (N % 2, N / 2)

def binaryFuse (lanes : Nat × Nat) : Nat :=
  2 * lanes.2 + lanes.1

theorem binaryRoundTrip (N : Nat) :
    binaryFuse (binarySplit N) = N := by
  unfold binaryFuse binarySplit
  calc
    2 * (N / 2) + N % 2 =
        N % 2 + 2 * (N / 2) :=
      Nat.add_comm _ _
    _ = N :=
      Nat.mod_add_div N 2

def binaryDissolution : GodelDissolution where
  delta := binarySplit
  mu := binaryFuse
  fixedPoint := binaryRoundTrip

theorem binary_imscrib_identity (N : Nat) :
    binaryDissolution.mu
      (binaryDissolution.delta N) = N :=
  binaryDissolution.fixedPoint N

/-! ## 2. Binary Channel Readout -/

def binaryEvenChannel (N : Nat) : Nat :=
  (binarySplit N).1

def binaryOddChannel (N : Nat) : Nat :=
  (binarySplit N).2

theorem binaryEvenChannel_bound (N : Nat) :
    binaryEvenChannel N < 2 := by
  unfold binaryEvenChannel binarySplit
  exact Nat.mod_lt N (by decide)

theorem binaryChannel_recombination (N : Nat) :
    binaryFuse
      (binaryEvenChannel N, binaryOddChannel N) = N :=
  binaryRoundTrip N

/-! ## 3. Proper GCD Factorization -/

structure ProperFactorPair (N : Nat) where
  P0 : Nat
  P1 : Nat
  left_nonunit : 1 < P0
  right_nonunit : 1 < P1
  productClosure : P0 * P1 = N

theorem gcd_divides_input
    (N candidate : Nat) :
    Nat.gcd candidate N ∣ N :=
  Nat.gcd_dvd_right candidate N

theorem gcd_quotient_product
    (N candidate : Nat) :
    Nat.gcd candidate N *
      (N / Nat.gcd candidate N) = N := by
  exact Nat.mul_div_cancel'
    (gcd_divides_input N candidate)

/--
A proper gcd has a complementary quotient strictly greater than one.
The proof separates the two possible quotients 0 and 1.
-/
theorem gcd_complement_gt_one
    (N candidate : Nat)
    (hlt : Nat.gcd candidate N < N)
    (hg : 1 < Nat.gcd candidate N) :
    1 < N / Nat.gcd candidate N := by

  let g := Nat.gcd candidate N
  let q := N / g

  have hgpos : 0 < g :=
    Nat.lt_trans (by decide : 0 < 1) hg

  have hNpos : 0 < N :=
    Nat.lt_trans hgpos hlt

  have hprod : g * q = N := by
    dsimp [g, q]
    exact gcd_quotient_product N candidate

  have hqpos : 0 < q := by
    by_contra hq
    have hqzero : q = 0 :=
      Nat.eq_zero_of_not_pos hq
    have hNzero : N = 0 := by
      calc
        N = g * q := hprod.symm
        _ = 0 := by rw [hqzero, Nat.mul_zero]
    exact (Nat.ne_of_gt hNpos) hNzero

  by_cases hq : 1 < q
  · exact hq
  · have hqle : q ≤ 1 :=
      Nat.le_of_not_gt hq
    have hqge : 1 ≤ q :=
      Nat.succ_le_iff.mpr hqpos
    have hqeq : q = 1 :=
      Nat.le_antisymm hqle hqge
    have hge : g = N := by
      calc
        g = g * q := by rw [hqeq]; simp
        _ = N := hprod
    exact False.elim ((Nat.ne_of_lt hlt) hge)
/-- Extract two proper factors from an ENGAGR gcd. -/
def gcdProperPair
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    ProperFactorPair N := by

  have hg : 1 < Nat.gcd candidate N := h.1
  have hlt : Nat.gcd candidate N < N := h.2

  have hquot :
      1 < N / Nat.gcd candidate N :=
    gcd_complement_gt_one N candidate hlt hg

  have hprod :
      Nat.gcd candidate N *
        (N / Nat.gcd candidate N) = N :=
    gcd_quotient_product N candidate

  exact
    ⟨Nat.gcd candidate N,
     N / Nat.gcd candidate N,
     hg,
     hquot,
     hprod⟩

/-- Convert proper GCD factors into the membrane certificate. -/
def gcdVerifiedPair
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    VerifiedFactorPair N :=
  ⟨
    (gcdProperPair N candidate h).P0,
    (gcdProperPair N candidate h).P1,
    (gcdProperPair N candidate h).productClosure
  ⟩

theorem gcdVerified_left_nonunit
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    1 < (gcdVerifiedPair N candidate h).P0 :=
  (gcdProperPair N candidate h).left_nonunit

theorem gcdVerified_right_nonunit
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    1 < (gcdVerifiedPair N candidate h).P1 :=
  (gcdProperPair N candidate h).right_nonunit

theorem gcdVerified_exact
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (gcdVerifiedPair N candidate h).P0 *
      (gcdVerifiedPair N candidate h).P1 = N :=
  (gcdProperPair N candidate h).productClosure

/-! ## 4. Exact Membrane Factor Selection -/

def unitFallback (N : Nat) : VerifiedFactorPair N :=
  ⟨N, 1, by simp⟩

/--
Use proper GCD factors when ENGAGR succeeds.
Otherwise preserve exact closure with the unit fallback.
-/
noncomputable def membraneFactors
    (N candidate : Nat) :
    VerifiedFactorPair N := by
  classical
  exact
    if h : paradoxCondition N candidate then
      gcdVerifiedPair N candidate h
    else
      unitFallback N

/-- Every factor selection has exact product closure. -/
theorem membraneFactors_exact
    (N candidate : Nat) :
    (membraneFactors N candidate).P0 *
      (membraneFactors N candidate).P1 = N := by
  classical
  by_cases h : paradoxCondition N candidate
  · simpa [membraneFactors, h] using
      gcdVerified_exact N candidate h
  · simp [membraneFactors, h, unitFallback]

/-- Successful engagement produces two nonunit factors. -/
theorem membraneFactors_proper
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    1 < (membraneFactors N candidate).P0 ∧
    1 < (membraneFactors N candidate).P1 := by
  classical
  simpa [membraneFactors, h] using
    And.intro
      (gcdVerified_left_nonunit N candidate h)
      (gcdVerified_right_nonunit N candidate h)

/-- An unsuccessful engagement selects the unit fallback. -/
theorem membraneFactors_fallback
    (N candidate : Nat)
    (h : ¬ paradoxCondition N candidate) :
    membraneFactors N candidate = unitFallback N := by
  classical
  simp [membraneFactors, h]

/-! ## 5. Complete Binary Membrane Output -/

structure BinaryMembraneOutput (N : Nat) where
  evenLane : Nat
  oddLane : Nat
  binaryClosure :
    binaryFuse (evenLane, oddLane) = N
  factors : VerifiedFactorPair N
  phase : Belnap4

noncomputable def runBinaryMembrane
    (N candidate : Nat) :
    BinaryMembraneOutput N :=
  {
    evenLane := binaryEvenChannel N
    oddLane := binaryOddChannel N
    binaryClosure := binaryChannel_recombination N
    factors := membraneFactors N candidate
    phase := engagementState N candidate
  }

/-! ## 6. Pipeline Certificates -/

theorem runBinaryMembrane_reconstruct
    (N candidate : Nat) :
    binaryFuse
      ((runBinaryMembrane N candidate).evenLane,
       (runBinaryMembrane N candidate).oddLane) = N :=
  (runBinaryMembrane N candidate).binaryClosure

theorem runBinaryMembrane_factor_closure
    (N candidate : Nat) :
    (runBinaryMembrane N candidate).factors.P0 *
      (runBinaryMembrane N candidate).factors.P1 = N :=
  (runBinaryMembrane N candidate).factors.productClosure

theorem runBinaryMembrane_phase
    (N candidate : Nat) :
    PSystem.isGlut
      (runBinaryMembrane N candidate).phase
      ↔ paradoxCondition N candidate :=
  engagement_glut_iff N candidate

/-- Successful ENGAGR produces proper certified factors. -/
theorem runBinaryMembrane_engaged
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    PSystem.isGlut
      (runBinaryMembrane N candidate).phase ∧
    1 < (runBinaryMembrane N candidate).factors.P0 ∧
    1 < (runBinaryMembrane N candidate).factors.P1 ∧
    (runBinaryMembrane N candidate).factors.P0 *
      (runBinaryMembrane N candidate).factors.P1 = N := by
  constructor
  · exact (runBinaryMembrane_phase N candidate).2 h
  constructor
  · exact (membraneFactors_proper N candidate h).1
  constructor
  · exact (membraneFactors_proper N candidate h).2
  · exact runBinaryMembrane_factor_closure N candidate

theorem runBinaryMembrane_unengaged
    (N candidate : Nat)
    (h : ¬ paradoxCondition N candidate) :
    (runBinaryMembrane N candidate).factors.P0 = N ∧
    (runBinaryMembrane N candidate).factors.P1 = 1 := by
  change
    (membraneFactors N candidate).P0 = N ∧
    (membraneFactors N candidate).P1 = 1
  rw [membraneFactors_fallback N candidate h]
  constructor <;> rfl

theorem runBinaryMembrane_failed_candidate_closes
    (N candidate : Nat)
    (h : ¬ paradoxCondition N candidate) :
    (runBinaryMembrane N candidate).factors.P0 *
      (runBinaryMembrane N candidate).factors.P1 = N :=
  runBinaryMembrane_factor_closure N candidate

/-! ## 7. Binary Ground-State Reconstruction -/

def binaryGroundN : Nat :=
  836395761902793056162479809868390235450428133654496069409301

def binaryGroundEven : Nat :=
  binaryEvenChannel binaryGroundN

def binaryGroundOdd : Nat :=
  binaryOddChannel binaryGroundN

theorem binaryGround_reconstruction :
    binaryFuse
      (binaryGroundEven, binaryGroundOdd) =
        binaryGroundN :=
  binaryChannel_recombination binaryGroundN

theorem binaryGround_even_bound :
    binaryGroundEven < 2 :=
  binaryEvenChannel_bound binaryGroundN

end Imscribing.Paraconsistent.BinaryMembrane