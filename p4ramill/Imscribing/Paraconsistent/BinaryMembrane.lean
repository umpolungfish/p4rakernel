
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

/-- The first proper factor divides the represented number. -/
theorem properFactorPair_left_dvd
    {N : Nat}
    (f : ProperFactorPair N) :
    f.P0 ∣ N := by
  refine ⟨f.P1, ?_⟩
  exact f.productClosure.symm

/-- The second proper factor divides the represented number. -/
theorem properFactorPair_right_dvd
    {N : Nat}
    (f : ProperFactorPair N) :
    f.P1 ∣ N := by
  refine ⟨f.P0, ?_⟩
  calc
    N = f.P0 * f.P1 :=
      f.productClosure.symm
    _ = f.P1 * f.P0 :=
      Nat.mul_comm _ _

/-- A proper factor is strictly smaller than its product. -/
theorem properFactorPair_left_lt_input
    {N : Nat}
    (f : ProperFactorPair N) :
    f.P0 < N := by
  have hp : 0 < f.P0 :=
    Nat.lt_trans (by decide : 0 < 1) f.left_nonunit
  calc
    f.P0 = f.P0 * 1 := by simp
    _ < f.P0 * f.P1 :=
      Nat.mul_lt_mul_of_pos_left f.right_nonunit hp
    _ = N :=
      f.productClosure

/-- The complementary proper factor is strictly smaller than its product. -/
theorem properFactorPair_right_lt_input
    {N : Nat}
    (f : ProperFactorPair N) :
    f.P1 < N := by
  have hp : 0 < f.P1 :=
    Nat.lt_trans (by decide : 0 < 1) f.right_nonunit
  calc
    f.P1 = 1 * f.P1 := by simp
    _ < f.P0 * f.P1 :=
      Nat.mul_lt_mul_of_pos_right f.left_nonunit hp
    _ = N :=
      f.productClosure

/--
Two nonunit natural-number factors have a product of at least four.
-/
theorem properFactorPair_input_ge_four
    {N : Nat}
    (f : ProperFactorPair N) :
    4 ≤ N := by
  have h0 : 2 ≤ f.P0 :=
    Nat.succ_le_iff.mpr f.left_nonunit
  have h1 : 2 ≤ f.P1 :=
    Nat.succ_le_iff.mpr f.right_nonunit
  calc
    4 = 2 * 2 := by decide
    _ ≤ f.P0 * f.P1 :=
      Nat.mul_le_mul h0 h1
    _ = N :=
      f.productClosure

/--
A proper factor pair certifies that its input is not prime.
-/
theorem properFactorPair_input_not_prime
    {N : Nat}
    (f : ProperFactorPair N) :
    ¬ Nat.Prime N := by
  intro hp
  rcases
      Nat.Prime.eq_one_or_self_of_dvd
        hp f.P0 (properFactorPair_left_dvd f) with hOne | hN
  · exact (Nat.ne_of_gt f.left_nonunit) hOne
  · exact
      (Nat.ne_of_lt
        (properFactorPair_left_lt_input f)) hN

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
A prime input cannot satisfy ENGAGR.

The GCD divides the prime input, so it must equal one or the
entire input. ENGAGR excludes both cases.
-/
theorem prime_input_not_engaged
    {N candidate : Nat}
    (hprime : Nat.Prime N) :
    ¬ paradoxCondition N candidate := by
  intro h
  rcases
      Nat.Prime.eq_one_or_self_of_dvd
        hprime (Nat.gcd candidate N)
        (gcd_divides_input N candidate) with hOne | hN
  · exact (Nat.ne_of_gt h.1) hOne
  · exact (Nat.ne_of_lt h.2) hN

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

/-! ## 4. GCD Identity and Greatest-Divisor Certificates -/

/-- The GCD factor divides the candidate as well as N. -/
theorem gcdVerified_left_dvd_candidate
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (gcdVerifiedPair N candidate h).P0 ∣ candidate := by
  change Nat.gcd candidate N ∣ candidate
  exact Nat.gcd_dvd_left candidate N

/--
Every common divisor of candidate and N divides the emitted GCD factor.
This certifies its greatest-common-divisor property.
-/
theorem gcdVerified_left_greatest
    (N candidate d : Nat)
    (h : paradoxCondition N candidate)
    (hdCandidate : d ∣ candidate)
    (hdN : d ∣ N) :
    d ∣ (gcdVerifiedPair N candidate h).P0 := by
  change d ∣ Nat.gcd candidate N
  exact Nat.dvd_gcd hdCandidate hdN

/-- The first GCD certificate component is the actual GCD. -/
theorem gcdVerified_left_eq_gcd
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (gcdVerifiedPair N candidate h).P0 =
      Nat.gcd candidate N := by
  rfl

/-! ## 5. Verified Factor Divisibility -/

/-- The first component of any verified pair divides N. -/
theorem verifiedFactorPair_left_dvd
    {N : Nat}
    (f : VerifiedFactorPair N) :
    f.P0 ∣ N := by
  refine ⟨f.P1, ?_⟩
  exact f.productClosure.symm

/-- The second component of any verified pair divides N. -/
theorem verifiedFactorPair_right_dvd
    {N : Nat}
    (f : VerifiedFactorPair N) :
    f.P1 ∣ N := by
  refine ⟨f.P0, ?_⟩
  calc
    N = f.P0 * f.P1 :=
      f.productClosure.symm
    _ = f.P1 * f.P0 :=
      Nat.mul_comm _ _

/-! ## 6. Exact Membrane Factor Selection -/

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

/-- Both selected factors divide N, including the fallback case. -/
theorem membraneFactors_divisibility
    (N candidate : Nat) :
    (membraneFactors N candidate).P0 ∣ N ∧
    (membraneFactors N candidate).P1 ∣ N := by
  constructor
  · exact verifiedFactorPair_left_dvd
      (membraneFactors N candidate)
  · exact verifiedFactorPair_right_dvd
      (membraneFactors N candidate)

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

/--
The membrane emits two nonunit factors exactly when ENGAGR succeeds.
-/
theorem membraneFactors_proper_iff
    (N candidate : Nat) :
    (1 < (membraneFactors N candidate).P0 ∧
     1 < (membraneFactors N candidate).P1)
      ↔ paradoxCondition N candidate := by
  constructor
  · intro hp
    by_contra h
    have hf := membraneFactors_fallback N candidate h
    rw [hf] at hp
    exact (Nat.lt_irrefl 1)
      (by simpa [unitFallback] using hp.2)
  · intro h
    exact membraneFactors_proper N candidate h

/-- Recover a `ProperFactorPair` from a successful membrane selection. -/
noncomputable def membraneProperPair
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    ProperFactorPair N := by
  let f := membraneFactors N candidate
  exact
    ⟨
      f.P0,
      f.P1,
      (membraneFactors_proper N candidate h).1,
      (membraneFactors_proper N candidate h).2,
      f.productClosure
    ⟩

/-- Both engaged factors are strictly smaller than their input N. -/
theorem membraneFactors_strict_bounds
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (membraneFactors N candidate).P0 < N ∧
    (membraneFactors N candidate).P1 < N := by
  let f := membraneProperPair N candidate h
  exact
    ⟨
      properFactorPair_left_lt_input f,
      properFactorPair_right_lt_input f
    ⟩

/-- Successful engagement forces the input to be at least four. -/
theorem membraneFactors_input_ge_four
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    4 ≤ N :=
  properFactorPair_input_ge_four
    (membraneProperPair N candidate h)

/-- Successful engagement certifies that N is not prime. -/
theorem membraneFactors_engaged_input_not_prime
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    ¬ Nat.Prime N :=
  properFactorPair_input_not_prime
    (membraneProperPair N candidate h)

/-- On engagement, the selected first factor divides the candidate. -/
theorem membraneFactors_engaged_left_dvd_candidate
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (membraneFactors N candidate).P0 ∣ candidate := by
  classical
  simpa [membraneFactors, h] using
    gcdVerified_left_dvd_candidate N candidate h

/--
The selected first factor retains the greatest-common-divisor property.
-/
theorem membraneFactors_engaged_left_greatest
    (N candidate d : Nat)
    (h : paradoxCondition N candidate)
    (hdCandidate : d ∣ candidate)
    (hdN : d ∣ N) :
    d ∣ (membraneFactors N candidate).P0 := by
  classical
  simpa [membraneFactors, h] using
    gcdVerified_left_greatest
      N candidate d h hdCandidate hdN

/-! ## 7. Complete Binary Membrane Output -/

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

/-! ## 8. Pipeline Certificates -/

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

/-- Both factors emitted by the complete pipeline divide N. -/
theorem runBinaryMembrane_factor_divisibility
    (N candidate : Nat) :
    (runBinaryMembrane N candidate).factors.P0 ∣ N ∧
    (runBinaryMembrane N candidate).factors.P1 ∣ N := by
  constructor
  · exact verifiedFactorPair_left_dvd
      (runBinaryMembrane N candidate).factors
  · exact verifiedFactorPair_right_dvd
      (runBinaryMembrane N candidate).factors

/-- Both engaged pipeline factors are strictly smaller than N. -/
theorem runBinaryMembrane_strict_factor_bounds
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (runBinaryMembrane N candidate).factors.P0 < N ∧
    (runBinaryMembrane N candidate).factors.P1 < N := by
  simpa [runBinaryMembrane] using
    membraneFactors_strict_bounds N candidate h

/-- Every engaged pipeline input is at least four. -/
theorem runBinaryMembrane_engaged_input_ge_four
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    4 ≤ N :=
  membraneFactors_input_ge_four N candidate h

/-- An engaged pipeline certifies that its input is not prime. -/
theorem runBinaryMembrane_engaged_input_not_prime
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    ¬ Nat.Prime N :=
  membraneFactors_engaged_input_not_prime N candidate h

theorem runBinaryMembrane_phase
    (N candidate : Nat) :
    PSystem.isGlut
      (runBinaryMembrane N candidate).phase
      ↔ paradoxCondition N candidate :=
  engagement_glut_iff N candidate

/--
A prime input cannot produce an ENGAGR glut.
-/
theorem runBinaryMembrane_prime_not_glut
    (N candidate : Nat)
    (hprime : Nat.Prime N) :
    ¬ PSystem.isGlut
        (runBinaryMembrane N candidate).phase := by
  rw [runBinaryMembrane_phase]
  exact prime_input_not_engaged hprime

/--
The complete pipeline reports a glut exactly when its factor pair
contains two nonunit factors.
-/
theorem runBinaryMembrane_proper_iff_engaged
    (N candidate : Nat) :
    (1 < (runBinaryMembrane N candidate).factors.P0 ∧
     1 < (runBinaryMembrane N candidate).factors.P1)
      ↔ PSystem.isGlut
          (runBinaryMembrane N candidate).phase := by
  exact
    (membraneFactors_proper_iff N candidate).trans
      (runBinaryMembrane_phase N candidate).symm

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

/--
Full engaged-state certificate:
glut phase, divisibility of both factors, nonunit factors,
and exact product closure.
-/
theorem runBinaryMembrane_engaged_certificate
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    PSystem.isGlut
      (runBinaryMembrane N candidate).phase ∧
    (runBinaryMembrane N candidate).factors.P0 ∣ N ∧
    (runBinaryMembrane N candidate).factors.P1 ∣ N ∧
    1 < (runBinaryMembrane N candidate).factors.P0 ∧
    1 < (runBinaryMembrane N candidate).factors.P1 ∧
    (runBinaryMembrane N candidate).factors.P0 *
      (runBinaryMembrane N candidate).factors.P1 = N := by
  exact
    ⟨
      (runBinaryMembrane_phase N candidate).2 h,
      (runBinaryMembrane_factor_divisibility N candidate).1,
      (runBinaryMembrane_factor_divisibility N candidate).2,
      (membraneFactors_proper N candidate h).1,
      (membraneFactors_proper N candidate h).2,
      runBinaryMembrane_factor_closure N candidate
    ⟩

/--
Extended engaged-state certificate:
both factors divide N, are strictly below N, are nonunits,
and multiply exactly to N.
-/
theorem runBinaryMembrane_engaged_proper_certificate
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    PSystem.isGlut
      (runBinaryMembrane N candidate).phase ∧
    (runBinaryMembrane N candidate).factors.P0 ∣ N ∧
    (runBinaryMembrane N candidate).factors.P1 ∣ N ∧
    1 < (runBinaryMembrane N candidate).factors.P0 ∧
    1 < (runBinaryMembrane N candidate).factors.P1 ∧
    (runBinaryMembrane N candidate).factors.P0 < N ∧
    (runBinaryMembrane N candidate).factors.P1 < N ∧
    (runBinaryMembrane N candidate).factors.P0 *
      (runBinaryMembrane N candidate).factors.P1 = N ∧
    4 ≤ N := by
  have hdiv :=
    runBinaryMembrane_factor_divisibility N candidate
  have hproper :=
    membraneFactors_proper N candidate h
  have hbounds :=
    runBinaryMembrane_strict_factor_bounds N candidate h
  exact
    ⟨
      (runBinaryMembrane_phase N candidate).2 h,
      hdiv.1,
      hdiv.2,
      hproper.1,
      hproper.2,
      hbounds.1,
      hbounds.2,
      runBinaryMembrane_factor_closure N candidate,
      runBinaryMembrane_engaged_input_ge_four N candidate h
    ⟩

/--
The engaged pipeline's first factor is the GCD of candidate and N:
it divides both, and every common divisor divides it.
-/
theorem runBinaryMembrane_engaged_gcd_certificate
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (runBinaryMembrane N candidate).factors.P0 ∣ candidate ∧
    (runBinaryMembrane N candidate).factors.P0 ∣ N ∧
    (∀ d : Nat, d ∣ candidate → d ∣ N →
      d ∣ (runBinaryMembrane N candidate).factors.P0) := by
  constructor
  · change (membraneFactors N candidate).P0 ∣ candidate
    exact membraneFactors_engaged_left_dvd_candidate
      N candidate h
  constructor
  · change (membraneFactors N candidate).P0 ∣ N
    exact (membraneFactors_divisibility N candidate).1
  · intro d hdc hdN
    change d ∣ (membraneFactors N candidate).P0
    exact membraneFactors_engaged_left_greatest
      N candidate d h hdc hdN

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

/-- Every prime input selects the exact unit fallback. -/
theorem runBinaryMembrane_prime_fallback
    (N candidate : Nat)
    (hprime : Nat.Prime N) :
    (runBinaryMembrane N candidate).factors.P0 = N ∧
    (runBinaryMembrane N candidate).factors.P1 = 1 :=
  runBinaryMembrane_unengaged N candidate
    (prime_input_not_engaged hprime)

theorem runBinaryMembrane_failed_candidate_closes
    (N candidate : Nat)
    (h : ¬ paradoxCondition N candidate) :
    (runBinaryMembrane N candidate).factors.P0 *
      (runBinaryMembrane N candidate).factors.P1 = N :=
  runBinaryMembrane_factor_closure N candidate

/-! ## 9. Binary Ground-State Reconstruction -/

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

/-! ## 10. Existential ENGAGR Characterization -/

/--
Any ENGAGR witness supplies a nontrivial factorization of N.
The GCD and its complementary quotient are the two factors.
-/
theorem engagement_implies_factorization
    (N : Nat)
    (h : ∃ candidate : Nat, paradoxCondition N candidate) :
    ∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N := by
  rcases h with ⟨candidate, hc⟩
  let f := gcdProperPair N candidate hc
  exact
    ⟨f.P0, f.P1,
      f.left_nonunit,
      f.right_nonunit,
      f.productClosure⟩

/--
Any nontrivial factorization of N supplies an ENGAGR witness.

Choose the first factor as candidate. Since it divides N,
the GCD of that candidate and N is the candidate itself.
-/
theorem factorization_implies_engagement
    (N : Nat)
    (h : ∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) :
    ∃ candidate : Nat, paradoxCondition N candidate := by
  rcases h with ⟨a, b, ha, hb, hab⟩
  refine ⟨a, ?_⟩

  have haN : a ∣ N := by
    exact ⟨b, hab.symm⟩

  have hgcd : Nat.gcd a N = a := by
    apply Nat.dvd_antisymm
    · exact Nat.gcd_dvd_left a N
    · exact Nat.dvd_gcd (dvd_refl a) haN

  have haPos : 0 < a :=
    Nat.lt_trans (by decide : 0 < 1) ha

  constructor
  · simpa [hgcd] using ha
  · rw [hgcd]
    calc
      a = a * 1 := by simp
      _ < a * b :=
        Nat.mul_lt_mul_of_pos_left hb haPos
      _ = N := hab

/--
Existence of an ENGAGR candidate is equivalent to a
nontrivial factorization of N.
-/
theorem exists_engagement_iff_factorization
    (N : Nat) :
    (∃ candidate : Nat, paradoxCondition N candidate) ↔
    (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) := by
  constructor
  · exact engagement_implies_factorization N
  · exact factorization_implies_engagement N

/--
Existence of a pipeline glut is equivalent to a nontrivial
factorization of N.
-/
theorem runBinaryMembrane_glut_exists_iff_factorization
    (N : Nat) :
    (∃ candidate : Nat,
      PSystem.isGlut
        (runBinaryMembrane N candidate).phase) ↔
    (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) := by
  constructor
  · rintro ⟨candidate, hglut⟩
    apply engagement_implies_factorization N
    exact
      ⟨candidate,
        (runBinaryMembrane_phase N candidate).1 hglut⟩
  · intro hfactor
    obtain ⟨candidate, hEng⟩ :=
      factorization_implies_engagement N hfactor
    exact
      ⟨candidate,
        (runBinaryMembrane_phase N candidate).2 hEng⟩

end Imscribing.Paraconsistent.BinaryMembrane
