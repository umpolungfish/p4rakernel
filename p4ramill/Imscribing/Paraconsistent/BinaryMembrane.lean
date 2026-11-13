
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

theorem properFactorPair_left_dvd
    {N : Nat}
    (f : ProperFactorPair N) :
    f.P0 ∣ N := by
  refine ⟨f.P1, ?_⟩
  exact f.productClosure.symm

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

theorem gcdVerified_left_dvd_candidate
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (gcdVerifiedPair N candidate h).P0 ∣ candidate := by
  change Nat.gcd candidate N ∣ candidate
  exact Nat.gcd_dvd_left candidate N

theorem gcdVerified_left_greatest
    (N candidate d : Nat)
    (h : paradoxCondition N candidate)
    (hdCandidate : d ∣ candidate)
    (hdN : d ∣ N) :
    d ∣ (gcdVerifiedPair N candidate h).P0 := by
  change d ∣ Nat.gcd candidate N
  exact Nat.dvd_gcd hdCandidate hdN

theorem gcdVerified_left_eq_gcd
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (gcdVerifiedPair N candidate h).P0 =
      Nat.gcd candidate N := by
  rfl

/-! ## 5. Verified Factor Divisibility -/

theorem verifiedFactorPair_left_dvd
    {N : Nat}
    (f : VerifiedFactorPair N) :
    f.P0 ∣ N := by
  refine ⟨f.P1, ?_⟩
  exact f.productClosure.symm

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

noncomputable def membraneFactors
    (N candidate : Nat) :
    VerifiedFactorPair N := by
  classical
  exact
    if h : paradoxCondition N candidate then
      gcdVerifiedPair N candidate h
    else
      unitFallback N

theorem membraneFactors_exact
    (N candidate : Nat) :
    (membraneFactors N candidate).P0 *
      (membraneFactors N candidate).P1 = N := by
  classical
  by_cases h : paradoxCondition N candidate
  · simpa [membraneFactors, h] using
      gcdVerified_exact N candidate h
  · simp [membraneFactors, h, unitFallback]

theorem membraneFactors_divisibility
    (N candidate : Nat) :
    (membraneFactors N candidate).P0 ∣ N ∧
    (membraneFactors N candidate).P1 ∣ N := by
  constructor
  · exact verifiedFactorPair_left_dvd
      (membraneFactors N candidate)
  · exact verifiedFactorPair_right_dvd
      (membraneFactors N candidate)

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

theorem membraneFactors_fallback
    (N candidate : Nat)
    (h : ¬ paradoxCondition N candidate) :
    membraneFactors N candidate = unitFallback N := by
  classical
  simp [membraneFactors, h]

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

theorem membraneFactors_input_ge_four
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    4 ≤ N :=
  properFactorPair_input_ge_four
    (membraneProperPair N candidate h)

theorem membraneFactors_engaged_input_not_prime
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    ¬ Nat.Prime N :=
  properFactorPair_input_not_prime
    (membraneProperPair N candidate h)

theorem membraneFactors_engaged_left_dvd_candidate
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (membraneFactors N candidate).P0 ∣ candidate := by
  classical
  simpa [membraneFactors, h] using
    gcdVerified_left_dvd_candidate N candidate h

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

theorem runBinaryMembrane_factor_divisibility
    (N candidate : Nat) :
    (runBinaryMembrane N candidate).factors.P0 ∣ N ∧
    (runBinaryMembrane N candidate).factors.P1 ∣ N := by
  constructor
  · exact verifiedFactorPair_left_dvd
      (runBinaryMembrane N candidate).factors
  · exact verifiedFactorPair_right_dvd
      (runBinaryMembrane N candidate).factors

theorem runBinaryMembrane_strict_factor_bounds
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (runBinaryMembrane N candidate).factors.P0 < N ∧
    (runBinaryMembrane N candidate).factors.P1 < N := by
  simpa [runBinaryMembrane] using
    membraneFactors_strict_bounds N candidate h

theorem runBinaryMembrane_engaged_input_ge_four
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    4 ≤ N :=
  membraneFactors_input_ge_four N candidate h

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

theorem runBinaryMembrane_prime_not_glut
    (N candidate : Nat)
    (hprime : Nat.Prime N) :
    ¬ PSystem.isGlut
        (runBinaryMembrane N candidate).phase := by
  rw [runBinaryMembrane_phase]
  exact prime_input_not_engaged hprime

theorem runBinaryMembrane_proper_iff_engaged
    (N candidate : Nat) :
    (1 < (runBinaryMembrane N candidate).factors.P0 ∧
     1 < (runBinaryMembrane N candidate).factors.P1)
      ↔ PSystem.isGlut
          (runBinaryMembrane N candidate).phase := by
  exact
    (membraneFactors_proper_iff N candidate).trans
      (runBinaryMembrane_phase N candidate).symm

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

theorem exists_engagement_iff_factorization
    (N : Nat) :
    (∃ candidate : Nat, paradoxCondition N candidate) ↔
    (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) := by
  constructor
  · exact engagement_implies_factorization N
  · exact factorization_implies_engagement N

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

/-! ## 11. Exact Factorization Realization -/

theorem membraneFactors_engaged_components
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (membraneFactors N candidate).P0 =
      Nat.gcd candidate N ∧
    (membraneFactors N candidate).P1 =
      N / Nat.gcd candidate N := by
  classical
  simp [membraneFactors, h, gcdVerifiedPair, gcdProperPair]

theorem runBinaryMembrane_engaged_components
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    (runBinaryMembrane N candidate).factors.P0 =
      Nat.gcd candidate N ∧
    (runBinaryMembrane N candidate).factors.P1 =
      N / Nat.gcd candidate N := by
  simpa [runBinaryMembrane] using
    membraneFactors_engaged_components N candidate h

theorem runBinaryMembrane_realizes_factorization
    (N a b : Nat)
    (ha : 1 < a)
    (hb : 1 < b)
    (hab : a * b = N) :
    (runBinaryMembrane N a).factors.P0 = a ∧
    (runBinaryMembrane N a).factors.P1 = b := by

  have haN : a ∣ N := by
    exact ⟨b, hab.symm⟩

  have hgcd : Nat.gcd a N = a := by
    apply Nat.dvd_antisymm
    · exact Nat.gcd_dvd_left a N
    · exact Nat.dvd_gcd (dvd_refl a) haN

  have haPos : 0 < a :=
    Nat.lt_trans (by decide : 0 < 1) ha

  have hquot : N / Nat.gcd a N = b := by
    rw [hgcd, ← hab]
    exact Nat.mul_div_cancel_left b haPos

  have hEng : paradoxCondition N a := by
    constructor
    · simpa [hgcd] using ha
    · rw [hgcd]
      calc
        a = a * 1 := by simp
        _ < a * b :=
          Nat.mul_lt_mul_of_pos_left hb haPos
        _ = N := hab

  have hcomponents :=
    runBinaryMembrane_engaged_components N a hEng

  constructor
  · calc
      (runBinaryMembrane N a).factors.P0 =
          Nat.gcd a N :=
        hcomponents.1
      _ = a := hgcd
  · calc
      (runBinaryMembrane N a).factors.P1 =
          N / Nat.gcd a N :=
        hcomponents.2
      _ = b := hquot

/-! ## 12. Bounded Witness Normalization -/

theorem gcd_normalization_engages
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    paradoxCondition N (Nat.gcd candidate N) := by

  have hgcd :
      Nat.gcd (Nat.gcd candidate N) N =
        Nat.gcd candidate N := by
    apply Nat.dvd_antisymm
    · exact Nat.gcd_dvd_left _ _
    · exact Nat.dvd_gcd
        (dvd_refl (Nat.gcd candidate N))
        (gcd_divides_input N candidate)

  constructor
  · simpa only [hgcd] using h.1
  · simpa only [hgcd] using h.2

theorem engagement_has_bounded_witness
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    ∃ normalizedCandidate : Nat,
      normalizedCandidate < N ∧
      paradoxCondition N normalizedCandidate := by
  exact
    ⟨
      Nat.gcd candidate N,
      h.2,
      gcd_normalization_engages N candidate h
    ⟩

theorem exists_engagement_iff_bounded_witness
    (N : Nat) :
    (∃ candidate : Nat, paradoxCondition N candidate) ↔
    (∃ candidate : Nat,
      candidate < N ∧ paradoxCondition N candidate) := by
  constructor
  · rintro ⟨candidate, h⟩
    exact engagement_has_bounded_witness N candidate h
  · rintro ⟨candidate, _hbound, h⟩
    exact ⟨candidate, h⟩

theorem runBinaryMembrane_glut_has_bounded_witness
    (N : Nat)
    (h :
      ∃ candidate : Nat,
        PSystem.isGlut
          (runBinaryMembrane N candidate).phase) :
    ∃ normalizedCandidate : Nat,
      normalizedCandidate < N ∧
      PSystem.isGlut
        (runBinaryMembrane N normalizedCandidate).phase := by

  rcases h with ⟨candidate, hglut⟩

  have heng :
      paradoxCondition N candidate :=
    (runBinaryMembrane_phase N candidate).1 hglut

  rcases
      engagement_has_bounded_witness N candidate heng with
    ⟨normalizedCandidate, hbound, hnormalized⟩

  exact
    ⟨
      normalizedCandidate,
      hbound,
      (runBinaryMembrane_phase N normalizedCandidate).2
        hnormalized
    ⟩

theorem runBinaryMembrane_glut_factor_is_normalized_witness
    (N candidate : Nat)
    (hglut :
      PSystem.isGlut
        (runBinaryMembrane N candidate).phase) :
    ∃ normalizedCandidate : Nat,
      normalizedCandidate < N ∧
      normalizedCandidate =
        (runBinaryMembrane N candidate).factors.P0 ∧
      PSystem.isGlut
        (runBinaryMembrane N normalizedCandidate).phase := by

  have heng :
      paradoxCondition N candidate :=
    (runBinaryMembrane_phase N candidate).1 hglut

  refine
    ⟨
      Nat.gcd candidate N,
      heng.2,
      ?_,
      ?_
    ⟩

  · exact
      (runBinaryMembrane_engaged_components
        N candidate heng).1.symm

  · exact
      (runBinaryMembrane_phase
        N (Nat.gcd candidate N)).2
        (gcd_normalization_engages N candidate heng)

/-! ## 13. Executable Bounded Candidate Search -/

/--
A Boolean decision procedure for ENGAGR, expressed directly
as two decidable natural-number comparisons.
-/
def engagementTest (N candidate : Nat) : Bool :=
  decide (1 < Nat.gcd candidate N) &&
    decide (Nat.gcd candidate N < N)

/-- The Boolean test agrees with the proposition ENGAGR. -/
theorem engagementTest_correct
    (N candidate : Nat) :
    engagementTest N candidate = true ↔
      paradoxCondition N candidate := by
  simp [engagementTest, paradoxCondition]

/--
The finite list of all candidates below N satisfying ENGAGR.
-/
def engagementCandidates (N : Nat) : List Nat :=
  (List.range N).filter (engagementTest N)

/-- Membership in the candidate list is exactly bounded ENGAGR. -/
theorem engagementCandidates_mem_iff
    (N candidate : Nat) :
    candidate ∈ engagementCandidates N ↔
      candidate < N ∧ paradoxCondition N candidate := by
  simp [engagementCandidates, engagementTest_correct]

/--
Return the first successful candidate, or none when no
candidate below N satisfies ENGAGR.
-/
def engagementSearch (N : Nat) : Option Nat :=
  (engagementCandidates N).head?

/-- Every returned candidate satisfies ENGAGR. -/
theorem engagementSearch_sound
    (N candidate : Nat)
    (hsearch : engagementSearch N = some candidate) :
    candidate < N ∧ paradoxCondition N candidate := by

  cases he : engagementCandidates N with
  | nil =>
      simp [engagementSearch, he] at hsearch
  | cons first rest =>
      have hfirst : first = candidate := by
        simpa [engagementSearch, he] using hsearch
      subst candidate
      exact
        (engagementCandidates_mem_iff N first).mp
          (by simp [he])

/--
The search returns a candidate exactly when an ENGAGR
candidate exists.
-/
theorem engagementSearch_success_iff_engagement
    (N : Nat) :
    (∃ candidate : Nat,
      engagementSearch N = some candidate) ↔
    (∃ candidate : Nat, paradoxCondition N candidate) := by

  constructor
  · rintro ⟨candidate, hsearch⟩
    exact
      ⟨candidate,
        (engagementSearch_sound N candidate hsearch).2⟩

  · rintro ⟨candidate, hc⟩
    obtain ⟨bounded, hbound, hb⟩ :=
      engagement_has_bounded_witness N candidate hc

    have hmem : bounded ∈ engagementCandidates N :=
      (engagementCandidates_mem_iff N bounded).2
        ⟨hbound, hb⟩

    cases he : engagementCandidates N with
    | nil =>
        simp [he] at hmem
    | cons first rest =>
        exact ⟨first, by simp [engagementSearch, he]⟩

/--
The executable search succeeds exactly when N has a
nontrivial factorization.
-/
theorem engagementSearch_success_iff_factorization
    (N : Nat) :
    (∃ candidate : Nat,
      engagementSearch N = some candidate) ↔
    (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) :=
  (engagementSearch_success_iff_engagement N).trans
    (exists_engagement_iff_factorization N)

/--
Every returned search result carries its pipeline certificate:
bounded candidate, ENGAGR, glut state, and exact GCD factors.
-/
theorem engagementSearch_pipeline_certificate
    (N candidate : Nat)
    (hsearch : engagementSearch N = some candidate) :
    candidate < N ∧
    paradoxCondition N candidate ∧
    PSystem.isGlut
      (runBinaryMembrane N candidate).phase ∧
    (runBinaryMembrane N candidate).factors.P0 =
      Nat.gcd candidate N ∧
    (runBinaryMembrane N candidate).factors.P1 =
      N / Nat.gcd candidate N := by

  have hs :=
    engagementSearch_sound N candidate hsearch

  have hf :=
    runBinaryMembrane_engaged_components N candidate hs.2

  exact
    ⟨
      hs.1,
      hs.2,
      (runBinaryMembrane_phase N candidate).2 hs.2,
      hf.1,
      hf.2
    ⟩

/-- An unsuccessful exhaustive search means no nontrivial factorization exists. -/
theorem engagementSearch_none_iff_no_factorization
    (N : Nat) :
    engagementSearch N = none ↔
    ¬ (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) := by

  constructor
  · intro hnone hfactor
    obtain ⟨candidate, hsearch⟩ :=
      (engagementSearch_success_iff_factorization N).2 hfactor
    rw [hnone] at hsearch
    cases hsearch

  · intro hno
    by_contra hsome
    cases hs : engagementSearch N with
    | none =>
        exact hsome hs
    | some candidate =>
        apply hno
        exact
          (engagementSearch_success_iff_factorization N).1
            ⟨candidate, hs⟩

end Imscribing.Paraconsistent.BinaryMembrane
