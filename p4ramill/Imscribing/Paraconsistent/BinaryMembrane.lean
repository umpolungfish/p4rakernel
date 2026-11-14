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

/-- Boolean decision procedure for ENGAGR. -/
def engagementTest (N candidate : Nat) : Bool :=
  decide (1 < Nat.gcd candidate N) &&
    decide (Nat.gcd candidate N < N)

theorem engagementTest_correct
    (N candidate : Nat) :
    engagementTest N candidate = true ↔
      paradoxCondition N candidate := by
  simp [engagementTest, paradoxCondition]

/-- All successful candidates below N, in ascending order. -/
def engagementCandidates (N : Nat) : List Nat :=
  (List.range N).filter (engagementTest N)

theorem engagementCandidates_mem_iff
    (N candidate : Nat) :
    candidate ∈ engagementCandidates N ↔
      candidate < N ∧ paradoxCondition N candidate := by
  simp [engagementCandidates, engagementTest_correct]

/-- Return the first successful candidate, or none. -/
def engagementSearch (N : Nat) : Option Nat :=
  (engagementCandidates N).head?

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

theorem engagementSearch_success_iff_factorization
    (N : Nat) :
    (∃ candidate : Nat,
      engagementSearch N = some candidate) ↔
    (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) :=
  (engagementSearch_success_iff_engagement N).trans
    (exists_engagement_iff_factorization N)

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

/-! ## 14. GCD Normalization as an Idempotent Projection -/

/-- Canonical normalization sends any candidate to its GCD with N. -/
def normalizeCandidate (N candidate : Nat) : Nat :=
  Nat.gcd candidate N

/-- Normalization is idempotent. -/
theorem normalizeCandidate_idempotent
    (N candidate : Nat) :
    normalizeCandidate N
      (normalizeCandidate N candidate) =
        normalizeCandidate N candidate := by
  change
    Nat.gcd (Nat.gcd candidate N) N =
      Nat.gcd candidate N
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · exact Nat.dvd_gcd
      (dvd_refl (Nat.gcd candidate N))
      (Nat.gcd_dvd_right candidate N)

/--
A candidate is a fixed point of normalization exactly when
it divides N.
-/
theorem normalizeCandidate_eq_self_iff_dvd
    (N candidate : Nat) :
    normalizeCandidate N candidate = candidate ↔
      candidate ∣ N := by
  change Nat.gcd candidate N = candidate ↔
    candidate ∣ N
  constructor
  · intro h
    rw [← h]
    exact Nat.gcd_dvd_right candidate N
  · intro hdiv
    apply Nat.dvd_antisymm
    · exact Nat.gcd_dvd_left candidate N
    · exact Nat.dvd_gcd (dvd_refl candidate) hdiv

/-- Normalization always produces a divisor of N. -/
theorem normalizeCandidate_divides_input
    (N candidate : Nat) :
    normalizeCandidate N candidate ∣ N :=
  Nat.gcd_dvd_right candidate N

/-- Every normalized candidate is a fixed point. -/
theorem normalizeCandidate_fixed_point
    (N candidate : Nat) :
    normalizeCandidate N
      (normalizeCandidate N candidate) =
        normalizeCandidate N candidate :=
  normalizeCandidate_idempotent N candidate

/--
A normalized engagement is a proper divisor of N together with
the nonunit and strict-bound certificates.
-/
structure NormalizedEngagement (N : Nat) where
  candidate : Nat
  dividesInput : candidate ∣ N
  nonunit : 1 < candidate
  proper : candidate < N

/--
Convert any successful ENGAGR witness into its canonical
normalized-divisor representation.
-/
def normalizedEngagementOfWitness
    (N candidate : Nat)
    (h : paradoxCondition N candidate) :
    NormalizedEngagement N :=
  ⟨
    normalizeCandidate N candidate,
    normalizeCandidate_divides_input N candidate,
    by
      simpa [normalizeCandidate] using h.1,
    by
      simpa [normalizeCandidate] using h.2
  ⟩

/--
Every normalized engagement is already fixed by GCD normalization.
-/
theorem normalizedEngagement_fixed
    (N : Nat)
    (w : NormalizedEngagement N) :
    normalizeCandidate N w.candidate = w.candidate :=
  (normalizeCandidate_eq_self_iff_dvd N w.candidate).2
    w.dividesInput

/--
A normalized proper divisor is itself an ENGAGR candidate.
-/
theorem normalizedEngagement_engages
    (N : Nat)
    (w : NormalizedEngagement N) :
    paradoxCondition N w.candidate := by

  have hfixed :
      Nat.gcd w.candidate N = w.candidate := by
    exact
      (normalizeCandidate_eq_self_iff_dvd N w.candidate).2
        w.dividesInput

  change
    1 < Nat.gcd w.candidate N ∧
    Nat.gcd w.candidate N < N

  rw [hfixed]
  exact ⟨w.nonunit, w.proper⟩

/--
An ENGAGR candidate exists exactly when the normalized
proper-divisor space is inhabited.
-/
theorem exists_engagement_iff_normalized_divisor
    (N : Nat) :
    (∃ candidate : Nat, paradoxCondition N candidate) ↔
    Nonempty (NormalizedEngagement N) := by
  constructor
  · rintro ⟨candidate, h⟩
    exact ⟨normalizedEngagementOfWitness N candidate h⟩
  · rintro ⟨w⟩
    exact ⟨w.candidate, normalizedEngagement_engages N w⟩

/--
Existence of an ENGAGR witness is equivalent to existence
of a proper divisor strictly between 1 and N.
-/
theorem exists_engagement_iff_proper_divisor
    (N : Nat) :
    (∃ candidate : Nat, paradoxCondition N candidate) ↔
    (∃ d : Nat, d ∣ N ∧ 1 < d ∧ d < N) := by
  constructor
  · rintro ⟨candidate, h⟩
    let w := normalizedEngagementOfWitness N candidate h
    exact
      ⟨w.candidate, w.dividesInput, w.nonunit, w.proper⟩
  · rintro ⟨d, hd, hdgt, hdlt⟩
    have hfixed : Nat.gcd d N = d :=
      (normalizeCandidate_eq_self_iff_dvd N d).2 hd
    refine ⟨d, ?_⟩
    change 1 < Nat.gcd d N ∧ Nat.gcd d N < N
    rw [hfixed]
    exact ⟨hdgt, hdlt⟩

/--
The normalized-divisor representation is equivalent to
the existence of a pipeline glut.
-/
theorem runBinaryMembrane_glut_exists_iff_normalized_divisor
    (N : Nat) :
    (∃ candidate : Nat,
      PSystem.isGlut
        (runBinaryMembrane N candidate).phase) ↔
    Nonempty (NormalizedEngagement N) := by
  rw [← exists_engagement_iff_normalized_divisor]
  constructor
  · rintro ⟨candidate, hglut⟩
    exact
      ⟨candidate,
        (runBinaryMembrane_phase N candidate).1 hglut⟩
  · rintro ⟨candidate, heng⟩
    exact
      ⟨candidate,
        (runBinaryMembrane_phase N candidate).2 heng⟩

/-! ## 15. Square-Root-Bounded 6k ± 1 Wheel Search -/

/--
Every proper factorization has a nonunit factor no larger than
the square root of the input.
-/
theorem factorization_has_small_divisor
    (N a b : Nat)
    (ha : 1 < a)
    (hb : 1 < b)
    (hab : a * b = N) :
    ∃ d : Nat,
      d ≤ Nat.sqrt N ∧
      1 < d ∧
      d ∣ N := by
  by_cases hable : a ≤ b
  · have hsq : a * a ≤ N := by
      calc
        a * a ≤ a * b :=
          Nat.mul_le_mul_left a hable
        _ = N := hab
    refine ⟨a, Nat.le_sqrt.mpr hsq, ha, ?_⟩
    exact ⟨b, hab.symm⟩
  · have hba : b ≤ a := by omega
    have hsq : b * b ≤ N := by
      calc
        b * b ≤ a * b :=
          Nat.mul_le_mul_right b hba
        _ = N := hab
    refine ⟨b, Nat.le_sqrt.mpr hsq, hb, ?_⟩
    refine ⟨a, ?_⟩
    calc
      N = a * b := hab.symm
      _ = b * a := Nat.mul_comm _ _

/--
The finite specification of the reduced search domain:
nonunit divisors no larger than sqrt N.
-/
def divisorEngagementDivisors (N : Nat) : Finset Nat :=
  (Finset.range (Nat.sqrt N + 1)).filter
    (fun d => 1 < d ∧ d ∣ N)

theorem divisorEngagementDivisors_mem_iff
    (N d : Nat) :
    d ∈ divisorEngagementDivisors N ↔
      d ≤ Nat.sqrt N ∧ 1 < d ∧ d ∣ N := by
  simp [divisorEngagementDivisors, and_assoc]

/--
The unfiltered 6-wheel: test 2 and 3 explicitly, then enumerate
numbers congruent to 1 or 5 modulo 6.
-/
def divisorEngagementWheelRaw (N : Nat) : List Nat :=
  [2, 3] ++
    (List.range (Nat.sqrt N / 6 + 1)).flatMap
      (fun k => [6 * k + 1, 6 * k + 5])

/--
The 6-wheel trial candidates. Values 2 and 3 are handled separately;
all remaining generated values have the form 6*k+1 or 6*k+5.
Only nonunit divisors at most sqrt N survive the filter.
-/
def divisorEngagementCandidates (N : Nat) : List Nat :=
  (divisorEngagementWheelRaw N).filter
    (fun d =>
      decide (1 < d ∧
        d ≤ Nat.sqrt N ∧
        d ∣ N))

/--
Every emitted candidate is a nonunit divisor no larger than
the square root.
-/
theorem divisorEngagementCandidates_mem_sound
    (N d : Nat)
    (hmem : d ∈ divisorEngagementCandidates N) :
    d ≤ Nat.sqrt N ∧
    1 < d ∧
    d ∣ N := by
  rcases List.mem_filter.mp hmem with ⟨hraw, htest⟩
  have hprop :
      1 < d ∧
      d ≤ Nat.sqrt N ∧
      d ∣ N :=
    of_decide_eq_true htest
  exact ⟨hprop.2.1, hprop.1, hprop.2.2⟩

/--
Every square-root-bounded nonunit divisor gives an entry in the
6-wheel search. If it is divisible by 2 or 3, that small factor
is tested explicitly. Otherwise it is congruent to 1 or 5 modulo 6.
-/
theorem small_divisor_has_wheel_candidate
    (N d : Nat)
    (hbound : d ≤ Nat.sqrt N)
    (hgt : 1 < d)
    (hdvd : d ∣ N) :
    ∃ candidate : Nat,
      candidate ∈ divisorEngagementCandidates N := by
  have addCandidate
      (x : Nat)
      (hraw : x ∈ divisorEngagementWheelRaw N)
      (hxOne : 1 < x)
      (hxBound : x ≤ Nat.sqrt N)
      (hxdvd : x ∣ N) :
      x ∈ divisorEngagementCandidates N := by
    apply List.mem_filter.mpr
    exact ⟨hraw, by
      simp [divisorEngagementCandidates, hxOne, hxBound, hxdvd]⟩

  by_cases hEven : d % 2 = 0
  · have hdEq : d = 2 * (d / 2) := by
      have hmod := Nat.mod_add_div d 2
      omega
    have h2dvd : 2 ∣ N := by
      rcases hdvd with ⟨c, hNc⟩
      refine ⟨(d / 2) * c, ?_⟩
      calc
        N = d * c := hNc
        _ = (2 * (d / 2)) * c :=
          congrArg (fun x => x * c) hdEq
        _ = 2 * ((d / 2) * c) :=
          Nat.mul_assoc 2 (d / 2) c
    have h2bound : 2 ≤ Nat.sqrt N := by omega
    have hraw2 : 2 ∈ divisorEngagementWheelRaw N := by
      simp [divisorEngagementWheelRaw]
    exact ⟨2, addCandidate 2 hraw2 (by decide) h2bound h2dvd⟩

  · by_cases hThird : d % 3 = 0
    · have hdEq : d = 3 * (d / 3) := by
        have hmod := Nat.mod_add_div d 3
        omega
      have h3dvd : 3 ∣ N := by
        rcases hdvd with ⟨c, hNc⟩
        refine ⟨(d / 3) * c, ?_⟩
        calc
          N = d * c := hNc
          _ = (3 * (d / 3)) * c :=
            congrArg (fun x => x * c) hdEq
          _ = 3 * ((d / 3) * c) :=
            Nat.mul_assoc 3 (d / 3) c
      have h3bound : 3 ≤ Nat.sqrt N := by
        have hmod := Nat.mod_add_div d 3
        omega
      have hraw3 : 3 ∈ divisorEngagementWheelRaw N := by
        simp [divisorEngagementWheelRaw]
      exact ⟨3, addCandidate 3 hraw3 (by decide) h3bound h3dvd⟩

    · have h2ne : d % 2 ≠ 0 := hEven
      have h3ne : d % 3 ≠ 0 := hThird
      have hmod2 : d % 2 + 2 * (d / 2) = d :=
        Nat.mod_add_div d 2
      have hmod3 : d % 3 + 3 * (d / 3) = d :=
        Nat.mod_add_div d 3
      have hmod6 : d % 6 + 6 * (d / 6) = d :=
        Nat.mod_add_div d 6
      have hmod2lt : d % 2 < 2 :=
        Nat.mod_lt d (by decide)
      have hmod3lt : d % 3 < 3 :=
        Nat.mod_lt d (by decide)
      have hmod6lt : d % 6 < 6 :=
        Nat.mod_lt d (by decide)
      have hmod2pos : 0 < d % 2 := by omega
      have hmod3pos : 0 < d % 3 := by omega
      have hres : d % 6 = 1 ∨ d % 6 = 5 := by omega

      have hsMod :
          Nat.sqrt N % 6 + 6 * (Nat.sqrt N / 6) = Nat.sqrt N :=
        Nat.mod_add_div (Nat.sqrt N) 6
      have hsModLt : Nat.sqrt N % 6 < 6 :=
        Nat.mod_lt (Nat.sqrt N) (by decide)

      rcases hres with hOne | hFive
      · let k : Nat := d / 6
        have hkBound : k < Nat.sqrt N / 6 + 1 := by
          dsimp [k]
          omega
        have hkMem : k ∈ List.range (Nat.sqrt N / 6 + 1) :=
          List.mem_range.mpr hkBound
        have hdEq : d = 6 * k + 1 := by
          dsimp [k]
          omega
        have hinner : d ∈ [6 * k + 1, 6 * k + 5] := by
          simp [hdEq]
        have hflat :
            d ∈
              (List.range (Nat.sqrt N / 6 + 1)).flatMap
                (fun j => [6 * j + 1, 6 * j + 5]) := by
          apply List.mem_flatMap.mpr
          exact ⟨k, hkMem, hinner⟩
        have hraw : d ∈ divisorEngagementWheelRaw N := by
          unfold divisorEngagementWheelRaw
          exact List.mem_append_right _ hflat
        exact ⟨d, addCandidate d hraw hgt hbound hdvd⟩

      · let k : Nat := d / 6
        have hkBound : k < Nat.sqrt N / 6 + 1 := by
          dsimp [k]
          omega
        have hkMem : k ∈ List.range (Nat.sqrt N / 6 + 1) :=
          List.mem_range.mpr hkBound
        have hdEq : d = 6 * k + 5 := by
          dsimp [k]
          omega
        have hinner : d ∈ [6 * k + 1, 6 * k + 5] := by
          simp [hdEq]
        have hflat :
            d ∈
              (List.range (Nat.sqrt N / 6 + 1)).flatMap
                (fun j => [6 * j + 1, 6 * j + 5]) := by
          apply List.mem_flatMap.mpr
          exact ⟨k, hkMem, hinner⟩
        have hraw : d ∈ divisorEngagementWheelRaw N := by
          unfold divisorEngagementWheelRaw
          exact List.mem_append_right _ hflat
        exact ⟨d, addCandidate d hraw hgt hbound hdvd⟩

/--
The 6-wheel list is contained in the full
square-root-bounded divisor specification.
-/
theorem divisorEngagementCandidates_subset_divisors
    (N d : Nat)
    (hmem : d ∈ divisorEngagementCandidates N) :
    d ∈ divisorEngagementDivisors N := by
  have hs :=
    divisorEngagementCandidates_mem_sound N d hmem
  exact
    (divisorEngagementDivisors_mem_iff N d).2
      ⟨hs.1, hs.2.1, hs.2.2⟩

/-- Return the first trial divisor, or none. -/
def divisorEngagementSearch (N : Nat) : Option Nat :=
  (divisorEngagementCandidates N).head?

/--
A returned candidate is a nonunit divisor below N.
-/
theorem divisorEngagementSearch_sound
    (N candidate : Nat)
    (hsearch : divisorEngagementSearch N = some candidate) :
    candidate < N ∧
    1 < candidate ∧
    candidate ∣ N := by
  cases hlist : divisorEngagementCandidates N with
  | nil =>
      simp [divisorEngagementSearch, hlist] at hsearch
  | cons first rest =>
      have hfirst : first = candidate := by
        simpa [divisorEngagementSearch, hlist] using hsearch
      subst candidate
      have hmem :
          first ∈ divisorEngagementCandidates N := by
        simp [hlist]
      have hs :=
        divisorEngagementCandidates_mem_sound N first hmem
      have hsquare : first * first ≤ N :=
        Nat.le_sqrt.mp hs.1
      have hpos : 0 < first :=
        Nat.lt_trans (by decide : 0 < 1) hs.2.1
      have hltSquare : first < first * first := by
        calc
          first = first * 1 := by simp
          _ < first * first :=
            Nat.mul_lt_mul_of_pos_left hs.2.1 hpos
      exact
        ⟨lt_of_lt_of_le hltSquare hsquare,
          hs.2.1,
          hs.2.2⟩

/--
The 6-wheel search succeeds exactly when a proper
nonunit divisor exists.
-/
theorem divisorEngagementSearch_success_iff_proper_divisor
    (N : Nat) :
    (∃ candidate : Nat,
      divisorEngagementSearch N = some candidate) ↔
    (∃ d : Nat, d ∣ N ∧ 1 < d ∧ d < N) := by
  constructor
  · rintro ⟨candidate, hsearch⟩
    have hs :=
      divisorEngagementSearch_sound N candidate hsearch
    exact ⟨candidate, hs.2.2, hs.2.1, hs.1⟩
  · rintro ⟨d, hdvd, hgt, hlt⟩
    have hEngagement :
        ∃ candidate : Nat, paradoxCondition N candidate :=
      (exists_engagement_iff_proper_divisor N).2
        ⟨d, hdvd, hgt, hlt⟩
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (exists_engagement_iff_factorization N).1
        hEngagement
    obtain ⟨small, hsmallBound, hsmallNonunit, hsmallDvd⟩ :=
      factorization_has_small_divisor N a b ha hb hab
    obtain ⟨wheelCandidate, hwheel⟩ :=
      small_divisor_has_wheel_candidate
        N small hsmallBound hsmallNonunit hsmallDvd
    cases hlist : divisorEngagementCandidates N with
    | nil =>
        simp [hlist] at hwheel
    | cons first rest =>
        exact
          ⟨first, by simp [divisorEngagementSearch, hlist]⟩

/-- A proper divisor is itself an ENGAGR witness because gcd d N = d. -/
theorem properDivisor_engages
    (N d : Nat)
    (hdvd : d ∣ N)
    (hgt : 1 < d)
    (hlt : d < N) :
    paradoxCondition N d := by
  have hfixed : Nat.gcd d N = d := by
    exact (normalizeCandidate_eq_self_iff_dvd N d).2 hdvd
  change 1 < Nat.gcd d N ∧ Nat.gcd d N < N
  rw [hfixed]
  exact ⟨hgt, hlt⟩

theorem divisorEngagementSearch_success_iff_normalized_divisor
    (N : Nat) :
    (∃ candidate : Nat,
      divisorEngagementSearch N = some candidate) ↔
    Nonempty (NormalizedEngagement N) := by
  constructor
  · rintro ⟨candidate, hsearch⟩
    obtain ⟨hbound, hgt, hdvd⟩ :=
      divisorEngagementSearch_sound N candidate hsearch
    exact ⟨⟨candidate, hdvd, hgt, hbound⟩⟩
  · rintro ⟨w⟩
    exact
      (divisorEngagementSearch_success_iff_proper_divisor N).2
        ⟨w.candidate, w.dividesInput, w.nonunit, w.proper⟩

theorem divisorEngagementSearch_success_iff_factorization
    (N : Nat) :
    (∃ candidate : Nat,
      divisorEngagementSearch N = some candidate) ↔
    (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) := by
  exact
    (divisorEngagementSearch_success_iff_proper_divisor N).trans
      ((exists_engagement_iff_proper_divisor N).symm.trans
        (exists_engagement_iff_factorization N))

/--
A successful divisor search returns an exact proper factor and quotient,
and the same pair is emitted by the membrane.
-/
theorem divisorEngagementSearch_pipeline_certificate
    (N candidate : Nat)
    (hsearch : divisorEngagementSearch N = some candidate) :
    candidate ∣ N ∧
    1 < candidate ∧
    candidate < N ∧
    1 < N / candidate ∧
    candidate * (N / candidate) = N ∧
    PSystem.isGlut
      (runBinaryMembrane N candidate).phase ∧
    (runBinaryMembrane N candidate).factors.P0 = candidate ∧
    (runBinaryMembrane N candidate).factors.P1 = N / candidate := by
  have hs :=
    divisorEngagementSearch_sound N candidate hsearch
  have hfixed : Nat.gcd candidate N = candidate := by
    exact (normalizeCandidate_eq_self_iff_dvd N candidate).2 hs.2.2
  have hquotientNonunit :
      1 < N / Nat.gcd candidate N :=
    gcd_complement_gt_one N candidate
      (by simpa [hfixed] using hs.1)
      (by simpa [hfixed] using hs.2.1)
  have hquotient : 1 < N / candidate := by
    simpa [hfixed] using hquotientNonunit
  have hclosure : candidate * (N / candidate) = N :=
    Nat.mul_div_cancel' hs.2.2
  have heng : paradoxCondition N candidate := by
    change 1 < Nat.gcd candidate N ∧ Nat.gcd candidate N < N
    rw [hfixed]
    exact ⟨hs.2.1, hs.1⟩
  have hcomponents :=
    runBinaryMembrane_engaged_components N candidate heng
  refine
    ⟨hs.2.2, hs.2.1, hs.1, hquotient, hclosure,
      (runBinaryMembrane_phase N candidate).2 heng, ?_, ?_⟩
  · calc
      (runBinaryMembrane N candidate).factors.P0 =
          Nat.gcd candidate N := hcomponents.1
      _ = candidate := hfixed
  · simpa [hfixed] using hcomponents.2

/-! ## 16. Divisor Search Equivalence and Exact Output -/

/--
The finite search specification is exactly the range
up to the square root, filtered by nonunit status and divisibility.
-/
theorem divisorEngagementDivisors_eq_filter
    (N : Nat) :
    divisorEngagementDivisors N =
      (Finset.range (Nat.sqrt N + 1)).filter
        (fun d => 1 < d ∧ d ∣ N) := rfl

/--
The reduced divisor search and the earlier bounded ENGAGR
search agree on whether a witness exists.
-/
theorem divisorEngagementSearch_success_iff_bounded_search
    (N : Nat) :
    (∃ candidate : Nat,
      divisorEngagementSearch N = some candidate) ↔
    (∃ candidate : Nat, engagementSearch N = some candidate) := by
  rw [divisorEngagementSearch_success_iff_factorization,
    engagementSearch_success_iff_factorization]

/-- Any successful divisor-search result is an exact factor pair. -/
def divisorSearchFactorPair
    (N candidate : Nat)
    (hsearch : divisorEngagementSearch N = some candidate) :
    ProperFactorPair N := by
  have hcert :=
    divisorEngagementSearch_pipeline_certificate N candidate hsearch
  exact
    ⟨candidate, N / candidate,
      hcert.2.1,
      hcert.2.2.2.1,
      hcert.2.2.2.2.1⟩

/-- The divisor search's emitted pair reconstructs the input. -/
theorem divisorSearchFactorPair_closure
    (N candidate : Nat)
    (hsearch : divisorEngagementSearch N = some candidate) :
    (divisorSearchFactorPair N candidate hsearch).P0 *
      (divisorSearchFactorPair N candidate hsearch).P1 = N :=
  (divisorSearchFactorPair N candidate hsearch).productClosure

/-- The divisor search's factors are both strict nonunits. -/
theorem divisorSearchFactorPair_proper
    (N candidate : Nat)
    (hsearch : divisorEngagementSearch N = some candidate) :
    1 < (divisorSearchFactorPair N candidate hsearch).P0 ∧
    1 < (divisorSearchFactorPair N candidate hsearch).P1 := by
  exact
    ⟨(divisorSearchFactorPair N candidate hsearch).left_nonunit,
      (divisorSearchFactorPair N candidate hsearch).right_nonunit⟩

/-- No divisor-search candidate exists exactly when no proper factorization exists. -/
theorem divisorEngagementSearch_none_iff_no_factorization
    (N : Nat) :
    divisorEngagementSearch N = none ↔
    ¬ (∃ a b : Nat, 1 < a ∧ 1 < b ∧ a * b = N) := by
  constructor
  · intro hnone hfactor
    obtain ⟨candidate, hsearch⟩ :=
      (divisorEngagementSearch_success_iff_factorization N).2 hfactor
    rw [hnone] at hsearch
    cases hsearch
  · intro hno
    by_contra hsome
    cases hs : divisorEngagementSearch N with
    | none =>
        exact hsome hs
    | some candidate =>
        apply hno
        exact
          (divisorEngagementSearch_success_iff_factorization N).1
            ⟨candidate, hs⟩

end Imscribing.Paraconsistent.BinaryMembrane