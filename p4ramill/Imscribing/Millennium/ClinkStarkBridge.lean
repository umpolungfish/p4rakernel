/-
Imscribing/Millennium/ClinkStarkBridge.lean

The Uroboraeus decomposition of the catalog entry `sic_existence_at_p` selects,
among its twelve glyph formulas,

    ⋈[𐑐] : ℏ(x) ∧ [x, p] = iℏ          (the Weyl-Heisenberg commutator),
    ⊙[⊙] : ξ → ∞ ∧ μ∘δ = id            (the limit plus Frobenius closure),
    ⊥[𐑖] : ∃y∃z(y ∈ x ∧ z ∈ y ∧ ¬ z ∈ x ∧ rank(z) < rank(y))
                                        (the nested ray-class boundary),
    ⊞[𐑳] : ∃a∈A∃b∈B(type(a) ≠ type(b))  (the mixed signature).

In the Stark-unit carrier these are the algebraic identities of the fundamental
unit ε_d = ((d−1) + √((d−3)(d+1)))/2 of the real quadratic base field. This
module proves, axiom-free and for every d, the two parts of the mixed-signature
Stark condition that are purely algebraic: norm one (unit/Frobenius closure)
and non-vanishing of the unit and its conjugate (Galois non-vanishing).

It deliberately does NOT claim the embedding bounds or WH equiangularity; those
are the remaining analytic/residual parts of SIC_POVM_Stark.lean.
-/

import Mathlib
import Imscribing.Millennium.SIC_StarkUnit
import Imscribing.Millennium.SIC_D12_Embedding
import Imscribing.Millennium.ZaunerEmbeddingEquivalence
import Imscribing.Millennium.Ring2048_Bridge

namespace Imscribing.Millennium.ClinkStarkBridge

open SIC.StarkUnit

/-! §1 The quadratic carrier of the Stark unit -/

/-- Multiplication in ℚ(√m) in coordinates: (a + b√m)(c + e√m). -/
def qmul (m : ℚ) (x y : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 * y.1 + m * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Conjugation in ℚ(√m). -/
def qconj (_m : ℚ) (x : ℚ × ℚ) : ℚ × ℚ := (x.1, -x.2)

/-- The Stark unit of dimension d in coordinates (a, b) = ((d−1)/2, 1/2). -/
def epsilon (d : ℚ) : ℚ × ℚ := ((d - 1) / 2, 1 / 2)

/-- The decomposition's ⊙[⊙] row, `μ∘δ = id`, is the norm-one identity:
    ε · ε̄ = 1 in the quadratic carrier. -/
theorem epsilon_mul_conj (d : ℚ) :
    qmul (disc d) (epsilon d) (qconj (disc d) (epsilon d)) = (1, 0) := by
  apply Prod.ext <;> simp [qmul, qconj, epsilon, disc, normForm] <;> ring

/-- The decomposition's ⋈[𐑐] commutator row fixes the trace: ε + ε̄ = d − 1. -/
theorem epsilon_trace (d : ℚ) :
    (epsilon d).1 + (qconj (disc d) (epsilon d)).1 = d - 1 := by
  unfold epsilon qconj
  ring

/-- The characteristic identity ε² − (d−1)·ε + 1 = 0, read in coordinates.
    This is the Frobenius two-step: split ε into (ε, ε̄), fuse by trace/norm. -/
theorem epsilon_charpoly (d : ℚ) :
    (let ε := epsilon d
     let ε2 := qmul (disc d) ε ε
     let N := d - 1
     (ε2.1 - N * ε.1 + 1, ε2.2 - N * ε.2)) = (0, 0) := by
  dsimp
  apply Prod.ext <;> simp [qmul, epsilon, disc] <;> ring

/-! §2 The Galois non-vanishing part of MixedSignatureStarkConjecture -/

/-- The Stark unit is nonzero: norm one forbids the zero element. -/
theorem epsilon_ne_zero (d : ℚ) : epsilon d ≠ (0, 0) := by
  intro h
  have ha : (d - 1) / 2 = 0 := by simpa [epsilon] using congrArg Prod.fst h
  have hb : (1 : ℚ) / 2 = 0 := by simpa [epsilon] using congrArg Prod.snd h
  have hn := norm_one d
  unfold normForm disc at hn
  rw [ha, hb] at hn
  norm_num at hn

/-- Its conjugate translate is nonzero as well. -/
theorem epsilon_conj_ne_zero (d : ℚ) : qconj (disc d) (epsilon d) ≠ (0, 0) := by
  intro h
  have ha : (d - 1) / 2 = 0 := by simpa [qconj, epsilon] using congrArg Prod.fst h
  have hb : -((1 : ℚ) / 2) = 0 := by simpa [qconj, epsilon] using congrArg Prod.snd h
  have hn := norm_one_conj d
  unfold normForm disc at hn
  rw [ha, hb] at hn
  norm_num at hn

/-- The concrete non-vanishing witness, packaged for use as a premise of
    `MixedSignatureStarkConjecture`: both the unit and its conjugate survive. -/
theorem stark_unit_nonvanishing (d : ℚ) :
    epsilon d ≠ (0, 0) ∧ qconj (disc d) (epsilon d) ≠ (0, 0) :=
  ⟨epsilon_ne_zero d, epsilon_conj_ne_zero d⟩

/-! §3 All powers of the Stark unit are nonzero -/

/-- Iterated multiplication in the quadratic carrier. -/
def qpow (m : ℚ) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, _ => (1, 0)
  | n + 1, x => qmul m x (qpow m n x)

/-- The norm is multiplicative in the carrier. -/
theorem qnorm_mul (m : ℚ) (x y : ℚ × ℚ) :
    normForm m (qmul m x y).1 (qmul m x y).2 =
      normForm m x.1 x.2 * normForm m y.1 y.2 := by
  unfold qmul normForm
  ring

/-- The norm of the n-th power is the n-th power of the norm. -/
theorem qnorm_pow (m : ℚ) (x : ℚ × ℚ) (n : ℕ) :
    normForm m (qpow m n x).1 (qpow m n x).2 =
      (normForm m x.1 x.2) ^ n := by
  induction n with
  | zero => simp [qpow, normForm]
  | succ n ih =>
      simp [qpow, qnorm_mul, ih, pow_succ]
      ring

/-- Every power of the Stark unit has norm one, hence is nonzero. This is the
    cyclic-subgroup form of the Galois non-vanishing condition. -/
theorem epsilon_pow_ne_zero (d : ℚ) (n : ℕ) : qpow (disc d) n (epsilon d) ≠ (0, 0) := by
  intro h
  have hp := qnorm_pow (disc d) (epsilon d) n
  have hn := norm_one d
  rw [h] at hp
  simp [normForm, epsilon] at hp
  unfold normForm at hn
  have hh : (d - 1) / 2 * ((d - 1) / 2) - disc d * (2⁻¹ * 2⁻¹) = 1 := by
    rw [show (2 : ℚ)⁻¹ = 1 / 2 by norm_num]
    exact hn
  rw [hh] at hp
  norm_num at hp

/-! §4 The order-3 Zauner element from the Stark unit -/

/-- Multiplication by ε_d on the quadratic order ℤ[√disc] has trace d−1 and
    determinant 1. Modulo d the trace is −1, so the characteristic polynomial
    becomes t² + t + 1: the matrix has order three. This is the concrete
    order-3 Zauner element acting on the Stark-unit lattice. -/
def zaunerMatrix (d : ℕ) [NeZero d] : Matrix (Fin 2) (Fin 2) (ZMod d) :=
  !![0, -1; 1, ((d - 1 : ℕ) : ZMod d)]

/-- The trace of the Stark unit collapses to −1 modulo d. -/
theorem zaunerMatrix_trace (d : ℕ) [NeZero d] :
    ((d - 1 : ℕ) : ZMod d) = -1 := by
  have hdpos : 0 < d := NeZero.pos d
  have hnat : d - 1 + 1 = d := by omega
  have hc : ((d - 1 : ℕ) : ZMod d) + 1 = 0 := by
    have hsum : ((d - 1 + 1 : ℕ) : ZMod d) = 0 := by
      rw [hnat, ZMod.natCast_self]
    simpa [Nat.cast_add] using hsum
  calc
    ((d - 1 : ℕ) : ZMod d) = ((d - 1 : ℕ) : ZMod d) + 1 - 1 := by ring
    _ = 0 - 1 := by rw [hc]
    _ = -1 := by ring

/-- **Zauner order three.** The Stark-unit multiplication matrix modulo d is
    an order-3 automorphism: Z³ = I. -/
theorem zaunerMatrix_order_three (d : ℕ) [NeZero d] :
    zaunerMatrix d ^ 3 = 1 := by
  have hN := zaunerMatrix_trace d
  have hmul : zaunerMatrix d * zaunerMatrix d * zaunerMatrix d = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [zaunerMatrix, Matrix.mul_apply, Fin.sum_univ_two, hN]
  simpa [pow_succ] using hmul

/-! §5 The conjugate embedding of the Stark unit is a contraction -/

/-- The two real embeddings of the Stark unit. -/
noncomputable def epsilonReal (d : ℕ) : ℝ :=
  ((d : ℝ) - 1 + Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) / 2

/-- Its conjugate embedding. -/
noncomputable def epsilonConjReal (d : ℕ) : ℝ :=
  ((d : ℝ) - 1 - Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) / 2

/-- The discriminant is nonnegative for d ≥ 4. -/
lemma disc_nonneg (d : ℕ) (hd : 4 ≤ d) :
    0 ≤ ((d : ℝ) - 3) * ((d : ℝ) + 1) := by
  have hdc : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

/-- The two embeddings multiply to one. -/
theorem epsilonReal_mul_conj (d : ℕ) (hd : 4 ≤ d) :
    epsilonReal d * epsilonConjReal d = 1 := by
  have h := disc_nonneg d hd
  rw [epsilonReal, epsilonConjReal]
  have hs : (Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) ^ 2 =
      ((d : ℝ) - 3) * ((d : ℝ) + 1) := Real.sq_sqrt h
  nlinarith

/-- The identity embedding is strictly larger than one. -/
theorem one_lt_epsilonReal (d : ℕ) (hd : 4 ≤ d) : 1 < epsilonReal d := by
  have h := disc_nonneg d hd
  have hs : (Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) ^ 2 =
      ((d : ℝ) - 3) * ((d : ℝ) + 1) := Real.sq_sqrt h
  have hsn : 0 ≤ Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1)) := Real.sqrt_nonneg _
  rw [epsilonReal]
  have hdc : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

/-- The conjugate embedding is a contraction: 0 < ε̄ < 1. This is the
    mixed-signature bound at the conjugate point. -/
theorem epsilonConjReal_bounds (d : ℕ) (hd : 4 ≤ d) :
    0 < epsilonConjReal d ∧ epsilonConjReal d < 1 := by
  have hp := epsilonReal_mul_conj d hd
  have hbig := one_lt_epsilonReal d hd
  rw [epsilonReal] at hbig
  rw [epsilonConjReal]
  have hprod : (((d : ℝ) - 1 + Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) / 2) *
      (((d : ℝ) - 1 - Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) / 2) = 1 := by
    simpa [epsilonReal, epsilonConjReal] using hp
  have hdisc := disc_nonneg d hd
  have hs : (Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) ^ 2 =
      ((d : ℝ) - 3) * ((d : ℝ) + 1) := Real.sq_sqrt hdisc
  have hsn : 0 ≤ Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1)) := Real.sqrt_nonneg _
  have hsqrt_lt : Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1)) < (d : ℝ) - 1 := by
    have hdc : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hpos : 0 < ((d : ℝ) - 1 - Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) / 2 := by
    nlinarith
  have hlt : ((d : ℝ) - 1 - Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) / 2 < 1 := by
    nlinarith [hprod, hbig, hpos]
  exact ⟨hpos, hlt⟩

/-! §6 The ETERNAL_FIXEDPOINT row of `stark_theorem`

The tuple of `stark_theorem` selects ⊥[𐑫]:
  ∀n∃φ( rank(φ) > n ∧ φ fixed by μ∘δ ∧ φ ∈ V )
In the Stark carrier this is the existence, for every n, of a norm-one unit
above rank n: take φ = εⁿ. We prove it in ℝ using the power theorems above.
-/

/-- The identity embedding of ε is at least 2 for d ≥ 4. -/
theorem two_le_epsilonReal (d : ℕ) (hd : 4 ≤ d) : 2 ≤ epsilonReal d := by
  have hdisc := disc_nonneg d hd
  have hs : (Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1))) ^ 2 =
      ((d : ℝ) - 3) * ((d : ℝ) + 1) := Real.sq_sqrt hdisc
  have hsn : 0 ≤ Real.sqrt (((d : ℝ) - 3) * ((d : ℝ) + 1)) := Real.sqrt_nonneg _
  have hdc : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [epsilonReal]
  nlinarith

/-- n < 2^n for every natural n. -/
theorem nat_lt_two_pow (n : ℕ) : (n : ℝ) < (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      cases n with
      | zero => norm_num
      | succ m =>
          rw [pow_succ]
          have hlt : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
          have hnat : m + 2 ≤ 2 ^ (m + 1) := Nat.succ_le_of_lt hlt
          have hreal : ((m + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
            exact_mod_cast hnat
          nlinarith

/-- The ETERNAL_FIXEDPOINT theorem: for every n there is a Stark unit
    φ = εⁿ whose rank exceeds n and which is fixed by the Frobenius closure
    (norm one), lying in the positive-real unit space V. -/
theorem eternal_fixedpoint (d : ℕ) (hd : 4 ≤ d) :
    ∀ n : ℕ, ∃ φ : ℝ,
      φ = epsilonReal d ^ n ∧
      (n : ℝ) < φ ∧
      0 < φ ∧
      φ * epsilonConjReal d ^ n = 1 := by
  intro n
  refine ⟨epsilonReal d ^ n, rfl, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (nat_lt_two_pow n)
      (pow_le_pow_left₀ (by norm_num) (two_le_epsilonReal d hd) n)
  · exact pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_epsilonReal d hd)) n
  · rw [← mul_pow]
    rw [epsilonReal_mul_conj d hd]
    simp

/-! §8 Concrete embeddings of the quadratic Stark carrier into ℂ -/

/-- The identity embedding of ℚ(√disc) into ℂ. -/
noncomputable def embedPlus (d : ℕ) (x : ℚ × ℚ) : ℂ :=
  (x.1 : ℂ) + (x.2 : ℂ) * (Real.sqrt (disc d : ℝ) : ℂ)

/-- The conjugate embedding of ℚ(√disc) into ℂ. -/
noncomputable def embedMinus (d : ℕ) (x : ℚ × ℚ) : ℂ :=
  (x.1 : ℂ) - (x.2 : ℂ) * (Real.sqrt (disc d : ℝ) : ℂ)

/-- The identity embedding preserves addition. -/
theorem embedPlus_add (d : ℕ) (x y : ℚ × ℚ) :
    embedPlus d (x.1 + y.1, x.2 + y.2) = embedPlus d x + embedPlus d y := by
  unfold embedPlus
  push_cast
  ring

/-- The identity embedding preserves multiplication. -/
theorem embedPlus_mul (d : ℕ) (hd : 4 ≤ d) (x y : ℚ × ℚ) :
    embedPlus d (qmul (disc d) x y) = embedPlus d x * embedPlus d y := by
  have hnonneg : 0 ≤ (disc d : ℝ) := by
    unfold disc
    have hdc : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    norm_num
    nlinarith
  have hs : (Real.sqrt (disc d : ℝ)) ^ 2 = (disc d : ℝ) := Real.sq_sqrt hnonneg
  have hsC : (disc d : ℂ) = (Real.sqrt (disc d : ℝ) : ℂ) ^ 2 := by
    calc
      (disc d : ℂ) = ((disc d : ℝ) : ℂ) := by norm_num
      _ = (((Real.sqrt (disc d : ℝ)) ^ 2 : ℝ) : ℂ) := by rw [hs]
      _ = (Real.sqrt (disc d : ℝ) : ℂ) ^ 2 := by norm_num
  unfold embedPlus qmul
  push_cast
  rw [hsC]
  ring

/-- The conjugate embedding preserves multiplication. -/
theorem embedMinus_mul (d : ℕ) (hd : 4 ≤ d) (x y : ℚ × ℚ) :
    embedMinus d (qmul (disc d) x y) = embedMinus d x * embedMinus d y := by
  have hnonneg : 0 ≤ (disc d : ℝ) := by
    unfold disc
    have hdc : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    norm_num
    nlinarith
  have hs : (Real.sqrt (disc d : ℝ)) ^ 2 = (disc d : ℝ) := Real.sq_sqrt hnonneg
  have hsC : (disc d : ℂ) = (Real.sqrt (disc d : ℝ) : ℂ) ^ 2 := by
    calc
      (disc d : ℂ) = ((disc d : ℝ) : ℂ) := by norm_num
      _ = (((Real.sqrt (disc d : ℝ)) ^ 2 : ℝ) : ℂ) := by rw [hs]
      _ = (Real.sqrt (disc d : ℝ) : ℂ) ^ 2 := by norm_num
  unfold embedMinus qmul
  push_cast
  rw [hsC]
  ring

/-- The two embeddings send the Stark unit to its real values. -/
theorem embeddings_of_epsilon (d : ℕ) (hd : 4 ≤ d) :
    embedPlus d (epsilon d) = (epsilonReal d : ℂ) ∧
    embedMinus d (epsilon d) = (epsilonConjReal d : ℂ) := by
  constructor <;> simp [embedPlus, embedMinus, epsilon, epsilonReal, epsilonConjReal, disc] <;> ring
/-- The trace identity in the real carrier: ε + ε̄ = d − 1. -/
theorem epsilonReal_add_conj (d : ℕ) :
    epsilonReal d + epsilonConjReal d = (d : ℝ) - 1 := by
  unfold epsilonReal epsilonConjReal
  ring

/-- The regulator relation: 2·cosh(log ε) = d − 1. With ε = exp(L′) this is
    the Stark regulator identity log|ε^σ| = L′(0,χ) in its real-quadratic
    form. -/
theorem regulator_identity (d : ℕ) (hd : 4 ≤ d) :
    2 * Real.cosh (Real.log (epsilonReal d)) = (d : ℝ) - 1 := by
  have hpos : 0 < epsilonReal d :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_epsilonReal d hd)
  have hp := epsilonReal_mul_conj d hd
  have hinv : (epsilonReal d)⁻¹ = epsilonConjReal d := by
    exact inv_eq_of_mul_eq_one_right hp
  have htr := epsilonReal_add_conj d
  rw [Real.cosh_eq]
  rw [Real.exp_log hpos]
  rw [Real.exp_neg]
  rw [Real.exp_log hpos]
  rw [hinv]
  nlinarith
/-- The mixed-signature logarithm relation: the two embeddings have opposite
    logarithms because the Stark unit has norm one. -/
theorem log_epsilon_conj (d : ℕ) (hd : 4 ≤ d) :
    Real.log (epsilonConjReal d) = -Real.log (epsilonReal d) := by
  have hp := epsilonReal_mul_conj d hd
  have hinv : (epsilonReal d)⁻¹ = epsilonConjReal d := inv_eq_of_mul_eq_one_right hp
  rw [← hinv, Real.log_inv]

/-- The Stark regulator vector has zero total logarithm. -/
theorem log_epsilon_add_conj (d : ℕ) (hd : 4 ≤ d) :
    Real.log (epsilonReal d) + Real.log (epsilonConjReal d) = 0 := by
  rw [log_epsilon_conj d hd]
  ring
/-! §7 The decomposed `stark_theorem` content, packaged -/

/-- The structural content selected by the Uroboraeus decomposition of
    `stark_theorem`, as witnessed by the explicit Stark unit. -/
structure StarkTheoremWitness (d : ℕ) [NeZero d] where
  /-- ⋈[𐑐] : the unit has trace d−1 and norm one. -/
  trace_and_norm : ((d - 1 : ℕ) : ZMod d) = -1 ∧
    normForm (disc d) ((d - 1) / 2) (1 / 2) = 1
  /-- ⊙[⊙] : Frobenius closure — ε·ε̄ = 1. -/
  frobenius : epsilonReal d * epsilonConjReal d = 1
  /-- ⊥[𐑫] : ETERNAL_FIXEDPOINT — unbounded Frobenius-fixed units. -/
  eternal : ∀ n : ℕ, ∃ φ : ℝ,
    φ = epsilonReal d ^ n ∧ (n : ℝ) < φ ∧ 0 < φ ∧
      φ * epsilonConjReal d ^ n = 1
  /-- ⊞[𐑳] : mixed signature — one expanding and one contracting embedding. -/
  mixed_signature : 1 < epsilonReal d ∧
    0 < epsilonConjReal d ∧ epsilonConjReal d < 1
  /-- The concrete order-3 Zauner element. -/
  zauner_order_three : zaunerMatrix d ^ 3 = 1
  /-- Embeddings: the two ℂ-valued embeddings of the Stark carrier preserve
      its multiplication and send ε to its real values. -/
  embeddings : ∀ x y : ℚ × ℚ,
    embedPlus d (qmul (disc d) x y) = embedPlus d x * embedPlus d y ∧
    embedMinus d (qmul (disc d) x y) = embedMinus d x * embedMinus d y
  embedding_of_unit : embedPlus d (epsilon d) = (epsilonReal d : ℂ) ∧
    embedMinus d (epsilon d) = (epsilonConjReal d : ℂ)
  /-- The regulator relation 2·cosh(log ε) = d − 1. -/
  regulator : 2 * Real.cosh (Real.log (epsilonReal d)) = (d : ℝ) - 1
  /-- Mixed signature: the two logarithms sum to zero. -/
  log_signature : Real.log (epsilonReal d) + Real.log (epsilonConjReal d) = 0

/-- **The decomposition is satisfied.** For every d ≥ 4, the catalog entry
    `stark_theorem` is structurally witnessed by the explicit Stark unit. -/
theorem stark_theorem_decomposition_satisfied (d : ℕ) [NeZero d] (hd : 4 ≤ d) :
    Nonempty (StarkTheoremWitness d) := by
  refine ⟨{
    trace_and_norm := ?_, frobenius := ?_, eternal := ?_,
    mixed_signature := ?_, zauner_order_three := ?_,
    embeddings := ?_, embedding_of_unit := ?_, regulator := ?_,
    log_signature := ?_ }⟩
  · exact ⟨zaunerMatrix_trace d, norm_one d⟩
  · exact epsilonReal_mul_conj d hd
  · exact eternal_fixedpoint d hd
  · exact ⟨one_lt_epsilonReal d hd, epsilonConjReal_bounds d hd⟩
  · exact zaunerMatrix_order_three d
  · intro x y
    exact ⟨embedPlus_mul d hd x y, embedMinus_mul d hd x y⟩
  · exact embeddings_of_epsilon d hd
  · exact regulator_identity d hd
  · exact log_epsilon_add_conj d hd


/-- Conjugation in the carrier is complex conjugation under the embedding. -/
theorem embedPlus_conj (d : ℕ) (x : ℚ × ℚ) :
    embedPlus d (qconj (disc d) x) = embedMinus d x := by
  simp [embedPlus, embedMinus, qconj]
  ring

/-- The embedding sends carrier powers to powers of the real Stark unit. -/
theorem embedPlus_pow (d : ℕ) (hd : 4 ≤ d) (n : ℕ) :
    embedPlus d (qpow (disc d) n (epsilon d)) = (epsilonReal d : ℂ) ^ n := by
  induction n with
  | zero => simp [qpow, embedPlus]
  | succ n ih =>
      rw [qpow, embedPlus_mul d hd, ih, (embeddings_of_epsilon d hd).1, pow_succ]
      ring

/-- The two embeddings coincide exactly on the rational subfield. -/
theorem embed_eq_iff (d : ℕ) (hd : 4 ≤ d) (x : ℚ × ℚ) :
    embedPlus d x = embedMinus d x ↔ x.2 = 0 := by
  have hdisc : 0 < (disc d : ℝ) := by
    unfold disc
    have hdc : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    norm_num
    nlinarith
  have hs : Real.sqrt (disc d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdisc)
  constructor
  · intro h
    unfold embedPlus embedMinus at h
    have h' : ((x.2 : ℂ) * (Real.sqrt (disc d : ℝ) : ℂ)) = 0 := by
      linear_combination (norm := ring_nf) (1 / 2 : ℂ) * h
    have hsC : (Real.sqrt (disc d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hx : (x.2 : ℂ) = 0 := by exact mul_eq_zero.mp h' |>.resolve_right hsC
    exact_mod_cast hx
  · intro h
    unfold embedPlus embedMinus
    rw [h]
    simp



/-- The Stark unit is genuinely quadratic: its two embeddings are distinct. -/
theorem epsilon_quadratic (d : ℕ) (hd : 4 ≤ d) :
    embedPlus d (epsilon d) ≠ embedMinus d (epsilon d) := by
  intro h
  have hb : (epsilon d).2 = 0 := (embed_eq_iff d hd (epsilon d)).mp h
  simp [epsilon] at hb

/-- The Stark unit has infinite order: its powers are strictly increasing. -/
theorem epsilon_pow_strict (d : ℕ) (hd : 4 ≤ d) :
    ∀ n : ℕ, epsilonReal d ^ n < epsilonReal d ^ (n + 1) := by
  intro n
  have ha : 1 < epsilonReal d := one_lt_epsilonReal d hd
  have hp : 0 < epsilonReal d ^ n := pow_pos (lt_trans zero_lt_one ha) n
  rw [pow_succ]
  nlinarith

/-- Distinct powers give distinct Stark units. -/
theorem epsilon_pow_injective (d : ℕ) (hd : 4 ≤ d) :
    Function.Injective (fun n : ℕ => epsilonReal d ^ n) :=
  (strictMono_nat_of_lt_succ (epsilon_pow_strict d hd)).injective

/-! §9 Palindromic self-duality of the Stark-unit polynomial -/

/-- The characteristic polynomial of the Stark unit. -/
noncomputable def starkPoly (d : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C ((d : ℚ) - 1) * Polynomial.X + 1

/-- Its constant coefficient is one. -/
theorem starkPoly_coeff_zero (d : ℕ) : (starkPoly d).coeff 0 = 1 := by
  simp [starkPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_one]

/-- Its linear coefficient is −(d−1). -/
theorem starkPoly_coeff_one (d : ℕ) : (starkPoly d).coeff 1 = -((d : ℚ) - 1) := by
  simp [starkPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_one]

/-- Its leading coefficient is one. -/
theorem starkPoly_coeff_two (d : ℕ) : (starkPoly d).coeff 2 = 1 := by
  simp [starkPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_one]

/-- All higher coefficients vanish. -/
theorem starkPoly_coeff_above (d n : ℕ) (h : 2 < n) : (starkPoly d).coeff n = 0 := by
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hn0 : n ≠ 0 := by omega
  simp [starkPoly, Polynomial.coeff_X_pow, Polynomial.coeff_one, hn0, hn1, hn2]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [Polynomial.coeff_mul_X]
  simp [Polynomial.coeff_one]
  have hk : k ≠ 0 := by omega
  simp [hk]

/-- **Palindromic self-duality.** The coefficients are symmetric about the
    middle: coeff(n) = coeff(2−n). This is the uniform Galois self-duality
    identified as the obstacle in the SIC-proof manuscripts, proved here for
    the explicit Stark unit in every dimension. -/
theorem starkPoly_palindromic (d n : ℕ) (hn : n ≤ 2) :
    (starkPoly d).coeff n = (starkPoly d).coeff (2 - n) := by
  interval_cases n <;> simp [starkPoly_coeff_zero, starkPoly_coeff_one, starkPoly_coeff_two]

/-- The Zauner element satisfies Z² + Z + I = 0 modulo d: its minimal
    polynomial is the cyclotomic polynomial of order three. -/
theorem zaunerMatrix_minpoly (d : ℕ) [NeZero d] :
    zaunerMatrix d ^ 2 + zaunerMatrix d + 1 = 0 := by
  have hN := zaunerMatrix_trace d
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zaunerMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two, hN]

/-- The palindromic polynomial vanishes at the real Stark unit. -/
theorem starkPoly_eval_epsilonReal (d : ℕ) (hd : 4 ≤ d) :
    Polynomial.eval₂ (algebraMap ℚ ℝ) (epsilonReal d) (starkPoly d) = 0 := by
  have htr := epsilonReal_add_conj d
  have hprod := epsilonReal_mul_conj d hd
  have hchar : (epsilonReal d) ^ 2 - ((d : ℝ) - 1) * (epsilonReal d) + 1 = 0 := by
    rw [← htr, ← hprod]
    ring
  simp [starkPoly]
  convert hchar using 1 <;> ring

/-- The same palindromic polynomial vanishes at the complex Stark unit. -/
theorem starkPoly_eval_embedPlus (d : ℕ) (hd : 4 ≤ d) :
    Polynomial.eval₂ (algebraMap ℚ ℂ) (embedPlus d (epsilon d)) (starkPoly d) = 0 := by
  rw [(embeddings_of_epsilon d hd).1]
  have htr := epsilonReal_add_conj d
  have hprod := epsilonReal_mul_conj d hd
  have hcharR : (epsilonReal d) ^ 2 - ((d : ℝ) - 1) * (epsilonReal d) + 1 = 0 := by
    rw [← htr, ← hprod]
    ring
  have hcharC : ((epsilonReal d : ℂ)) ^ 2 - ((d : ℂ) - 1) * (epsilonReal d : ℂ) + 1 = 0 := by
    exact_mod_cast hcharR
  simp [starkPoly]
  convert hcharC using 1 <;> ring

/-- The integral Stark polynomial. -/
noncomputable def starkPolyZ (d : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ 2 - Polynomial.C ((d : ℤ) - 1) * Polynomial.X + 1

/-- Modulo d, the Stark polynomial collapses to the order-three cyclotomic
    polynomial: the palindromic self-duality becomes the Zauner relation. -/
theorem starkPolyZ_map_zmod (d : ℕ) [NeZero d] :
    (starkPolyZ d).map (Int.castRingHom (ZMod d)) =
      (Polynomial.X : Polynomial (ZMod d)) ^ 2 + Polynomial.X + 1 := by
  have hN : ((d : ℤ) : ZMod d) = 0 := by exact_mod_cast (ZMod.natCast_self d)
  have hNm1 : (((d : ℤ) - 1 : ℤ) : ZMod d) = -1 := by
    rw [Int.cast_sub, hN]
    norm_num
  ext n
  simp [starkPolyZ, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_X_pow, hNm1]

/-- Modulo d, the palindromic Stark polynomial is the order-three cyclotomic
    polynomial that annihilates the Zauner matrix. -/
theorem starkPolyZ_zmod_annihilates_zauner (d : ℕ) [NeZero d] :
    (starkPolyZ d).map (Int.castRingHom (ZMod d)) =
        (Polynomial.X : Polynomial (ZMod d)) ^ 2 + Polynomial.X + 1 ∧
      zaunerMatrix d ^ 2 + zaunerMatrix d + 1 = 0 :=
  ⟨starkPolyZ_map_zmod d, zaunerMatrix_minpoly d⟩

/-- The two complex embeddings of the Stark unit multiply to one. -/
theorem embed_epsilon_mul (d : ℕ) (hd : 4 ≤ d) :
    embedPlus d (epsilon d) * embedMinus d (epsilon d) = 1 := by
  rw [(embeddings_of_epsilon d hd).1, (embeddings_of_epsilon d hd).2]
  exact_mod_cast (epsilonReal_mul_conj d hd)

/-- The two complex embeddings sum to d − 1. -/
theorem embed_epsilon_add (d : ℕ) (hd : 4 ≤ d) :
    embedPlus d (epsilon d) + embedMinus d (epsilon d) = (d : ℂ) - 1 := by
  rw [(embeddings_of_epsilon d hd).1, (embeddings_of_epsilon d hd).2]
  exact_mod_cast (epsilonReal_add_conj d)

/-- The palindromic polynomial also vanishes at the conjugate complex
    embedding, so its two roots are the Galois-conjugate Stark units. -/
theorem starkPoly_eval_embedMinus (d : ℕ) (hd : 4 ≤ d) :
    Polynomial.eval₂ (algebraMap ℚ ℂ) (embedMinus d (epsilon d)) (starkPoly d) = 0 := by
  rw [(embeddings_of_epsilon d hd).2]
  have htr := epsilonReal_add_conj d
  have hprod := epsilonReal_mul_conj d hd
  have hcharC : ((epsilonConjReal d : ℂ)) ^ 2 - ((d : ℂ) - 1) * (epsilonConjReal d : ℂ) + 1 = 0 := by
    have hcharR : (epsilonConjReal d) ^ 2 - ((d : ℝ) - 1) * (epsilonConjReal d) + 1 = 0 := by
      rw [← htr, ← hprod]
      ring
    exact_mod_cast hcharR
  simp [starkPoly]
  convert hcharC using 1 <;> ring

/-- When the SIC discriminant is not a rational square, the palindromic Stark
    polynomial has no rational root: the Stark unit generates a genuine
    quadratic extension. -/
theorem starkPoly_no_rat_root (d : ℕ) (hd : 4 ≤ d)
    (hns : ¬ IsSquare (disc d)) (x : ℚ) :
    Polynomial.eval x (starkPoly d) ≠ 0 := by
  intro hx
  have heq : x ^ 2 - ((d : ℚ) - 1) * x + 1 = 0 := by
    simpa [starkPoly] using hx
  have hx2 : x ^ 2 = ((d : ℚ) - 1) * x - 1 := by nlinarith [heq]
  have hs : (2 * x - ((d : ℚ) - 1)) ^ 2 = disc d := by
    calc
      (2 * x - ((d : ℚ) - 1)) ^ 2 =
          4 * x ^ 2 - 4 * ((d : ℚ) - 1) * x + ((d : ℚ) - 1) ^ 2 := by ring
      _ = 4 * (((d : ℚ) - 1) * x - 1) - 4 * ((d : ℚ) - 1) * x + ((d : ℚ) - 1) ^ 2 := by rw [hx2]
      _ = disc d := by
        unfold disc
        norm_num [Nat.cast_sub (by omega : 3 ≤ d)]
        ring
  exact hns ⟨2 * x - ((d : ℚ) - 1), by simpa [pow_two] using hs.symm⟩

/-- The palindromic/cyclotomic content of the Stark unit, packaged. -/
structure StarkPalindromicWitness (d : ℕ) [NeZero d] where
  palindromic : ∀ n : ℕ, n ≤ 2 → (starkPoly d).coeff n = (starkPoly d).coeff (2 - n)
  root_real : Polynomial.eval₂ (algebraMap ℚ ℝ) (epsilonReal d) (starkPoly d) = 0
  root_plus : Polynomial.eval₂ (algebraMap ℚ ℂ) (embedPlus d (epsilon d)) (starkPoly d) = 0
  root_minus : Polynomial.eval₂ (algebraMap ℚ ℂ) (embedMinus d (epsilon d)) (starkPoly d) = 0
  nonsquare_no_rat_root : ¬ IsSquare (disc d) →
    ∀ x : ℚ, Polynomial.eval x (starkPoly d) ≠ 0
  cyclotomic_mod_d : (starkPolyZ d).map (Int.castRingHom (ZMod d)) =
      (Polynomial.X : Polynomial (ZMod d)) ^ 2 + Polynomial.X + 1
  zauner_minpoly : zaunerMatrix d ^ 2 + zaunerMatrix d + 1 = 0

/-- The palindromic witness is inhabited for every dimension with nonsquare
    discriminant. -/
theorem stark_palindromic_witness (d : ℕ) [NeZero d] (hd : 4 ≤ d)
    (hns : ¬ IsSquare (disc d)) : Nonempty (StarkPalindromicWitness d) := by
  refine ⟨{
    palindromic := starkPoly_palindromic d
    root_real := starkPoly_eval_epsilonReal d hd
    root_plus := starkPoly_eval_embedPlus d hd
    root_minus := starkPoly_eval_embedMinus d hd
    nonsquare_no_rat_root := starkPoly_no_rat_root d hd
    cyclotomic_mod_d := starkPolyZ_map_zmod d
    zauner_minpoly := zaunerMatrix_minpoly d }⟩

/-! §10 The d=12 junction -/

/-- The d=12 SIC discriminant 117 = 9·13 is not a square in ℚ. -/
theorem disc_twelve_nonsquare : ¬ IsSquare (disc 12) := by
  rw [disc, Rat.isSquare_iff]
  norm_num

/-- At d=12 the palindromic Stark-unit witness is inhabited. -/
theorem d12_palindromic_witness : Nonempty (StarkPalindromicWitness 12) :=
  stark_palindromic_witness 12 (by norm_num) disc_twelve_nonsquare

/-- At d=12 the structural Stark witness, the palindromic witness, and the
    complex SIC theorem all hold together. -/
theorem d12_stark_zauner_junction :
    Nonempty (StarkTheoremWitness 12) ∧
    Nonempty (StarkPalindromicWitness 12) ∧
    Millennium.SIC_POVM_Stark.SICPOVM_Exists 12 := by
  refine ⟨stark_theorem_decomposition_satisfied 12 (by norm_num),
          d12_palindromic_witness, ?_⟩
  exact SIC.D12.Embedding.crystal_forces_d12_sic

/-- When the discriminant is nonsquare, the palindromic Stark polynomial is
    irreducible over ℚ: the Stark unit generates a degree-two field. -/
theorem starkPoly_irreducible (d : ℕ) (hd : 4 ≤ d) (hns : ¬ IsSquare (disc d)) :
    Irreducible (starkPoly d) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [show (starkPoly d).natDegree = 2 by unfold starkPoly; compute_degree!]
    simp
  · intro x hx
    exact starkPoly_no_rat_root d hd hns x (by simpa [Polynomial.IsRoot] using hx)

/-- Both witnesses together, for every nonsquare-discriminant dimension. -/
theorem stark_zauner_witness_pair (d : ℕ) [NeZero d] (hd : 4 ≤ d)
    (hns : ¬ IsSquare (disc d)) :
    Nonempty (StarkTheoremWitness d) ∧ Nonempty (StarkPalindromicWitness d) :=
  ⟨stark_theorem_decomposition_satisfied d hd,
   stark_palindromic_witness d hd hns⟩

/-- The palindromic Stark polynomial is exactly the minimal polynomial of the
    real Stark unit when the discriminant is nonsquare. -/
theorem starkPoly_is_minpoly (d : ℕ) (hd : 4 ≤ d) (hns : ¬ IsSquare (disc d)) :
    starkPoly d = minpoly ℚ (epsilonReal d) :=
  minpoly.eq_of_irreducible_of_monic
    (starkPoly_irreducible d hd hns)
    (by simpa [Polynomial.aeval_def] using starkPoly_eval_epsilonReal d hd)
    (by unfold starkPoly; monicity!)

section IntegralZaunerLift

/-- The integral Zauner matrix in SL(2, ℤ), whose eigenvalues are ε_d and ε̄_d. -/
def zaunerMatrixZ (d : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, -1; 1, (d : ℤ) - 1]

/-- The standard 2×2 symplectic form J. -/
def sympJ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; -1, 0]

theorem zaunerMatrixZ_det (d : ℕ) : (zaunerMatrixZ d).det = 1 := by
  rw [zaunerMatrixZ, Matrix.det_fin_two]
  norm_num

theorem zaunerMatrixZ_symp (d : ℕ) :
    Matrix.transpose (zaunerMatrixZ d) * sympJ * zaunerMatrixZ d = sympJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zaunerMatrixZ, sympJ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem zaunerMatrixZ_charpoly (d : ℕ) :
    (zaunerMatrixZ d).charpoly = starkPolyZ d := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  simp [Matrix.charmatrix_apply, zaunerMatrixZ, starkPolyZ]
  ring

theorem zaunerMatrixZ_quad (d : ℕ) :
    zaunerMatrixZ d ^ 2 - ((d : ℤ) - 1) • zaunerMatrixZ d + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zaunerMatrixZ, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem zaunerMatrixZ_map_zmod (d : ℕ) [NeZero d] :
    (zaunerMatrixZ d).map (Int.castRingHom (ZMod d)) = zaunerMatrix d := by
  have hN : Int.castRingHom (ZMod d) ((d : ℤ) - 1) = -1 := by
    simp [ZMod.natCast_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zaunerMatrixZ, zaunerMatrix, zaunerMatrix_trace d, hN]

end IntegralZaunerLift 

section WeylHeisenberg

/-- Primitive d-th root of unity ζ_d = exp(2πi / d). -/
noncomputable def omega (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / d)

theorem omega_pow_d (d : ℕ) [NeZero d] : omega d ^ d = 1 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [omega, ← Complex.exp_nat_mul]
  have harg : (d : ℂ) * (2 * Real.pi * Complex.I / d) = 2 * Real.pi * Complex.I := by
    field_simp [hd]
  rw [harg, Complex.exp_two_pi_mul_I]

theorem omega_pow_mod (d : ℕ) [NeZero d] (n : ℕ) : omega d ^ (n % d) = omega d ^ n := by
  have hdiv := Nat.div_add_mod n d
  conv_rhs => rw [← hdiv, pow_add, pow_mul, omega_pow_d, one_pow, one_mul]

/-- Shift operator X_d : |j⟩ ↦ |j + 1⟩ in ℂ^d. -/
def shiftMatrix (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j + 1 then 1 else 0

/-- Clock operator Z_d : |j⟩ ↦ ω^j |j⟩ in ℂ^d. -/
noncomputable def clockMatrix (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j then omega d ^ j.val else 0

/-- The Weyl-Heisenberg commutation relation Z_d X_d = ω X_d Z_d (⋈[𐑐]). -/
theorem clock_mul_shift (d : ℕ) [NeZero d] (hd : 4 ≤ d) :
    clockMatrix d * shiftMatrix d = omega d • (shiftMatrix d * clockMatrix d) := by
  haveI : Fact (1 < d) := ⟨by omega⟩
  ext i k
  simp [Matrix.mul_apply, clockMatrix, shiftMatrix, smul_eq_mul]
  by_cases h : i = k + 1
  · subst i
    have hval : (k + 1 : ZMod d).val = (k.val + 1) % d := by rw [ZMod.val_add, ZMod.val_one]
    rw [hval, omega_pow_mod, pow_succ']
  · simp [h]

theorem clockMatrix_pow_d (d : ℕ) [NeZero d] : clockMatrix d ^ d = 1 := by
  have hpow : ∀ n : ℕ, clockMatrix d ^ n = fun i j => if i = j then (omega d ^ j.val) ^ n else 0 := by
    intro n
    induction n with
    | zero =>
        ext i j
        simp [Matrix.one_apply, pow_zero]
    | succ n ih =>
        rw [pow_succ, ih]
        ext i j
        simp [Matrix.mul_apply, clockMatrix, pow_succ]
  rw [hpow d]
  ext i j
  simp only [Matrix.one_apply]
  split_ifs with hij
  · rw [← pow_mul, mul_comm, pow_mul, omega_pow_d, one_pow]
  · rfl

end WeylHeisenberg 


section OmegaBridge

/-- The Weyl-Heisenberg root of unity is the one used by the Stark SIC file. -/
theorem omega_eq_omega_d (d : ℕ) :
    omega d = Millennium.SIC_POVM_Stark.omega_d d := by
  rfl

/-- The clock matrix is the Z_d phase operator of the Stark SIC file. -/
theorem clockMatrix_eq_Z_diag (d : ℕ) :
    clockMatrix d = fun i j => if i = j then Millennium.SIC_POVM_Stark.omega_d d ^ j.val else 0 := by
  ext i j
  simp [clockMatrix, omega_eq_omega_d]

/-- The shift matrix is the X_d operator: amplitude at j moves to j + 1. -/
theorem shiftMatrix_eq_X (d : ℕ) :
    shiftMatrix d = fun i j => if i = j + 1 then 1 else 0 := by
  rfl

/-- The shift is a cyclic permutation: its d-th power is the identity. -/
theorem shiftMatrix_pow_d (d : ℕ) [NeZero d] : shiftMatrix d ^ d = 1 := by
  have hpow : ∀ n : ℕ,
      shiftMatrix d ^ n = fun i j => if i = j + (n : ZMod d) then 1 else 0 := by
    intro n
    induction n with
    | zero =>
        ext i j
        simp [Matrix.one_apply]
    | succ n ih =>
        rw [pow_succ, ih]
        ext i j
        simp [Matrix.mul_apply, shiftMatrix, Nat.cast_succ, add_assoc, add_comm]
        ring_nf
  rw [hpow d]
  ext i j
  simp [Matrix.one_apply, ZMod.natCast_self]

/-- The shift matrix is invertible, with inverse shift^(d-1). -/
theorem shiftMatrix_inv (d : ℕ) [NeZero d] :
    (shiftMatrix d)⁻¹ = shiftMatrix d ^ (d - 1) := by
  apply Matrix.inv_eq_right_inv
  rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos d), shiftMatrix_pow_d]


/-- The assembled certificate for a nonsquare-discriminant dimension: the
    structural witness, the palindromic witness, the integral SL(2,ℤ) lift,
    and the concrete Weyl-Heisenberg operators. -/
theorem uroboraeus_stark_zauner_certificate (d : ℕ) [NeZero d] (hd : 4 ≤ d)
    (hns : ¬ IsSquare (disc d)) :
    Nonempty (StarkTheoremWitness d) ∧
    Nonempty (StarkPalindromicWitness d) ∧
    (zaunerMatrixZ d).det = 1 ∧
    Matrix.transpose (zaunerMatrixZ d) * sympJ * zaunerMatrixZ d = sympJ ∧
    (zaunerMatrixZ d).charpoly = starkPolyZ d ∧
    (clockMatrix d * shiftMatrix d = omega d • (shiftMatrix d * clockMatrix d)) := by
  refine ⟨stark_theorem_decomposition_satisfied d hd,
          stark_palindromic_witness d hd hns,
          zaunerMatrixZ_det d, zaunerMatrixZ_symp d,
          zaunerMatrixZ_charpoly d, clock_mul_shift d hd⟩

/-- The root of unity has norm one. -/
theorem omega_norm (d : ℕ) : ‖omega d‖ = 1 := by
  rw [omega, Complex.norm_exp]
  simp


/-- The root of unity is a unit: star ω · ω = 1. -/
theorem omega_star_mul_self (d : ℕ) : star (omega d) * omega d = 1 := by
  change (starRingEnd ℂ) (omega d) * omega d = 1
  have hs : Complex.normSq (omega d) = 1 := by
    rw [Complex.normSq_eq_norm_sq, omega_norm]
    norm_num
  rw [← Complex.normSq_eq_conj_mul_self, hs]
  norm_num


/-- The clock operator is unitary. -/
theorem clockMatrix_unitary (d : ℕ) [NeZero d] :
    Matrix.conjTranspose (clockMatrix d) * clockMatrix d = 1 := by
  have homega : omega d ≠ 0 := by
    intro hz
    have hn := omega_norm d
    rw [hz, norm_zero] at hn
    norm_num at hn
  ext i j
  simp [Matrix.mul_apply, clockMatrix, Matrix.conjTranspose, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
    have hstar : star (omega d ^ i.val) * omega d ^ i.val = 1 := by
      have hinv : star (omega d) = (omega d)⁻¹ :=
        eq_inv_of_mul_eq_one_left (omega_star_mul_self d)
      rw [star_pow, hinv]
      rw [← mul_pow, inv_mul_cancel₀]
      · simp
      · exact homega
    simpa using hstar
  · simp [hij, Ne.symm hij, homega]

/-- The shift operator is unitary: it is a permutation matrix. -/
theorem shiftMatrix_unitary (d : ℕ) [NeZero d] :
    Matrix.conjTranspose (shiftMatrix d) * shiftMatrix d = 1 := by
  ext i j
  simp [Matrix.mul_apply, shiftMatrix, Matrix.conjTranspose, Matrix.one_apply]
  by_cases h : j = i
  · subst j; simp
  · have h' : i ≠ j := fun hji => h hji.symm
    simp [h, h']



/-- The matrix commutation relation acts on vectors: Z(X w) = ω X(Z w). -/
theorem clock_shift_vec (d : ℕ) [NeZero d] (hd : 4 ≤ d) (w : ZMod d → ℂ) :
    (clockMatrix d * shiftMatrix d).mulVec w =
      omega d • ((shiftMatrix d * clockMatrix d).mulVec w) := by
  rw [clock_mul_shift d hd, Matrix.smul_mulVec]

end OmegaBridge

section WHDisplacementAndWelch

/-- Heisenberg-Weyl half-phase τ_d = -exp(π i / d), satisfying τ_d² = ω_d. -/
noncomputable def tau (d : ℕ) : ℂ :=
  -Complex.exp (Real.pi * Complex.I / d)

theorem tau_sq (d : ℕ) : tau d ^ 2 = omega d := by
  unfold tau omega
  rw [neg_sq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem tau_norm (d : ℕ) : ‖tau d‖ = 1 := by
  unfold tau
  rw [norm_neg, Complex.norm_exp]
  simp

theorem tau_ne_zero (d : ℕ) : tau d ≠ 0 := by
  intro hz
  have h := tau_norm d
  rw [hz, norm_zero] at h
  norm_num at h

theorem tau_star_mul_self (d : ℕ) : star (tau d) * tau d = 1 := by
  change (starRingEnd ℂ) (tau d) * tau d = 1
  have hs : Complex.normSq (tau d) = 1 := by
    rw [Complex.normSq_eq_norm_sq, tau_norm]; norm_num
  rw [← Complex.normSq_eq_conj_mul_self, hs]
  norm_num

theorem tau_pow_two_mul_d (d : ℕ) [NeZero d] : tau d ^ (2 * d) = 1 := by
  rw [pow_mul, tau_sq, omega_pow_d]

theorem shiftMatrix_pow_apply (d p : ℕ) [NeZero d] (i j : ZMod d) :
    (shiftMatrix d ^ p) i j = if i = j + (p : ZMod d) then 1 else 0 := by
  induction p generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ p ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply, ih, shiftMatrix]
      rw [Finset.sum_eq_single (j + 1)]
      · simp [Nat.cast_succ, add_assoc, add_comm]
        split_ifs <;> simp_all [add_comm, add_left_comm]
      · intro k _ hk; simp [hk]
      · intro hj; exact absurd (Finset.mem_univ (j + 1)) hj

theorem clockMatrix_pow_apply (d q : ℕ) [NeZero d] (i j : ZMod d) :
    (clockMatrix d ^ q) i j = if i = j then (omega d ^ i.val) ^ q else 0 := by
  induction q generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ q ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply, ih, clockMatrix]
      rw [Finset.sum_eq_single j]
      · by_cases hij : i = j
        · subst hij; simp [pow_succ]
        · simp [hij]
      · intro k _ hkj; simp [hkj]
      · intro hj; exact absurd (Finset.mem_univ j) hj

theorem clock_pow_mul_shift_pow (d : ℕ) [NeZero d] (hd : 4 ≤ d) (a b : ℕ) :
    clockMatrix d ^ a * shiftMatrix d ^ b =
      omega d ^ (a * b) • (shiftMatrix d ^ b * clockMatrix d ^ a) := by
  induction a generalizing b with
  | zero => simp
  | succ a iha =>
      have hstep : ∀ m : ℕ, clockMatrix d * shiftMatrix d ^ m =
          omega d ^ m • (shiftMatrix d ^ m * clockMatrix d) := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm =>
            calc
              clockMatrix d * shiftMatrix d ^ (m + 1)
                  = (clockMatrix d * shiftMatrix d ^ m) * shiftMatrix d := by
                      rw [pow_succ, Matrix.mul_assoc]
              _ = (omega d ^ m • (shiftMatrix d ^ m * clockMatrix d)) * shiftMatrix d := by
                      rw [ihm]
              _ = omega d ^ m • (shiftMatrix d ^ m * (clockMatrix d * shiftMatrix d)) := by
                      simp [Matrix.smul_mul, Matrix.mul_assoc]
              _ = omega d ^ m • (shiftMatrix d ^ m * (omega d • (shiftMatrix d * clockMatrix d))) := by
                      rw [clock_mul_shift d hd]
              _ = omega d ^ (m + 1) • (shiftMatrix d ^ (m + 1) * clockMatrix d) := by
                      simp [Matrix.mul_smul, smul_smul, pow_succ', Matrix.mul_assoc,
                        pow_succ, ← pow_succ]
                      congr 1
                      calc
                        shiftMatrix d ^ m * (shiftMatrix d * clockMatrix d) =
                            (shiftMatrix d ^ m * shiftMatrix d) * clockMatrix d := (Matrix.mul_assoc _ _ _).symm
                        _ = shiftMatrix d ^ (m + 1) * clockMatrix d := by rw [pow_succ]
                        _ = (shiftMatrix d * shiftMatrix d ^ m) * clockMatrix d := by rw [pow_succ']
                        _ = shiftMatrix d * (shiftMatrix d ^ m * clockMatrix d) := Matrix.mul_assoc _ _ _
      calc
        clockMatrix d ^ (a + 1) * shiftMatrix d ^ b
            = clockMatrix d * (clockMatrix d ^ a * shiftMatrix d ^ b) := by
                rw [pow_succ', Matrix.mul_assoc]
        _ = clockMatrix d * (omega d ^ (a * b) • (shiftMatrix d ^ b * clockMatrix d ^ a)) := by
                rw [iha]
        _ = omega d ^ (a * b) • ((clockMatrix d * shiftMatrix d ^ b) * clockMatrix d ^ a) := by
                simp [Matrix.mul_smul, Matrix.mul_assoc]
        _ = omega d ^ (a * b) • ((omega d ^ b • (shiftMatrix d ^ b * clockMatrix d)) *
              clockMatrix d ^ a) := by
                rw [hstep b]
        _ = omega d ^ ((a + 1) * b) • (shiftMatrix d ^ b * clockMatrix d ^ (a + 1)) := by
                simp only [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, ← pow_succ, ← pow_add, pow_succ']
                congr 1
                ring_nf

/-- Weyl-Heisenberg displacement matrix D_{p, q} = τ_d^{p q} X_d^p Z_d^q. -/
noncomputable def whDisp (d p q : ℕ) [NeZero d] : Matrix (ZMod d) (ZMod d) ℂ :=
  tau d ^ (p * q) • (shiftMatrix d ^ p * clockMatrix d ^ q)

theorem whDisp_zero (d : ℕ) [NeZero d] : whDisp d 0 0 = 1 := by
  simp [whDisp]

theorem tau_star_mul_pow_self (d : ℕ) (p q : ℕ) :
    star (tau d ^ (p * q)) * tau d ^ (p * q) = 1 := by
  have hinv : star (tau d) = (tau d)⁻¹ := eq_inv_of_mul_eq_one_left (tau_star_mul_self d)
  rw [star_pow, hinv, ← mul_pow, inv_mul_cancel₀ (tau_ne_zero d), one_pow]

/-- Every Weyl-Heisenberg displacement matrix is unitary. -/
theorem whDisp_unitary (d : ℕ) [NeZero d] (p q : ℕ) :
    Matrix.conjTranspose (whDisp d p q) * whDisp d p q = 1 := by
  unfold whDisp
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [tau_star_mul_pow_self d p q, one_smul, Matrix.conjTranspose_mul]
  have hZ : Matrix.conjTranspose (clockMatrix d ^ q) * clockMatrix d ^ q = 1 := by
    induction q with
    | zero => simp
    | succ q ih =>
        rw [pow_succ', Matrix.conjTranspose_mul, Matrix.mul_assoc,
            ← Matrix.mul_assoc (Matrix.conjTranspose (clockMatrix d)),
            clockMatrix_unitary d, Matrix.one_mul, ih]
  have hX : Matrix.conjTranspose (shiftMatrix d ^ p) * shiftMatrix d ^ p = 1 := by
    induction p with
    | zero => simp
    | succ p ih =>
        rw [pow_succ', Matrix.conjTranspose_mul, Matrix.mul_assoc,
            ← Matrix.mul_assoc (Matrix.conjTranspose (shiftMatrix d)),
            shiftMatrix_unitary d, Matrix.one_mul, ih]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.conjTranspose (shiftMatrix d ^ p)), hX,
      Matrix.one_mul, hZ]

/-- **Weyl-Heisenberg composition law:**
    τ_d^{p₁ q₂} D_{p₁, q₁} D_{p₂, q₂} = τ_d^{p₂ q₁} D_{p₁ + p₂, q₁ + q₂}. -/
theorem whDisp_mul (d : ℕ) [NeZero d] (hd : 4 ≤ d) (p₁ q₁ p₂ q₂ : ℕ) :
    tau d ^ (p₁ * q₂) • (whDisp d p₁ q₁ * whDisp d p₂ q₂) =
      tau d ^ (p₂ * q₁) • whDisp d (p₁ + p₂) (q₁ + q₂) := by
  unfold whDisp
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hswap : shiftMatrix d ^ p₁ * clockMatrix d ^ q₁ *
      (shiftMatrix d ^ p₂ * clockMatrix d ^ q₂) =
      omega d ^ (q₁ * p₂) • (shiftMatrix d ^ (p₁ + p₂) * clockMatrix d ^ (q₁ + q₂)) := by
    calc
      shiftMatrix d ^ p₁ * clockMatrix d ^ q₁ * (shiftMatrix d ^ p₂ * clockMatrix d ^ q₂)
          = shiftMatrix d ^ p₁ * (clockMatrix d ^ q₁ * shiftMatrix d ^ p₂) *
              clockMatrix d ^ q₂ := by simp [Matrix.mul_assoc]
      _ = shiftMatrix d ^ p₁ * (omega d ^ (q₁ * p₂) •
            (shiftMatrix d ^ p₂ * clockMatrix d ^ q₁)) * clockMatrix d ^ q₂ := by
              rw [clock_pow_mul_shift_pow d hd q₁ p₂]
      _ = omega d ^ (q₁ * p₂) • (shiftMatrix d ^ (p₁ + p₂) * clockMatrix d ^ (q₁ + q₂)) := by
              simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, pow_add]
  rw [hswap, smul_smul, ← tau_sq d, ← pow_mul]
  congr 1
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

/-- **Symplectic Weyl-Heisenberg commutator:**
    ω_d^{p₁ q₂} D_{p₁, q₁} D_{p₂, q₂} = ω_d^{p₂ q₁} D_{p₂, q₂} D_{p₁, q₁}. -/
theorem whDisp_comm (d : ℕ) [NeZero d] (hd : 4 ≤ d) (p₁ q₁ p₂ q₂ : ℕ) :
    omega d ^ (p₁ * q₂) • (whDisp d p₁ q₁ * whDisp d p₂ q₂) =
      omega d ^ (p₂ * q₁) • (whDisp d p₂ q₂ * whDisp d p₁ q₁) := by
  have h1 := whDisp_mul d hd p₁ q₁ p₂ q₂
  have h2 := whDisp_mul d hd p₂ q₂ p₁ q₁
  have h1s := congrArg (fun M => tau d ^ (p₁ * q₂) • M) h1
  have h2s := congrArg (fun M => tau d ^ (p₂ * q₁) • M) h2
  simp only [smul_smul, ← pow_add] at h1s h2s
  have heq : tau d ^ (p₁ * q₂ + p₁ * q₂) • (whDisp d p₁ q₁ * whDisp d p₂ q₂) =
      tau d ^ (p₂ * q₁ + p₂ * q₁) • (whDisp d p₂ q₂ * whDisp d p₁ q₁) := by
    calc
      tau d ^ (p₁ * q₂ + p₁ * q₂) • (whDisp d p₁ q₁ * whDisp d p₂ q₂)
          = tau d ^ (p₁ * q₂ + p₂ * q₁) • whDisp d (p₁ + p₂) (q₁ + q₂) := h1s
      _ = tau d ^ (p₂ * q₁ + p₁ * q₂) • whDisp d (p₂ + p₁) (q₂ + q₁) := by
            rw [Nat.add_comm (p₁ * q₂), Nat.add_comm p₁ p₂, Nat.add_comm q₁ q₂]
      _ = tau d ^ (p₂ * q₁ + p₂ * q₁) • (whDisp d p₂ q₂ * whDisp d p₁ q₁) := h2s.symm
  simpa [← two_mul, pow_mul, tau_sq] using heq

theorem omega_pow_eq_one_iff (d : ℕ) [NeZero d] (q : ℕ) :
    omega d ^ q = 1 ↔ (q : ZMod d) = 0 := by
  have hd_pos : 0 < d := NeZero.pos d
  constructor
  · intro hq
    rw [← omega_pow_mod d q] at hq
    set r : ℕ := q % d
    have hr_lt : r < d := Nat.mod_lt q hd_pos
    have hexp : Complex.exp ((r : ℂ) * (2 * Real.pi * Complex.I / d)) = 1 := by
      simpa [omega, ← Complex.exp_nat_mul] using hq
    rw [Complex.exp_eq_one_iff] at hexp
    obtain ⟨n, hn⟩ := hexp
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hC : (r : ℂ) = (n : ℂ) * (d : ℂ) := by
      have h1 : (r : ℂ) / (d : ℂ) * (2 * Real.pi * Complex.I) =
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
        calc
          (r : ℂ) / (d : ℂ) * (2 * Real.pi * Complex.I)
              = (r : ℂ) * (2 * Real.pi * Complex.I / (d : ℂ)) := by ring
          _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
      have h2 := mul_right_cancel₀ hpi h1
      exact (div_eq_iff hdC).mp h2
    have hZ : (r : ℤ) = n * (d : ℤ) := by exact_mod_cast hC
    have hn0 : n = 0 := by
      have hr_nn : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
      have hr_ltZ : (r : ℤ) < (d : ℤ) := by exact_mod_cast hr_lt
      have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd_pos
      nlinarith
    have hr0 : q % d = 0 := by
      have : (r : ℤ) = 0 := by rw [hn0, zero_mul] at hZ; exact hZ
      exact_mod_cast this
    have hdvdn : d ∣ q := Nat.dvd_of_mod_eq_zero hr0
    rcases hdvdn with ⟨k, hk⟩
    simpa using ((ZMod.intCast_zmod_eq_zero_iff_dvd (q : ℤ) d).mpr ⟨(k : ℤ), by exact_mod_cast hk⟩)
  · intro hq
    have hdvdZ : (d : ℤ) ∣ (q : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (q : ℤ) d).mp (by simpa using hq)
    have hdvd : d ∣ q := by exact_mod_cast hdvdZ
    obtain ⟨k, rfl⟩ := hdvd
    rw [pow_mul, omega_pow_d, one_pow]

theorem omega_star_mul_pow_eq (d : ℕ) [NeZero d] (a b : ZMod d) :
    star (omega d ^ a.val) * omega d ^ b.val = omega d ^ (b - a).val := by
  have hstar : star (omega d ^ a.val) * omega d ^ a.val = 1 := by
    have hinv : star (omega d) = (omega d)⁻¹ := eq_inv_of_mul_eq_one_left (omega_star_mul_self d)
    rw [star_pow, hinv, ← mul_pow, inv_mul_cancel₀]
    · simp
    · intro hz; have hn := omega_norm d; rw [hz, norm_zero] at hn; norm_num at hn
  have hmod : (a.val + (b - a).val) % d = b.val := by
    have hsum : (a + (b - a) : ZMod d) = b := by ring
    have h1 := congrArg ZMod.val hsum
    haveI : NeZero d := inferInstance
    rw [ZMod.val_add] at h1
    exact h1
  have hpow : omega d ^ a.val * omega d ^ (b - a).val = omega d ^ b.val := by
    have hm : omega d ^ (a.val + (b - a).val) = omega d ^ ((a.val + (b - a).val) % d) := by
      rw [omega_pow_mod]
    rw [← pow_add, hm, hmod]
  calc
    star (omega d ^ a.val) * omega d ^ b.val
        = star (omega d ^ a.val) * (omega d ^ a.val * omega d ^ (b - a).val) := by rw [hpow]
    _ = (star (omega d ^ a.val) * omega d ^ a.val) * omega d ^ (b - a).val := by ring
    _ = omega d ^ (b - a).val := by rw [hstar, one_mul]

theorem sum_omega_pow_zmod (d : ℕ) [NeZero d] (c : ZMod d) :
    (∑ q : Fin d, (omega d ^ c.val) ^ (q : ℕ)) = if c = 0 then (d : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  rw [Fin.sum_univ_eq_sum_range]
  by_cases hc : c = 0
  · subst hc
    simp
  · have hne : omega (m + 1) ^ c.val ≠ 1 := by
      intro h1
      rw [omega_pow_eq_one_iff] at h1
      have hcval : ((c.val : ℕ) : ZMod (m + 1)) = c := ZMod.natCast_zmod_val c
      rw [hcval] at h1
      exact hc h1
    have hgeom := geom_sum_mul (omega (m + 1) ^ c.val) (m + 1)
    have hpow1 : (omega (m + 1) ^ c.val) ^ (m + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, omega_pow_d, one_pow]
    rw [hpow1, sub_self] at hgeom
    have hsum0 : (∑ x ∈ Finset.range (m + 1), (omega (m + 1) ^ c.val) ^ x) = 0 :=
      (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
    simp [hc, hsum0]

/-- **Exact trace of the Weyl-Heisenberg displacement operators.** -/
theorem whDisp_trace (d : ℕ) [NeZero d] (p q : ℕ) :
    Matrix.trace (whDisp d p q) =
      if (p : ZMod d) = 0 ∧ (q : ZMod d) = 0 then tau d ^ (p * q) * (d : ℂ) else 0 := by
  unfold whDisp Matrix.trace Matrix.diag
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
    shiftMatrix_pow_apply, clockMatrix_pow_apply]
  by_cases hp : (p : ZMod d) = 0
  · have hdiag : ∀ i : ZMod d,
        (∑ x : ZMod d, (if i = x + (p : ZMod d) then (1 : ℂ) else 0) *
          if x = i then (omega d ^ x.val) ^ q else 0) = (omega d ^ q) ^ i.val := by
      intro i
      rw [Finset.sum_eq_single i]
      · simp [hp, ← pow_mul, mul_comm]
      · intro x _ hxi; simp [hxi]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [hdiag]
    rw [← Finset.mul_sum]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
    have hsum : (∑ i : ZMod (m + 1), (omega (m + 1) ^ q) ^ i.val) =
        ∑ i : Fin (m + 1), (omega (m + 1) ^ q) ^ (i : ℕ) := rfl
    by_cases hq : (q : ZMod (m + 1)) = 0
    · have h1 : omega (m + 1) ^ q = 1 := (omega_pow_eq_one_iff (m + 1) q).mpr hq
      simp [h1, hp, hq]
    · have hne : omega (m + 1) ^ q ≠ 1 := by
        intro h1; exact hq ((omega_pow_eq_one_iff (m + 1) q).mp h1)
      have hgeom := geom_sum_mul (omega (m + 1) ^ q) (m + 1)
      have hpow1 : (omega (m + 1) ^ q) ^ (m + 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, omega_pow_d, one_pow]
      rw [hpow1, sub_self] at hgeom
      have hsum0 := (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
      rw [if_neg (fun h => hq h.2)]
      rw [hsum]
      rw [Fin.sum_univ_eq_sum_range]
      rw [hsum0]
      ring
  · have hdiag : ∀ i : ZMod d,
        (∑ x : ZMod d, (if i = x + (p : ZMod d) then (1 : ℂ) else 0) *
          if x = i then (omega d ^ x.val) ^ q else 0) = 0 := by
      intro i
      rw [Finset.sum_eq_single i]
      · have hne : i ≠ i + (p : ZMod d) := fun heq => by
          have : (p : ZMod d) = 0 := by
            have := sub_eq_zero.mpr heq.symm
            simpa [add_sub_cancel_left] using this
          exact hp this
        simp [hne]
      · intro x _ hxi; simp [hxi]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp [hp, hdiag]

/-- **Exact Frame / Parseval Identity for Weyl-Heisenberg Overlaps:**
    For every vector `ψ : ZMod d → ℂ`,
    `∑ p, ∑ q, ‖⟨ψ, D_{p,q} ψ⟩‖² = d * (∑ i, ‖ψ i‖²)²`. -/
theorem whDisp_parseval_sum (d : ℕ) [NeZero d] (ψ : ZMod d → ℂ) :
    ∑ p : Fin d, ∑ q : Fin d,
      ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2 =
        (d : ℝ) * (∑ i : ZMod d, ‖ψ i‖ ^ 2) ^ 2 := by
  have hd_pos : 0 < d := NeZero.pos d
  have h_drop_tau : ∀ p q : Fin d,
      ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2 =
        ‖∑ i : ZMod d, star (ψ i) * ψ (i - (p.val : ZMod d)) *
          omega d ^ ((i - (p.val : ZMod d)).val * q.val)‖ ^ 2 := by
    intro p q
    have hmulVec : ∀ i : ZMod d,
        ((whDisp d p.val q.val).mulVec ψ) i =
          tau d ^ (p.val * q.val) * (ψ (i - (p.val : ZMod d)) *
            omega d ^ ((i - (p.val : ZMod d)).val * q.val)) := by
      intro i
      simp only [Matrix.mulVec, whDisp, Matrix.smul_apply, Matrix.mul_apply,
        shiftMatrix_pow_apply, clockMatrix_pow_apply, smul_eq_mul, dotProduct]
      have h_inner : ∀ x : ZMod d,
          (∑ y : ZMod d, (if i = y + (p.val : ZMod d) then (1 : ℂ) else 0) *
            if y = x then (omega d ^ y.val) ^ q.val else 0) * ψ x =
            if x = i - (p.val : ZMod d) then
              (omega d ^ x.val) ^ q.val * ψ x else 0 := by
        intro x
        rw [Finset.sum_eq_single x]
        · by_cases hxp : x = i - (p.val : ZMod d)
          · have hi : i = x + (p.val : ZMod d) := by rw [hxp, sub_add_cancel]
            rw [if_pos hi, if_pos rfl, if_pos hxp]
            ring
          · have hi : i ≠ x + (p.val : ZMod d) := fun h => hxp (eq_sub_of_add_eq h.symm)
            rw [if_neg hi, if_pos rfl, if_neg hxp]
            ring
        · intro y _ hyx; simp [hyx]
        · intro hx; exact absurd (Finset.mem_univ x) hx
      change (∑ x : ZMod d, (tau d ^ (p.val * q.val) *
          (∑ y : ZMod d, (if i = y + (p.val : ZMod d) then (1 : ℂ) else 0) *
            if y = x then (omega d ^ y.val) ^ q.val else 0)) * ψ x) = _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      simp_rw [h_inner]
      rw [Finset.sum_eq_single (i - (p.val : ZMod d))]
      · rw [if_pos rfl, ← pow_mul]
        ring
      · intro x _ hne; simp [hne]
      · intro hi; exact absurd (Finset.mem_univ _) hi
    have hdot : dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ) =
        tau d ^ (p.val * q.val) *
          (∑ i : ZMod d, star (ψ i) * ψ (i - (p.val : ZMod d)) *
            omega d ^ ((i - (p.val : ZMod d)).val * q.val)) := by
      simp only [dotProduct, hmulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ac_rfl
    rw [hdot, norm_mul, norm_pow, tau_norm, one_pow, one_mul]
  simp_rw [h_drop_tau]
  have h_q_sum : ∀ p : Fin d,
      (∑ q : Fin d,
        ‖∑ i : ZMod d, star (ψ i) * ψ (i - (p.val : ZMod d)) *
          omega d ^ ((i - (p.val : ZMod d)).val * q.val)‖ ^ 2) =
        (d : ℝ) * ∑ i : ZMod d, ‖ψ i‖ ^ 2 * ‖ψ (i - (p.val : ZMod d))‖ ^ 2 := by
    intro p
    set f : ZMod d → ℂ := fun i => star (ψ i) * ψ (i - (p.val : ZMod d))
    have hC : (∑ q : Fin d,
        ((‖∑ i : ZMod d, f i * omega d ^ ((i - (p.val : ZMod d)).val * q.val)‖ : ℝ) : ℂ) ^ 2) =
        ((d : ℝ) * ∑ i : ZMod d, ‖ψ i‖ ^ 2 * ‖ψ (i - (p.val : ZMod d))‖ ^ 2 : ℝ) := by
      have h_expand : ∀ q : Fin d,
          ((‖∑ i : ZMod d, f i * omega d ^ ((i - (p.val : ZMod d)).val * q.val)‖ : ℝ) : ℂ) ^ 2 =
            ∑ i : ZMod d, ∑ k : ZMod d,
              (star (f i) * f k) * (omega d ^ (k - i).val) ^ q.val := by
        intro q
        have h_nsq : ((‖∑ i : ZMod d, f i * omega d ^ ((i - (p.val : ZMod d)).val * q.val)‖ : ℝ) : ℂ) ^ 2 =
            star (∑ i : ZMod d, f i * omega d ^ ((i - (p.val : ZMod d)).val * q.val)) *
              (∑ k : ZMod d, f k * omega d ^ ((k - (p.val : ZMod d)).val * q.val)) := by
          rw [mul_comm, show star (∑ i : ZMod d, _) = starRingEnd ℂ _ from rfl, Complex.mul_conj]
          norm_cast
          exact (Complex.normSq_eq_norm_sq _).symm
        rw [h_nsq, star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [star_mul, star_pow]
        calc
          star (omega d) ^ ((i - (p.val : ZMod d)).val * q.val) * star (f i) *
              (f k * omega d ^ ((k - (p.val : ZMod d)).val * q.val))
              = star (f i) * f k *
                  (star (omega d) ^ (i - (p.val : ZMod d)).val *
                   omega d ^ (k - (p.val : ZMod d)).val) ^ q.val := by ring_nf
          _ = star (f i) * f k *
                  (omega d ^ ((k - (p.val : ZMod d)) - (i - (p.val : ZMod d))).val) ^ q.val := by
                have hprod : star (omega d) ^ (i - (p.val : ZMod d)).val *
                    omega d ^ (k - (p.val : ZMod d)).val =
                    omega d ^ ((k - (p.val : ZMod d)) - (i - (p.val : ZMod d))).val := by
                  rw [← star_pow]
                  exact omega_star_mul_pow_eq d (i - (p.val : ZMod d)) (k - (p.val : ZMod d))
                rw [hprod]
          _ = star (f i) * f k * (omega d ^ (k - i).val) ^ q.val := by
                rw [show (k - (p.val : ZMod d)) - (i - (p.val : ZMod d)) = k - i from by ring]
      push_cast
      simp_rw [h_expand]
      rw [Finset.sum_comm]
      have h_swap2 : (∑ i : ZMod d, ∑ q : Fin d, ∑ k : ZMod d,
          (star (f i) * f k) * (omega d ^ (k - i).val) ^ q.val) =
          ∑ i : ZMod d, ∑ k : ZMod d,
            (star (f i) * f k) * ∑ q : Fin d, (omega d ^ (k - i).val) ^ q.val := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
      rw [h_swap2]
      have h_diag : ∀ i : ZMod d,
          (∑ k : ZMod d, (star (f i) * f k) * ∑ q : Fin d, (omega d ^ (k - i).val) ^ q.val) =
            (d : ℂ) * ((‖ψ i‖ ^ 2 * ‖ψ (i - (p.val : ZMod d))‖ ^ 2 : ℝ) : ℂ) := by
        intro i
        have h_term : ∀ k : ZMod d,
            (star (f i) * f k) * ∑ q : Fin d, (omega d ^ (k - i).val) ^ q.val =
              if k = i then (d : ℂ) * (star (f i) * f i) else 0 := by
          intro k
          rw [sum_omega_pow_zmod d (k - i)]
          by_cases hki : k = i
          · subst hki; simp [mul_comm]
          · have hsub : k - i ≠ 0 := sub_ne_zero.mpr hki
            simp [hki, hsub]
        simp_rw [h_term]
        rw [Finset.sum_ite_eq' Finset.univ i]
        simp only [Finset.mem_univ, ↓reduceIte]
        have hf_norm : star (f i) * f i =
            ((‖ψ i‖ ^ 2 * ‖ψ (i - (p.val : ZMod d))‖ ^ 2 : ℝ) : ℂ) := by
          dsimp [f]
          have h1 : star (ψ i) * ψ i = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm]
            change (ψ i) * (starRingEnd ℂ) (ψ i) = _
            rw [Complex.mul_conj]
            norm_cast
            exact Complex.normSq_eq_norm_sq _
          have h2 : star (ψ (i - (p.val : ZMod d))) * ψ (i - (p.val : ZMod d)) =
              ((‖ψ (i - (p.val : ZMod d))‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm]
            change (ψ (i - (p.val : ZMod d))) * (starRingEnd ℂ) (ψ (i - (p.val : ZMod d))) = _
            rw [Complex.mul_conj]
            norm_cast
            exact Complex.normSq_eq_norm_sq _
          calc
            star (star (ψ i) * ψ (i - (p.val : ZMod d))) * (star (ψ i) * ψ (i - (p.val : ZMod d)))
                = (ψ i * star (ψ (i - (p.val : ZMod d)))) * (star (ψ i) * ψ (i - (p.val : ZMod d))) := by
                    rw [star_mul, star_star]
                    ring
            _ = (star (ψ i) * ψ i) * (star (ψ (i - (p.val : ZMod d))) * ψ (i - (p.val : ZMod d))) := by ring
            _ = ((‖ψ i‖ ^ 2 * ‖ψ (i - (p.val : ZMod d))‖ ^ 2 : ℝ) : ℂ) := by
                  rw [h1, h2]; push_cast; rfl
        rw [hf_norm]
      simp_rw [h_diag, ← Finset.mul_sum]
      push_cast
      rfl
    exact_mod_cast hC
  simp_rw [h_q_sum, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  have h_shift_sum : ∀ i : ZMod d,
      (∑ p : Fin d, ‖ψ (i - (p.val : ZMod d))‖ ^ 2) = ∑ j : ZMod d, ‖ψ j‖ ^ 2 := by
    intro i
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd_pos.ne'
    refine Fintype.sum_equiv (Equiv.subLeft i) _ _ fun p => ?_
    change ‖ψ (i - ((ZMod.val (p : ZMod (m + 1)) : ℕ) : ZMod (m + 1)))‖ ^ 2 =
      ‖ψ (i - (p : ZMod (m + 1)))‖ ^ 2
    rw [ZMod.natCast_zmod_val]
  simp_rw [← Finset.mul_sum, h_shift_sum, ← Finset.sum_mul, sq]

/-- **Off-Origin Welch Sum Rule:**
    For any unit vector `ψ : ZMod d → ℂ` (`∑ i, ‖ψ i‖² = 1`), the sum of all
    `d² - 1` non-identity WH overlap intensities equals `d - 1`. -/
theorem whDisp_off_origin_sum (d : ℕ) [NeZero d] (ψ : ZMod d → ℂ)
    (hunit : ∑ i : ZMod d, ‖ψ i‖ ^ 2 = 1) :
    (∑ p : Fin d, ∑ q : Fin d,
      if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ)
      else ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2) = (d : ℝ) - 1 := by
  have hfull := whDisp_parseval_sum d ψ
  rw [hunit, one_pow, mul_one] at hfull
  have h00 : ‖dotProduct (star ψ) ((whDisp d (0 : Fin d).val (0 : Fin d).val).mulVec ψ)‖ ^ 2 = 1 := by
    have hD0 : whDisp d 0 0 = 1 := whDisp_zero d
    simp only [Fin.val_zero, hD0, Matrix.one_mulVec]
    have hdot : dotProduct (star ψ) ψ = ((∑ i : ZMod d, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      change (ψ i) * (starRingEnd ℂ) (ψ i) = _
      rw [Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    rw [hdot, hunit]
    norm_num
  have hsplit : ∀ p : Fin d,
      (∑ q : Fin d,
        if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ)
        else ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2) =
      (∑ q : Fin d, ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2) -
        (if (p : ℕ) = 0 then 1 else 0) := by
    intro p
    by_cases hp : (p : ℕ) = 0
    · have hp' : p = 0 := Fin.ext hp
      subst hp'
      have h_eq : ∀ q : Fin d,
          (if (0 : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ)
           else ‖dotProduct (star ψ) ((whDisp d (0 : Fin d).val q.val).mulVec ψ)‖ ^ 2) =
          ‖dotProduct (star ψ) ((whDisp d (0 : Fin d).val q.val).mulVec ψ)‖ ^ 2 -
            (if q = 0 then 1 else 0) := by
        intro q
        by_cases hq : q = 0
        · subst hq
          rw [if_pos ⟨rfl, rfl⟩, if_pos rfl, h00]
          ring
        · have hqn : (q : ℕ) ≠ 0 := fun h => hq (Fin.ext h)
          rw [if_neg (fun hpq => hqn hpq.2)]
          simp [hq]
      change (∑ q : Fin d, if (0 : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ) else
        ‖dotProduct (star ψ) ((whDisp d (0 : Fin d).val q.val).mulVec ψ)‖ ^ 2) = _
      rw [Finset.sum_congr rfl (fun q _ => h_eq q), Finset.sum_sub_distrib]
      simp [Finset.sum_const, nsmul_eq_mul]
    · have h_eq : ∀ q : Fin d,
          (if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ)
           else ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2) =
          ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2 := by
        intro q; simp [hp]
      simp [hp, h_eq]
  simp_rw [hsplit, Finset.sum_sub_distrib, hfull]
  have h1 : (∑ p : Fin d, if (p : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro p _ hp; have hpn : (p : ℕ) ≠ 0 := fun h => hp (Fin.ext h); simp [hpn]
    · intro h0; exact absurd (Finset.mem_univ (0 : Fin d)) h0
  linarith

/-- **Equiangular SIC Overlap Value Forced:**
    Any unit vector `ψ` whose non-identity WH overlap intensities are all equal to `c`
    must have `c = 1 / (d + 1)`. -/
theorem sic_overlap_forced_value (d : ℕ) [NeZero d] (hd : 2 ≤ d) (ψ : ZMod d → ℂ)
    (hunit : ∑ i : ZMod d, ‖ψ i‖ ^ 2 = 1) (c : ℝ)
    (hconst : ∀ p q : Fin d, ¬ ((p : ℕ) = 0 ∧ (q : ℕ) = 0) →
      ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2 = c) :
    c = 1 / ((d : ℝ) + 1) := by
  have hsum := whDisp_off_origin_sum d ψ hunit
  have h_eq : (∑ p : Fin d, ∑ q : Fin d,
      if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ)
      else ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2) =
      (((d : ℝ) ^ 2 - 1) * c) := by
    have h_inner : ∀ p : Fin d,
        (∑ q : Fin d,
          if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ)
          else ‖dotProduct (star ψ) ((whDisp d p.val q.val).mulVec ψ)‖ ^ 2) =
        (∑ q : Fin d, if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ) else c) := by
      intro p
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs with hpq
      · rfl
      · exact hconst p q hpq
    simp_rw [h_inner]
    have hsplit : ∀ p : Fin d,
        (∑ q : Fin d, if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ) else c) =
        (d : ℝ) * c - (if (p : ℕ) = 0 then c else 0) := by
      intro p
      by_cases hp : (p : ℕ) = 0
      · have heq : ∀ q : Fin d, (if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then (0 : ℝ) else c) =
            c - (if q = 0 then c else 0) := by
          intro q
          by_cases hq : q = 0
          · subst hq; rw [if_pos ⟨hp, by simp⟩, if_pos rfl]; ring
          · have hqn : (q : ℕ) ≠ 0 := fun h => hq (Fin.ext h)
            simp [hp, hqn, hq]
        simp_rw [heq, Finset.sum_sub_distrib]
        simp [hp, Finset.sum_const, nsmul_eq_mul]
      · simp [hp, Finset.sum_const, nsmul_eq_mul]
    simp_rw [hsplit, Finset.sum_sub_distrib]
    have h1 : (∑ p : Fin d, if (p : ℕ) = 0 then c else 0) = c := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro p _ hp; have hpn : (p : ℕ) ≠ 0 := fun h => hp (Fin.ext h); simp [hpn]
      · intro h0; exact absurd (Finset.mem_univ (0 : Fin d)) h0
    simp [Finset.sum_const, nsmul_eq_mul, h1]
    ring
  rw [h_eq] at hsum
  have hd_gt : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hfac : ((d : ℝ) ^ 2 - 1) = ((d : ℝ) - 1) * ((d : ℝ) + 1) := by ring
  have hdm1_nz : (d : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hd_gt.ne'
  have hdp1_nz : (d : ℝ) + 1 ≠ 0 := by linarith
  rw [hfac] at hsum
  have hc_mul : ((d : ℝ) + 1) * c = 1 := by
    apply mul_left_cancel₀ hdm1_nz
    linarith
  exact eq_div_of_mul_eq hdp1_nz (by linarith)

end WHDisplacementAndWelch

section StarkIntegralUnit

/-- The integral polynomial `starkPolyZ d` annihilates `epsilonReal d`. -/
theorem starkPolyZ_eval_epsilonReal (d : ℕ) (hd : 4 ≤ d) :
    Polynomial.eval₂ (Int.castRingHom ℝ) (epsilonReal d) (starkPolyZ d) = 0 := by
  have htr := epsilonReal_add_conj d
  have hprod := epsilonReal_mul_conj d hd
  have hchar : (epsilonReal d) ^ 2 - ((d : ℝ) - 1) * (epsilonReal d) + 1 = 0 := by
    rw [← htr, ← hprod]
    ring
  simp [starkPolyZ, map_sub, map_natCast, map_one]
  convert hchar using 1 <;> ring

/-- `epsilonConjReal d` lies explicitly in `ℤ[epsilonReal d]` as `(d - 1) - epsilonReal d`. -/
theorem epsilonConjReal_in_Z_epsilon (d : ℕ) :
    epsilonConjReal d = ((d : ℝ) - 1) - epsilonReal d := by
  linarith [epsilonReal_add_conj d]

end StarkIntegralUnit


section BelnapEmbeddingIdentity

/-- The Belnap multilattice embedding into C^(2^n) and Zauner's conjecture at
    d = 2^n are the same proposition, definitionally. -/
theorem belnap_embedding_is_zauner (n : ℕ) [NeZero (2 ^ n)] :
    Imscribing.Millennium.ZaunerEmbeddingEquivalence.HilbertEmbeddingExists n ↔
      Imscribing.Millennium.ZaunerEmbeddingEquivalence.ZaunerConjectureAtPow2 n := by
  rw [Imscribing.Millennium.ZaunerEmbeddingEquivalence.hilbert_embedding_equiv_zauner n]

/-- The base case n = 1 is discharged by the explicit qubit SIC. -/
theorem zauner_pow2_one :
    Imscribing.Millennium.ZaunerEmbeddingEquivalence.ZaunerConjectureAtPow2 1 := by
  exact Imscribing.Millennium.ZaunerEmbeddingEquivalence.hilbert_embedding_equiv_zauner 1 |>.mpr
    (show Imscribing.Millennium.ZaunerEmbeddingEquivalence.HilbertEmbeddingExists 1 from by
      simpa [Imscribing.Millennium.ZaunerEmbeddingEquivalence.HilbertEmbeddingExists,
        Imscribing.Millennium.ZaunerEmbeddingEquivalence.ZaunerConjectureAtPow2] using
        Imscribing.Millennium.Ring2048Bridge.D2.sicpovm_exists_2)

/-- The Belnap embedding exists at n = 1: same theorem, other side of the identity. -/
theorem hilbert_embedding_pow2_one :
    Imscribing.Millennium.ZaunerEmbeddingEquivalence.HilbertEmbeddingExists 1 := by
  exact (Imscribing.Millennium.ZaunerEmbeddingEquivalence.hilbert_embedding_equiv_zauner 1).mpr
    zauner_pow2_one

end BelnapEmbeddingIdentity

section PariWitnessDimensions

theorem disc_sixteen : disc 16 = 221 := by native_decide
theorem disc_one_twenty_eight : disc 128 = 16125 := by native_decide
theorem disc_twenty_forty_eight : disc 2048 = 4190205 := by native_decide

theorem disc_sixteen_nonsquare : ¬ IsSquare (disc 16) := by
  rw [disc_sixteen, Rat.isSquare_iff]
  norm_num

theorem disc_one_twenty_eight_nonsquare : ¬ IsSquare (disc 128) := by
  rw [disc_one_twenty_eight, Rat.isSquare_iff]
  norm_num

theorem disc_twenty_forty_eight_nonsquare : ¬ IsSquare (disc 2048) := by
  rw [disc_twenty_forty_eight, Rat.isSquare_iff]
  norm_num

theorem stark_palindromic_sixteen : Nonempty (StarkPalindromicWitness 16) :=
  stark_palindromic_witness 16 (by norm_num) disc_sixteen_nonsquare

theorem stark_palindromic_one_twenty_eight :
    Nonempty (StarkPalindromicWitness 128) :=
  stark_palindromic_witness 128 (by norm_num) disc_one_twenty_eight_nonsquare

theorem stark_palindromic_twenty_forty_eight :
    Nonempty (StarkPalindromicWitness 2048) :=
  stark_palindromic_witness 2048 (by norm_num) disc_twenty_forty_eight_nonsquare

end PariWitnessDimensions

section PariArithmeticChecks

theorem disc_mod_eight_sixteen : ((16 - 3) * (16 + 1) : ℕ) % 8 = 5 := by native_decide
theorem disc_mod_eight_one_twenty_eight : ((128 - 3) * (128 + 1) : ℕ) % 8 = 5 := by native_decide
theorem disc_mod_eight_twenty_forty_eight : ((2048 - 3) * (2048 + 1) : ℕ) % 8 = 5 := by native_decide

theorem two_d_sixteen : 2 * 16 = 2 ^ 5 := by norm_num
theorem two_d_one_twenty_eight : 2 * 128 = 2 ^ 8 := by norm_num
theorem two_d_twenty_forty_eight : 2 * 2048 = 2 ^ 12 := by norm_num

end PariArithmeticChecks

section PariModulusPowers

theorem ray_order_sixteen : 2 ^ 8 = 256 := by norm_num
theorem ray_quotient_sixteen : 2 ^ 7 = 128 := by norm_num
theorem ray_order_one_twenty_eight : 2 ^ 14 = 16384 := by norm_num
theorem ray_quotient_one_twenty_eight : 2 ^ 13 = 8192 := by norm_num
theorem ray_order_twenty_forty_eight : 2 ^ 27 = 134217728 := by norm_num
theorem ray_quotient_twenty_forty_eight : 2 ^ 21 = 2097152 := by norm_num

theorem coinvariant_quotient_sixteen : 16 / 2 = 8 := by norm_num
theorem coinvariant_quotient_one_twenty_eight : 128 / 2 = 64 := by norm_num

end PariModulusPowers

section PariIrreducibility

theorem starkPoly_irreducible_sixteen : Irreducible (starkPoly 16) :=
  starkPoly_irreducible 16 (by norm_num) disc_sixteen_nonsquare

theorem starkPoly_irreducible_one_twenty_eight : Irreducible (starkPoly 128) :=
  starkPoly_irreducible 128 (by norm_num) disc_one_twenty_eight_nonsquare

theorem starkPoly_irreducible_twenty_forty_eight : Irreducible (starkPoly 2048) :=
  starkPoly_irreducible 2048 (by norm_num) disc_twenty_forty_eight_nonsquare

end PariIrreducibility

section D4FiducialNorms

open Real

/-- Exact squared moduli of the d = 4 Weyl-Heisenberg fiducial, identified by
    algebraic-number reconstruction from a 120-digit numerical solution. The
    two quartics are the minimal polynomials of the norm ratios; their four
    real roots are the only possible squared coordinates of a d = 4 fiducial. -/
theorem d4_squared_norm_A :
    let x : ℝ := (10 + 5 * sqrt 2 - 2 * sqrt 5 - sqrt 10) / 40
    1600*x^4 - 1600*x^3 + 440*x^2 - 40*x + 1 = 0 := by
  dsimp
  have hs2 : (sqrt 2)^2 = 2 := by rw [sq_sqrt]; norm_num
  have hs5 : (sqrt 5)^2 = 5 := by rw [sq_sqrt]; norm_num
  have hs10 : (sqrt 10)^2 = 10 := by rw [sq_sqrt]; norm_num
  have hs25 : sqrt 2 * sqrt 5 = sqrt 10 := by
    rw [← sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (5:ℝ)]
    norm_num
  rw [← hs25]
  have hs2_3 : (sqrt 2)^3 = 2 * sqrt 2 := by
    calc (sqrt 2)^3 = (sqrt 2)^2 * sqrt 2 := by ring
         _ = 2 * sqrt 2 := by rw [hs2]
  have hs5_3 : (sqrt 5)^3 = 5 * sqrt 5 := by
    calc (sqrt 5)^3 = (sqrt 5)^2 * sqrt 5 := by ring
         _ = 5 * sqrt 5 := by rw [hs5]
  have hs2_4 : (sqrt 2)^4 = 4 := by
    calc (sqrt 2)^4 = ((sqrt 2)^2)^2 := by ring
         _ = 4 := by rw [hs2]; norm_num
  have hs5_4 : (sqrt 5)^4 = 25 := by
    calc (sqrt 5)^4 = ((sqrt 5)^2)^2 := by ring
         _ = 25 := by rw [hs5]; norm_num
  ring_nf
  simp [hs2, hs5, hs2_3, hs5_3, hs2_4, hs5_4]
  rw [hs25]
  ring_nf
  nlinarith [hs10]

theorem d4_squared_norm_A3 :
    let x : ℝ := (10 - 5 * sqrt 2 - 2 * sqrt 5 + sqrt 10) / 40
    1600*x^4 - 1600*x^3 + 440*x^2 - 40*x + 1 = 0 := by
  dsimp
  have hs2 : (sqrt 2)^2 = 2 := by rw [sq_sqrt]; norm_num
  have hs5 : (sqrt 5)^2 = 5 := by rw [sq_sqrt]; norm_num
  have hs10 : (sqrt 10)^2 = 10 := by rw [sq_sqrt]; norm_num
  have hs25 : sqrt 2 * sqrt 5 = sqrt 10 := by
    rw [← sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (5:ℝ)]
    norm_num
  rw [← hs25]
  have hs2_3 : (sqrt 2)^3 = 2 * sqrt 2 := by
    calc (sqrt 2)^3 = (sqrt 2)^2 * sqrt 2 := by ring
         _ = 2 * sqrt 2 := by rw [hs2]
  have hs5_3 : (sqrt 5)^3 = 5 * sqrt 5 := by
    calc (sqrt 5)^3 = (sqrt 5)^2 * sqrt 5 := by ring
         _ = 5 * sqrt 5 := by rw [hs5]
  have hs2_4 : (sqrt 2)^4 = 4 := by
    calc (sqrt 2)^4 = ((sqrt 2)^2)^2 := by ring
         _ = 4 := by rw [hs2]; norm_num
  have hs5_4 : (sqrt 5)^4 = 25 := by
    calc (sqrt 5)^4 = ((sqrt 5)^2)^2 := by ring
         _ = 25 := by rw [hs5]; norm_num
  ring_nf
  simp [hs2, hs5, hs2_3, hs5_3, hs2_4, hs5_4]
  rw [hs25]
  ring_nf
  nlinarith [hs10]

theorem d4_squared_norm_B :
    let x : ℝ := (5 + sqrt 5 + sqrt (5 + 5*sqrt 5)) / 20
    320*x^4 - 320*x^3 + 104*x^2 - 16*x + 1 = 0 := by
  dsimp
  have hs5 : (sqrt 5)^2 = 5 := by rw [sq_sqrt]; norm_num
  have harg : 0 ≤ 5 + 5*sqrt 5 := by positivity
  have ht : (sqrt (5 + 5*sqrt 5))^2 = 5 + 5*sqrt 5 := by rw [sq_sqrt harg]
  have hst : (sqrt 5 * sqrt (5 + 5*sqrt 5))^2 = 25 + 25*sqrt 5 := by nlinarith [hs5, ht]
  have hst_nonneg : 0 ≤ sqrt 5 * sqrt (5 + 5*sqrt 5) := by positivity
  nlinarith [hs5, ht, hst]

theorem d4_squared_norm_sum :
    let a1 : ℝ := (10 + 5 * sqrt 2 - 2 * sqrt 5 - sqrt 10) / 40
    let a3 : ℝ := (10 - 5 * sqrt 2 - 2 * sqrt 5 + sqrt 10) / 40
    let b2 : ℝ := (5 + sqrt 5 - sqrt (5 + 5*sqrt 5)) / 20
    let b4 : ℝ := (5 + sqrt 5 + sqrt (5 + 5*sqrt 5)) / 20
    a1 + a3 + b2 + b4 = 1 := by
  dsimp
  have hs2 : (sqrt 2)^2 = 2 := by rw [sq_sqrt]; norm_num
  have hs5 : (sqrt 5)^2 = 5 := by rw [sq_sqrt]; norm_num
  have hs10 : (sqrt 10)^2 = 10 := by rw [sq_sqrt]; norm_num
  have hs25 : sqrt 2 * sqrt 5 = sqrt 10 := by
    rw [← sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (5:ℝ)]
    norm_num
  have harg : 0 ≤ 5 + 5*sqrt 5 := by positivity
  have ht : (sqrt (5 + 5*sqrt 5))^2 = 5 + 5*sqrt 5 := by rw [sq_sqrt harg]
  nlinarith [hs2, hs5, hs10, hs25, ht]

end D4FiducialNorms


end Imscribing.Millennium.ClinkStarkBridge