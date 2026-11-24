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
    (zaunerMatrixZ d)ᵀ * sympJ * zaunerMatrixZ d = sympJ := by
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

section QuadRingHom

/-- Explicit carrier for ℚ(√m) so multiplication is `qmul m` without colliding
    with the componentwise ring instance on `ℚ × ℚ`. -/
@[ext]
structure QuadCarrier (m : ℚ) where
  re : ℚ
  im : ℚ

namespace QuadCarrier

instance (m : ℚ) : Zero (QuadCarrier m) := ⟨⟨0, 0⟩⟩
instance (m : ℚ) : One (QuadCarrier m) := ⟨⟨1, 0⟩⟩
instance (m : ℚ) : Add (QuadCarrier m) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance (m : ℚ) : Neg (QuadCarrier m) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance (m : ℚ) : Sub (QuadCarrier m) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance (m : ℚ) : Mul (QuadCarrier m) :=
  ⟨fun x y => ⟨x.re * y.re + m * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

instance (m : ℚ) : CommRing (QuadCarrier m) where
  add_assoc a b c := by ext <;> simp [HAdd.hAdd, Add.add] <;> ring
  zero_add a := by ext <;> simp [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]
  add_zero a := by ext <;> simp [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]
  nsmul := nsmulRec
  neg_add_cancel a := by ext <;> simp [HAdd.hAdd, Add.add, Neg.neg, OfNat.ofNat, Zero.zero]
  add_comm a b := by ext <;> simp [HAdd.hAdd, Add.add] <;> ring
  left_distrib a b c := by ext <;> simp [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul] <;> ring
  right_distrib a b c := by ext <;> simp [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul] <;> ring
  zero_mul a := by ext <;> simp [HMul.hMul, Mul.mul, OfNat.ofNat, Zero.zero]
  mul_zero a := by ext <;> simp [HMul.hMul, Mul.mul, OfNat.ofNat, Zero.zero]
  mul_assoc a b c := by ext <;> simp [HMul.hMul, Mul.mul] <;> ring
  one_mul a := by ext <;> simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one]
  mul_one a := by ext <;> simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one]
  zsmul := zsmulRec
  mul_comm a b := by ext <;> simp [HMul.hMul, Mul.mul] <;> ring
  sub_eq_add_neg a b := by ext <;> simp [HSub.hSub, Sub.sub, HAdd.hAdd, Add.add, Neg.neg]

def eps (d : ℚ) : QuadCarrier (disc d) := ⟨(d - 1) / 2, 1 / 2⟩
def conj (m : ℚ) (x : QuadCarrier m) : QuadCarrier m := ⟨x.re, -x.im⟩

theorem eps_mul_conj (d : ℚ) : eps d * conj (disc d) (eps d) = 1 := by
  ext <;> simp [HMul.hMul, Mul.mul, eps, conj, disc, OfNat.ofNat, One.one] <;> ring

noncomputable def embedPlusHom (d : ℕ) (hd : 4 ≤ d) : QuadCarrier (disc d) →+* ℂ where
  toFun x := embedPlus d (x.re, x.im)
  map_one' := by simp [embedPlus, OfNat.ofNat, One.one]
  map_mul' x y := by simpa [HMul.hMul, Mul.mul, qmul] using embedPlus_mul d hd (x.re, x.im) (y.re, y.im)
  map_zero' := by simp [embedPlus, OfNat.ofNat, Zero.zero]
  map_add' x y := by simpa [HAdd.hAdd, Add.add] using embedPlus_add d (x.re, x.im) (y.re, y.im)

end QuadCarrier
end QuadRingHom 

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
theorem clock_mul_shift (d : ℕ) [NeZero d] :
    clockMatrix d * shiftMatrix d = omega d • (shiftMatrix d * clockMatrix d) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply]
  simp only [clockMatrix, shiftMatrix, smul_eq_mul]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single k]
  · split_ifs with h
    · subst h
      have hval : (k + 1 : ZMod d).val = (k.val + 1) % d := by
        rw [← ZMod.val_natCast (k.val + 1) d]
        simp [ZMod.natCast_zmod_val]
      rw [hval, omega_pow_mod, pow_succ']
      ring
    · simp
  · intro j _ hjk
    simp [Ne.symm hjk]
  · intro hk; exact absurd (Finset.mem_univ k) hk
  · intro j _ hji
    simp [hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

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
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · by_cases hij : i = j
          · subst hij; simp [pow_succ]
          · simp [hij]
        · intro k _ hki; simp [hki]
        · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hpow d]
  ext i j
  simp only [Matrix.one_apply]
  split_ifs with hij
  · rw [← pow_mul, mul_comm, pow_mul, omega_pow_d, one_pow]
  · rfl

end WeylHeisenberg 

end Imscribing.Millennium.ClinkStarkBridge
