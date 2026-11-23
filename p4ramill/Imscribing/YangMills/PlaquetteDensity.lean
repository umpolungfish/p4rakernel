/-
  Haar nullity on SU(N): V_00 = 0 and V_00 + conj V_11 = 0 are Haar-null.
  Implements Step 1 of the unconditional-closure blueprint (standard axioms).
-/
import Mathlib
import Imscribing.YangMills.SUNHaar
import Imscribing.YangMills.LatticeLimitDensity

set_option maxHeartbeats 8000000

open scoped BigOperators ENNReal NNReal Matrix
open MeasureTheory Matrix

noncomputable section
namespace YangMills

section Step1

variable {N : ℕ}
variable (suHaar : Measure (specialUnitaryGroup (Fin N) ℂ))
  [IsProbabilityMeasure suHaar] [suHaar.IsMulLeftInvariant] [suHaar.IsMulRightInvariant]

/-- Index `0 : Fin N` when `2 ≤ N`. -/
def idx0 (hN : 2 ≤ N) : Fin N := ⟨0, by omega⟩

/-- Index `1 : Fin N` when `2 ≤ N`. -/
def idx1 (hN : 2 ≤ N) : Fin N := ⟨1, by omega⟩

/-- Real `2 × 2` rotation matrix in `SU(2)`. -/
def rot2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), (Real.sin θ : ℂ); -(Real.sin θ : ℂ), (Real.cos θ : ℂ)]

lemma rot2_mem_unitary (θ : ℝ) : rot2 θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot2, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_ofReal]
  all_goals
    apply Complex.ext <;>
      simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  all_goals ring_nf
  all_goals try nlinarith [Real.cos_sq_add_sin_sq θ]

lemma rot2_det (θ : ℝ) : (rot2 θ).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [rot2]
  ring_nf
  exact_mod_cast Real.cos_sq_add_sin_sq θ

/-- Equivalence splitting `{0, m}` from the remaining indices of `Fin N`. -/
def splitTwoEquiv (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) :
    Fin 2 ⊕ {j : Fin N // j ≠ idx0 hN ∧ j ≠ ⟨m, hmN⟩} ≃ Fin N where
  toFun
    | Sum.inl 0 => idx0 hN
    | Sum.inl 1 => ⟨m, hmN⟩
    | Sum.inr j => j.1
  invFun j :=
    if h0 : j = idx0 hN then Sum.inl 0
    else if hm : j = ⟨m, hmN⟩ then Sum.inl 1
    else Sum.inr ⟨j, h0, hm⟩
  left_inv x := by
    have h0m : idx0 hN ≠ ⟨m, hmN⟩ := by
      intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
    rcases x with (i | ⟨j, hj0, hjm⟩)
    · fin_cases i
      · simp
      · simp [h0m.symm]
    · simp [hj0, hjm]
  right_inv j := by
    have h0m : idx0 hN ≠ ⟨m, hmN⟩ := by
      intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
    by_cases h0 : j = idx0 hN <;> by_cases hm : j = ⟨m, hmN⟩ <;>
      simp [h0, hm, h0m, h0m.symm]

lemma reindex_mul_local {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A B : Matrix m m ℂ) : Matrix.reindex e e (A * B) =
      Matrix.reindex e e A * Matrix.reindex e e B := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.mul_apply]
  exact (Equiv.sum_comp e.symm (fun k => A (e.symm i) k * B k (e.symm j))).symm

lemma reindex_one_local {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) : Matrix.reindex e e (1 : Matrix m m ℂ) = 1 := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply, e.symm.injective.eq_iff]

/-- Real rotation `R₀ₘ(θ) ∈ SU(N)` in the `(0, m)`-plane. -/
def rot0m (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ) :
    specialUnitaryGroup (Fin N) ℂ :=
  let e := splitTwoEquiv hN hm1 hmN
  let B : Matrix (Fin 2 ⊕ {j : Fin N // j ≠ idx0 hN ∧ j ≠ ⟨m, hmN⟩})
      (Fin 2 ⊕ {j : Fin N // j ≠ idx0 hN ∧ j ≠ ⟨m, hmN⟩}) ℂ :=
    Matrix.fromBlocks (rot2 θ) 0 0 1
  ⟨Matrix.reindex e e B, by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      have hB : B * Bᴴ = 1 := by
        dsimp [B]
        rw [Matrix.fromBlocks_conjTranspose]
        rw [Matrix.fromBlocks_multiply]
        have hrot : rot2 θ * (rot2 θ)ᴴ = 1 :=
          Matrix.mem_unitaryGroup_iff.mp (rot2_mem_unitary θ)
        simp [hrot, Matrix.fromBlocks_one]
      calc (Matrix.reindex e e B) * (Matrix.reindex e e B)ᴴ
          = (Matrix.reindex e e B) * (Matrix.reindex e e Bᴴ) := by
              rw [Matrix.conjTranspose_reindex]
        _ = Matrix.reindex e e (B * Bᴴ) := by exact (reindex_mul_local e B Bᴴ).symm
        _ = Matrix.reindex e e 1 := by rw [hB]
        _ = 1 := reindex_one_local e
    · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂, rot2_det θ,
        Matrix.det_one, mul_one]⟩

lemma rot0m_entry_idx0 (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ) (k : Fin N) :
    ((rot0m hN hm1 hmN θ : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) k) =
      if k = idx0 hN then (Real.cos θ : ℂ)
      else if k = ⟨m, hmN⟩ then (Real.sin θ : ℂ)
      else 0 := by
  have h0m : idx0 hN ≠ ⟨m, hmN⟩ := by
    intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
  simp only [rot0m, Matrix.reindex_apply]
  by_cases hk0 : k = idx0 hN
  · subst hk0; simp [splitTwoEquiv, rot2]
  · by_cases hkm : k = ⟨m, hmN⟩
    · subst hkm; simp [splitTwoEquiv, rot2, h0m.symm]
    · simp [splitTwoEquiv, hk0, hkm]

lemma rot0m_entry_idxm (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ) (k : Fin N) :
    ((rot0m hN hm1 hmN θ : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ k) =
      if k = idx0 hN then -(Real.sin θ : ℂ)
      else if k = ⟨m, hmN⟩ then (Real.cos θ : ℂ)
      else 0 := by
  have h0m : idx0 hN ≠ ⟨m, hmN⟩ := by
    intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
  simp only [rot0m, Matrix.reindex_apply]
  by_cases hk0 : k = idx0 hN
  · subst hk0; simp [splitTwoEquiv, rot2, h0m.symm]
  · by_cases hkm : k = ⟨m, hmN⟩
    · subst hkm; simp [splitTwoEquiv, rot2, h0m.symm]
    · simp [splitTwoEquiv, hk0, hkm, h0m.symm]

lemma rot0m_entry_other (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ)
    {j : Fin N} (hj0 : j ≠ idx0 hN) (hjm : j ≠ ⟨m, hmN⟩) (k : Fin N) :
    ((rot0m hN hm1 hmN θ : Matrix (Fin N) (Fin N) ℂ) j k) = if j = k then 1 else 0 := by
  have h0m : idx0 hN ≠ ⟨m, hmN⟩ := by
    intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
  simp only [rot0m, Matrix.reindex_apply]
  by_cases hk0 : k = idx0 hN
  · subst hk0; simp [splitTwoEquiv, hj0, hjm, h0m.symm]
  · by_cases hkm : k = ⟨m, hmN⟩
    · subst hkm; simp [splitTwoEquiv, hj0, hjm, h0m.symm]
    · simp [splitTwoEquiv, hj0, hjm, hk0, hkm, Matrix.one_apply, Subtype.ext_iff, h0m.symm]

lemma rot0m_mul_idx0 (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ)
    (V : specialUnitaryGroup (Fin N) ℂ) :
    ((rot0m hN hm1 hmN θ * V : specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) =
      (Real.cos θ : ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
        (Real.sin θ : ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) := by
  have h0m : idx0 hN ≠ ⟨m, hmN⟩ := by
    intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
  change (((rot0m hN hm1 hmN θ : specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (V : Matrix (Fin N) (Fin N) ℂ)) (idx0 hN) (idx0 hN) = _
  rw [Matrix.mul_apply]
  simp_rw [rot0m_entry_idx0 hN hm1 hmN θ]
  rw [Finset.sum_eq_add_of_mem (idx0 hN) ⟨m, hmN⟩ (Finset.mem_univ _) (Finset.mem_univ _) h0m
    (by intro c _ hc; simp [hc.1, hc.2])]
  simp [h0m, h0m.symm]

lemma rot0m_mul_idxm (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ)
    (V : specialUnitaryGroup (Fin N) ℂ) :
    ((rot0m hN hm1 hmN θ * V : specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) =
      -(Real.sin θ : ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
        (Real.cos θ : ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) := by
  have h0m : idx0 hN ≠ ⟨m, hmN⟩ := by
    intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
  change (((rot0m hN hm1 hmN θ : specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (V : Matrix (Fin N) (Fin N) ℂ)) ⟨m, hmN⟩ (idx0 hN) = _
  rw [Matrix.mul_apply]
  simp_rw [rot0m_entry_idxm hN hm1 hmN θ]
  rw [Finset.sum_eq_add_of_mem (idx0 hN) ⟨m, hmN⟩ (Finset.mem_univ _) (Finset.mem_univ _) h0m
    (by intro c _ hc; simp [hc.1, hc.2])]
  simp [h0m, h0m.symm]

lemma rot0m_mul_other (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ)
    (V : specialUnitaryGroup (Fin N) ℂ) {j : Fin N} (hj0 : j ≠ idx0 hN) (hjm : j ≠ ⟨m, hmN⟩) :
    ((rot0m hN hm1 hmN θ * V : specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) =
      (V : Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) := by
  change (((rot0m hN hm1 hmN θ : specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (V : Matrix (Fin N) (Fin N) ℂ)) j (idx0 hN) = _
  rw [Matrix.mul_apply]
  simp_rw [rot0m_entry_other hN hm1 hmN θ hj0 hjm]
  simp

lemma rot0m_continuous (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) :
    Continuous (rot0m hN hm1 hmN) := by
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]; intro i
  rw [continuous_pi_iff]; intro j
  have h0m : idx0 hN ≠ (⟨m, hmN⟩ : Fin N) := by
    intro h; have := congrArg Fin.val h; simp [idx0] at this; omega
  let ent : ℝ → ℂ := fun θ =>
    ((rot0m hN hm1 hmN θ : specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j
  change Continuous ent
  by_cases hi0 : i = idx0 hN
  · subst i
    by_cases hj0 : j = idx0 hN
    · subst j
      have hfun : ent = fun θ : ℝ => (Real.cos θ : ℂ) := by
        funext θ
        simp [ent, rot0m_entry_idx0 hN hm1 hmN θ]
      rw [hfun]
      exact Complex.continuous_ofReal.comp Real.continuous_cos
    · by_cases hjm : j = (⟨m, hmN⟩ : Fin N)
      · subst j
        have hfun : ent = fun θ : ℝ => (Real.sin θ : ℂ) := by
          funext θ
          simp [ent, rot0m_entry_idx0 hN hm1 hmN θ, h0m.symm]
        rw [hfun]
        exact Complex.continuous_ofReal.comp Real.continuous_sin
      · have hfun : ent = fun _ : ℝ => (0 : ℂ) := by
          funext θ
          simp [ent, rot0m_entry_idx0 hN hm1 hmN θ, hj0, hjm]
        rw [hfun]
        exact continuous_const
  · by_cases him : i = (⟨m, hmN⟩ : Fin N)
    · subst i
      by_cases hj0 : j = idx0 hN
      · subst j
        have hfun : ent = fun θ : ℝ => -(Real.sin θ : ℂ) := by
          funext θ
          simp [ent, rot0m_entry_idxm hN hm1 hmN θ]
        rw [hfun]
        exact (Complex.continuous_ofReal.comp Real.continuous_sin).neg
      · by_cases hjm : j = (⟨m, hmN⟩ : Fin N)
        · subst j
          have hfun : ent = fun θ : ℝ => (Real.cos θ : ℂ) := by
            funext θ
            simp [ent, rot0m_entry_idxm hN hm1 hmN θ, h0m, h0m.symm]
          rw [hfun]
          exact Complex.continuous_ofReal.comp Real.continuous_cos
        · have hfun : ent = fun _ : ℝ => (0 : ℂ) := by
            funext θ
            simp [ent, rot0m_entry_idxm hN hm1 hmN θ, hj0, hjm]
          rw [hfun]
          exact continuous_const
    · by_cases hji : j = i
      · subst j
        have hfun : ent = fun _ : ℝ => (1 : ℂ) := by
          funext θ
          simp [ent, rot0m_entry_other hN hm1 hmN θ hi0 him i]
        rw [hfun]
        exact continuous_const
      · have hij : i ≠ j := fun h => hji h.symm
        have hfun : ent = fun _ : ℝ => (0 : ℂ) := by
          funext θ
          simp [ent, rot0m_entry_other hN hm1 hmN θ hi0 him j, hij]
        rw [hfun]
        exact continuous_const

/-- `K m := {V ∈ SU(N) | ∀ j ≤ m, V_{j 0} = 0}`. -/
def KmSet (hN : 2 ≤ N) (m : ℕ) : Set (specialUnitaryGroup (Fin N) ℂ) :=
  {V | ∀ j : Fin N, j.1 ≤ m → (V : Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) = 0}

/-- `A m := {V ∈ SU(N) | (∀ 1 ≤ j < m, V_{j 0} = 0) ∧ (V_{00} ≠ 0 ∨ V_{m 0} ≠ 0)}`. -/
def AmSet (hN : 2 ≤ N) {m : ℕ} (hmN : m < N) : Set (specialUnitaryGroup (Fin N) ℂ) :=
  {V | (∀ j : Fin N, 1 ≤ j.1 → j.1 < m → (V : Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) = 0) ∧
    ((V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) ≠ 0 ∨
      (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) ≠ 0)}

lemma AmSet_measurable (hN : 2 ≤ N) {m : ℕ} (hmN : m < N) : MeasurableSet (AmSet hN hmN) := by
  have h1 : MeasurableSet {V : specialUnitaryGroup (Fin N) ℂ |
      ∀ j : Fin N, 1 ≤ j.1 → j.1 < m → (V : Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) = 0} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact (isClosed_eq (Continuous.matrix_elem continuous_subtype_val j (idx0 hN))
      continuous_const).measurableSet
  have h2 : MeasurableSet {V : specialUnitaryGroup (Fin N) ℂ |
      (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) ≠ 0 ∨
      (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) ≠ 0} := by
    refine MeasurableSet.union ?_ ?_
    · exact (isOpen_ne.preimage
        (Continuous.matrix_elem continuous_subtype_val (idx0 hN) (idx0 hN))).measurableSet
    · exact (isOpen_ne.preimage
        (Continuous.matrix_elem continuous_subtype_val (⟨m, hmN⟩ : Fin N) (idx0 hN))).measurableSet
  exact h1.inter h2

lemma KmSet_top_eq_empty (hN : 2 ≤ N) : KmSet hN (N - 1) = ∅ := by
  ext V
  simp only [KmSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
  have hunit : (V : Matrix (Fin N) (Fin N) ℂ)ᴴ * (V : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.2.1
  have h00 : ((V : Matrix (Fin N) (Fin N) ℂ)ᴴ * (V : Matrix (Fin N) (Fin N) ℂ))
      (idx0 hN) (idx0 hN) = 1 := by rw [hunit, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h00
  by_contra hall
  push_neg at hall
  have hzero : ∑ j : Fin N, (V : Matrix (Fin N) (Fin N) ℂ)ᴴ (idx0 hN) j *
      (V : Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj := hall j (Nat.le_pred_of_lt j.isLt)
    simp [hj]
  rw [hzero] at h00
  exact zero_ne_one h00

lemma rot0m_mem_AmSet_iff (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) (θ : ℝ)
    (V : specialUnitaryGroup (Fin N) ℂ) :
    rot0m hN hm1 hmN θ * V ∈ AmSet hN hmN ↔ V ∈ AmSet hN hmN := by
  have h_mid : (∀ j : Fin N, 1 ≤ j.1 → j.1 < m →
      ((rot0m hN hm1 hmN θ * V : specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) = 0) ↔
      (∀ j : Fin N, 1 ≤ j.1 → j.1 < m →
        (V : Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) = 0) := by
    constructor <;> intro h j hj1 hjm
    · have hj0 : j ≠ idx0 hN := fun h' => by have := congrArg Fin.val h'; simp [idx0] at this; omega
      have hjm' : j ≠ ⟨m, hmN⟩ := fun h' => by have := congrArg Fin.val h'; simp at this; omega
      rw [← rot0m_mul_other hN hm1 hmN θ V hj0 hjm']
      exact h j hj1 hjm
    · have hj0 : j ≠ idx0 hN := fun h' => by have := congrArg Fin.val h'; simp [idx0] at this; omega
      have hjm' : j ≠ ⟨m, hmN⟩ := fun h' => by have := congrArg Fin.val h'; simp at this; omega
      rw [rot0m_mul_other hN hm1 hmN θ V hj0 hjm']
      exact h j hj1 hjm
  have h_nz : (((rot0m hN hm1 hmN θ * V : specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) ≠ 0 ∨
      ((rot0m hN hm1 hmN θ * V : specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) ≠ 0) ↔
      ((V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) ≠ 0 ∨
        (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) ≠ 0) := by
    rw [rot0m_mul_idx0 hN hm1 hmN θ V, rot0m_mul_idxm hN hm1 hmN θ V]
    constructor
    · intro h
      by_contra hab
      push_neg at hab
      rcases hab with ⟨ha, hb⟩
      rcases h with h1 | h2
      · apply h1; simp [ha, hb]
      · apply h2; simp [ha, hb]
    · intro h
      by_contra h12
      push_neg at h12
      rcases h12 with ⟨h1, h2⟩
      have htrig : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq θ
      have ha : (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) = 0 := by
        have hs : ((Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2) *
            (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) = 0 := by
          linear_combination (Real.cos θ : ℂ) * h1 - (Real.sin θ : ℂ) * h2
        simpa [htrig] using hs
      have hb : (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) = 0 := by
        have hs : ((Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2) *
            (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) = 0 := by
          linear_combination (Real.sin θ : ℂ) * h1 + (Real.cos θ : ℂ) * h2
        simpa [htrig] using hs
      exact h.elim (fun h => h ha) (fun h => h hb)
  simp only [AmSet, Set.mem_setOf_eq, h_mid, h_nz]

lemma exp_I_mul_conj (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) * star (Complex.exp (Complex.I * (θ : ℂ))) = 1 := by
  change Complex.exp (Complex.I * (θ : ℂ)) * (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ))) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

/-- Diagonal SU(N) element diag(e^{iθ}, e^{iθ}, e^{-2iθ}, 1, ..., 1) for N >= 3. -/
noncomputable def psiDiag (hN3 : 3 ≤ N) (θ : ℝ) : specialUnitaryGroup (Fin N) ℂ := by
  let d : Fin N → ℂ := fun j =>
    if j.1 = 0 then Complex.exp (Complex.I * θ)
    else if j.1 = 1 then Complex.exp (Complex.I * θ)
    else if j.1 = 2 then Complex.exp (-2 * Complex.I * θ)
    else 1
  refine ⟨Matrix.diagonal d, ?_⟩
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · have hd_norm : ∀ i, d i * star (d i) = 1 := by
      intro i
      dsimp [d]
      split_ifs with h0 h1 h2
      · exact exp_I_mul_conj θ
      · exact exp_I_mul_conj θ
      · rw [show -2 * Complex.I * (θ : ℂ) = Complex.I * ((-2 * θ : ℝ) : ℂ) by push_cast; ring]
        exact exp_I_mul_conj (-2 * θ)
      · simp
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.mul_apply, Matrix.diagonal_apply] using hd_norm i
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Matrix.mul_apply, Matrix.diagonal_apply, hij, hji]
  · rw [Matrix.det_diagonal]
    let i0 : Fin N := ⟨0, by omega⟩
    let i1 : Fin N := ⟨1, by omega⟩
    let i2 : Fin N := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
    have h02 : i0 ≠ i2 := by intro h; have := congrArg Fin.val h; simp [i0, i2] at this
    have h12 : i1 ≠ i2 := by intro h; have := congrArg Fin.val h; simp [i1, i2] at this
    have hs0 : (∏ j : Fin N, d j) = d i0 * ((Finset.univ.erase i0).prod d) :=
      (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i0)).symm
    have hs1 : ((Finset.univ.erase i0).prod d) = d i1 * (((Finset.univ.erase i0).erase i1).prod d) :=
      (Finset.mul_prod_erase _ d (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩)).symm
    have hs2 : (((Finset.univ.erase i0).erase i1).prod d) =
        d i2 * ((((Finset.univ.erase i0).erase i1).erase i2).prod d) :=
      (Finset.mul_prod_erase _ d (Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_erase.mpr ⟨h02.symm, Finset.mem_univ i2⟩⟩)).symm
    rw [hs0, hs1, hs2]
    have hrest : ((((Finset.univ : Finset (Fin N)).erase i0).erase i1).erase i2).prod d = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hj2 : j ≠ i2 := (Finset.mem_erase.mp hj).1
      have hj1 : j ≠ i1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hj0 : j ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2).1
      have h0v : j.1 ≠ 0 := fun h => hj0 (Fin.ext h)
      have h1v : j.1 ≠ 1 := fun h => hj1 (Fin.ext h)
      have h2v : j.1 ≠ 2 := fun h => hj2 (Fin.ext h)
      simp [d, h0v, h1v, h2v]
    rw [hrest, mul_one]
    simp only [d, i0, i1, i2]
    norm_num
    rw [← Complex.exp_add, ← Complex.exp_add]
    have hzero : Complex.I * (θ : ℂ) + (Complex.I * (θ : ℂ) + -(2 * Complex.I * (θ : ℂ))) = 0 := by ring
    rw [hzero, Complex.exp_zero]

lemma psiDiag_continuous (hN3 : 3 ≤ N) : Continuous (psiDiag hN3) := by
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]; intro i
  rw [continuous_pi_iff]; intro j
  by_cases hij : i = j
  · subst j
    simp only [psiDiag, Matrix.diagonal_apply_eq]
    split_ifs <;> fun_prop
  · simp [psiDiag, hij]
    exact continuous_const

/-- Step 1a: Haar-nullity of `{V | V₀₀ = 0}`. -/
theorem suHaar_v00_eq_zero (hN : 2 ≤ N) :
    suHaar {V : specialUnitaryGroup (Fin N) ℂ |
      (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) = 0} = 0 := by
  have hK_zero : ∀ k : ℕ, k ≤ N - 1 → suHaar (KmSet hN (N - 1 - k)) = 0 := by
    intro k hk
    induction k with
    | zero => simp [KmSet_top_eq_empty]
    | succ k ih =>
      have hk' : k ≤ N - 1 := Nat.le_of_succ_le hk
      have ih' := ih hk'
      set m : ℕ := N - 1 - k
      have hm1 : 1 ≤ m := by omega
      have hmN : m < N := by omega
      have hm_sub : N - 1 - (k + 1) = m - 1 := by omega
      rw [hm_sub]
      let E : Set (specialUnitaryGroup (Fin N) ℂ) :=
        AmSet hN hmN ∩ {V | (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) = 0}
      have hE_meas : MeasurableSet E := (AmSet_measurable hN hmN).inter
        (isClosed_eq (Continuous.matrix_elem continuous_subtype_val (idx0 hN) (idx0 hN))
          continuous_const).measurableSet
      have hE_null : suHaar E = 0 := by
        refine haar_null_of_slice_null suHaar (rot0m hN hm1 hmN) ?_ hE_meas ?_
        · exact ((continuous_mul.comp
            (Continuous.prodMk ((rot0m_continuous hN hm1 hmN).comp continuous_fst) continuous_snd))).measurable
        · intro V
          by_cases hV : V ∈ AmSet hN hmN
          · have hsub : {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ rot0m hN hm1 hmN θ * V ∈ E} ⊆
                {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
                  (Real.cos θ : ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
                    (Real.sin θ : ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) ⟨m, hmN⟩ (idx0 hN) = 0} := by
              intro θ ⟨hθ_mem, hθ_E⟩
              exact ⟨hθ_mem, by
                rw [← rot0m_mul_idx0 hN hm1 hmN θ V]
                exact hθ_E.2⟩
            exact measure_mono_null hsub (volume_trig_zero_set_eq_zero _ _ hV.2)
          · have hempty : {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ rot0m hN hm1 hmN θ * V ∈ E} = ∅ := by
              ext θ
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
              intro _ hmem
              exact hV ((rot0m_mem_AmSet_iff hN hm1 hmN θ V).mp hmem.1)
            rw [hempty, measure_empty]
      have hsub : KmSet hN (m - 1) ⊆ KmSet hN m ∪ E := by
        intro V hV
        by_cases hmV : V ∈ KmSet hN m
        · exact Or.inl hmV
        · right
          constructor
          · constructor
            · intro j hj1 hjm
              exact hV j (Nat.le_pred_of_lt hjm)
            · have hex : ∃ j : Fin N, j.1 ≤ m ∧
                  (V : Matrix (Fin N) (Fin N) ℂ) j (idx0 hN) ≠ 0 := by
                simpa [KmSet] using hmV
              rcases hex with ⟨j, hjm_le, hjne⟩
              by_cases hj0 : j = idx0 hN
              · left; simpa [hj0] using hjne
              · by_cases hjm_eq : j = (⟨m, hmN⟩ : Fin N)
                · right; simpa [hjm_eq] using hjne
                · have hj_ne_m : j.1 ≠ m := by
                    intro h; apply hjm_eq; exact Fin.ext h
                  have hj_lt : j.1 < m := lt_of_le_of_ne hjm_le hj_ne_m
                  have hj_le_pred : j.1 ≤ m - 1 := Nat.le_pred_of_lt hj_lt
                  exact False.elim (hjne (hV j hj_le_pred))
          · exact hV (idx0 hN) (by simp [idx0])
      have hle : suHaar (KmSet hN (m - 1)) ≤ suHaar (KmSet hN m ∪ E) := measure_mono hsub
      have hunion : suHaar (KmSet hN m ∪ E) ≤ suHaar (KmSet hN m) + suHaar E :=
        measure_union_le _ _
      rw [ih', hE_null, add_zero] at hunion
      exact le_antisymm (hle.trans hunion) (zero_le _)
  have h0 := hK_zero (N - 1) (le_refl _)
  rw [Nat.sub_self] at h0
  have heq : KmSet hN 0 = {V : specialUnitaryGroup (Fin N) ℂ |
      (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) = 0} := by
    ext V
    simp only [KmSet, Set.mem_setOf_eq]
    constructor
    · intro h; exact h (idx0 hN) (by simp [idx0])
    · intro h j hj
      have hj0 : j = idx0 hN := Fin.ext (by simp [idx0]; omega)
      rw [hj0]
      exact h
  rwa [← heq]

/-- Step 1b: Haar-nullity of `{V | V₀₀ + conj V₁₁ = 0}`. -/
theorem suHaar_v00_add_conj_v11_eq_zero (hN : 2 ≤ N) :
    suHaar {V : specialUnitaryGroup (Fin N) ℂ |
      (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
        star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) = 0} = 0 := by
  by_cases hN2 : N = 2
  · subst N
    have heq : {V : specialUnitaryGroup (Fin 2) ℂ |
        (V : Matrix (Fin 2) (Fin 2) ℂ) (idx0 hN) (idx0 hN) +
          star ((V : Matrix (Fin 2) (Fin 2) ℂ) (idx1 hN) (idx1 hN)) = 0} =
        {V : specialUnitaryGroup (Fin 2) ℂ |
          (V : Matrix (Fin 2) (Fin 2) ℂ) (idx0 hN) (idx0 hN) = 0} := by
      ext V
      have hunit : (V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 :=
        Matrix.mem_unitaryGroup_iff.mp V.2.1
      have hdet : (V : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := V.2.2
      have hadj : (V : Matrix (Fin 2) (Fin 2) ℂ).adjugate = (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
        calc
          (V : Matrix (Fin 2) (Fin 2) ℂ).adjugate =
              (V : Matrix (Fin 2) (Fin 2) ℂ).adjugate *
                ((V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) := by rw [hunit, mul_one]
          _ = ((V : Matrix (Fin 2) (Fin 2) ℂ).adjugate * (V : Matrix (Fin 2) (Fin 2) ℂ)) *
                (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [mul_assoc]
          _ = ((V : Matrix (Fin 2) (Fin 2) ℂ).det • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
                (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [Matrix.adjugate_mul]
          _ = (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [hdet, one_smul, one_mul]
      have h00 : (V : Matrix (Fin 2) (Fin 2) ℂ).adjugate 0 0 =
          (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ 0 0 := by rw [hadj]
      rw [Matrix.adjugate_fin_two] at h00
      simp only [Matrix.conjTranspose_apply] at h00
      have h11 : (V : Matrix (Fin 2) (Fin 2) ℂ) (idx1 hN) (idx1 hN) =
          star ((V : Matrix (Fin 2) (Fin 2) ℂ) (idx0 hN) (idx0 hN)) := by
        simpa [idx0, idx1] using h00
      simp only [Set.mem_setOf_eq, h11, star_star]
      constructor
      · intro h; linear_combination (1 / 2 : ℂ) * h
      · intro h; simp [h]
    rw [heq]
    exact suHaar_v00_eq_zero suHaar hN
  · have hN3 : 3 ≤ N := by omega
    let H0c : Set (specialUnitaryGroup (Fin N) ℂ) :=
      {V | (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
        star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) = 0}
    let K0 : Set (specialUnitaryGroup (Fin N) ℂ) :=
      {V | (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) = 0}
    let E : Set (specialUnitaryGroup (Fin N) ℂ) := H0c ∩ K0ᶜ
    have hE_meas : MeasurableSet E := by
      refine MeasurableSet.inter ?_ ?_
      · exact (isClosed_eq ((Continuous.matrix_elem continuous_subtype_val (idx0 hN) (idx0 hN)).add
          ((Continuous.matrix_elem continuous_subtype_val (idx1 hN) (idx1 hN)).star)) continuous_const).measurableSet
      · exact (isOpen_ne.preimage (Continuous.matrix_elem continuous_subtype_val (idx0 hN) (idx0 hN))).measurableSet
    have hE_null : suHaar E = 0 := by
      refine haar_null_of_slice_null suHaar (psiDiag hN3) ?_ hE_meas ?_
      · exact ((continuous_mul.comp
          (Continuous.prodMk ((psiDiag_continuous hN3).comp continuous_fst) continuous_snd))).measurable
      · intro V
        by_cases hV0 : (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) = 0
        · have hempty : {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ psiDiag hN3 θ * V ∈ E} = ∅ := by
            ext θ
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
            intro _ hmem
            exact hmem.2 (by
              change ((((psiDiag hN3 θ : specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
                (V : Matrix (Fin N) (Fin N) ℂ)) (idx0 hN) (idx0 hN)) = 0
              simpa [psiDiag, Matrix.mul_apply, Matrix.diagonal_apply, idx0] using hV0)
          rw [hempty, measure_empty]
        · set a := (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN)
          set b := star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN))
          have hsub : {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ psiDiag hN3 θ * V ∈ E} ⊆
              {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
                Complex.exp (2 * Complex.I * (θ : ℂ)) = -(b / a)} := by
            intro θ ⟨hθ_mem, hθ_E⟩
            exact ⟨hθ_mem, by
              have h00 : ((psiDiag hN3 θ * V : specialUnitaryGroup (Fin N) ℂ) :
                  Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) =
                  Complex.exp (Complex.I * θ) * a := by
                change ((psiDiag hN3 θ : Matrix (Fin N) (Fin N) ℂ) *
                  (V : Matrix (Fin N) (Fin N) ℂ)) (idx0 hN) (idx0 hN) = _
                simp [psiDiag, Matrix.mul_apply, Matrix.diagonal_apply, idx0, a]
              have h11 : ((psiDiag hN3 θ * V : specialUnitaryGroup (Fin N) ℂ) :
                  Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN) =
                  Complex.exp (Complex.I * θ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN) := by
                change ((psiDiag hN3 θ : Matrix (Fin N) (Fin N) ℂ) *
                  (V : Matrix (Fin N) (Fin N) ℂ)) (idx1 hN) (idx1 hN) = _
                simp [psiDiag, Matrix.mul_apply, Matrix.diagonal_apply, idx1]
              have h11_star : star (((psiDiag hN3 θ * V : specialUnitaryGroup (Fin N) ℂ) :
                  Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) =
                  Complex.exp (-Complex.I * θ) * b := by
                rw [h11]
                change (starRingEnd ℂ) (Complex.exp (Complex.I * θ) *
                  (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) = _
                rw [map_mul, ← Complex.exp_conj]
                simp [b]
              have hsum := hθ_E.1
              change ((psiDiag hN3 θ * V : specialUnitaryGroup (Fin N) ℂ) :
                  Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
                star (((psiDiag hN3 θ * V : specialUnitaryGroup (Fin N) ℂ) :
                  Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) = 0 at hsum
              rw [h00, h11_star] at hsum
              have hexp_mul : Complex.exp (Complex.I * θ) *
                  (Complex.exp (Complex.I * θ) * a + Complex.exp (-Complex.I * θ) * b) =
                  Complex.exp (2 * Complex.I * θ) * a + b := by
                have h2 : Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ) =
                    Complex.exp (2 * Complex.I * θ) := by
                  rw [← Complex.exp_add]; congr 1 <;> ring
                have h0 : Complex.exp (Complex.I * θ) * Complex.exp (-Complex.I * θ) = 1 := by
                  rw [← Complex.exp_add]; simp
                calc
                  Complex.exp (Complex.I * θ) * (Complex.exp (Complex.I * θ) * a + Complex.exp (-Complex.I * θ) * b)
                      = (Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ)) * a +
                          (Complex.exp (Complex.I * θ) * Complex.exp (-Complex.I * θ)) * b := by ring
                  _ = Complex.exp (2 * Complex.I * θ) * a + b := by rw [h2, h0, one_mul]
              have hzero : Complex.exp (2 * Complex.I * θ) * a + b = 0 := by
                rw [← hexp_mul, hsum, mul_zero]
              field_simp [a, hV0]
              linear_combination hzero⟩
          exact measure_mono_null hsub (volume_exp_two_eq_zero _)
    have hK0_null : suHaar K0 = 0 := suHaar_v00_eq_zero suHaar hN
    have hsub : H0c ⊆ E ∪ K0 := by
      intro V hV
      by_cases hK : V ∈ K0
      · exact Or.inr hK
      · exact Or.inl ⟨hV, hK⟩
    have hle1 : suHaar H0c ≤ suHaar (E ∪ K0) := measure_mono hsub
    have hle2 : suHaar (E ∪ K0) ≤ suHaar E + suHaar K0 := measure_union_le E K0
    have hle : suHaar H0c ≤ suHaar E + suHaar K0 := hle1.trans hle2
    rw [hE_null, hK0_null, add_zero] at hle
    exact le_antisymm hle (zero_le _)

end Step1
end YangMills
