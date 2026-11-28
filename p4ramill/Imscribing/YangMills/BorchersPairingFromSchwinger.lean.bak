
import Imscribing.YangMills.BorchersContinuumReconstruction
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure

/-!
# Borchers Sesquilinear Pairing & Time-Shift Algebra from Continuum Schwinger Functionals
-/

noncomputable section

namespace Imscribing.YangMills.BorchersSchwinger

open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction

/-- Reflection-conjugation, tensor product, and positive-time shift data on
    `EuclideanSchwartz` / `PosSchwartzSubmodule`. -/
structure ReflectTensorData where
  reflectConj : ∀ m : ℕ, EuclideanSchwartz m → EuclideanSchwartz m
  reflectConj_zero_one : reflectConj 0 vacTest0 = vacTest0
  reflectConj_add : ∀ m (f g : EuclideanSchwartz m),
    reflectConj m (f + g) = reflectConj m f + reflectConj m g
  reflectConj_smul : ∀ m (c : ℂ) (f : EuclideanSchwartz m),
    reflectConj m (c • f) = star c • reflectConj m f
  reflectConj_seminorm_le : ∀ m j (f : EuclideanSchwartz m),
    SchwartzMap.seminorm ℂ j 0 (reflectConj m f) ≤ SchwartzMap.seminorm ℂ j 0 f
  tensor : ∀ m n : ℕ, EuclideanSchwartz m → EuclideanSchwartz n → EuclideanSchwartz (m + n)
  tensor_zero_one : tensor 0 0 vacTest0 vacTest0 = vacTest0
  tensor_add_left : ∀ m n (f₁ f₂ : EuclideanSchwartz m) (g : EuclideanSchwartz n),
    tensor m n (f₁ + f₂) g = tensor m n f₁ g + tensor m n f₂ g
  tensor_smul_left : ∀ m n (c : ℂ) (f : EuclideanSchwartz m) (g : EuclideanSchwartz n),
    tensor m n (c • f) g = c • tensor m n f g
  tensor_add_right : ∀ m n (f : EuclideanSchwartz m) (g₁ g₂ : EuclideanSchwartz n),
    tensor m n f (g₁ + g₂) = tensor m n f g₁ + tensor m n f g₂
  tensor_smul_right : ∀ m n (c : ℂ) (f : EuclideanSchwartz m) (g : EuclideanSchwartz n),
    tensor m n f (c • g) = c • tensor m n f g
  tensor_seminorm_le : ∀ m n k : ℕ, ∃ C_t : ℝ, 0 ≤ C_t ∧
    ∀ (f : EuclideanSchwartz m) (g : EuclideanSchwartz n),
      SchwartzMap.seminorm ℂ k 0 (tensor m n f g) ≤
        C_t * (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 f) *
              (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 g)
  shiftPos : ℝ → ∀ n : ℕ, PosSchwartzSubmodule n →ₗ[ℂ] PosSchwartzSubmodule n
  shiftPos_vac : ∀ t : ℝ, 0 ≤ t →
    shiftPos t 0 ⟨vacTest0, Or.inl rfl⟩ = ⟨vacTest0, Or.inl rfl⟩
  shiftPos_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ n (f : PosSchwartzSubmodule n),
    shiftPos (s + t) n f = shiftPos s n (shiftPos t n f)
  shiftPos_seminorm_le : ∀ (n k : ℕ) (f : PosSchwartzSubmodule n),
    ∃ C_s : ℝ, 0 ≤ C_s ∧ ∀ t : ℝ, 0 ≤ t → ∀ j ≤ k,
      SchwartzMap.seminorm ℂ j 0 (shiftPos t n f).1 ≤ C_s * (1 + t) ^ k

private def termEval (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (m n : ℕ) (fm : PosSchwartzSubmodule m) (gn : PosSchwartzSubmodule n) : ℂ :=
  C.S (m + n) (R.tensor m n (R.reflectConj m fm.1) gn.1)

private lemma termEval_zero_left (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (n : ℕ) (gn : PosSchwartzSubmodule n) : termEval C R 0 n 0 gn = 0 := by
  dsimp [termEval]
  have h1 : R.reflectConj 0 (0 : PosSchwartzSubmodule 0).1 = 0 := by
    have h0 : (0 : EuclideanSchwartz 0) = (0 : ℂ) • (0 : EuclideanSchwartz 0) := by simp
    rw [show (0 : PosSchwartzSubmodule 0).1 = 0 from rfl, h0, R.reflectConj_smul]
    simp
  have h2 : R.tensor 0 n 0 gn.1 = 0 := by
    have h0 : (0 : EuclideanSchwartz 0) = (0 : ℂ) • (0 : EuclideanSchwartz 0) := by simp
    rw [h0, R.tensor_smul_left]
    simp
  rw [h1, h2, map_zero]

private lemma termEval_add_left (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (m n : ℕ) (a b : PosSchwartzSubmodule m) (gn : PosSchwartzSubmodule n) :
    termEval C R m n (a + b) gn = termEval C R m n a gn + termEval C R m n b gn := by
  dsimp [termEval]
  rw [AddSubmonoidClass.coe_add, R.reflectConj_add, R.tensor_add_left, map_add]

private lemma termEval_smul_left (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (m n : ℕ) (c : ℂ) (fm : PosSchwartzSubmodule m) (gn : PosSchwartzSubmodule n) :
    termEval C R m n (c • fm) gn = star c * termEval C R m n fm gn := by
  dsimp [termEval]
  rw [SetLike.val_smul, R.reflectConj_smul, R.tensor_smul_left, map_smul, smul_eq_mul]

private lemma termEval_add_right (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (m n : ℕ) (fm : PosSchwartzSubmodule m) (a b : PosSchwartzSubmodule n) :
    termEval C R m n fm (a + b) = termEval C R m n fm a + termEval C R m n fm b := by
  dsimp [termEval]
  rw [AddSubmonoidClass.coe_add, R.tensor_add_right, map_add]

private lemma termEval_smul_right (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (m n : ℕ) (c : ℂ) (fm : PosSchwartzSubmodule m) (gn : PosSchwartzSubmodule n) :
    termEval C R m n fm (c • gn) = c * termEval C R m n fm gn := by
  dsimp [termEval]
  rw [SetLike.val_smul, R.tensor_smul_right, map_smul, smul_eq_mul]

/-- Borchers sesquilinear pairing on `BorchersPos` induced by `C : ContinuumSchwingerOS`
    and `R : ReflectTensorData`. -/
def borchersForm (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (F G : BorchersPos) : ℂ :=
  F.sum fun m fm => G.sum fun n gn => termEval C R m n fm gn

theorem borchersForm_add_left (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (F₁ F₂ G : BorchersPos) :
    borchersForm C R (F₁ + F₂) G = borchersForm C R F₁ G + borchersForm C R F₂ G := by
  unfold borchersForm
  rw [DFinsupp.sum_add_index']
  · intro m
    simp only [DFinsupp.sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    dsimp [termEval]
    have h1 : R.reflectConj m (0 : PosSchwartzSubmodule m).1 = 0 := by
      have h0 : (0 : EuclideanSchwartz m) = (0 : ℂ) • (0 : EuclideanSchwartz m) := by simp
      rw [show (0 : PosSchwartzSubmodule m).1 = 0 from rfl, h0, R.reflectConj_smul]
      simp
    have h2 : R.tensor m n 0 (G n).1 = 0 := by
      have h0 : (0 : EuclideanSchwartz m) = (0 : ℂ) • (0 : EuclideanSchwartz m) := by simp
      rw [h0, R.tensor_smul_left]; simp
    rw [h1, h2, map_zero]
  · intro m a b
    simp only [DFinsupp.sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => termEval_add_left C R m n a b (G n)

theorem borchersForm_smul_left (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (c : ℂ) (F G : BorchersPos) :
    borchersForm C R (c • F) G = star c * borchersForm C R F G := by
  unfold borchersForm
  simp only [DFinsupp.sum]
  rw [Finset.mul_sum]
  have h_sub : (c • F).support ⊆ F.support := DFinsupp.support_smul
  rw [← Finset.sum_subset h_sub]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [DFinsupp.coe_smul, Pi.smul_apply]
    exact termEval_smul_left C R m n c (F m) (G n)
  · intro m _ hm
    have hm0 : (c • F) m = 0 := DFinsupp.not_mem_support_iff.mp hm
    rw [hm0]
    refine Finset.sum_eq_zero fun n _ => ?_
    dsimp [termEval]
    have h1 : R.reflectConj m (0 : PosSchwartzSubmodule m).1 = 0 := by
      have h0 : (0 : EuclideanSchwartz m) = (0 : ℂ) • (0 : EuclideanSchwartz m) := by simp
      rw [show (0 : PosSchwartzSubmodule m).1 = 0 from rfl, h0, R.reflectConj_smul]; simp
    have h2 : R.tensor m n 0 (G n).1 = 0 := by
      have h0 : (0 : EuclideanSchwartz m) = (0 : ℂ) • (0 : EuclideanSchwartz m) := by simp
      rw [h0, R.tensor_smul_left]; simp
    rw [h1, h2, map_zero]

theorem borchersForm_add_right (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (F G₁ G₂ : BorchersPos) :
    borchersForm C R F (G₁ + G₂) = borchersForm C R F G₁ + borchersForm C R F G₂ := by
  unfold borchersForm
  simp only [DFinsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (G₁ + G₂).sum (fun n gn => termEval C R m n (F m) gn) = _
  rw [DFinsupp.sum_add_index']
  · intro n
    dsimp [termEval]
    have h2 : R.tensor m n (R.reflectConj m (F m).1) (0 : PosSchwartzSubmodule n).1 = 0 := by
      have h0 : (0 : EuclideanSchwartz n) = (0 : ℂ) • (0 : EuclideanSchwartz n) := by simp
      rw [show (0 : PosSchwartzSubmodule n).1 = 0 from rfl, h0, R.tensor_smul_right]; simp
    rw [h2, map_zero]
  · intro n a b
    exact termEval_add_right C R m n (F m) a b

theorem borchersForm_smul_right (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (c : ℂ) (F G : BorchersPos) :
    borchersForm C R F (c • G) = c * borchersForm C R F G := by
  unfold borchersForm
  simp only [DFinsupp.sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  have h_sub : (c • G).support ⊆ G.support := DFinsupp.support_smul
  rw [← Finset.sum_subset h_sub]
  · refine Finset.sum_congr rfl fun n _ => ?_
    simp only [DFinsupp.coe_smul, Pi.smul_apply]
    exact termEval_smul_right C R m n c (F m) (G n)
  · intro n _ hn
    have hn0 : (c • G) n = 0 := DFinsupp.not_mem_support_iff.mp hn
    rw [hn0]
    dsimp [termEval]
    have h2 : R.tensor m n (R.reflectConj m (F m).1) (0 : PosSchwartzSubmodule n).1 = 0 := by
      have h0 : (0 : EuclideanSchwartz n) = (0 : ℂ) • (0 : EuclideanSchwartz n) := by simp
      rw [show (0 : PosSchwartzSubmodule n).1 = 0 from rfl, h0, R.tensor_smul_right]; simp
    rw [h2, map_zero]

theorem borchersForm_vac (C : ContinuumSchwingerOS) (R : ReflectTensorData) :
    borchersForm C R borchersVac borchersVac = 1 := by
  unfold borchersForm borchersVac
  rw [DFinsupp.sum_single_index]
  · rw [DFinsupp.sum_single_index]
    · dsimp [termEval]
      have h1 : (⟨(1 : EuclideanSchwartz 0), Or.inl rfl⟩ : PosSchwartzSubmodule 0).1 = vacTest0 := rfl
      rw [h1, R.reflectConj_zero_one, R.tensor_zero_one]
      exact C.S_zero
    · dsimp [termEval]
      have h2 : R.tensor 0 0 (R.reflectConj 0 (⟨(1 : EuclideanSchwartz 0), Or.inl rfl⟩ :
          PosSchwartzSubmodule 0).1) (0 : PosSchwartzSubmodule 0).1 = 0 := by
        have h0 : (0 : EuclideanSchwartz 0) = (0 : ℂ) • (0 : EuclideanSchwartz 0) := by simp
        rw [show (0 : PosSchwartzSubmodule 0).1 = 0 from rfl, h0, R.tensor_smul_right]; simp
      rw [h2, map_zero]
  · simp only [DFinsupp.sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    exact termEval_zero_left C R n _

/-- Positive Euclidean time-shift operator on `BorchersPos`. -/
def borchersShift (R : ReflectTensorData) (t : ℝ) : BorchersPos →ₗ[ℂ] BorchersPos :=
  DFinsupp.mapRange.linearMap (R.shiftPos t)

theorem borchersShift_vac (R : ReflectTensorData) (t : ℝ) (ht : 0 ≤ t) :
    borchersShift R t borchersVac = borchersVac := by
  unfold borchersShift borchersVac
  ext n x
  by_cases hn : n = 0
  · subst hn
    simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.single_eq_same]
    have hvac := R.shiftPos_vac t ht
    have h1 : (⟨(1 : EuclideanSchwartz 0), Or.inl rfl⟩ : PosSchwartzSubmodule 0) =
        ⟨vacTest0, Or.inl rfl⟩ := rfl
    rw [h1, hvac]
  · simp [DFinsupp.mapRange.linearMap_apply, DFinsupp.single_eq_of_ne hn]

theorem borchersShift_add (R : ReflectTensorData) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (F : BorchersPos) :
    borchersShift R (s + t) F = borchersShift R s (borchersShift R t F) := by
  unfold borchersShift
  ext n x
  simp only [DFinsupp.mapRange.linearMap_apply]
  rw [R.shiftPos_add s t hs ht n (F n)]

/-- Polynomial bound on `(borchersForm C R (borchersShift R t F) (borchersShift R t F)).re`
    derived directly from `C.linear_growth_E0`. -/
theorem borchers_E0_poly_bound (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (F : BorchersPos) :
    ∃ C₀ r : ℝ, 0 < C₀ ∧ 0 ≤ r ∧
      ∀ t ≥ 0, (borchersForm C R (borchersShift R t F) (borchersShift R t F)).re ≤
        C₀ ^ 2 * (1 + t) ^ (2 * r) := by
  obtain ⟨C_E0, α, k, hC_E0, hα, h_E0⟩ := C.linear_growth_E0
  choose C_s hC_s_nn hC_s_bd using fun n : ℕ => R.shiftPos_seminorm_le n k (F n)
  choose C_t hC_t_nn hC_t_bd using fun m n : ℕ => R.tensor_seminorm_le m n k
  let M_bd : ℝ := ∑ m ∈ F.support, ∑ n ∈ F.support,
    C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) * C_t m n *
      (((k + 1 : ℕ) : ℝ) * C_s m) * (((k + 1 : ℕ) : ℝ) * C_s n)
  have hM_nn : 0 ≤ M_bd := by
    refine Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => ?_
    have h1 : 0 ≤ C_E0 ^ (m + n) := pow_nonneg hC_E0.le _
    have h2 : 0 ≤ (Nat.factorial (m + n) : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have := hC_t_nn m n; have := hC_s_nn m; have := hC_s_nn n
    positivity
  let C₀ : ℝ := Real.sqrt M_bd + 1
  have hC₀_pos : 0 < C₀ := by positivity
  have hM_le_sq : M_bd ≤ C₀ ^ 2 := by
    dsimp [C₀]
    have hsq : Real.sqrt M_bd ^ 2 = M_bd := Real.sq_sqrt hM_nn
    nlinarith [Real.sqrt_nonneg M_bd]
  refine ⟨C₀, (k : ℝ), hC₀_pos, Nat.cast_nonneg k, fun t ht => ?_⟩
  have h_re_le : (borchersForm C R (borchersShift R t F) (borchersShift R t F)).re ≤
      ‖borchersForm C R (borchersShift R t F) (borchersShift R t F)‖ :=
    Complex.re_le_norm _
  have h_supp : (borchersShift R t F).support ⊆ F.support := DFinsupp.support_mapRange
  have h_norm_le : ‖borchersForm C R (borchersShift R t F) (borchersShift R t F)‖ ≤
      M_bd * (1 + t) ^ (2 * (k : ℝ)) := by
    unfold borchersForm
    simp only [DFinsupp.sum]
    rw [← Finset.sum_subset h_supp]
    · have h_inner_sub : ∀ m ∈ F.support,
          (∑ n ∈ (borchersShift R t F).support,
            termEval C R m n ((borchersShift R t F) m) ((borchersShift R t F) n)) =
          ∑ n ∈ F.support,
            termEval C R m n ((borchersShift R t F) m) ((borchersShift R t F) n) := by
        intro m _
        refine Finset.sum_subset h_supp fun n _ hn => ?_
        have hn0 : (borchersShift R t F) n = 0 := DFinsupp.not_mem_support_iff.mp hn
        rw [hn0]
        dsimp [termEval]
        have h2 : R.tensor m n (R.reflectConj m ((borchersShift R t F) m).1)
            (0 : PosSchwartzSubmodule n).1 = 0 := by
          have h0 : (0 : EuclideanSchwartz n) = (0 : ℂ) • (0 : EuclideanSchwartz n) := by simp
          rw [show (0 : PosSchwartzSubmodule n).1 = 0 from rfl, h0, R.tensor_smul_right]; simp
        rw [h2, map_zero]
      have h_sum_eq :
          (∑ m ∈ F.support, ∑ n ∈ (borchersShift R t F).support,
            termEval C R m n ((borchersShift R t F) m) ((borchersShift R t F) n)) =
          ∑ m ∈ F.support, ∑ n ∈ F.support,
            termEval C R m n ((borchersShift R t F) m) ((borchersShift R t F) n) :=
        Finset.sum_congr rfl h_inner_sub
      rw [h_sum_eq]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun m _ => ?_
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun n _ => ?_
      dsimp [termEval, borchersShift]
      simp only [DFinsupp.mapRange.linearMap_apply]
      have h1 := h_E0 (m + n) (R.tensor m n (R.reflectConj m (R.shiftPos t m (F m)).1)
        (R.shiftPos t n (F n)).1)
      have h2 := hC_t_bd m n (R.reflectConj m (R.shiftPos t m (F m)).1) (R.shiftPos t n (F n)).1
      have h_sum_refl :
          (∑ j ∈ Finset.range (k + 1),
            SchwartzMap.seminorm ℂ j 0 (R.reflectConj m (R.shiftPos t m (F m)).1)) ≤
          ((k + 1 : ℕ) : ℝ) * C_s m * (1 + t) ^ k := by
        calc (∑ j ∈ Finset.range (k + 1),
              SchwartzMap.seminorm ℂ j 0 (R.reflectConj m (R.shiftPos t m (F m)).1))
            ≤ ∑ j ∈ Finset.range (k + 1),
                SchwartzMap.seminorm ℂ j 0 (R.shiftPos t m (F m)).1 :=
              Finset.sum_le_sum fun j _ => R.reflectConj_seminorm_le m j _
          _ ≤ ∑ _j ∈ Finset.range (k + 1), C_s m * (1 + t) ^ k :=
              Finset.sum_le_sum fun j hj =>
                hC_s_bd m t ht j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
          _ = ((k + 1 : ℕ) : ℝ) * C_s m * (1 + t) ^ k := by
              simp [Finset.sum_const]; ring
      have h_sum_g :
          (∑ j ∈ Finset.range (k + 1),
            SchwartzMap.seminorm ℂ j 0 (R.shiftPos t n (F n)).1) ≤
          ((k + 1 : ℕ) : ℝ) * C_s n * (1 + t) ^ k := by
        calc (∑ j ∈ Finset.range (k + 1),
              SchwartzMap.seminorm ℂ j 0 (R.shiftPos t n (F n)).1)
            ≤ ∑ _j ∈ Finset.range (k + 1), C_s n * (1 + t) ^ k :=
              Finset.sum_le_sum fun j hj =>
                hC_s_bd n t ht j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
          _ = ((k + 1 : ℕ) : ℝ) * C_s n * (1 + t) ^ k := by
              simp [Finset.sum_const]; ring
      have h_pow_r : (1 + t) ^ k * (1 + t) ^ k = (1 + t) ^ (2 * (k : ℝ)) := by
        have h1t : 0 ≤ 1 + t := by linarith
        rw [← pow_add, show k + k = 2 * k by ring, ← Real.rpow_natCast (1 + t) (2 * k)]
        push_cast; rfl
      have h_fac_nn : 0 ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) :=
        mul_nonneg (pow_nonneg hC_E0.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      calc ‖C.S (m + n) (R.tensor m n (R.reflectConj m (R.shiftPos t m (F m)).1)
              (R.shiftPos t n (F n)).1)‖
          ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) *
              SchwartzMap.seminorm ℂ k 0 (R.tensor m n (R.reflectConj m (R.shiftPos t m (F m)).1)
                (R.shiftPos t n (F n)).1) := h1
        _ ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) *
              (C_t m n *
                (∑ j ∈ Finset.range (k + 1),
                  SchwartzMap.seminorm ℂ j 0 (R.reflectConj m (R.shiftPos t m (F m)).1)) *
                (∑ j ∈ Finset.range (k + 1),
                  SchwartzMap.seminorm ℂ j 0 (R.shiftPos t n (F n)).1)) :=
            mul_le_mul_of_nonneg_left h2 h_fac_nn
        _ ≤ C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) *
              (C_t m n * (((k + 1 : ℕ) : ℝ) * C_s m * (1 + t) ^ k) *
                (((k + 1 : ℕ) : ℝ) * C_s n * (1 + t) ^ k)) := by
            refine mul_le_mul_of_nonneg_left ?_ h_fac_nn
            refine mul_le_mul ?_ h_sum_g
              (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
              (mul_nonneg (hC_t_nn m n) (by positivity))
            exact mul_le_mul_of_nonneg_left h_sum_refl (hC_t_nn m n)
        _ = (C_E0 ^ (m + n) * ((Nat.factorial (m + n) : ℝ) ^ α) * C_t m n *
              (((k + 1 : ℕ) : ℝ) * C_s m) * (((k + 1 : ℕ) : ℝ) * C_s n)) *
              (1 + t) ^ (2 * (k : ℝ)) := by
            rw [← h_pow_r]; ring
    · intro m _ hm
      have hm0 : (borchersShift R t F) m = 0 := DFinsupp.not_mem_support_iff.mp hm
      rw [hm0]
      refine Finset.sum_eq_zero fun n _ => ?_
      exact termEval_zero_left C R n _
  have h_final : M_bd * (1 + t) ^ (2 * (k : ℝ)) ≤ C₀ ^ 2 * (1 + t) ^ (2 * (k : ℝ)) :=
    mul_le_mul_of_nonneg_right hM_le_sq (Real.rpow_nonneg (by linarith) _)
  exact le_trans h_re_le (le_trans h_norm_le h_final)

/-- Package `(C, R)` and the RP/symmetry/clustering axioms into `OSBorchers.EuclideanPreData BorchersPos`. -/
def buildBorchersPreData (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (h_herm : ∀ F G : BorchersPos, borchersForm C R G F = star (borchersForm C R F G))
    (h_rp : ∀ F : BorchersPos, 0 ≤ (borchersForm C R F F).re)
    (h_symm : ∀ t : ℝ, 0 ≤ t → ∀ F G : BorchersPos,
      borchersForm C R F (borchersShift R t G) = borchersForm C R (borchersShift R t F) G)
    (h_cluster : ∀ t : ℝ, 0 ≤ t → ∀ F : BorchersPos,
      borchersForm C R borchersVac F = 0 →
      (borchersForm C R (borchersShift R t F) (borchersShift R t F)).re ≤
        Real.exp (-2 * C.cluster_rate * t) * (borchersForm C R F F).re) :
    EuclideanPreData BorchersPos where
  B := borchersForm C R
  B_add_left := borchersForm_add_left C R
  B_smul_left := borchersForm_smul_left C R
  B_add_right := borchersForm_add_right C R
  B_smul_right := borchersForm_smul_right C R
  B_herm := h_herm
  B_nonneg := h_rp
  e₀ := borchersVac
  B_vac := borchersForm_vac C R
  θ := borchersShift R
  θ_vac := borchersShift_vac R
  θ_symm := h_symm
  θ_add := borchersShift_add R
  θ_poly := borchers_E0_poly_bound C R
  Δ := C.cluster_rate
  Δ_pos := C.cluster_rate_pos
  θ_decay := h_cluster

end Imscribing.YangMills.BorchersSchwinger