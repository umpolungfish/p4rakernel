/-
  Imscribing/YangMills/SUNHaar.lean

  Topological group, compactness and Haar probability measure on SU(N),
  built from Mathlib's product topology on matrices and the closed-unit-box
  compactness argument.  Standard axioms only.
-/
import Mathlib
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option maxHeartbeats 8000000

open Matrix MeasureTheory TopologicalSpace Set Filter

namespace YangMills

abbrev SUN (N : ℕ) := Matrix.specialUnitaryGroup (Fin N) ℂ

/-! ### Topology -/

private lemma continuous_matrix_star (N : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => star A) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_conj.comp ((continuous_apply i).comp (continuous_apply j))

private lemma continuous_matrix_mul (N : ℕ) :
    Continuous (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 * p.2) := by
  rw [show (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 * p.2) =
      (fun p => fun i j => ∑ k, p.1 i k * p.2 k j) by funext p i j; rw [Matrix.mul_apply]]
  fun_prop

private lemma continuous_matrix_det (N : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => Matrix.det A) := by
  rw [show (fun A : Matrix (Fin N) (Fin N) ℂ => Matrix.det A) =
      (fun A => ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • ∏ i, A (σ i) i) by
    funext A; rw [Matrix.det_apply]]
  fun_prop

instance sun_isTopologicalGroup (N : ℕ) : IsTopologicalGroup (SUN N) where
  continuous_mul := by
    rw [continuous_induced_rng]
    exact (continuous_matrix_mul N).comp (continuous_subtype_val.prodMap continuous_subtype_val)
  continuous_inv := by
    rw [continuous_induced_rng]
    simpa only [Function.comp_apply] using (continuous_matrix_star N).comp continuous_subtype_val

/-! ### Closedness and compactness -/

private lemma mem_unitaryGroup_iff_star_mul (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    A ∈ unitaryGroup (Fin N) ℂ ↔ star A * A = 1 := by
  constructor
  · intro h; exact h.1
  · intro h
    exact ⟨h, by rw [← mul_eq_one_comm] at h; exact h⟩

lemma sun_isClosed_carrier (N : ℕ) :
    IsClosed (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hstar := continuous_matrix_star N
  have hmul := continuous_matrix_mul N
  have hdet := continuous_matrix_det N
  have h1 : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | star A * A = 1} :=
    isClosed_eq (hmul.comp (hstar.prodMk continuous_id)) continuous_const
  have h2 : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | Matrix.det A = 1} :=
    isClosed_eq hdet continuous_const
  have h3 : Matrix.specialUnitaryGroup (Fin N) ℂ =
      {A : Matrix (Fin N) (Fin N) ℂ | star A * A = 1} ∩ {A : Matrix (Fin N) (Fin N) ℂ | Matrix.det A = 1} := by
    ext A
    change A ∈ specialUnitaryGroup (Fin N) ℂ ↔ (star A * A = 1 ∧ Matrix.det A = 1)
    rw [Matrix.mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff_star_mul]
  rw [h3]
  exact h1.inter h2

lemma sun_subset_unitBox (N : ℕ) :
    (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
      Set.univ.pi (fun _ : Fin N => Set.univ.pi (fun _ : Fin N => Metric.closedBall (0:ℂ) 1)) := by
  intro A hA i _ j _
  rw [Metric.mem_closedBall, dist_zero_right]
  have hunit : star A * A = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hA).1.1
  have hjj := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M j j) hunit
  have hjj_re := congrArg Complex.re hjj
  have hsum : (∑ k : Fin N, ‖A k j‖ ^ 2) = 1 := by
    simpa [Matrix.mul_apply, Complex.normSq_apply, Complex.sq_norm, star_apply, mul_comm] using hjj_re
  have hle : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (‖A k j‖)) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i j)]

instance sun_compactSpace (N : ℕ) : CompactSpace (SUN N) := by
  have hbox : IsCompact
      (Set.univ.pi (fun _ : Fin N => Set.univ.pi (fun _ : Fin N => Metric.closedBall (0:ℂ) 1))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  exact isCompact_iff_compactSpace.mp (hbox.of_isClosed_subset (sun_isClosed_carrier N) (sun_subset_unitBox N))

/-! ### Measurable structure -/

instance sun_measurableSpace (N : ℕ) : MeasurableSpace (SUN N) := borel (SUN N)
instance sun_borelSpace (N : ℕ) : BorelSpace (SUN N) := ⟨rfl⟩

/-! ### Haar probability measure -/

noncomputable def sunHaar (N : ℕ) : Measure (SUN N) :=
  Measure.haarMeasure (⊤ : PositiveCompacts (SUN N))

instance sunHaar_isProbability (N : ℕ) : IsProbabilityMeasure (sunHaar N) := by
  refine ⟨?_⟩
  change Measure.haarMeasure (⊤ : PositiveCompacts (SUN N)) ((⊤ : PositiveCompacts (SUN N)) : Set (SUN N)) = 1
  exact Measure.haarMeasure_self

instance sunHaar_leftInvariant (N : ℕ) : (sunHaar N).IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _



namespace YangMills

#print axioms YangMills.sunHaar
#print axioms YangMills.sun_compactSpace

end YangMills

/-- A nontrivial element of SU(N) for N >= 2: diagonal (-1,-1,1,...,1). -/
noncomputable def sunFlip (N : ℕ) (h : 2 ≤ N) : SUN N := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  let d : Fin N → ℂ := fun i => if i = i0 ∨ i = i1 then (-1 : ℂ) else 1
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal d
  have hdsq : ∀ i, d i * d i = 1 := by
    intro i; by_cases hd : i = i0 ∨ i = i1 <;> simp [d, hd]
  have hstar : star A = A := by
    ext i j
    by_cases hij : i = j
    · subst j; by_cases hd : i = i0 ∨ i = i1 <;> simp [A, star_apply, d, hd]
    · simp [A, star_apply, Matrix.diagonal, hij]
      intro hji; exact (hij hji.symm).elim
  have hAA : A * A = 1 := by
    rw [← Matrix.diagonal_one (n := Fin N)]
    dsimp [A]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal, hdsq]
    · simp [Matrix.diagonal, hij]
  refine ⟨A, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · constructor
    · rw [hstar]; exact hAA
    · rw [hstar]; exact hAA
  · dsimp [A]
    rw [Matrix.det_diagonal]
    have hi01 : i0 ≠ i1 := by intro he; have := congrArg Fin.val he; simp [i0,i1] at this
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i0)]
    have hi1mem : i1 ∈ Finset.univ \ {i0} := by simp [hi01.symm]
    rw [Finset.prod_eq_mul_prod_diff_singleton hi1mem]
    have hrest : ∀ x ∈ (Finset.univ \ {i0}) \ {i1}, d x = 1 := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hx
      simp [d, hx.1, hx.2]
    rw [Finset.prod_congr rfl hrest]
    simp [d, hi01]

lemma sunFlip_ne_one (N : ℕ) (h : 2 ≤ N) : (sunFlip N h : SUN N) ≠ 1 := by
  intro heq
  have hval := congrArg (fun U : SUN N => U.1 ⟨0, by omega⟩ ⟨0, by omega⟩) heq
  change (if (⟨0, by omega⟩ : Fin N) = ⟨0, by omega⟩ ∨
              (⟨0, by omega⟩ : Fin N) = ⟨1, by omega⟩ then (-1 : ℂ) else 1) = 1 at hval
  norm_num at hval

end YangMills
