/-
  Step 2 of the unconditional-closure blueprint: pushforward of Haar under the
  plaquette defect f_0 is absolutely continuous w.r.t. Lebesgue measure.
-/
import Mathlib
import Imscribing.YangMills.PlaquetteDensity
import Imscribing.YangMills.SubmersionDensity

set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal Matrix
open MeasureTheory Matrix Filter

noncomputable section
namespace YangMills

variable {N : ℕ}
variable (hN : 2 ≤ N)
variable (suHaar : Measure (specialUnitaryGroup (Fin N) ℂ))
  [IsProbabilityMeasure suHaar] [suHaar.IsMulLeftInvariant] [suHaar.IsMulRightInvariant]

/-- f₀(U) := 1 - (1/N) Re Tr(U). -/
noncomputable def f0 (M : ℕ) (U : specialUnitaryGroup (Fin M) ℂ) : ℝ :=
  1 - (1 / (M : ℝ)) * (Matrix.trace (U : Matrix (Fin M) (Fin M) ℂ)).re

lemma f0_continuous (M : ℕ) : Continuous (f0 M) := by
  unfold f0
  fun_prop

example (t : ℝ) : star (Complex.exp (Complex.I * t)) = Complex.exp (-Complex.I * t) := by
  change (starRingEnd ℂ) (Complex.exp (Complex.I * t)) = Complex.exp (-Complex.I * t)
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- γ₀₁(θ) := diag(e^{iθ}, e^{-iθ}, 1, ..., 1) ∈ SU(N). -/
noncomputable def gamma01 (θ : ℝ) : specialUnitaryGroup (Fin N) ℂ := by
  let d : Fin N → ℂ := fun j =>
    if j.1 = 0 then Complex.exp (Complex.I * θ)
    else if j.1 = 1 then Complex.exp (-Complex.I * θ) else 1
  refine ⟨Matrix.diagonal d, ?_⟩
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · have hd_norm : ∀ i, d i * star (d i) = 1 := by
      intro i
      dsimp [d]
      split_ifs with h0 h1
      · exact exp_I_mul_conj θ
      · rw [show -Complex.I * (θ : ℂ) = Complex.I * ((-θ : ℝ) : ℂ) by push_cast; ring]
        exact exp_I_mul_conj (-θ)
      · simp
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.mul_apply, Matrix.diagonal_apply] using hd_norm i
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Matrix.mul_apply, Matrix.diagonal_apply, hij, hji]
  · rw [Matrix.det_diagonal]
    have h01 : (idx0 hN) ≠ (idx1 hN) := by
      intro h; have := congrArg Fin.val h; simp [idx0, idx1] at this
    have hs0 : (∏ j : Fin N, d j) = d (idx0 hN) * ((Finset.univ.erase (idx0 hN)).prod d) :=
      (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ (idx0 hN))).symm
    have hs1 : ((Finset.univ.erase (idx0 hN)).prod d) =
        d (idx1 hN) * (((Finset.univ.erase (idx0 hN)).erase (idx1 hN)).prod d) :=
      (Finset.mul_prod_erase _ d
        (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (idx1 hN)⟩)).symm
    rw [hs0, hs1]
    have hrest : (((Finset.univ.erase (idx0 hN)).erase (idx1 hN)).prod d) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hj1 : j ≠ idx1 hN := (Finset.mem_erase.mp hj).1
      have hj0 : j ≠ idx0 hN := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have h0v : j.1 ≠ 0 := fun h => hj0 (Fin.ext h)
      have h1v : j.1 ≠ 1 := fun h => hj1 (Fin.ext h)
      simp [d, h0v, h1v]
    rw [hrest, mul_one]
    simp [d, idx0, idx1]
    rw [← Complex.exp_add]
    rw [show Complex.I * (θ : ℂ) + -(Complex.I * (θ : ℂ)) = 0 by ring, Complex.exp_zero]

lemma gamma01_continuous : Continuous (gamma01 hN) := by
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]; intro i
  rw [continuous_pi_iff]; intro j
  by_cases hij : i = j
  · subst j
    simp only [gamma01, Matrix.diagonal_apply_eq]
    split_ifs <;> fun_prop
  · simp [gamma01, hij]
    exact continuous_const


lemma f0_gamma01_formula (V : specialUnitaryGroup (Fin N) ℂ) :
    ∃ c0 : ℝ, ∀ θ : ℝ,
      f0 N (gamma01 hN θ * V) =
        c0 - (1 / (N : ℝ)) *
          (Complex.exp (Complex.I * θ) *
            ((V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
              star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)))).re := by
  have h01 : idx0 hN ≠ idx1 hN := by
    intro h; have := congrArg Fin.val h; simp [idx0, idx1] at this
  let c0 : ℝ := 1 - (1 / (N : ℝ)) *
    (∑ j ∈ (Finset.univ.erase (idx0 hN)).erase (idx1 hN),
      ((V : Matrix (Fin N) (Fin N) ℂ) j j).re)
  refine ⟨c0, fun θ => ?_⟩
  -- trace of gamma01 θ * V
  have htr : Matrix.trace (((gamma01 hN θ : specialUnitaryGroup (Fin N) ℂ) *
      V : specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Complex.exp (Complex.I * θ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
      Complex.exp (-Complex.I * θ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN) +
      ∑ j ∈ (Finset.univ.erase (idx0 hN)).erase (idx1 hN),
        (V : Matrix (Fin N) (Fin N) ℂ) j j := by
    change Matrix.trace ((gamma01 hN θ : Matrix (Fin N) (Fin N) ℂ) *
      (V : Matrix (Fin N) (Fin N) ℂ)) = _
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    have hdiag : ∀ j : Fin N, (∑ k : Fin N, (V : Matrix (Fin N) (Fin N) ℂ) j k *
        (gamma01 hN θ : Matrix (Fin N) (Fin N) ℂ) k j) =
        (if j.1 = 0 then Complex.exp (Complex.I * θ)
         else if j.1 = 1 then Complex.exp (-Complex.I * θ) else 1) *
          (V : Matrix (Fin N) (Fin N) ℂ) j j := by
      intro j
      rw [Finset.sum_eq_single j]
      · simp [gamma01, Matrix.diagonal_apply, mul_comm]
      · intro k _ hkj
        simp [gamma01, Matrix.diagonal_apply, hkj]
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    simp_rw [hdiag]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (idx0 hN))]
    rw [← Finset.add_sum_erase (Finset.univ.erase (idx0 hN)) _
      (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (idx1 hN)⟩)]
    have hrest : (∑ j ∈ (Finset.univ.erase (idx0 hN)).erase (idx1 hN),
        (if j.1 = 0 then Complex.exp (Complex.I * θ)
         else if j.1 = 1 then Complex.exp (-Complex.I * θ) else 1) *
          (V : Matrix (Fin N) (Fin N) ℂ) j j) =
        ∑ j ∈ (Finset.univ.erase (idx0 hN)).erase (idx1 hN),
          (V : Matrix (Fin N) (Fin N) ℂ) j j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj1 : j ≠ idx1 hN := (Finset.mem_erase.mp hj).1
      have hj0 : j ≠ idx0 hN := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have h0v : j.1 ≠ 0 := fun h => hj0 (Fin.ext h)
      have h1v : j.1 ≠ 1 := fun h => hj1 (Fin.ext h)
      simp [h0v, h1v]
    rw [hrest]
    simp [idx0, idx1, add_assoc]
  have hre : (Complex.exp (Complex.I * θ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
      Complex.exp (-Complex.I * θ) * (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)).re =
      (Complex.exp (Complex.I * θ) *
        ((V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
          star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)))).re := by
    have hconj : (Complex.exp (-Complex.I * θ) *
        (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)).re =
        (Complex.exp (Complex.I * θ) *
          star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN))).re := by
      rw [← Complex.conj_re]
      congr 1
      change (starRingEnd ℂ) (Complex.exp (-Complex.I * θ) *
        (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) = _
      rw [map_mul]
      have he : (starRingEnd ℂ) (Complex.exp (-Complex.I * θ)) = Complex.exp (Complex.I * θ) := by
        rw [← Complex.exp_conj]
        congr 1
        simp
      rw [he]
      simp
    rw [Complex.add_re, hconj, ← Complex.add_re, ← mul_add]
  unfold f0
  rw [htr, Complex.add_re, Complex.add_re]
  rw [← Complex.add_re]
  rw [hre]
  simp only [c0, Complex.re_sum]
  ring


/-- Slice-null lemma: for a nonzero defect w, the gamma01 slice of a null set
    under f₀ has Lebesgue measure zero. -/
lemma gamma01_slice_null (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (V : specialUnitaryGroup (Fin N) ℂ)
    (hV : (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
      star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) ≠ 0)
    (S : Set ℝ) (hS_meas : MeasurableSet S) (hS_vol : volume S = 0) :
    volume {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
      gamma01 hN θ * V ∈ f0 N ⁻¹' S ∩
    {V | (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
      star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) ≠ 0}} = 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let H0 : Set (specialUnitaryGroup (Fin N) ℂ) :=
    {V | (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
      star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) ≠ 0}
  let E : Set (specialUnitaryGroup (Fin N) ℂ) := f0 N ⁻¹' S ∩ H0
  set w : ℂ := (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
        star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN))
  have hw : w ≠ 0 := hV
  obtain ⟨c0, hc0⟩ := f0_gamma01_formula hN V
  let r : ℝ := ‖w‖
  let α : ℝ := Complex.arg w
  let R : ℝ := r / (N : ℝ)
  have hr_pos : 0 < r := norm_pos_iff.mpr hw
  have hR_pos : 0 < R := div_pos hr_pos hNpos
  have hw_re : w.re = r * Real.cos α := by
    rw [show α = Complex.arg w by rfl, Complex.cos_arg hw]
    field_simp [hr_pos.ne']
    simp [r]
  have hw_im : w.im = r * Real.sin α := by
    rw [show α = Complex.arg w by rfl, Complex.sin_arg w]
    field_simp [hr_pos.ne']
    simp [r]
  let g : ℝ → ℝ := fun θ => c0 - R * Real.cos (θ + α)
  have hg_eq : ∀ θ : ℝ, f0 N (gamma01 hN θ * V) = g θ := by
    intro θ
    rw [hc0 θ]
    have hre_mul : (Complex.exp (Complex.I * θ) * w).re = r * Real.cos (θ + α) := by
      rw [mul_comm Complex.I (θ : ℂ), Complex.exp_mul_I]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, mul_one, zero_mul]
      rw [hw_re, hw_im, Real.cos_add]
      ring
    rw [hre_mul]
    simp [g, R]
    ring
  have hg_contDiff : ContDiff ℝ 1 g := by
    unfold g
    fun_prop
  have hg_deriv : ∀ θ : ℝ, deriv g θ = R * Real.sin (θ + α) := by
    intro θ
    have h1 : HasDerivAt (fun t : ℝ => t + α) 1 θ := (hasDerivAt_id θ).add_const α
    have h2' := (Real.hasDerivAt_cos (θ + α)).comp θ h1
    have h2 : HasDerivAt (fun t : ℝ => Real.cos (t + α)) (-Real.sin (θ + α)) θ := by
      simpa using h2' 
    have h3 : HasDerivAt g (0 - R * (-Real.sin (θ + α))) θ :=
      (hasDerivAt_const θ c0).sub (h2.const_mul R)
    simpa using h3.deriv
  let Ik : ℤ → Set ℝ := fun k => Set.Ioo (-α + (k : ℝ) * Real.pi)
    (-α + ((k : ℝ) + 1) * Real.pi)
  have hIk_null : ∀ k : ℤ, volume (Ik k ∩ g ⁻¹' S) = 0 := by
    intro k
    have hopen : IsOpen (Ik k) := isOpen_Ioo
    have hsubm := submersion_1d hopen hg_contDiff.contDiffOn (fun θ hθ => by
      rw [hg_deriv θ]
      refine mul_ne_zero hR_pos.ne' ?_
      have hlt1 : (k : ℝ) * Real.pi < θ + α := by linarith [hθ.1]
      have hlt2 : θ + α < ((k : ℝ) + 1) * Real.pi := by linarith [hθ.2]
      intro hsin
      rw [Real.sin_eq_zero_iff] at hsin
      obtain ⟨n, hn⟩ := hsin
      have hgt : (k : ℝ) < n := by
        have : (k : ℝ) * Real.pi < (n : ℝ) * Real.pi := by linarith
        nlinarith [Real.pi_pos]
      have hlt : (n : ℝ) < (k : ℝ) + 1 := by
        have : (n : ℝ) * Real.pi < ((k : ℝ) + 1) * Real.pi := by linarith
        nlinarith [Real.pi_pos]
      have : k < n ∧ n < k + 1 := ⟨by exact_mod_cast hgt, by exact_mod_cast hlt⟩
      omega)
    obtain ⟨ρ, hρ⟩ := hsubm
    have hac : (volume.restrict (Ik k)).map g ≪ volume := by
      rw [hρ]
      exact withDensity_absolutelyContinuous volume ρ
    have hmap0 := hac hS_vol
    rw [Measure.map_apply hg_contDiff.continuous.measurable hS_meas,
      Measure.restrict_apply (hg_contDiff.continuous.measurable hS_meas)] at hmap0
    simpa [Set.inter_comm] using hmap0
  let pts : Set ℝ := Set.range (fun k : ℤ => -α + (k : ℝ) * Real.pi)
  have hpts_null : volume pts = 0 := (Set.countable_range _).measure_zero volume
  have hcover : Set.univ ⊆ pts ∪ ⋃ k : ℤ, Ik k := by
    intro θ _
    let k : ℤ := Int.floor ((θ + α) / Real.pi)
    by_cases heq : θ + α = (k : ℝ) * Real.pi
    · left
      exact ⟨k, by linarith⟩
    · right
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      constructor
      · have hk_le : (k : ℝ) * Real.pi ≤ θ + α := by
          have := Int.floor_le ((θ + α) / Real.pi)
          exact (le_div_iff₀ Real.pi_pos).mp this
        have hk_lt : (k : ℝ) * Real.pi < θ + α := lt_of_le_of_ne hk_le (fun h => heq h.symm)
        linarith
      · have hk_lt : θ + α < ((k : ℝ) + 1) * Real.pi := by
          have := Int.lt_floor_add_one ((θ + α) / Real.pi)
          exact (div_lt_iff₀ Real.pi_pos).mp this
        linarith
  have hgS_null : volume (g ⁻¹' S) = 0 := by
    have hsub : g ⁻¹' S ⊆ pts ∪ ⋃ k : ℤ, (Ik k ∩ g ⁻¹' S) := by
      intro θ hθ
      rcases hcover (Set.mem_univ θ) with hpt | hk
      · exact Or.inl hpt
      · rcases Set.mem_iUnion.mp hk with ⟨k, hk⟩
        exact Or.inr (Set.mem_iUnion.mpr ⟨k, hk, hθ⟩)
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    exact ⟨hpts_null, measure_iUnion_null hIk_null⟩
  have hslice : volume {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
      gamma01 hN θ * V ∈ E} = 0 := by
    refine measure_mono_null ?_ hgS_null
    intro θ hθ
    change g θ ∈ S
    rw [← hg_eq θ]
    exact hθ.2.1
  exact hslice

/-- Step 2a: the Haar pushforward along f₀ is absolutely continuous. -/
theorem f0_pushforward_absolutelyContinuous (hN : 2 ≤ N)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ) :
    (suHaar.map (f0 N)) ≪ volume := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let H0 : Set (specialUnitaryGroup (Fin N) ℂ) :=
    {V | (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
      star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) ≠ 0}
  have hH0_meas : MeasurableSet H0 :=
    (isOpen_ne.preimage
      ((Continuous.matrix_elem continuous_subtype_val (idx0 hN) (idx0 hN)).add
        ((Continuous.matrix_elem continuous_subtype_val (idx1 hN) (idx1 hN)).star))).measurableSet
  have hH0c_null : suHaar H0ᶜ = 0 := by
    simpa [H0, Set.compl_setOf, not_not] using
      suHaar_v00_add_conj_v11_eq_zero suHaar hN
  refine Measure.AbsolutelyContinuous.mk ?_
  intro S hS_meas hS_vol
  rw [Measure.map_apply (f0_continuous N).measurable hS_meas]
  let E : Set (specialUnitaryGroup (Fin N) ℂ) := f0 N ⁻¹' S ∩ H0
  have hE_meas : MeasurableSet E := (f0_continuous N).measurable hS_meas |>.inter hH0_meas
  have hE_null : suHaar E = 0 := by
    have hgamma_meas : Measurable (fun p : ℝ × specialUnitaryGroup (Fin N) ℂ =>
        gamma01 hN p.1 * p.2) :=
      (continuous_mul.comp
        (Continuous.prodMk ((gamma01_continuous hN).comp continuous_fst) continuous_snd)).measurable
    refine haar_null_of_slice_null suHaar (gamma01 hN) hgamma_meas hE_meas ?_
    intro V
    by_cases hV : V ∈ H0
    · exact gamma01_slice_null hN submersion_1d V hV S hS_meas hS_vol
    · have hempty : {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ gamma01 hN θ * V ∈ E} = ∅ := by
        ext θ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hmem
        apply hV
        have h00 : ((gamma01 hN θ * V : specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) =
              Complex.exp (Complex.I * θ) *
                (V : Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) := by
          change ((((gamma01 hN θ : specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) * (V : Matrix (Fin N) (Fin N) ℂ))
              (idx0 hN) (idx0 hN)) = _
          simp [gamma01, Matrix.mul_apply, Matrix.diagonal_apply, idx0]
        have h11 : ((gamma01 hN θ * V : specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN) =
              Complex.exp (-Complex.I * θ) *
                (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN) := by
          change ((((gamma01 hN θ : specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) * (V : Matrix (Fin N) (Fin N) ℂ))
              (idx1 hN) (idx1 hN)) = _
          simp [gamma01, Matrix.mul_apply, Matrix.diagonal_apply, idx1]
        have h11s : star (((gamma01 hN θ * V : specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) =
              Complex.exp (Complex.I * θ) *
                star ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) := by
          rw [h11]
          change (starRingEnd ℂ) (Complex.exp (-Complex.I * θ) *
              (V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) =
            Complex.exp (Complex.I * θ) *
              (starRingEnd ℂ) ((V : Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN))
          rw [map_mul]
          congr 1
          rw [← Complex.exp_conj]
          congr 1 <;> simp
        have hsum := hmem.2
        change ((gamma01 hN θ * V : specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) (idx0 hN) (idx0 hN) +
          star (((gamma01 hN θ * V : specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) (idx1 hN) (idx1 hN)) ≠ 0 at hsum
        rw [h00, h11s, ← mul_add] at hsum
        exact (mul_ne_zero_iff.mp hsum).2
      rw [hempty, measure_empty]
  have hsub : f0 N ⁻¹' S ⊆ E ∪ H0ᶜ := by
    intro V hV
    by_cases hH : V ∈ H0
    · exact Or.inl ⟨hV, hH⟩
    · exact Or.inr hH
  have hle1 : suHaar (f0 N ⁻¹' S) ≤ suHaar (E ∪ H0ᶜ) := measure_mono hsub
  have hle2 : suHaar (E ∪ H0ᶜ) ≤ suHaar E + suHaar H0ᶜ := measure_union_le E H0ᶜ
  have hle : suHaar (f0 N ⁻¹' S) ≤ suHaar E + suHaar H0ᶜ := hle1.trans hle2
  rw [hE_null, hH0c_null, add_zero] at hle
  exact le_antisymm hle (bot_le)

/-- Step 2b: Haar invariance gives the two-sided version for free. -/
theorem f0_twosided_pushforward_absolutelyContinuous (hN' : 2 ≤ N)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (A B : specialUnitaryGroup (Fin N) ℂ) :
    (suHaar.map (fun U => f0 N (A * U * B))) ≪ volume := by
  have hleft : suHaar.map (fun U : specialUnitaryGroup (Fin N) ℂ => A * U) = suHaar := by
    simpa using (map_mul_left_eq_self suHaar A)
  have hright : suHaar.map (fun U : specialUnitaryGroup (Fin N) ℂ => U * B) = suHaar := by
    simpa using (map_mul_right_eq_self suHaar B)
  have h_inv : suHaar.map (fun U : specialUnitaryGroup (Fin N) ℂ => A * U * B) = suHaar := by
    have hcomp : (fun U : specialUnitaryGroup (Fin N) ℂ => A * U * B) =
        (fun U => U * B) ∘ (fun U => A * U) := rfl
    rw [hcomp, ← Measure.map_map (continuous_mul_right B).measurable
      (continuous_mul_left A).measurable, hleft, hright]
  have hmap : suHaar.map (fun U => f0 N (A * U * B)) = suHaar.map (f0 N) := by
    calc
      suHaar.map (fun U => f0 N (A * U * B))
          = (suHaar.map (fun U => A * U * B)).map (f0 N) := by
              exact (Measure.map_map (f0_continuous N).measurable
                ((continuous_mul_right B).comp (continuous_mul_left A)).measurable).symm
      _ = suHaar.map (f0 N) := by rw [h_inv]
  rw [hmap]
  exact f0_pushforward_absolutelyContinuous suHaar hN' submersion_1d

end YangMills
