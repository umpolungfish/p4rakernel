import Imscribing.WitnessedClosure

/-!
# NativeDomainCancellation

Status: builds. The audited theorems depend on `propext`, `Classical.choice`,
`Quot.sound` only.

`CancellationNecessity` and `extB_force_extends` are stated on
`strip = (-1,1) × ℝ³`. `NSBlowupStatement` is stated on `[0,1) × ℝ³`, with rest
at t = 0, an endpoint. A time translation does not relate the two (the lengths
differ and the singular time is fixed), and a rescaling changes ν and p. This
file instead states the same cancellation chain directly on
`openHalf = (0,1) × ℝ³`, using only smoothness on `Ico 0 1 × ℝ³`, which is what
the statement supplies.

  * `ftc_from_zero`: FTC from the endpoint t = 0, by a limit from the open
    interval.
  * `rest_bounded_acceleration_no_blowup_Ioo`
  * `cancellation_necessary_Ioo`, `fullB_cancellation_Ioo`
  * `statementLoc_forces_cancellation`: statement ⇒ cancellation, on the
    statement's own domain.

The strip-based chain is unchanged and is not used here.
-/

noncomputable section
namespace Imscribing.NativeDomain

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Imscribing.ExtensionRegister
open Imscribing.CancellationNecessity
open Imscribing.WitnessedClosure
open Lean
open Set Filter
open scoped Topology ContDiff

/-- The statement's own open domain. -/
abbrev openHalf : Set Domain := Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)

theorem isOpen_openHalf : IsOpen openHalf := isOpen_Ioo.prod isOpen_univ

/-! ## Endpoint FTC -/

theorem continuousWithinAt_Ioi_of_Ico {E : Type*} [TopologicalSpace E] (g : ℝ → E)
    (h : ContinuousOn g (Ico (0 : ℝ) 1)) : ContinuousWithinAt g (Ioi 0) 0 := by
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    first
    | exact Ioo_mem_nhdsGT zero_lt_one
    | exact Ioo_mem_nhdsWithin_Ioi' zero_lt_one
  have hmem : Ico (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Filter.mem_of_superset hIoo Ioo_subset_Ico_self
  have h0 : ContinuousWithinAt g (Ico 0 1) 0 := h 0 ⟨le_rfl, zero_lt_one⟩
  first
  | exact h0.mono_of_mem_nhdsWithin hmem
  | exact h0.mono_of_mem hmem

/-- `‖g t - g 0‖ ≤ C t`, where the derivative bound is only on the open interval
    and continuity is only right-sided at 0. -/
theorem ftc_from_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hcont : ContinuousWithinAt g (Ioi 0) 0)
    (hdiff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ g t)
    (C : ℝ) (hC : ∀ t ∈ Ioo (0 : ℝ) 1, ‖deriv g t‖ ≤ C)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : ‖g t - g 0‖ ≤ C * t := by
  have key : ∀ t' ∈ Ioo (0 : ℝ) 1, ‖g t - g t'‖ ≤ C * ‖t - t'‖ := fun t' ht' =>
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hC (convex_Ioo 0 1) ht' ht
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    first
    | exact Ioo_mem_nhdsGT zero_lt_one
    | exact Ioo_mem_nhdsWithin_Ioi' zero_lt_one
  have hlim1 : Tendsto (fun t' => ‖g t - g t'‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖g t - g 0‖) :=
    (tendsto_const_nhds.sub hcont).norm
  have hlim2 : Tendsto (fun t' : ℝ => C * ‖t - t'‖) (𝓝[>] (0 : ℝ)) (𝓝 (C * ‖t - 0‖)) := by
    have hc : Continuous (fun t' : ℝ => C * ‖t - t'‖) :=
      continuous_const.mul (continuous_const.sub continuous_id).norm
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t' in 𝓝[>] (0 : ℝ), ‖g t - g t'‖ ≤ C * ‖t - t'‖ :=
    Filter.mem_of_superset hmem (fun t' ht' => key t' ht')
  have hle : ‖g t - g 0‖ ≤ C * ‖t - 0‖ := le_of_tendsto_of_tendsto hlim1 hlim2 hev
  rw [sub_zero, Real.norm_of_nonneg ht.1.le] at hle
  exact hle

/-! ## Time regularity on the statement's domain -/

theorem continuousWithinAt_time_zero (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space))) (x : Space) :
    ContinuousWithinAt (fun t : ℝ => u (t, x)) (Ioi 0) 0 := by
  have hco : ContinuousOn (fun t : ℝ => u (t, x)) (Ico 0 1) :=
    hu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ x⟩)
  exact continuousWithinAt_Ioi_of_Ico _ hco

theorem differentiableAt_time_Ioo (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t := by
  have hz : ((t, x) : Domain) ∈ openHalf := ⟨ht, mem_univ x⟩
  have hu' : ContDiffOn ℝ ∞ u openHalf :=
    hu.mono (Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl)
  have hd : DifferentiableAt ℝ u (t, x) :=
    (hu'.contDiffAt (isOpen_openHalf.mem_nhds hz)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (fun s : ℝ => ((s, x) : Domain)) t :=
    differentiableAt_id.prodMk (differentiableAt_const x)
  exact hd.comp t hg

/-! ## Rest + bounded acceleration excludes blowup -/

theorem rest_bounded_acceleration_no_blowup_Ioo (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)))
    (hrest : ∀ x : Space, u (0, x) = 0) (C : ℝ)
    (hC : ∀ z ∈ openHalf, ‖timeDerivative u z‖ ≤ C) : ¬ BlowsUp u 1 := by
  intro hb
  have h0 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
  have h1 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  obtain ⟨t, ⟨x, hx⟩, ht0, ht1⟩ := ((hb |C|).and (h0.and h1)).exists
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hftc := ftc_from_zero (fun s : ℝ => u (s, x))
    (continuousWithinAt_time_zero u hu x)
    (fun s hs => differentiableAt_time_Ioo u hu hs x) C
    (fun s hs => by
      rw [deriv_time_eq]
      exact hC (s, x) ⟨hs, mem_univ x⟩) ht
  have hftc' : ‖u (t, x)‖ ≤ C * t := by
    have h := hftc
    simp only [hrest x, sub_zero] at h
    exact h
  have h2 : C * t ≤ |C| :=
    calc C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht0.le
      _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) ht1.le
  linarith [hx, hftc', h2]

/-! ## Cancellation on the native domain -/

theorem cancellation_necessary_Ioo (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)))
    (hrest : ∀ x : Space, u (0, x) = 0) (hb : BlowsUp u 1)
    (hj : JetsBoundedOn openHalf (residualForce ν u pr)) :
    (¬ ∃ C : ℝ, ∀ z ∈ openHalf, ‖timeDerivative u z‖ ≤ C) ∧
    (¬ ∃ C : ℝ, ∀ z ∈ openHalf,
      ‖transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z‖ ≤ C) := by
  have hacc : ¬ ∃ C : ℝ, ∀ z ∈ openHalf, ‖timeDerivative u z‖ ≤ C :=
    fun ⟨C, hC⟩ => rest_bounded_acceleration_no_blowup_Ioo u hu hrest C hC hb
  refine ⟨hacc, ?_⟩
  rintro ⟨C₃, h3⟩
  obtain ⟨C₁, h1⟩ := hj 0
  refine hacc ⟨C₁ + C₃, fun z hz => ?_⟩
  have hres : ‖residualForce ν u pr z‖ ≤ C₁ := by
    simpa [norm_iteratedFDeriv_zero] using h1 z hz
  have hid : timeDerivative u z = residualForce ν u pr z -
      (transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z) := by
    have h : residualForce ν u pr z = timeDerivative u z + transport u z +
        (-ν) • spatialLaplacian u z + pressureGradient pr z := rfl
    rw [h]
    abel
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add hres (h3 z hz))

/-- Cancellation is forced inside the full cell, on the statement's domain. -/
theorem fullB_cancellation_Ioo (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)))
    (hF : FullBlowsUp ν u pr openHalf 1) :
    (¬ ∃ C : ℝ, ∀ z ∈ openHalf, ‖timeDerivative u z‖ ≤ C) ∧
    (¬ ∃ C : ℝ, ∀ z ∈ openHalf,
      ‖transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z‖ ≤ C) :=
  cancellation_necessary_Ioo ν u pr hu hF.rest hF.blow.blowsUp hF.jets

/-- Any witness of the local statement exhibits forced cancellation, with no
    extension to t < 0 and no strip. -/
theorem statementLoc_forces_cancellation (ν : ℝ) (h : NSBlowupStatementLoc ν) :
    ∃ (u : Velocity) (pr : Pressure),
      (¬ ∃ C : ℝ, ∀ z ∈ openHalf, ‖timeDerivative u z‖ ≤ C) ∧
      (¬ ∃ C : ℝ, ∀ z ∈ openHalf,
        ‖transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z‖ ≤ C) := by
  obtain ⟨_, f, u, pr, hf, hfc, hu, hp, hNS, hrest, hen, hb⟩ := h
  have hj : JetsBoundedOn openHalf (residualForce ν u pr) :=
    jetsBoundedOn_of_compactSupport isOpen_openHalf f hf hfc (fun z hz => (hNS z hz).1)
  exact ⟨u, pr, cancellation_necessary_Ioo ν u pr hu hrest hb.blowsUp hj⟩

end Imscribing.NativeDomain
end

#print axioms Imscribing.NativeDomain.ftc_from_zero
#print axioms Imscribing.NativeDomain.cancellation_necessary_Ioo
#print axioms Imscribing.NativeDomain.statementLoc_forces_cancellation
