import Imscribing.ExtensionRegister

/-!
# CancellationNecessity

STATUS: written against your uploaded files + compiled CheapB_Control and
ExtensionRegister. NOT compiled. No `sorry`. See LIKELY FRICTION at the bottom.

## Direction of the arrows

Everything before this file ran tower → analysis (the tower returns whatever it
is fed). Here the arrows run analysis → tower-visible structure. Hypotheses are
analytic facts about (u, p); conclusions are statements about the four carried
momentum terms and about which scales must be active.

## Results

 (A) FTC.  Rest start + bounded acceleration  ⇒  u bounded  ⇒  no blowup.
     [`rest_bounded_acceleration_no_blowup`]
 (B) CANCELLATION IS NECESSARY.  In the B cell (rest start, blowup, bounded
     residual) the acceleration term is unbounded, and transport + viscous +
     pressure is ALSO unbounded: it must cancel the acceleration up to a
     bounded remainder.   [`extB_cancellation_necessary`]
 (C) TOWER FACE OF (B).  Every scale-n injection `injectionForce ν u p n` is
     bounded while the carried `acceleration` component is not.
     [`tower_return_bounded_terms_unbounded`]
 (D) EVERY FINAL INTERVAL IS ACTIVE.  Under *local* blowup the acceleration is
     unbounded on [t₀,1)×ℝ³ for EVERY t₀ < 1 — no finite stage of the tower
     (no t₀ < 1) carries the blowup. A finite tower cannot suffice.
     [`localBlowup_forces_unbounded_acceleration`]
 (E) `BlowsUp` is too weak.  Growth at spatial infinity satisfies it with no
     singularity (`drift`). `LocalBlowsUp` fixes this; it implies `BlowsUp`.
     [`drift_blowsUp`, `drift_not_localBlowsUp`]

What is still by definition, not by necessity: that the tower's round trip
returns the residual (`carriedReEntry ∘ carriedLift = id`). (B)–(D) say the
four-term decomposition and the multi-scale structure are *needed*; they do not
say the tower is the *only* structure that could carry them. That would need a
universal-property statement and is not proved here.
-/

noncomputable section
namespace Imscribing.CancellationNecessity

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Imscribing.FalsifierRegister
open Imscribing.ExtensionRegister
open Set
open scoped ContDiff

/-! ## Helpers -/

theorem mem_strip {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (x : Space) :
    ((t, x) : Domain) ∈ strip := by
  show ((t, x) : Domain) ∈ Ioo (-1 : ℝ) 1 ×ˢ (univ : Set Space)
  exact ⟨ht, mem_univ x⟩

theorem differentiableAt_time (u : Velocity) (hu : ContDiffOn ℝ ∞ u strip)
    (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) (x : Space) :
    DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t := by
  have hz : ((t, x) : Domain) ∈ strip := mem_strip ht x
  have hd : DifferentiableAt ℝ u (t, x) :=
    (hu.contDiffAt (hstrip_unconditional.mem_nhds hz)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (fun s : ℝ => ((s, x) : Domain)) t :=
    differentiableAt_id.prodMk (differentiableAt_const x)
  exact hd.comp t hg

theorem deriv_time_eq (u : Velocity) (x : Space) (y : ℝ) :
    deriv (fun s : ℝ => u (s, x)) y = timeDerivative u (y, x) := by
  unfold timeDerivative
  exact (fderiv_apply_one_eq_deriv).symm

/-- Forward-in-time growth bound at a fixed spatial point. -/
theorem ftc_forward (u : Velocity) (hu : ContDiffOn ℝ ∞ u strip)
    (t0 : ℝ) (ht0 : -1 < t0) (C : ℝ)
    (hC : ∀ z ∈ strip, t0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C)
    (x : Space) {t : ℝ} (ht : t ∈ Ico t0 1) :
    ‖u (t, x)‖ ≤ ‖u (t0, x)‖ + C * (t - t0) := by
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun s : ℝ => u (s, x)) (C := C) (s := Ico t0 1)
    (fun y hy => differentiableAt_time u hu y ⟨by linarith [hy.1], hy.2⟩ x)
    (fun y hy => by
      rw [deriv_time_eq]
      exact hC (y, x) (mem_strip ⟨by linarith [hy.1], hy.2⟩ x) hy.1)
    (convex_Ico t0 1) ⟨le_rfl, lt_of_le_of_lt ht.1 ht.2⟩ ht
  have h1 : ‖u (t, x) - u (t0, x)‖ ≤ C * (t - t0) := by
    have h := hmv
    rw [Real.norm_of_nonneg (sub_nonneg.mpr ht.1)] at h
    exact h
  have h2 : ‖u (t, x)‖ - ‖u (t0, x)‖ ≤ ‖u (t, x) - u (t0, x)‖ := norm_sub_norm_le _ _
  linarith

/-! ## (A) Bounded acceleration and rest exclude blowup -/

theorem rest_bounded_acceleration_no_blowup (u : Velocity) (hu : ContDiffOn ℝ ∞ u strip)
    (hrest : ∀ x : Space, u (0, x) = 0) (C : ℝ)
    (hC : ∀ z ∈ strip, 0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C) :
    ¬ BlowsUp u 1 := by
  intro hb
  have h0 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
  have h1 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  obtain ⟨t, ⟨x, hx⟩, ht0, ht1⟩ := ((hb |C|).and (h0.and h1)).exists
  have hf := ftc_forward u hu 0 (by norm_num) C hC x ⟨ht0.le, ht1⟩
  rw [hrest x, norm_zero, zero_add] at hf
  nlinarith [le_abs_self C, abs_nonneg C,
    mul_nonneg (sub_nonneg.mpr (le_abs_self C)) ht0.le,
    mul_nonneg (abs_nonneg C) (sub_nonneg.mpr ht1.le)]

theorem blowup_forces_unbounded_acceleration (u : Velocity) (hu : ContDiffOn ℝ ∞ u strip)
    (hrest : ∀ x : Space, u (0, x) = 0) (hb : BlowsUp u 1) :
    ¬ ∃ C : ℝ, ∀ z ∈ strip, 0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C :=
  fun ⟨C, hC⟩ => rest_bounded_acceleration_no_blowup u hu hrest C hC hb

/-! ## (B) The other three terms must cancel the acceleration -/

theorem others_unbounded (ν : ℝ) (u : Velocity) (pr : Pressure) (t0 : ℝ)
    (hacc : ¬ ∃ C : ℝ, ∀ z ∈ strip, t0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C)
    (hres : ∃ C : ℝ, ∀ z ∈ strip, ‖residualForce ν u pr z‖ ≤ C) :
    ¬ ∃ C : ℝ, ∀ z ∈ strip, t0 ≤ z.1 →
      ‖transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z‖ ≤ C := by
  rintro ⟨C₃, h3⟩
  obtain ⟨C₁, h1⟩ := hres
  refine hacc ⟨C₁ + C₃, fun z hz hz0 => ?_⟩
  have hid : timeDerivative u z = residualForce ν u pr z -
      (transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z) := by
    have h : residualForce ν u pr z = timeDerivative u z + transport u z +
        (-ν) • spatialLaplacian u z + pressureGradient pr z := rfl
    rw [h]
    abel
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add (h1 z hz) (h3 z hz hz0))

theorem residual_bounded_of_jets (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hj : JetsBoundedOn strip (residualForce ν u pr)) :
    ∃ C : ℝ, ∀ z ∈ strip, ‖residualForce ν u pr z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hj 0
  exact ⟨C, fun z hz => by simpa [norm_iteratedFDeriv_zero] using hC z hz⟩

/-- In the B cell, cancellation among the four carried terms is forced. -/
theorem extB_cancellation_necessary (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hu : ContDiffOn ℝ ∞ u strip) (hrest : ∀ x : Space, u (0, x) = 0)
    (hb : BlowsUp u 1) (hj : JetsBoundedOn strip (residualForce ν u pr)) :
    (¬ ∃ C : ℝ, ∀ z ∈ strip, 0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C) ∧
    (¬ ∃ C : ℝ, ∀ z ∈ strip, 0 ≤ z.1 →
      ‖transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z‖ ≤ C) := by
  have hacc := blowup_forces_unbounded_acceleration u hu hrest hb
  exact ⟨hacc, others_unbounded ν u pr 0 hacc (residual_bounded_of_jets ν u pr hj)⟩

/-! ## (C) Tower face -/

theorem tower_return_bounded_terms_unbounded (ν : ℝ) (u : Velocity) (pr : Pressure)
    (n : ℕ) (hu : ContDiffOn ℝ ∞ u strip) (hrest : ∀ x : Space, u (0, x) = 0)
    (hb : BlowsUp u 1) (hj : JetsBoundedOn strip (residualForce ν u pr)) :
    (∃ C : ℝ, ∀ z ∈ strip, ‖injectionForce ν u pr n z‖ ≤ C) ∧
    ¬ ∃ C : ℝ, ∀ z ∈ strip, 0 ≤ z.1 →
      ‖(momentumTerms ν u pr).acceleration z‖ ≤ C := by
  refine ⟨?_, (extB_cancellation_necessary ν u pr hu hrest hb hj).1⟩
  rw [injection_eq_differential_residual]
  exact residual_bounded_of_jets ν u pr hj

/-! ## (E) Localized blowup -/

/-- Blowup inside a fixed spatial ball: this is a singularity, not growth at infinity. -/
def LocalBlowsUp (u : Velocity) (T : ℝ) : Prop :=
  ∃ R : ℝ, ∀ M : ℝ, ∀ᶠ t in nhdsWithin T (Iio T),
    ∃ x : Space, ‖x‖ ≤ R ∧ M < ‖u (t, x)‖

theorem LocalBlowsUp.blowsUp {u : Velocity} {T : ℝ} (h : LocalBlowsUp u T) :
    BlowsUp u T := by
  obtain ⟨R, hR⟩ := h
  intro M
  filter_upwards [hR M] with t ht
  obtain ⟨x, _, hx⟩ := ht
  exact ⟨x, hx⟩

/-- u(t,x) = t · x₂ · e₀ : smooth, at rest, divergence-free, unbounded in x. -/
def drift (z : Domain) : Space := z.1 • (z.2 1) • basisVector 0

theorem drift_blowsUp : BlowsUp drift 1 := by
  intro M
  have h0 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
  filter_upwards [h0] with t ht0
  set c : ℝ := (|M| + 1) / t with hcdef
  have hc : t * c = |M| + 1 := by
    rw [hcdef]; field_simp
  refine ⟨EuclideanSpace.single (1 : Fin 3) c, ?_⟩
  have h1 : drift (t, EuclideanSpace.single (1 : Fin 3) c) = (t * c) • basisVector 0 := by
    simp [drift, smul_smul]
  have hnorm : ‖drift (t, EuclideanSpace.single (1 : Fin 3) c)‖ = |M| + 1 := by
    rw [h1, norm_smul, basisVector, EuclideanSpace.norm_single, norm_one, mul_one,
      hc, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  linarith [le_abs_self M]

/-- The old `BlowsUp` is satisfied by `drift`, which is bounded on every bounded
    spatial set: no singularity occurs. -/
theorem drift_not_localBlowsUp : ¬ LocalBlowsUp drift 1 := by
  rintro ⟨R, hR⟩
  have h0 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num))
  have h1 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  obtain ⟨t, ⟨x, hxR, hxM⟩, ht0, ht1⟩ := ((hR R).and (h0.and h1)).exists
  have hn : ‖drift (t, x)‖ = |t| * |x 1| := by
    simp [drift, norm_smul, basisVector, EuclideanSpace.norm_single]
  have hx1 : |x 1| ≤ R := by
    have h := PiLp.norm_apply_le x 1
    rw [Real.norm_eq_abs] at h
    linarith
  have hle : |t| * |x 1| ≤ R := by
    rw [abs_of_pos ht0]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (abs_nonneg (x 1))]
  linarith

/-! ## (D) Every final interval is active -/

theorem localBlowup_forces_unbounded_acceleration (u : Velocity)
    (hu : ContDiffOn ℝ ∞ u strip) (hb : LocalBlowsUp u 1)
    {t0 : ℝ} (ht0 : t0 ∈ Ioo (-1 : ℝ) 1) :
    ¬ ∃ C : ℝ, ∀ z ∈ strip, t0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨R, hR⟩ := hb
  have hcont : ContinuousOn (fun x : Space => u (t0, x)) (Metric.closedBall (0 : Space) R) :=
    hu.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => mem_strip ht0 x)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hcont
  have h0 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t0 < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds ht0.2)
  have h1 : ∀ᶠ t in nhdsWithin (1 : ℝ) (Iio 1), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  obtain ⟨t, ⟨x, hxR, hxM⟩, hlt0, hlt1⟩ := ((hR (K + |C| * 2)).and (h0.and h1)).exists
  have hball : x ∈ Metric.closedBall (0 : Space) R := mem_closedBall_zero_iff.mpr hxR
  have hK' : ‖u (t0, x)‖ ≤ K := hK x hball
  have hftc := ftc_forward u hu t0 ht0.1 C hC x ⟨hlt0.le, hlt1⟩
  have hCt : C * (t - t0) ≤ |C| * 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self C)) (sub_nonneg.mpr hlt0.le),
      mul_nonneg (abs_nonneg C) (by linarith [ht0.1] : (0 : ℝ) ≤ 2 - (t - t0))]
  linarith

/-- Corollary: no finite stage carries the blowup, even without a rest assumption. -/
theorem no_finite_stage (u : Velocity) (hu : ContDiffOn ℝ ∞ u strip)
    (hb : LocalBlowsUp u 1) :
    ∀ t0 ∈ Ioo (-1 : ℝ) 1,
      ¬ ∃ C : ℝ, ∀ z ∈ strip, t0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C :=
  fun _ ht0 => localBlowup_forces_unbounded_acceleration u hu hb ht0

end Imscribing.CancellationNecessity
end

/-
LIKELY FRICTION (could not check):

  * `Convex.norm_image_sub_le_of_norm_deriv_le`: I pass `f`, `C`, `s` by name; if the
    implicit names differ, drop the named args and ascribe the expected type
    `‖u (t, x) - u (t0, x)‖ ≤ C * ‖t - t0‖` on `hmv`.
  * `deriv_time_eq`: relies on `fderiv_apply_one_eq_deriv` (it compiled in CheapB_Control)
    with `(y, x).2` / `.1` reducing by defeq under `exact`.
  * `differentiableAt_time`: `differentiableAt_id.prodMk` (vs `DifferentiableAt.prodMk`)
    and `hd.comp t hg` implicit shape.
  * `drift_blowsUp` / `drift_not_localBlowsUp`: the `simp [drift, ...]` normal forms for
    `‖t • x 1 • e₀‖`; `PiLp.norm_apply_le` name and signature.
  * `localBlowup_forces_unbounded_acceleration`: `ContinuousOn.comp` composition shape
    (`u ∘ fun x => (t0, x)` vs the lambda), `IsCompact.exists_bound_of_continuousOn`,
    and `mem_closedBall_zero_iff`.
  * `others_unbounded`: `abel` after `rw [h]`; `h` is closed by `rfl`, as in your
    `differential_injection_connection`.
-/
#print axioms Imscribing.CancellationNecessity.extB_cancellation_necessary
#print axioms Imscribing.CancellationNecessity.tower_return_bounded_terms_unbounded
#print axioms Imscribing.CancellationNecessity.localBlowup_forces_unbounded_acceleration
#print axioms Imscribing.CancellationNecessity.drift_not_localBlowsUp
