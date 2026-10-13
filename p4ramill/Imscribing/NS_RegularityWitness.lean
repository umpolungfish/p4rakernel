import Imscribing.NS_InjectionField
import Imscribing.NS_KernelReentry
import Imscribing.NS_ResidualExtension
import Init.Paraconsistent
import Mathlib.MeasureTheory.Integral.Bochner.Basic

enable_trilattice

/-!
# NS_RegularityWitness

STATUS: written against the six uploaded files, NOT compiled. Expect to debug
lemma names (see the "likely friction" notes) but the statements are intended
to be right.

What this file adds, in terms of the gaps identified in review:

  A. (gap 3)  `ContDiffOn` versions of the smoothness lemmas, so `hregular` for
              `extendedResidual` can be DERIVED from smoothness of `u, p` on the
              open strip, instead of being assumed about the residual.
  B. (gap 5)  A regularity register whose value is COMPUTED from two proved
              facts (smooth on the strip, blows up at the endpoint). B is
              assembled from two vessels, never declared. Tied to `nativeHeld`.
  C. (gap 4)  An interface making the tower index `n` index something: a
              scale decomposition of the residual. Content is a hypothesis
              (`sum_eq`) that the published pulse data must discharge.
  D. (gap 6)  The extension past the singular time is not unique: it can be
              changed by any smooth field vanishing on the strip. This is the
              formal counterpart of "the tower's Witness is unique, the
              analysis's extension is free".
  E. (gap 2)  A Lean statement of the finite-time blowup theorem as a `Prop`
              (not proved), so the capstone has a target.

Nothing here uses `sorry`. Nothing here proves blowup.
-/

noncomputable section
namespace Imscribing.NSRegularityWitness

open Imscribing.NSInjectionField
open Imscribing.NSReentry
open Imscribing.NSResidualExtension
open Lean
open scoped ContDiff

/-! ## A. ContDiffOn smoothness of the differential residual -/

/-- Partial derivative in a spatial direction is the full Fréchet derivative
    applied to `(0, eᵢ)`, wherever the field is differentiable. -/
theorem spatialDerivative_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : Domain → E) (z : Domain) (hz : DifferentiableAt ℝ field z) (i : Fin 3) :
    spatialDerivative field i z = fderiv ℝ field z (0, basisVector i) := by
  have hg : HasFDerivAt (fun x : Space => (z.1, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hz' : DifferentiableAt ℝ field (z.1, z.2) := hz
  have hcomp : HasFDerivAt (fun x : Space => field (z.1, x))
      ((fderiv ℝ field (z.1, z.2)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) z.2 :=
    hz'.hasFDerivAt.comp z.2 hg
  unfold spatialDerivative
  rw [hcomp.fderiv]
  simp

/-- Time derivative is the Fréchet derivative applied to `(1, 0)`. -/
theorem timeDerivative_eq_fderiv (u : Velocity) (z : Domain)
    (hz : DifferentiableAt ℝ u z) :
    timeDerivative u z = fderiv ℝ u z (1, 0) := by
  have hg : HasFDerivAt (fun t : ℝ => (t, z.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hz' : DifferentiableAt ℝ u (z.1, z.2) := hz
  have hcomp : HasFDerivAt (fun t : ℝ => u (t, z.2))
      ((fderiv ℝ u (z.1, z.2)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space))) z.1 :=
    hz'.hasFDerivAt.comp z.1 hg
  unfold timeDerivative
  rw [hcomp.fderiv]
  simp

theorem spatialDerivative_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : Domain → E) {U : Set Domain} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ field U) (i : Fin 3) :
    ContDiffOn ℝ ∞ (spatialDerivative field i) U := by
  have hd : ContDiffOn ℝ ∞ (fun z => fderiv ℝ field z) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun z => fderiv ℝ field z (0, basisVector i)) U :=
    hd.clm_apply contDiffOn_const
  refine h2.congr ?_
  intro z hz
  exact spatialDerivative_eq_fderiv field z
    ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) i

theorem timeDerivative_contDiffOn (u : Velocity) {U : Set Domain} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (timeDerivative u) U := by
  have hd : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z) U :=
    hu.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z (1, 0)) U :=
    hd.clm_apply contDiffOn_const
  refine h2.congr ?_
  intro z hz
  exact timeDerivative_eq_fderiv u z
    ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

theorem transport_contDiffOn (u : Velocity) {U : Set Domain} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (transport u) U := by
  apply ContDiffOn.sum
  intro i _
  have hi : ContDiffOn ℝ ∞ (fun z => u z i) U :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
  exact hi.smul (spatialDerivative_contDiffOn u hU hu i)

theorem laplacian_contDiffOn (u : Velocity) {U : Set Domain} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (spatialLaplacian u) U := by
  apply ContDiffOn.sum
  intro i _
  exact spatialDerivative_contDiffOn _ hU (spatialDerivative_contDiffOn u hU hu i) i

theorem pressureGradient_contDiffOn (pr : Pressure) {U : Set Domain} (hU : IsOpen U)
    (hp : ContDiffOn ℝ ∞ pr U) :
    ContDiffOn ℝ ∞ (pressureGradient pr) U := by
  apply ContDiffOn.sum
  intro i _
  exact (spatialDerivative_contDiffOn pr hU hp i).smul contDiffOn_const

/-- The residual of `(u, p)` is smooth on an open set wherever `u, p` are. This
    is the lemma that lets `hregular` be derived. -/
theorem residualForce_contDiffOn (ν : ℝ) (u : Velocity) (pr : Pressure)
    {U : Set Domain} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hp : ContDiffOn ℝ ∞ pr U) :
    ContDiffOn ℝ ∞ (residualForce ν u pr) U := by
  show ContDiffOn ℝ ∞ (fun z => timeDerivative u z + transport u z +
      (-ν) • spatialLaplacian u z + pressureGradient pr z) U
  exact (((timeDerivative_contDiffOn u hU hu).add (transport_contDiffOn u hU hu)).add
    ((laplacian_contDiffOn u hU hu).const_smul (-ν))).add
    (pressureGradient_contDiffOn pr hU hp)

/-- Specialisation to the strip used by `extendedResidual`. The openness of the
    strip is taken as a hypothesis because its definition lives in
    `GenericEndpointExtension`. If it is `Ioo (-1) 1 ×ˢ univ`, discharge it with
    `isOpen_Ioo.prod isOpen_univ`. -/
theorem hregular_of_strip (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hstrip : IsOpen strip)
    (hu : ContDiffOn ℝ ∞ u strip) (hp : ContDiffOn ℝ ∞ pr strip) :
    ContDiffOn ℝ ∞ (residualForce ν u pr) strip :=
  residualForce_contDiffOn ν u pr hstrip hu hp

/-! ## B. Regularity register computed from two vessels -/

/-- Vessel 1 material: `u, p` are smooth on the open set `U`. -/
def StripSmooth (u : Velocity) (pr : Pressure) (U : Set Domain) : Prop :=
  ContDiffOn ℝ ∞ u U ∧ ContDiffOn ℝ ∞ pr U

/-- Vessel 2 material: the sup norm of `u(t)` exceeds every bound as `t ↑ T`.
    Stated with an existential witness point to avoid `iSup` junk values. -/
def BlowsUp (u : Velocity) (T : ℝ) : Prop :=
  ∀ M : ℝ, ∀ᶠ t in nhdsWithin T (Set.Iio T), ∃ x : Space, M < ‖u (t, x)‖

open MeasureTheory in
/-- Bounded energy on `[0, T)`.  Integrability is required explicitly: without
    it the Bochner integral of a non-`L²` field is the junk value `0`, and the
    bound would hold vacuously. -/
def EnergyBounded (u : Velocity) (T : ℝ) : Prop :=
  ∃ E : ℝ, ∀ t ∈ Set.Ico (0 : ℝ) T,
    Integrable (fun x : Space => ‖u (t, x)‖ ^ 2) ∧ ∫ x : Space, ‖u (t, x)‖ ^ 2 ≤ E

/-- Evidence pair to FOUR value: first bit is evidence for, second against. -/
def evidenceValue (hT hF : Prop) : Imscribing.Paraconsistent.Belnap := by
  classical
  exact if hT then (if hF then .B else .T) else (if hF then .F else .N)

theorem evidenceValue_B_iff (hT hF : Prop) :
    evidenceValue hT hF = .B ↔ hT ∧ hF := by
  classical
  unfold evidenceValue
  by_cases a : hT <;> by_cases b : hF <;> simp [a, b]

theorem evidenceValue_T_of (hT hF : Prop) (a : hT) (b : ¬ hF) :
    evidenceValue hT hF = .T := by
  classical
  unfold evidenceValue
  simp [a, b]

/-- The regularity question for a flow, as a native register value. -/
def regularityRegister (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) : Sixteen3 :=
  kernelSingleton (evidenceValue (StripSmooth u pr U) (BlowsUp u T))

/-- B is assembled from the two vessels: this is an iff, not a declaration. -/
theorem regularity_B_iff (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :
    evidenceValue (StripSmooth u pr U) (BlowsUp u T) = .B ↔
      StripSmooth u pr U ∧ BlowsUp u T :=
  evidenceValue_B_iff _ _

/-- A flow with both vessels has register equal to the native held value. -/
theorem regularity_register_eq_nativeHeld (u : Velocity) (pr : Pressure)
    (U : Set Domain) (T : ℝ)
    (hs : StripSmooth u pr U) (hb : BlowsUp u T) :
    regularityRegister u pr U T = nativeHeld := by
  unfold regularityRegister
  rw [(regularity_B_iff u pr U T).mpr ⟨hs, hb⟩]
  exact nativeHeld_value.symm

/-- CONTROL: the zero flow is smooth and does not blow up, so its value is T,
    not B. The register distinguishes the cases. -/
theorem zero_flow_not_blowup (U : Set Domain) (T : ℝ) : ¬ BlowsUp (fun _ => 0) T := by
  intro h
  obtain ⟨x, hx⟩ := (h 0).exists
  simp at hx

theorem zero_flow_strip_smooth (U : Set Domain) :
    StripSmooth (fun _ => 0) (fun _ => 0) U :=
  ⟨contDiffOn_const, contDiffOn_const⟩

theorem zero_flow_value_T (U : Set Domain) (T : ℝ) :
    evidenceValue (StripSmooth (fun _ => 0) (fun _ => 0) U) (BlowsUp (fun _ => 0) T) = .T :=
  evidenceValue_T_of _ _ (zero_flow_strip_smooth U) (zero_flow_not_blowup U T)

/-- The gate: both vessels, plus the two analytic bounds, give a B register AND
    a smooth force extension that agrees with the carried injection on the
    strip. Every hypothesis here is something the published profile must
    supply; this theorem is the interface, not the instantiation. -/
theorem blowup_force_extends (ν : ℝ) (u : Velocity) (pr : Pressure) (T : ℝ)
    (hstrip : IsOpen strip)
    (hs : StripSmooth u pr strip) (hb : BlowsUp u T)
    {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν u pr) core q)
    (he : ExteriorBounds (residualForce ν u pr) core) (n : ℕ) :
    regularityRegister u pr strip T = nativeHeld ∧
    ContDiff ℝ ∞ (extendedResidual ν u pr
      (hregular_of_strip ν u pr hstrip hs.1 hs.2) hc he) ∧
    ∀ z ∈ strip, extendedResidual ν u pr
      (hregular_of_strip ν u pr hstrip hs.1 hs.2) hc he z = injectionForce ν u pr n z :=
  ⟨regularity_register_eq_nativeHeld u pr strip T hs hb,
   extended_residual_smooth ν u pr _ hc he,
   fun _ hz => extended_residual_eq_injection ν u pr _ hc he n hz⟩

/-! ## C. Scale decomposition: making the tower index mean something -/

/-- A decomposition of the residual into contributions indexed by tower scale.
    `sum_eq` is the real content and must be discharged from the published
    construction (pulse seeds, shear-driven growth, internal momentum flux). -/
structure ScaleDecomposition (ν : ℝ) (u : Velocity) (pr : Pressure) where
  part : ℕ → Velocity
  sum_eq : ∀ z ∈ strip, HasSum (fun n => part n z) (residualForce ν u pr z)

/-- Each scale's contribution, carried up the tower and returned through
    collapse and cascade. -/
def scaleReturn {ν : ℝ} {u : Velocity} {pr : Pressure}
    (D : ScaleDecomposition ν u pr) (n : ℕ) : Velocity :=
  (carriedReEntry (carriedLift (Imscribing.CircumPunctum.p n, D.part n))).2

theorem scaleReturn_eq {ν : ℝ} {u : Velocity} {pr : Pressure}
    (D : ScaleDecomposition ν u pr) (n : ℕ) : scaleReturn D n = D.part n := rfl

/-- The residual is the sum of its scale returns. Per-scale returns are
    trivial (`scaleReturn_eq`); the substance is `sum_eq`. -/
theorem residual_is_sum_of_scale_returns {ν : ℝ} {u : Velocity} {pr : Pressure}
    (D : ScaleDecomposition ν u pr) {z : Domain} (hz : z ∈ strip) :
    HasSum (fun n => scaleReturn D n z) (residualForce ν u pr z) := by
  simpa [scaleReturn_eq] using D.sum_eq z hz

/-! ## D. The extension past the singular time is free -/

/-- Any smooth field vanishing on the strip can be added to a smooth extension
    without changing it on the strip. The tower's Witness is unique
    (`injection_reason`); the analytic extension is not. -/
theorem extension_not_unique (e h : Velocity)
    (he : ContDiff ℝ ∞ e) (hh : ContDiff ℝ ∞ h)
    (hvan : ∀ z ∈ strip, h z = 0) :
    ContDiff ℝ ∞ (e + h) ∧ ∀ z ∈ strip, (e + h) z = e z :=
  ⟨he.add hh, fun z hz => by simp [hvan z hz]⟩

/-! ## E. Target statement for the capstone (a Prop, not a theorem) -/

/-- Finite-time blowup with smooth compactly supported force, written against
    the actual differential residual. Time convention: interval `[0,1)`, zero
    initial datum, singular time `1`. If the published profile uses the strip
    `(-1,1)`, a time-translation lemma is needed to connect the two. -/
def NSBlowupStatement (ν : ℝ) : Prop :=
  0 < ν ∧ ∃ (f u : Velocity) (pr : Pressure),
    ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    ContDiffOn ℝ ∞ u (Set.Ico (0 : ℝ) 1 ×ˢ Set.univ) ∧
    ContDiffOn ℝ ∞ pr (Set.Ico (0 : ℝ) 1 ×ˢ Set.univ) ∧
    (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ,
        residualForce ν u pr z = f z ∧ divergence u z = 0) ∧
    (∀ x : Space, u (0, x) = 0) ∧
    EnergyBounded u 1 ∧ BlowsUp u 1

/-- What the capstone would look like once an instantiation exists: a witness
    for the statement yields a B regularity register on the open time interval.
    Conditional on the witness, as it must be. -/
theorem statement_gives_B (ν : ℝ) (h : NSBlowupStatement ν) :
    ∃ (u : Velocity) (pr : Pressure),
      regularityRegister u pr (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) 1 = nativeHeld := by
  obtain ⟨_, f, u, pr, _, _, hu, hp, _, _, _, hb⟩ := h
  refine ⟨u, pr, regularity_register_eq_nativeHeld u pr _ 1 ⟨?_, ?_⟩ hb⟩
  · exact hu.mono (Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl)
  · exact hp.mono (Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl)

end Imscribing.NSRegularityWitness
end

/-
LIKELY FRICTION (things I could not check):

  * `ContDiffOn.fderiv_of_isOpen` : name/signature drift across Mathlib versions.
    Fallback: `ContDiffOn.fderiv_of_isOpen hf hU (m := ∞) (by simp)` or use
    `contDiffOn_succ_iff_fderiv_of_isOpen`.
  * `HasFDerivAt.prodMk` vs `.prod` depending on Mathlib vintage (your existing
    files use `ContDiff.prodMk`, so `prodMk` should be right).
  * `Mathlib.MeasureTheory.Integral.Bochner.Basic` import path; replace with
    `import Mathlib` if it fails. `EnergyBounded` needs a MeasureSpace instance
    on `EuclideanSpace ℝ (Fin 3)` (should exist).
  * `strip` openness: `hregular_of_strip` takes it as a hypothesis because I
    cannot see `GenericEndpointExtension.openStrip`.
  * `Imscribing.CircumPunctum.p` : assumed to be the canonical value used as
    `p n` in NS_Reentry.
  * `Sixteen3` / `nativeHeld_value` live in `Lean` / `NSReentry`; the `open`
    lines may need adjusting after `enable_trilattice`.
  * In `zero_flow_not_blowup`, `.exists` needs `NeBot (nhdsWithin T (Iio T))`,
    which Mathlib provides for ℝ.
-/
#print axioms Imscribing.NSRegularityWitness.residualForce_contDiffOn
#print axioms Imscribing.NSRegularityWitness.regularity_register_eq_nativeHeld
#print axioms Imscribing.NSRegularityWitness.blowup_force_extends
#print axioms Imscribing.NSRegularityWitness.extension_not_unique