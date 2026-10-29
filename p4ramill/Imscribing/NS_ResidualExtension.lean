import Imscribing.NS_InjectionField
import Imscribing.PublishedNS.GenericEndpointExtension

/-!
Cancellation bounds feed an actual smooth extension of the differential
residual. The analytic inputs concern the residual on the open time strip,
not smoothness of the velocity at time one. The published profile itself is
not imported here; its cancellation and exterior estimates must instantiate
these explicit inputs. See paper (9.20), (10.9), and Lemmas 10.2--10.3.
-/

noncomputable section
namespace Imscribing.NSResidualExtension

open Imscribing.NSInjectionField Set
open scoped ContDiff

abbrev strip : Set Domain := NavierStokes.GenericEndpointExtension.openStrip

/-- All actual joint residual tensors vanish to every scale order in the core. -/
def CancellationBounds (f : Velocity) (core : Set Domain) (q : Domain → ℝ) : Prop :=
  ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ strip ∩ core,
    ‖iteratedFDeriv ℝ k f z‖ ≤ C * q z ^ N

/-- The exterior and cutoff transition regions have bounded actual jets. -/
def ExteriorBounds (f : Velocity) (core : Set Domain) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ strip \ core,
    ‖iteratedFDeriv ℝ k f z‖ ≤ C

/-- The core/exterior cover converts cancellation into the extension input. -/
theorem bounded_residual_jets {f : Velocity} {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds f core q) (he : ExteriorBounds f core) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ strip, ‖iteratedFDeriv ℝ k f z‖ ≤ C := by
  intro k
  obtain ⟨A, _, hA⟩ := hc k 0
  obtain ⟨B, hB⟩ := he k
  refine ⟨max A B, ?_⟩
  intro z hz
  by_cases hcore : z ∈ core
  · have hAz : ‖iteratedFDeriv ℝ k f z‖ ≤ A := by simpa using hA z ⟨hz, hcore⟩
    exact hAz.trans (le_max_left A B)
  · exact (hB z ⟨hz, hcore⟩).trans (le_max_right A B)

/-- The first positive cancellation order forces every actual tensor to zero. -/
theorem cancellation_jets_tendsto_zero {f : Velocity} {core : Set Domain}
    {q : Domain → ℝ} (hc : CancellationBounds f core q)
    (l : Filter Domain) (hcore : ∀ᶠ z in l, z ∈ strip ∩ core)
    (hq : Filter.Tendsto q l (nhds 0)) (k : ℕ) :
    Filter.Tendsto (iteratedFDeriv ℝ k f) l (nhds 0) := by
  obtain ⟨C, _, hC⟩ := hc k 1
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _))
  · filter_upwards [hcore] with z hz
    simpa only [pow_one] using hC z hz
  · simpa only [mul_zero] using hq.const_mul C

/-- Construct the extension using completed jets and the Taylor--Borel series. -/
def extendedResidual (ν : ℝ) (u : Velocity) (p : Pressure)
    (hregular : ContDiffOn ℝ ∞ (residualForce ν u p) strip)
    {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν u p) core q)
    (he : ExteriorBounds (residualForce ν u p) core) : Velocity :=
  NavierStokes.GenericEndpointExtension.extension (residualForce ν u p)
    hregular (bounded_residual_jets hc he)

theorem extended_residual_smooth (ν : ℝ) (u : Velocity) (p : Pressure)
    (hregular : ContDiffOn ℝ ∞ (residualForce ν u p) strip)
    {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν u p) core q)
    (he : ExteriorBounds (residualForce ν u p) core) :
    ContDiff ℝ ∞ (extendedResidual ν u p hregular hc he) :=
  NavierStokes.GenericEndpointExtension.extension_contDiff hregular
    (bounded_residual_jets hc he)

/-- The smooth force agrees with the carried injection before the singular time. -/
theorem extended_residual_eq_injection (ν : ℝ) (u : Velocity) (p : Pressure)
    (hregular : ContDiffOn ℝ ∞ (residualForce ν u p) strip)
    {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν u p) core q)
    (he : ExteriorBounds (residualForce ν u p) core)
    (n : ℕ) {z : Domain} (hz : z ∈ strip) :
    extendedResidual ν u p hregular hc he z = injectionForce ν u p n z := by
  rw [injection_eq_differential_residual]
  exact NavierStokes.GenericEndpointExtension.extension_eq hregular
    (bounded_residual_jets hc he) hz

/-- Every actual mixed derivative is preserved on the open pre-singular strip. -/
theorem extended_residual_preserves_jets (ν : ℝ) (u : Velocity) (p : Pressure)
    (hregular : ContDiffOn ℝ ∞ (residualForce ν u p) strip)
    {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν u p) core q)
    (he : ExteriorBounds (residualForce ν u p) core)
    (k : ℕ) {z : Domain} (hz : z ∈ strip) :
    iteratedFDeriv ℝ k (extendedResidual ν u p hregular hc he) z =
      iteratedFDeriv ℝ k (residualForce ν u p) z :=
  NavierStokes.GenericEndpointExtension.extension_iteratedFDeriv hregular
    (bounded_residual_jets hc he) k hz

/-- Spatial fibers outside the original support stay zero after extension. -/
theorem extended_residual_zero_fiber (ν : ℝ) (u : Velocity) (p : Pressure)
    (hregular : ContDiffOn ℝ ∞ (residualForce ν u p) strip)
    {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν u p) core q)
    (he : ExteriorBounds (residualForce ν u p) core)
    {x : Space} (hx : ∀ t ∈ Ioo (-1 : ℝ) 1, residualForce ν u p (t, x) = 0)
    (t : ℝ) : extendedResidual ν u p hregular hc he (t, x) = 0 :=
  NavierStokes.GenericEndpointExtension.extension_zero_of_fiber hregular
    (bounded_residual_jets hc he) hx t

/-- The construction has a fixed compact time-support bound. -/
theorem extended_residual_zero_time (ν : ℝ) (u : Velocity) (p : Pressure)
    (hregular : ContDiffOn ℝ ∞ (residualForce ν u p) strip)
    {core : Set Domain} {q : Domain → ℝ}
    (hc : CancellationBounds (residualForce ν u p) core q)
    (he : ExteriorBounds (residualForce ν u p) core)
    {t : ℝ} (ht : 2 ≤ |t|) (x : Space) :
    extendedResidual ν u p hregular hc he (t, x) = 0 :=
  NavierStokes.GenericEndpointExtension.extension_zero_parameter hregular
    (bounded_residual_jets hc he) ht x

theorem zero_cancellation (core : Set Domain) (q : Domain → ℝ) :
    CancellationBounds (fun _ => 0) core q := by
  intro k N
  refine ⟨0, le_rfl, ?_⟩
  intro z _
  simp [iteratedFDeriv_zero_fun]

theorem zero_exterior (core : Set Domain) : ExteriorBounds (fun _ => 0) core := by
  intro k
  refine ⟨0, ?_⟩
  intro z _
  simp [iteratedFDeriv_zero_fun]

/-- The extension construction itself maps the zero residual to zero everywhere. -/
theorem zero_extension_control (z : Domain) :
    NavierStokes.GenericEndpointExtension.extension (fun _ : Domain => (0 : Space))
      contDiffOn_const (bounded_residual_jets (zero_cancellation ∅ (fun _ => 0))
        (zero_exterior ∅)) z = 0 :=
  NavierStokes.GenericEndpointExtension.extension_zero_of_fiber contDiffOn_const
    (bounded_residual_jets (zero_cancellation ∅ (fun _ => 0)) (zero_exterior ∅))
    (fun _ _ => rfl) z.1

/-- Nonzero controls have bounded genuine tensors as well. -/
theorem constant_jets_bounded (v : Space) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ strip,
      ‖iteratedFDeriv ℝ k (fun _ : Domain => v) z‖ ≤ C := by
  intro k
  refine ⟨‖v‖, ?_⟩
  intro z _
  by_cases hk : k = 0
  · subst k
    simp only [norm_iteratedFDeriv_zero, le_refl]
  · simp only [iteratedFDeriv_const_of_ne hk, Pi.zero_apply, norm_zero]
    exact norm_nonneg v

/-- The constructed extension retains a nonzero force on the preterminal strip. -/
theorem nonzero_extension_control (v : Space) (hv : v ≠ 0)
    {z : Domain} (hz : z ∈ strip) :
    NavierStokes.GenericEndpointExtension.extension (fun _ : Domain => v)
      contDiffOn_const (constant_jets_bounded v) z ≠ 0 := by
  rw [NavierStokes.GenericEndpointExtension.extension_eq contDiffOn_const
    (constant_jets_bounded v) hz]
  exact hv

end Imscribing.NSResidualExtension
