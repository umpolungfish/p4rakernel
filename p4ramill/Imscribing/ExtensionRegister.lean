import Imscribing.NS_InjectionField
import Imscribing.NS_RegularityWitness
import Imscribing.NS_ResidualExtension
import Imscribing.FalsifierRegister
import Imscribing.CheapB_Control

/-!
# ExtensionRegister

STATUS: written against your uploaded files + the compiled CheapB_Control.
NOT compiled. No `sorry`. See LIKELY FRICTION at the bottom.

## Idea

`regularityRegister` returned B for the shear flow (CheapB_Control), so its B
carried no information about the analytic content. Here B additionally
requires that the residual's jets are bounded on the open set `U`:

    B  ⇔  smooth on U  ∧  blows up at T  ∧  residual jets bounded on U

Why this is the right extra conjunct, not an arbitrary one:

  (N) NECESSITY.  If the residual agrees on `U` with a smooth compactly
      supported force (what the Millennium statement requires), then its jets
      are bounded on `U`.   [`jetsBoundedOn_of_compactSupport`]
      So any genuine witness lands in B.   [`statement_gives_extB`]

  (S) SUFFICIENCY FOR THE EXTENSION.  Smooth + bounded jets gives a smooth
      extension of the residual (the Taylor–Borel construction already in
      `NS_ResidualExtension`).   [`extB_force_extends`]

  (D) DISCRIMINATION.  The shear (old register: B) now lands in T.
      [`shear_old_B_new_T`]

What this does NOT do: it does not make B inhabited. A flow in the new B cell
is a finite-time-blowup mechanism with smooth-extendable force, i.e. the open
problem. Nonemptiness of this cell is what the published profile has to supply.
(S) is also not the full statement: compact support in space/time and
gluing at t = 0 are separate obligations (flagged in NSBlowupStatement).
-/

noncomputable section
namespace Imscribing.ExtensionRegister

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Imscribing.FalsifierRegister
open Imscribing.CheapB
open Set
open scoped ContDiff

/-! ## Definitions -/

/-- All jets of `f` are bounded on `U`. -/
def JetsBoundedOn (U : Set Domain) (f : Velocity) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ U, ‖iteratedFDeriv ℝ k f z‖ ≤ C

/-- Blowup together with a residual that stays jet-bounded up to the singular time. -/
def ExtBlowsUp (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) : Prop :=
  BlowsUp u T ∧ JetsBoundedOn U (residualForce ν u pr)

/-- The extension-aware regularity register. -/
def extRegister (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :=
  kernelSingleton (evidenceValue (StripSmooth u pr U) (ExtBlowsUp ν u pr U T))

theorem extRegister_B_iff (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :
    evidenceValue (StripSmooth u pr U) (ExtBlowsUp ν u pr U T) = .B ↔
      StripSmooth u pr U ∧ ExtBlowsUp ν u pr U T :=
  evidenceValue_B_iff _ _

theorem extRegister_eq_nativeHeld (ν : ℝ) (u : Velocity) (pr : Pressure)
    (U : Set Domain) (T : ℝ)
    (hs : StripSmooth u pr U) (hb : ExtBlowsUp ν u pr U T) :
    extRegister ν u pr U T = nativeHeld := by
  unfold extRegister
  rw [(extRegister_B_iff ν u pr U T).mpr ⟨hs, hb⟩]
  exact nativeHeld_value.symm

/-- T and the native held value are different cells. -/
theorem T_ne_nativeHeld : kernelSingleton .T ≠ nativeHeld := by
  rw [nativeHeld_value]
  first
  | decide
  | (intro h
     have := congrArg Sixteen3.hasB h
     simpa [kernelSingleton, Sixteen3.ofBelnap] using this)

/-! ## (N) Necessity: a smooth compactly supported force bounds the jets -/

theorem jetsBoundedOn_of_compactSupport {U : Set Domain} (hU : IsOpen U)
    {f : Velocity} (F : Velocity) (hF : ContDiff ℝ ∞ F) (hcs : HasCompactSupport F)
    (heq : ∀ z ∈ U, f z = F z) : JetsBoundedOn U f := by
  unfold JetsBoundedOn
  intro k
  have hcont : Continuous (iteratedFDeriv ℝ k F) :=
    hF.continuous_iteratedFDeriv (by first | simp | exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hcs.iteratedFDeriv k)
  refine ⟨C, fun z hz => ?_⟩
  have hev : f =ᶠ[nhds z] F :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun w hw => heq w hw)
  rw [(hev.iteratedFDeriv ℝ k).self_of_nhds]
  exact hC z

/-- Every genuine witness of the blowup statement lands in the new B cell
    (on the open interval (0,1), where the statement's equation holds). -/
theorem statement_gives_extB (ν : ℝ) (h : NSBlowupStatement ν) :
    ∃ (u : Velocity) (pr : Pressure),
      extRegister ν u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) 1 = nativeHeld := by
  obtain ⟨_, f, u, pr, hf, hfc, hu, hp, hNS, _, _, hb⟩ := h
  have hU : IsOpen (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hsm : StripSmooth u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    ⟨hu.mono (Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl),
     hp.mono (Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl)⟩
  have hj : JetsBoundedOn (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) (residualForce ν u pr) :=
    jetsBoundedOn_of_compactSupport hU f hf hfc (fun z hz => (hNS z hz).1)
  exact ⟨u, pr, extRegister_eq_nativeHeld ν u pr _ 1 hsm ⟨hb, hj⟩⟩

/-! ## (S) Sufficiency for the smooth extension -/

theorem extB_force_extends (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hs : StripSmooth u pr strip)
    (hj : JetsBoundedOn strip (residualForce ν u pr)) :
    ∃ F : Velocity, ContDiff ℝ ∞ F ∧ ∀ z ∈ strip, F z = residualForce ν u pr z := by
  have hreg : ContDiffOn ℝ ∞ (residualForce ν u pr) strip :=
    hregular_of_strip_unconditional ν u pr hs.1 hs.2
  exact ⟨NavierStokes.GenericEndpointExtension.extension (residualForce ν u pr) hreg hj,
    NavierStokes.GenericEndpointExtension.extension_contDiff hreg hj,
    fun z hz => NavierStokes.GenericEndpointExtension.extension_eq hreg hj hz⟩

/-! ## (D) The shear no longer registers as B -/

/-- The shear's p = 0 residual has unbounded jets on any `U` containing (0,1)×ℝ³. -/
theorem shear_jets_unbounded_on {U : Set Domain}
    (hU : Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space) ⊆ U) (ν : ℝ) :
    ¬ JetsBoundedOn U (residualForce ν shear (fun _ => 0)) := by
  intro h
  unfold JetsBoundedOn at h
  obtain ⟨C, hC⟩ := h 0
  have hs2 : (2 : ℝ) ≤ |C| + 2 := by linarith [abs_nonneg C]
  set s : ℝ := |C| + 2 with hs
  have hspos : 0 < s := by linarith
  have hsinv : s⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hs2
  have hsinvpos : 0 < s⁻¹ := inv_pos.mpr hspos
  set t : ℝ := 1 - s⁻¹ with ht
  set x : Space := EuclideanSpace.single (1 : Fin 3) (1 : ℝ) with hx
  have hz0 : ((t, x) : Domain) ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space) :=
    ⟨⟨by rw [ht]; linarith, by rw [ht]; linarith⟩, mem_univ _⟩
  have hz : ((t, x) : Domain) ∈ U := hU hz0
  have hne : ((t, x) : Domain).1 ≠ 1 := by
    show t ≠ 1
    intro h1
    rw [ht] at h1
    linarith
  have h1t : 1 - t = s⁻¹ := by rw [ht]; ring
  have hval := hC _ hz
  rw [norm_iteratedFDeriv_zero, shear_residual ν _ hne] at hval
  have hnorm : ‖(((1 - t) ^ 2)⁻¹ * x 1) • basisVector 0‖ = s ^ 2 := by
    rw [h1t, norm_smul, basisVector, EuclideanSpace.norm_single, norm_one, mul_one]
    simp [hx, inv_pow]
  have hbig : C < s ^ 2 := by nlinarith [le_abs_self C, hs2]
  have hval' : s ^ 2 ≤ C := by
    have := hval
    simp only at this
    rwa [hnorm] at this
  linarith

theorem shear_extRegister_T (ν : ℝ) {U : Set Domain}
    (hU : Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space) ⊆ U)
    (hsm : StripSmooth shear (fun _ => 0) U) :
    extRegister ν shear (fun _ => 0) U 1 = kernelSingleton .T := by
  unfold extRegister
  rw [evidenceValue_T_of _ _ hsm (fun h => shear_jets_unbounded_on hU ν h.2)]

theorem shear_extRegister_T_strip (ν : ℝ) :
    extRegister ν shear (fun _ => 0) strip 1 = kernelSingleton .T :=
  shear_extRegister_T ν
    (Set.prod_mono (Set.Ioo_subset_Ioo (by norm_num) le_rfl) subset_rfl)
    ⟨shear_contDiffOn, contDiffOn_const⟩

/-- Same flow, two registers: the old one says B, the new one says T (≠ B). -/
theorem shear_old_B_new_T (ν : ℝ) :
    regularityRegister shear (fun _ => 0) strip 1 = nativeHeld ∧
    extRegister ν shear (fun _ => 0) strip 1 = kernelSingleton .T ∧
    extRegister ν shear (fun _ => 0) strip 1 ≠ nativeHeld :=
  ⟨shear_register_B, shear_extRegister_T_strip ν,
    by rw [shear_extRegister_T_strip ν]; exact T_ne_nativeHeld⟩

/-! ## Earlier controls still land outside B -/

theorem zero_flow_extRegister_T (ν : ℝ) :
    extRegister ν (fun _ : Domain => (0 : Space)) (fun _ : Domain => (0 : ℝ)) strip 1 =
      kernelSingleton .T := by
  unfold extRegister
  rw [evidenceValue_T_of _ _ (zero_flow_strip_smooth strip)
    (fun h => zero_flow_not_blowup strip 1 h.1)]

theorem time_linear_extRegister_T (ν : ℝ) (v : Space) :
    extRegister ν (timeLinearVelocity v) (fun _ : Domain => (0 : ℝ)) strip 1 =
      kernelSingleton .T := by
  unfold extRegister
  rw [evidenceValue_T_of _ _
    ⟨(timeLinearVelocity_contDiff v).contDiffOn, contDiffOn_const⟩
    (fun h => timeLinearVelocity_not_blowsUp v h.1)]

end Imscribing.ExtensionRegister
end

/-
LIKELY FRICTION (could not check):

  * `jetsBoundedOn_of_compactSupport`:
      - `ContDiff.continuous_iteratedFDeriv` argument order / the `m ≤ ∞` side goal
        (`(k : WithTop ℕ∞) ≤ ∞`); I try `simp` then `exact_mod_cast le_top`.
      - `Filter.EventuallyEq.iteratedFDeriv` explicit-𝕜 signature; if `hev.iteratedFDeriv ℝ k`
        fails, try `Filter.EventuallyEq.iteratedFDeriv ℝ hev k`.
      - `HasCompactSupport.iteratedFDeriv`, `Continuous.bounded_above_of_compact_support`
        should exist under those names.
  * `T_ne_nativeHeld`: `decide` needs `DecidableEq Sixteen3`; the fallback uses `Sixteen3.hasB`.
  * `extB_force_extends`: `extension`/`extension_contDiff`/`extension_eq` implicit-argument
    shapes copied from NS_ResidualExtension, where they compiled; `hj` is passed as the
    unfolded `∀ k, ∃ C, ∀ z ∈ strip, ...` (defeq to JetsBoundedOn strip).
  * `shear_jets_unbounded_on` is the compiled CheapB proof with `strip` replaced by
    an arbitrary `U ⊇ (0,1)×ℝ³`; the only new step is `0 < t` instead of `-1 < t`.
-/
#print axioms Imscribing.ExtensionRegister.shear_old_B_new_T
#print axioms Imscribing.ExtensionRegister.statement_gives_extB
#print axioms Imscribing.ExtensionRegister.extB_force_extends
