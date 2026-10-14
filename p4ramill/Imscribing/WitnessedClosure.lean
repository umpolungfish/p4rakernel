import Imscribing.ExtensionRegister
import Imscribing.CancellationNecessity

/-!
# WitnessedClosure

Builds on `NS_KernelReentry`, `NS_RegularityWitness` and `ExtensionRegister`.
The existing registers (`regularityRegister`, `extRegister`) are unchanged;
everything here is added alongside them under new names.

Status: builds. The audited theorems depend on `propext`, `Classical.choice`,
`Quot.sound` only.

## Contents

 1. Closure and evidence. `heldClosure` fixes a register exactly when it has the
    B member. For a register of the form `kernelSingleton (evidenceValue a b)`
    this is equivalent to `a ∧ b`. When the register is computed from the field
    and carried through the tower, the round trip returns it unchanged exactly
    when the evidence holds.
        [`closure_fixed_iff_evidence`, `fieldReturn_fixed_iff`, `*_closure_moves`]

 2. `FullBlowsUp`, an optional refinement of the blowup vessel: local blowup,
    bounded energy, bounded jets, uniform spatial support, divergence-free, rest
    at t = 0. A witness of `NSBlowupStatementLoc` (the statement with `LocalBlowsUp`
    in place of `BlowsUp`) lies in it. The converse is conditional on an explicit
    extension input, `CellExtension`.
        [`statementLoc_gives_fullB`, `statement_of_cell`]

 3. Controls under the refined register: the zero, time-linear and shear flows.

 4. Tower index. `injectionForce` does not depend on the scale index `n`
    (`injection_scale_independent`). `singleScaleDecomposition` is an instance of
    `ScaleDecomposition`. `LocalizedDecomposition` adds a localization predicate
    and a spread condition, which that instance does not satisfy.

Not covered here: inhabiting the cell, and relating `strip` to `(0,1) × ℝ³`
(see `NativeDomainCancellation`).
-/

noncomputable section
namespace Imscribing.WitnessedClosure

open Imscribing.NSInjectionField
open Imscribing.NSRegularityWitness
open Imscribing.NSResidualExtension
open Imscribing.NSReentry
open Imscribing.FalsifierRegister
open Imscribing.CheapB
open Imscribing.ExtensionRegister
open Imscribing.CancellationNecessity
open Lean
open Set
open scoped ContDiff

/-! ## 1. Closure fixedness is the witness test -/

theorem kernelSingleton_hasB_iff (v : Imscribing.Paraconsistent.Belnap) :
    (kernelSingleton v).hasB = true ↔ v = .B := by
  cases v <;>
    first
    | decide
    | simp [kernelSingleton, Sixteen3.ofBelnap]
    | (constructor <;> intro h <;> first | rfl | cases h)

/-- The whole point: for ANY pair of evidence Props, the held closure fixes the
    register exactly when both evidence Props hold. -/
theorem closure_fixed_iff_evidence (a b : Prop) :
    heldClosure (kernelSingleton (evidenceValue a b)) =
      kernelSingleton (evidenceValue a b) ↔ a ∧ b := by
  rw [heldClosure_fixed_iff, kernelSingleton_hasB_iff, evidenceValue_B_iff]

theorem closure_moves_of_not (a b : Prop) (h : ¬ (a ∧ b)) :
    heldClosure (kernelSingleton (evidenceValue a b)) ≠
      kernelSingleton (evidenceValue a b) :=
  fun hfix => h ((closure_fixed_iff_evidence a b).mp hfix)

theorem T_register_not_closed :
    heldClosure (kernelSingleton .T) ≠ kernelSingleton .T := by
  intro h
  have hb := (heldClosure_fixed_iff _).mp h
  have := (kernelSingleton_hasB_iff .T).mp hb
  cases this

/-! ## 2. The full cell -/

/-- The residual vanishes outside a fixed spatial ball, uniformly on `U`. -/
def UniformSpatialSupport (U : Set Domain) (f : Velocity) : Prop :=
  ∃ R : ℝ, ∀ z ∈ U, R < ‖z.2‖ → f z = 0

/-- Everything the blowup statement asks of a flow, other than smoothness. -/
structure FullBlowsUp (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :
    Prop where
  blow    : LocalBlowsUp u T
  energy  : EnergyBounded u T
  jets    : JetsBoundedOn U (residualForce ν u pr)
  support : UniformSpatialSupport U (residualForce ν u pr)
  div     : ∀ z ∈ U, divergence u z = 0
  rest    : ∀ x : Space, u (0, x) = 0

def fullRegister (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :
    Sixteen3 :=
  kernelSingleton (evidenceValue (StripSmooth u pr U) (FullBlowsUp ν u pr U T))

theorem fullRegister_B_iff (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ) :
    evidenceValue (StripSmooth u pr U) (FullBlowsUp ν u pr U T) = .B ↔
      StripSmooth u pr U ∧ FullBlowsUp ν u pr U T :=
  evidenceValue_B_iff _ _

theorem fullRegister_eq_nativeHeld (ν : ℝ) (u : Velocity) (pr : Pressure)
    (U : Set Domain) (T : ℝ) (hs : StripSmooth u pr U) (hb : FullBlowsUp ν u pr U T) :
    fullRegister ν u pr U T = nativeHeld := by
  unfold fullRegister
  rw [(fullRegister_B_iff ν u pr U T).mpr ⟨hs, hb⟩]
  exact nativeHeld_value.symm

theorem fullRegister_fixed_iff (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain)
    (T : ℝ) :
    heldClosure (fullRegister ν u pr U T) = fullRegister ν u pr U T ↔
      StripSmooth u pr U ∧ FullBlowsUp ν u pr U T := by
  unfold fullRegister
  exact closure_fixed_iff_evidence _ _

/-! ### Field-dependent round trip through the tower -/

/-- The overflow at scale `n+1`, carrying the residual FIELD together with the
    register COMPUTED FROM that field. -/
def fieldOverflow (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain) (T : ℝ)
    (n : ℕ) : RegisteredScale Velocity (n + 1) :=
  (momentumTerms ν u pr).registeredOverflow n (fullRegister ν u pr U T)

theorem fieldReturn_field (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain)
    (T : ℝ) (n : ℕ) :
    (registeredReEntry (fieldOverflow ν u pr U T n)).2.1 = residualForce ν u pr := rfl

theorem fieldReturn_register (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain)
    (T : ℝ) (n : ℕ) :
    (registeredReEntry (fieldOverflow ν u pr U T n)).2.2 =
      heldClosure (fullRegister ν u pr U T) := rfl

/-- The tower returns the register unchanged exactly when the field is a
    witness. For non-witnesses the return changes the register. -/
theorem fieldReturn_fixed_iff (ν : ℝ) (u : Velocity) (pr : Pressure) (U : Set Domain)
    (T : ℝ) (n : ℕ) :
    (registeredReEntry (fieldOverflow ν u pr U T n)).2.2 = fullRegister ν u pr U T ↔
      StripSmooth u pr U ∧ FullBlowsUp ν u pr U T := by
  rw [fieldReturn_register]
  exact fullRegister_fixed_iff ν u pr U T

/-! ### Necessity: the statement lands in the full cell -/

/-- The statement with local blowup (the statement as written uses `BlowsUp`,
    which `drift` satisfies without any singularity). -/
def NSBlowupStatementLoc (ν : ℝ) : Prop :=
  0 < ν ∧ ∃ (f u : Velocity) (pr : Pressure),
    ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    ContDiffOn ℝ ∞ u (Set.Ico (0 : ℝ) 1 ×ˢ Set.univ) ∧
    ContDiffOn ℝ ∞ pr (Set.Ico (0 : ℝ) 1 ×ˢ Set.univ) ∧
    (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ,
        residualForce ν u pr z = f z ∧ divergence u z = 0) ∧
    (∀ x : Space, u (0, x) = 0) ∧
    EnergyBounded u 1 ∧ LocalBlowsUp u 1

theorem statementLoc_implies_statement (ν : ℝ) (h : NSBlowupStatementLoc ν) :
    NSBlowupStatement ν := by
  obtain ⟨hν, f, u, pr, a, b, c, d, e, g, h1, hb⟩ := h
  exact ⟨hν, f, u, pr, a, b, c, d, e, g, h1, hb.blowsUp⟩

theorem spatialSupport_of_compactSupport {U : Set Domain} {F : Velocity}
    (hcs : HasCompactSupport F) {f : Velocity} (heq : ∀ z ∈ U, f z = F z) :
    UniformSpatialSupport U f := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hcs.isCompact.isBounded
  refine ⟨R, fun z hz hzR => ?_⟩
  rw [heq z hz]
  by_contra hne
  have hmem : z ∈ tsupport F := subset_tsupport _ hne
  have h1 : ‖z‖ ≤ R := hR z hmem
  have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  linarith

theorem statementLoc_gives_fullB (ν : ℝ) (h : NSBlowupStatementLoc ν) :
    ∃ (u : Velocity) (pr : Pressure),
      StripSmooth u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) ∧
      FullBlowsUp ν u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) 1 ∧
      fullRegister ν u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) 1 = nativeHeld := by
  obtain ⟨_, f, u, pr, hf, hfc, hu, hp, hNS, hrest, hen, hb⟩ := h
  have hU : IsOpen (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hsm : StripSmooth u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    ⟨hu.mono (Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl),
     hp.mono (Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl)⟩
  have hfull : FullBlowsUp ν u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) 1 :=
    { blow := hb
      energy := hen
      jets := jetsBoundedOn_of_compactSupport hU f hf hfc (fun z hz => (hNS z hz).1)
      support := spatialSupport_of_compactSupport hfc (fun z hz => (hNS z hz).1)
      div := fun z hz => (hNS z hz).2
      rest := hrest }
  exact ⟨u, pr, hsm, hfull, fullRegister_eq_nativeHeld ν u pr _ 1 hsm hfull⟩

/-! ### Converse, conditional on the extension input -/

/-- The obligation the cell does NOT discharge by itself: a smooth compactly
    supported force agreeing with the residual on (0,1)×ℝ³. (Taylor-Borel in
    space-time with compact time support; `extB_force_extends` gives smoothness
    on the (-1,1) strip but not compact support.) -/
def CellExtension (ν : ℝ) (u : Velocity) (pr : Pressure) : Prop :=
  ∃ F : Velocity, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
    ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space), F z = residualForce ν u pr z

theorem statement_of_cell (ν : ℝ) (hν : 0 < ν) (u : Velocity) (pr : Pressure)
    (hu0 : ContDiffOn ℝ ∞ u (Set.Ico (0 : ℝ) 1 ×ˢ Set.univ))
    (hp0 : ContDiffOn ℝ ∞ pr (Set.Ico (0 : ℝ) 1 ×ˢ Set.univ))
    (hcell : FullBlowsUp ν u pr (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) 1)
    (hext : CellExtension ν u pr) : NSBlowupStatementLoc ν := by
  obtain ⟨F, hF, hFc, hFeq⟩ := hext
  exact ⟨hν, F, u, pr, hF, hFc, hu0, hp0,
    fun z hz => ⟨(hFeq z hz).symm, hcell.div z hz⟩, hcell.rest, hcell.energy, hcell.blow⟩

/-! ### Cancellation is forced inside the full cell -/

theorem fullB_cancellation (ν : ℝ) (u : Velocity) (pr : Pressure)
    (hs : StripSmooth u pr strip) (hF : FullBlowsUp ν u pr strip 1) :
    (¬ ∃ C : ℝ, ∀ z ∈ strip, 0 ≤ z.1 → ‖timeDerivative u z‖ ≤ C) ∧
    (¬ ∃ C : ℝ, ∀ z ∈ strip, 0 ≤ z.1 →
      ‖transport u z + (-ν) • spatialLaplacian u z + pressureGradient pr z‖ ≤ C) :=
  extB_cancellation_necessary ν u pr hs.1 hF.rest hF.blow.blowsUp hF.jets

/-! ## 3. Controls: each lands in T, and the closure changes the register -/

theorem zero_fullRegister_T (ν : ℝ) :
    fullRegister ν (fun _ : Domain => (0 : Space)) (fun _ : Domain => (0 : ℝ)) strip 1 =
      kernelSingleton .T := by
  unfold fullRegister
  rw [evidenceValue_T_of _ _ (zero_flow_strip_smooth strip)
    (fun h => zero_flow_not_blowup strip 1 h.blow.blowsUp)]

theorem time_linear_fullRegister_T (ν : ℝ) (v : Space) :
    fullRegister ν (timeLinearVelocity v) (fun _ : Domain => (0 : ℝ)) strip 1 =
      kernelSingleton .T := by
  unfold fullRegister
  rw [evidenceValue_T_of _ _
    ⟨(timeLinearVelocity_contDiff v).contDiffOn, contDiffOn_const⟩
    (fun h => timeLinearVelocity_not_blowsUp v h.blow.blowsUp)]

theorem shear_fullRegister_T (ν : ℝ) :
    fullRegister ν shear (fun _ => (0 : ℝ)) strip 1 = kernelSingleton .T := by
  unfold fullRegister
  rw [evidenceValue_T_of _ _ ⟨shear_contDiffOn, contDiffOn_const⟩
    (fun h => shear_jets_unbounded_on
      (Set.prod_mono (Set.Ioo_subset_Ioo (by norm_num) le_rfl) subset_rfl) ν h.jets)]

theorem zero_closure_moves (ν : ℝ) :
    heldClosure (fullRegister ν (fun _ : Domain => (0 : Space))
      (fun _ : Domain => (0 : ℝ)) strip 1) ≠
    fullRegister ν (fun _ : Domain => (0 : Space)) (fun _ : Domain => (0 : ℝ)) strip 1 := by
  rw [zero_fullRegister_T]; exact T_register_not_closed

theorem time_linear_closure_moves (ν : ℝ) (v : Space) :
    heldClosure (fullRegister ν (timeLinearVelocity v) (fun _ : Domain => (0 : ℝ))
      strip 1) ≠
    fullRegister ν (timeLinearVelocity v) (fun _ : Domain => (0 : ℝ)) strip 1 := by
  rw [time_linear_fullRegister_T]; exact T_register_not_closed

theorem shear_closure_moves (ν : ℝ) :
    heldClosure (fullRegister ν shear (fun _ => (0 : ℝ)) strip 1) ≠
    fullRegister ν shear (fun _ => (0 : ℝ)) strip 1 := by
  rw [shear_fullRegister_T]; exact T_register_not_closed

/-- For comparison: the shear is B under `regularityRegister`, so its closure fixes it. -/
theorem shear_regularityRegister_closed :
    heldClosure (regularityRegister shear (fun _ => (0 : ℝ)) strip 1) =
      regularityRegister shear (fun _ => (0 : ℝ)) strip 1 := by
  rw [shear_register_B]; exact nativeHeld_fixed

/-! ## 4. The tower index -/

/-- `injectionForce` does not depend on the scale index `n`. -/
theorem injection_scale_independent (ν : ℝ) (u : Velocity) (pr : Pressure) (m n : ℕ) :
    injectionForce ν u pr m = injectionForce ν u pr n := by
  rw [injection_eq_differential_residual, injection_eq_differential_residual]

/-- A `ScaleDecomposition` with all of the residual at scale 0. -/
def singleScaleDecomposition (ν : ℝ) (u : Velocity) (pr : Pressure) :
    ScaleDecomposition ν u pr where
  part n := if n = 0 then residualForce ν u pr else 0
  sum_eq z _ := by
    have h : (fun n : ℕ => (if n = 0 then residualForce ν u pr else (0 : Velocity)) z) =
        fun n : ℕ => if n = 0 then residualForce ν u pr z else 0 := by
      funext n
      by_cases hn : n = 0 <;> simp [hn]
    rw [h]
    exact hasSum_ite_eq 0 _

/-- A decomposition whose parts obey a scale localization predicate `Loc n`, with
    at least two distinct scales active. -/
structure LocalizedDecomposition (Loc : ℕ → Velocity → Prop)
    (ν : ℝ) (u : Velocity) (pr : Pressure) extends ScaleDecomposition ν u pr where
  localized : ∀ n, Loc n (part n)
  spread : ∃ m n : ℕ, m ≠ n ∧ part m ≠ 0 ∧ part n ≠ 0

theorem singleScaleDecomposition_not_spread (ν : ℝ) (u : Velocity) (pr : Pressure) :
    ¬ ∃ m n : ℕ, m ≠ n ∧ (singleScaleDecomposition ν u pr).part m ≠ 0 ∧
      (singleScaleDecomposition ν u pr).part n ≠ 0 := by
  rintro ⟨m, n, hmn, hm, hn⟩
  have h0 : ∀ k : ℕ, (singleScaleDecomposition ν u pr).part k ≠ 0 → k = 0 := by
    intro k hk
    by_contra hk0
    exact hk (by simp [singleScaleDecomposition, hk0])
  exact hmn (by rw [h0 m hm, h0 n hn])

/-- The one-scale decomposition is not the underlying decomposition of any
    `LocalizedDecomposition`. -/
theorem singleScaleDecomposition_not_localizable (Loc : ℕ → Velocity → Prop)
    (ν : ℝ) (u : Velocity) (pr : Pressure)
    (D : LocalizedDecomposition Loc ν u pr) :
    D.toScaleDecomposition ≠ singleScaleDecomposition ν u pr := by
  intro h
  obtain ⟨m, n, hmn, hm, hn⟩ := D.spread
  apply singleScaleDecomposition_not_spread ν u pr
  refine ⟨m, n, hmn, ?_, ?_⟩
  · rw [← h]; exact hm
  · rw [← h]; exact hn

end Imscribing.WitnessedClosure
end

#print axioms Imscribing.WitnessedClosure.closure_fixed_iff_evidence
#print axioms Imscribing.WitnessedClosure.fieldReturn_fixed_iff
#print axioms Imscribing.WitnessedClosure.statementLoc_gives_fullB
#print axioms Imscribing.WitnessedClosure.statement_of_cell
#print axioms Imscribing.WitnessedClosure.shear_closure_moves
#print axioms Imscribing.WitnessedClosure.singleScaleDecomposition_not_localizable
