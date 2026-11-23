/-
  Step 3 of the unconditional-closure blueprint: joint density of plaquette
  defects under product Haar measure.  Lattice scaffolding.
-/
import Mathlib
import Imscribing.YangMills.PlaquetteStep2

set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal Matrix
open MeasureTheory Matrix Filter

noncomputable section
namespace YangMills

structure LatticeSetup (d L_t : ℕ) [NeZero d] [NeZero L_t] where
  Site : Type*
  [fintypeSite : Fintype Site]
  [decEqSite : DecidableEq Site]
  hd : 2 ≤ d
  hLt : 0 < L_t
  tCoord : Site → Fin L_t
  stepSite : Site → Fin d → Site
  step0_inj : Function.Injective (fun v => stepSite v ⟨0, by omega⟩)
  tCoord_step0 : ∀ v, tCoord (stepSite v ⟨0, by omega⟩) = tCoord v + 1

attribute [instance] LatticeSetup.fintypeSite LatticeSetup.decEqSite

variable {d L_t : ℕ} [NeZero d] [NeZero L_t]

abbrev LatLink [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) := lat.Site × Fin d

variable {N : ℕ}

variable (suHaar : Measure (specialUnitaryGroup (Fin N) ℂ))
  [IsProbabilityMeasure suHaar] [suHaar.IsMulLeftInvariant] [suHaar.IsMulRightInvariant]


noncomputable def plaquetteObs [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) (N : ℕ) (v : lat.Site)
    (U : LatLink lat → specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  let dir0 : Fin d := ⟨0, by have := lat.hd; omega⟩
  let dir1 : Fin d := ⟨1, by have := lat.hd; omega⟩
  f0 N (U (v, dir0) * U (lat.stepSite v dir0, dir1) *
    (U (lat.stepSite v dir1, dir0))⁻¹ * (U (v, dir1))⁻¹)

lemma plaquetteObs_measurable [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) (N : ℕ) (v : lat.Site) :
    Measurable (plaquetteObs lat N v) := by
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := by
    change SecondCountableTopology (Fin N → Fin N → ℂ)
    infer_instance
  letI : SecondCountableTopology (specialUnitaryGroup (Fin N) ℂ) :=
    TopologicalSpace.secondCountableTopology_induced (specialUnitaryGroup (Fin N) ℂ)
      (Matrix (Fin N) (Fin N) ℂ) (fun A => (A : Matrix (Fin N) (Fin N) ℂ))
  unfold plaquetteObs
  refine (f0_continuous N).measurable.comp ?_
  have heval : ∀ e : LatLink lat,
      Measurable (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ => U e) :=
    fun e => measurable_pi_apply e
  exact ((((heval _).mul (heval _)).mul (heval _).inv).mul (heval _).inv)

noncomputable def haarConfigMeasure [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) : Measure (LatLink lat → specialUnitaryGroup (Fin N) ℂ) :=
  Measure.pi (fun _ => suHaar)

instance [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) : IsProbabilityMeasure (haarConfigMeasure suHaar lat) := by
  unfold haarConfigMeasure
  infer_instance

noncomputable def splitLinkEquiv [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) (e : LatLink lat) :
    (LatLink lat → specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
        specialUnitaryGroup (Fin N) ℂ := by
  let p : LatLink lat → Prop := fun l => l ≠ e
  let e1 := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : LatLink lat => specialUnitaryGroup (Fin N) ℂ) p
  haveI : Unique {l : LatLink lat // ¬ p l} :=
    ⟨⟨⟨e, not_not.mpr rfl⟩⟩, fun ⟨l, hl⟩ => Subtype.ext (not_not.mp hl)⟩
  let e2 : ({l : LatLink lat // ¬ p l} → specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      specialUnitaryGroup (Fin N) ℂ :=
    MeasurableEquiv.piUnique (fun _ : {l : LatLink lat // ¬ p l} =>
      specialUnitaryGroup (Fin N) ℂ)
  exact e1.trans ((MeasurableEquiv.refl _).prodCongr e2)

lemma splitLinkEquiv_measurePreserving [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) (e : LatLink lat) :
    MeasurePreserving
      (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
        (fun l : {l : LatLink lat // l ≠ e} => U l.1, U e))
      (haarConfigMeasure suHaar lat)
      ((Measure.pi (fun _ : {l : LatLink lat // l ≠ e} => suHaar)).prod suHaar) := by
  let p : LatLink lat → Prop := fun l => l ≠ e
  haveI : Unique {l : LatLink lat // ¬ p l} :=
    ⟨⟨⟨e, not_not.mpr rfl⟩⟩, fun ⟨l, hl⟩ => Subtype.ext (not_not.mp hl)⟩
  have h1 : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : LatLink lat => specialUnitaryGroup (Fin N) ℂ) p)
      (haarConfigMeasure suHaar lat)
      ((Measure.pi (fun _ : {l : LatLink lat // p l} => suHaar)).prod
        (Measure.pi (fun _ : {l : LatLink lat // ¬ p l} => suHaar))) :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun _ : LatLink lat => suHaar) p
  have h2 : MeasurePreserving
      (MeasurableEquiv.piUnique (fun _ : {l : LatLink lat // ¬ p l} =>
        specialUnitaryGroup (Fin N) ℂ))
      (Measure.pi (fun _ : {l : LatLink lat // ¬ p l} => suHaar)) suHaar :=
    MeasureTheory.measurePreserving_piUnique _
  have hdef : ((default : {l : LatLink lat // ¬ p l}) : LatLink lat) = e :=
    not_not.mp (default : {l : LatLink lat // ¬ p l}).2
  convert ((MeasurePreserving.id _).prod h2).comp h1 using 1
  · funext U
    ext l <;> simp [hdef]

def tOrder [NeZero L_t] (lat : LatticeSetup d L_t) (tStar t : Fin L_t) : ℕ :=
  (t - (tStar + 1)).val

lemma tOrder_step0_lt [NeZero d] [NeZero L_t] (lat : LatticeSetup d L_t) (tStar : Fin L_t)
    {v : lat.Site} (hv : lat.tCoord v ≠ tStar) :
    tOrder lat tStar (lat.tCoord (lat.stepSite v ⟨0, by have := lat.hd; omega⟩)) =
      tOrder lat tStar (lat.tCoord v) + 1 := by
  have hLt := lat.hLt
  rw [lat.tCoord_step0]
  unfold tOrder
  have hne : lat.tCoord v - (tStar + 1) ≠ (-1 : Fin L_t) := by
    intro heq
    apply hv
    have hc := congrArg (fun z : Fin L_t => z + (tStar + 1)) heq
    change (lat.tCoord v - (tStar + 1)) + (tStar + 1) =
      (-1 : Fin L_t) + (tStar + 1) at hc
    have hleft : (lat.tCoord v - (tStar + 1)) + (tStar + 1) = lat.tCoord v := by abel
    have hcalc : (-1 : Fin L_t) + (tStar + 1) = tStar := by abel
    rw [hleft, hcalc] at hc
    exact hc
  let x : Fin L_t := lat.tCoord v - (tStar + 1)
  have hxval_ne : x.val ≠ L_t - 1 := by
    intro hx
    apply hne
    have hm1 : (⟨L_t - 1, by omega⟩ : Fin L_t) = -1 := by
      refine eq_neg_of_add_eq_zero_left ?_
      ext
      rw [Fin.val_add]
      change ((L_t - 1) + (1 % L_t)) % L_t = 0
      rw [Nat.mod_eq_of_lt (by omega : 1 < L_t)]
      rw [show L_t - 1 + 1 = L_t by omega]
      simp
    apply Fin.ext
    rw [hx]
    exact congrArg Fin.val hm1
  have hxval_lt : x.val + 1 < L_t := by
    have hxlt : x.val < L_t := x.isLt
    by_cases hxl : x.val < L_t - 1
    · omega
    · have : x.val = L_t - 1 := by omega
      exact False.elim (hxval_ne this)
  change ((lat.tCoord v + 1) - (tStar + 1)).val = x.val + 1
  have hrewrite : (lat.tCoord v + 1) - (tStar + 1) = x + 1 := by
    unfold x
    abel
  rw [hrewrite, Fin.val_add]
  have h1per : (1 : Fin L_t).val = 1 := by
    change 1 % L_t = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1per]
  exact Nat.mod_eq_of_lt hxval_lt

/-- A single plaquette defect has an absolutely continuous law under product Haar. -/
theorem plaquette_single_absolutelyContinuous (hN' : 2 ≤ N) (hLt2 : 2 ≤ L_t)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (lat : LatticeSetup d L_t) (v : lat.Site) :
    (haarConfigMeasure suHaar lat).map (plaquetteObs lat N v) ≪ volume := by
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := by
    change SecondCountableTopology (Fin N → Fin N → ℂ)
    infer_instance
  letI : SecondCountableTopology (specialUnitaryGroup (Fin N) ℂ) :=
    TopologicalSpace.secondCountableTopology_induced (specialUnitaryGroup (Fin N) ℂ)
      (Matrix (Fin N) (Fin N) ℂ) (fun A => (A : Matrix (Fin N) (Fin N) ℂ))
  let dir0 : Fin d := ⟨0, by have := lat.hd; omega⟩
  let dir1 : Fin d := ⟨1, by have := lat.hd; omega⟩
  have hd01 : dir0 ≠ dir1 := by
    intro h; have := congrArg Fin.val h; simp [dir0, dir1] at this
  have hstep_ne : lat.stepSite v dir0 ≠ v := by
    intro h
    have hc := lat.tCoord_step0 v
    rw [h] at hc
    have hsucc : (lat.tCoord v + 1 : Fin L_t) ≠ lat.tCoord v := by
      intro heq
      have hv := congrArg Fin.val heq
      rw [Fin.val_add] at hv
      change ((lat.tCoord v).val + (1 % L_t)) % L_t = (lat.tCoord v).val at hv
      have h1 : 1 % L_t = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1] at hv
      have hvlt : (lat.tCoord v).val + 1 < L_t := by
        by_contra hn
        have : (lat.tCoord v).val = L_t - 1 := by omega
        rw [this] at hv
        rw [show L_t - 1 + 1 = L_t by omega] at hv
        rw [Nat.mod_self] at hv
        omega
      rw [Nat.mod_eq_of_lt hvlt] at hv
      omega
    exact hsucc hc.symm
  let e : LatLink lat := (lat.stepSite v dir0, dir1)
  have he0 : (v, dir0) ≠ e := by
    intro h; have := congrArg Prod.snd h; exact hd01 this
  have he1 : (lat.stepSite v dir1, dir0) ≠ e := by
    intro h; have := congrArg Prod.snd h; exact hd01 this
  have he2 : (v, dir1) ≠ e := by
    intro h; have hv := congrArg Prod.fst h; exact hstep_ne hv.symm
  let A : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) → specialUnitaryGroup (Fin N) ℂ :=
    fun U => U ⟨(v, dir0), he0⟩
  let B : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) → specialUnitaryGroup (Fin N) ℂ :=
    fun U => (U ⟨(lat.stepSite v dir1, dir0), he1⟩)⁻¹ * (U ⟨(v, dir1), he2⟩)⁻¹
  refine Measure.AbsolutelyContinuous.mk ?_
  intro S hS hSvol
  let T : Set (({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
      specialUnitaryGroup (Fin N) ℂ) :=
    {p | f0 N (A p.1 * p.2 * B p.1) ∈ S}
  have hTmeas : MeasurableSet T := by
    dsimp [T]
    have hmeasA : Measurable A := by
      dsimp [A]; exact measurable_pi_apply _
    have hmeasB : Measurable B := by
      dsimp [B]
      exact ((measurable_pi_apply _).inv).mul ((measurable_pi_apply _).inv)
    exact ((f0_continuous N).measurable.comp
      (((hmeasA.comp measurable_fst).mul measurable_snd).mul
        (hmeasB.comp measurable_fst))) hS
  have hTvol : ((Measure.pi (fun _ : {l : LatLink lat // l ≠ e} => suHaar)).prod suHaar) T = 0 := by
    have hzero : (fun uRest => suHaar {g | f0 N (A uRest * g * B uRest) ∈ S}) = fun _ => 0 := by
      funext uRest
      have hac := f0_twosided_pushforward_absolutelyContinuous suHaar hN' submersion_1d
        (A uRest) (B uRest)
      have hz := hac hSvol
      have hmeasfun : Measurable (fun U : specialUnitaryGroup (Fin N) ℂ =>
          f0 N (A uRest * U * B uRest)) :=
        (f0_continuous N).measurable.comp
          (((measurable_const.mul measurable_id).mul measurable_const))
      rw [Measure.map_apply hmeasfun hS] at hz
      exact hz
    rw [Measure.prod_apply hTmeas]
    have hz' : (fun x => suHaar (Prod.mk x ⁻¹' T)) = fun _ => 0 := by
      funext x
      simpa [T] using congrFun hzero x
    rw [hz']
    simp
  rw [Measure.map_apply (plaquetteObs_measurable lat N v) hS]
  -- transfer via splitLinkEquiv
  have hmp := splitLinkEquiv_measurePreserving suHaar lat e
  have hpre : (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
      plaquetteObs lat N v U) ⁻¹' S =
      (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
        (fun l : {l : LatLink lat // l ≠ e} => U l.1, U e)) ⁻¹' T := by
    ext U
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    dsimp [T, plaquetteObs, A, B, e]
    simp [mul_assoc, dir0, dir1]
  rw [hpre]
  rw [← Measure.map_apply hmp.measurable hTmeas, hmp.map_eq, hTvol]

lemma plaquetteObs_update_eq_of_ne (lat : LatticeSetup d L_t) (N : ℕ) (v : lat.Site)
    (e : LatLink lat)
    (h0 : (v, (⟨0, by have := lat.hd; omega⟩ : Fin d)) ≠ e)
    (h1 : (lat.stepSite v (⟨0, by have := lat.hd; omega⟩ : Fin d),
           (⟨1, by have := lat.hd; omega⟩ : Fin d)) ≠ e)
    (h2 : (lat.stepSite v (⟨1, by have := lat.hd; omega⟩ : Fin d),
           (⟨0, by have := lat.hd; omega⟩ : Fin d)) ≠ e)
    (h3 : (v, (⟨1, by have := lat.hd; omega⟩ : Fin d)) ≠ e)
    (U : LatLink lat → specialUnitaryGroup (Fin N) ℂ) (g : specialUnitaryGroup (Fin N) ℂ) :
    plaquetteObs lat N v (Function.update U e g) = plaquetteObs lat N v U := by
  unfold plaquetteObs
  dsimp only
  rw [Function.update_of_ne h0, Function.update_of_ne h1,
    Function.update_of_ne h2, Function.update_of_ne h3]

lemma haarConfigMeasure_preimage_Ubase {β : Type*} [MeasurableSpace β]
    (lat : LatticeSetup d L_t) (e : LatLink lat)
    (Y : (LatLink lat → Matrix.specialUnitaryGroup (Fin N) ℂ) → β)
    (hYmeas : Measurable Y)
    (hYindep : ∀ (U : LatLink lat → Matrix.specialUnitaryGroup (Fin N) ℂ) (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
      Y (Function.update U e g) = Y U)
    (B : Set β) (hB : MeasurableSet B) :
    (Measure.pi (fun _ : {l : LatLink lat // l ≠ e} => suHaar))
        {uRest | Y (fun l => if h : l = e then 1 else uRest ⟨l, h⟩) ∈ B}
      = haarConfigMeasure suHaar lat {U | Y U ∈ B} := by
  let Ubase := fun (uRest : {l : LatLink lat // l ≠ e} → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (l : LatLink lat) => if h : l = e then 1 else uRest ⟨l, h⟩
  let μrest := Measure.pi (fun _ : {l : LatLink lat // l ≠ e} => suHaar)
  have hmp := splitLinkEquiv_measurePreserving suHaar lat e
  have hset : {U : LatLink lat → Matrix.specialUnitaryGroup (Fin N) ℂ | Y U ∈ B} =
      (fun U => (fun l : {l : LatLink lat // l ≠ e} => U l.1, U e)) ⁻¹'
        ({uRest | Y (Ubase uRest) ∈ B} ×ˢ Set.univ) := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    have hUbase : Ubase (fun l : {l : LatLink lat // l ≠ e} => U l.1) =
        Function.update U e 1 := by
      funext l
      by_cases hl : l = e
      · subst l
        simp [Ubase]
      · simp [Ubase, hl, Function.update_of_ne hl]
    rw [hUbase, hYindep U 1]
  have hUbase_meas : Measurable Ubase := by
    rw [measurable_pi_iff]
    intro l
    by_cases hl : l = e
    · subst l
      simp [Ubase]
    · simp [Ubase, hl]
      exact measurable_pi_apply (⟨l, hl⟩ : {l : LatLink lat // l ≠ e})
  have hAmeas : MeasurableSet {uRest | Y (Ubase uRest) ∈ B} :=
    hB.preimage (hYmeas.comp hUbase_meas)
  rw [hset, ← Measure.map_apply hmp.measurable (hAmeas.prod MeasurableSet.univ),
  ]
  change μrest {uRest | Y (Ubase uRest) ∈ B} =
    (Measure.map (fun U : LatLink lat → Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (fun l : {l : LatLink lat // l ≠ e} => U l.1, U e))
        (haarConfigMeasure suHaar lat))
      ({uRest | Y (Ubase uRest) ∈ B} ×ˢ Set.univ)
  rw [hmp.map_eq, Measure.prod_prod]
  simp [μrest]


lemma measurable_f0_two_sided {α : Type*} [MeasurableSpace α]
    (N : ℕ) (A B : α → specialUnitaryGroup (Fin N) ℂ)
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun p : α × specialUnitaryGroup (Fin N) ℂ => f0 N (A p.1 * p.2 * B p.1)) := by
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := by
    change SecondCountableTopology (Fin N → Fin N → ℂ)
    infer_instance
  letI : SecondCountableTopology (specialUnitaryGroup (Fin N) ℂ) :=
    TopologicalSpace.secondCountableTopology_induced (specialUnitaryGroup (Fin N) ℂ)
      (Matrix (Fin N) (Fin N) ℂ) (fun A => (A : Matrix (Fin N) (Fin N) ℂ))
  exact (f0_continuous N).measurable.comp
    (((hA.comp measurable_fst).mul measurable_snd).mul (hB.comp measurable_fst))

lemma measurable_Y_Ubase {γ β α δ : Type*} [MeasurableSpace γ] [MeasurableSpace β]
    [MeasurableSpace α] [MeasurableSpace δ]
    (Y : β → α) (hY : Measurable Y) (Ubase : γ → β) (hU : Measurable Ubase) :
    Measurable (fun p : γ × δ => Y (Ubase p.1)) := by
  exact hY.comp (hU.comp measurable_fst)



lemma ac_of_map_ac_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (E : α ≃ᵐ β) (volα : Measure α) (volβ : Measure β)
    (hEvol : Measure.map E volα = volβ)
    (ν : Measure β) (hν : ν ≪ volβ) : (ν.map E.symm) ≪ volα := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro S hS hSvol
  rw [Measure.map_apply E.symm.measurable hS]
  apply hν
  have hpreimg : E.symm ⁻¹' S = E '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨E.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa
  rw [hpreimg]
  have himg : MeasurableSet (E '' S) := (E.measurableSet_image).mpr hS
  have hvolimg : volβ (E '' S) = volα S := by
    rw [← hEvol, Measure.map_apply E.measurable himg]
    congr 1
    ext x
    simp
  rw [hvolimg, hSvol]




lemma ac_map_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (E : α → β) (μν : Measure α) (volβ : Measure β)
    (hmp : MeasurePreserving E μν volβ)
    (ν : Measure α) (hν : ν ≪ μν) : (ν.map E) ≪ volβ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro S hS hSvol
  rw [Measure.map_apply hmp.measurable hS]
  apply hν
  have hs0 := hmp.map_eq
  rw [← Measure.map_apply hmp.measurable hS, hs0]
  exact hSvol

/-- A parameter-dependent left and right translation of the last Haar
coordinate preserves the product measure. -/
private theorem measurePreserving_parametricHaarMul
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (A B : α → specialUnitaryGroup (Fin N) ℂ)
    (hT : Measurable (fun p : α × specialUnitaryGroup (Fin N) ℂ =>
      (p.1, A p.1 * p.2 * B p.1)))
    (htrans : ∀ a b : specialUnitaryGroup (Fin N) ℂ,
      suHaar.map (fun g => a * g * b) = suHaar) :
    MeasurePreserving (fun p : α × specialUnitaryGroup (Fin N) ℂ =>
      (p.1, A p.1 * p.2 * B p.1)) (μ.prod suHaar) (μ.prod suHaar) := by
  let T : α × specialUnitaryGroup (Fin N) ℂ → α × specialUnitaryGroup (Fin N) ℂ :=
    fun p => (p.1, A p.1 * p.2 * B p.1)
  change MeasurePreserving T (μ.prod suHaar) (μ.prod suHaar)
  refine ⟨hT, ?_⟩
  apply Measure.ext
  intro s hs
  have hsection (x : α) :
      suHaar {g | (x, A x * g * B x) ∈ s} = suHaar {g | (x, g) ∈ s} := by
    let φ : specialUnitaryGroup (Fin N) ℂ → specialUnitaryGroup (Fin N) ℂ :=
      fun g => A x * g * B x
    let secset : Set (specialUnitaryGroup (Fin N) ℂ) := {g | (x, g) ∈ s}
    have hφ : Measurable φ := by
      change Measurable (fun g => (T (x, g)).2)
      exact measurable_snd.comp (hT.comp (measurable_const.prodMk measurable_id))
    have hsx : MeasurableSet secset := by
      exact hs.preimage (measurable_const.prodMk measurable_id)
    calc
      suHaar {g | (x, A x * g * B x) ∈ s} = suHaar (φ ⁻¹' secset) := by
        congr 1
      _ = (suHaar.map φ) secset := (Measure.map_apply hφ hsx).symm
      _ = suHaar secset := by rw [htrans (A x) (B x)]
  calc
    (μ.prod suHaar).map T s = (μ.prod suHaar) (T ⁻¹' s) :=
      Measure.map_apply hT hs
    _ = ∫⁻ x, suHaar (Prod.mk x ⁻¹' (T ⁻¹' s)) ∂μ :=
      Measure.prod_apply (hs.preimage hT)
    _ = ∫⁻ x, suHaar (Prod.mk x ⁻¹' s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      simpa [T] using hsection x
    _ = (μ.prod suHaar) s := (Measure.prod_apply hs).symm

/-- There is a time slice unused by finitely many sites. -/

theorem plaquette_joint_absolutelyContinuous (hN' : 2 ≤ N) (hLt2 : 2 ≤ L_t)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (lat : LatticeSetup d L_t) :
    ∀ (r : ℕ), r + 1 ≤ L_t → ∀ (v : Fin r → lat.Site), Function.Injective v →
      ((haarConfigMeasure suHaar lat).map
        (fun U i => plaquetteObs lat N (v i) U) ≪ (volume : Measure (Fin r → ℝ))) ∧
      (haarConfigMeasure suHaar lat).map
        (fun U i => plaquetteObs lat N (v i) U) =
          Measure.pi (fun _ : Fin r => suHaar.map (f0 N)) := by
  intro r
  induction r with
  | zero =>
      intro hsize v hinj
      constructor
      ·
        have hFmeas : Measurable (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
            (fun i : Fin 0 => plaquetteObs lat N (v i) U)) := by
          rw [measurable_pi_iff]
          intro i
          exact i.elim0
        have hvol : (volume : Measure (Fin 0 → ℝ)) =
            Measure.dirac (fun i : Fin 0 => isEmptyElim i) := by
          rw [volume_pi]
          exact Measure.pi_of_empty _
        refine Measure.AbsolutelyContinuous.mk ?_
        intro S hS hSvol
        rw [Measure.map_apply hFmeas hS]
        rw [hvol] at hSvol
        by_cases hmem : (fun i : Fin 0 => isEmptyElim i) ∈ S
        · have hdir : (Measure.dirac (fun i : Fin 0 => isEmptyElim i)) S = 1 := by simp [hmem]
          rw [hdir] at hSvol
          norm_num at hSvol
        · have hpre : (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
              (fun i : Fin 0 => plaquetteObs lat N (v i) U)) ⁻¹' S = ∅ := by
            ext U
            simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro hU
            apply hmem
            simpa only [Subsingleton.elim
              (fun i : Fin 0 => plaquetteObs lat N (v i) U)
              (fun i : Fin 0 => isEmptyElim i)] using hU
          rw [hpre, measure_empty]
      ·
        let F : (LatLink lat → specialUnitaryGroup (Fin N) ℂ) → (Fin 0 → ℝ) :=
          fun U i => plaquetteObs lat N (v i) U
        have hF : Measurable F := by
          rw [measurable_pi_iff]
          intro i
          exact i.elim0
        let z : Fin 0 → ℝ := fun i => Fin.elim0 i
        have hmap : (haarConfigMeasure suHaar lat).map F = Measure.dirac z := by
          apply Measure.ext
          intro s hs
          by_cases hz : z ∈ s
          · rw [Measure.map_apply hF hs]
            have hpre : F ⁻¹' s = Set.univ := by
              ext U
              simp only [Set.mem_preimage, Set.mem_univ, iff_true]
              have hFU : F U = z := Subsingleton.elim _ _
              simpa [hFU] using hz
            rw [hpre]
            simp [hz]
          · rw [Measure.map_apply hF hs]
            have hpre : F ⁻¹' s = ∅ := by
              ext U
              simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
              intro hmem
              apply hz
              rw [← Subsingleton.elim (F U) z]
              exact hmem
            rw [hpre]
            simp [hz]
        have hpi : Measure.pi (fun _ : Fin 0 => suHaar.map (f0 N)) =
            Measure.dirac z := by
          simpa [z] using (Measure.pi_of_empty (fun _ : Fin 0 => suHaar.map (f0 N)))
        rw [hmap, hpi]
  | succ r ih =>
      intro hsize v hinj
      have hsize' : r + 1 ≤ L_t := by omega
      obtain ⟨tStar, htStar⟩ : ∃ t : Fin L_t, ∀ i : Fin (r + 1), lat.tCoord (v i) ≠ t := by
        by_contra h
        push_neg at h
        have hsub : (Finset.univ : Finset (Fin L_t)) ⊆
            Finset.univ.image (fun i : Fin (r + 1) => lat.tCoord (v i)) := by
          intro t ht
          obtain ⟨i, hi⟩ := h t
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
        have hcard := Finset.card_le_card hsub
        have himg : (Finset.univ.image (fun i : Fin (r + 1) => lat.tCoord (v i))).card ≤
            (Finset.univ : Finset (Fin (r + 1))).card := Finset.card_image_le
        simp only [Finset.card_univ, Fintype.card_fin] at hcard himg
        omega
      let fOrd : Fin (r + 1) → ℕ := fun i => tOrder lat tStar (lat.tCoord (v i))
      obtain ⟨i0, hi0mem, hi0⟩ := Finset.exists_max_image Finset.univ fOrd Finset.univ_nonempty
      let σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap i0 (Fin.last r)
      let v' : Fin (r + 1) → lat.Site := fun i => v (σ i)
      have hv'inj : Function.Injective v' := hinj.comp σ.injective
      have hmax : ∀ i : Fin (r + 1),
          tOrder lat tStar (lat.tCoord (v' i)) ≤
          tOrder lat tStar (lat.tCoord (v' (Fin.last r))) := by
        intro i
        have hi := hi0 (σ i) (Finset.mem_univ _)
        dsimp [fOrd, v', σ] at hi ⊢
        simpa using hi
      let dir0 : Fin d := ⟨0, by have := lat.hd; omega⟩
      let dir1 : Fin d := ⟨1, by have := lat.hd; omega⟩
      have hd01 : dir0 ≠ dir1 := by
        intro h
        have hv := congrArg Fin.val h
        change (0 : ℕ) = 1 at hv
        omega
      let w : lat.Site := v' (Fin.last r)
      have hstep_ne : lat.stepSite w dir0 ≠ w := by
        intro h
        have hc := lat.tCoord_step0 w
        rw [h] at hc
        have hsucc : (lat.tCoord w + 1 : Fin L_t) ≠ lat.tCoord w := by
          intro heq
          have hv := congrArg Fin.val heq
          rw [Fin.val_add] at hv
          change ((lat.tCoord w).val + (1 % L_t)) % L_t = (lat.tCoord w).val at hv
          rw [Nat.mod_eq_of_lt (by omega : 1 < L_t)] at hv
          have hvlt : (lat.tCoord w).val + 1 < L_t := by
            by_contra hn
            have : (lat.tCoord w).val = L_t - 1 := by omega
            rw [this] at hv
            rw [show L_t - 1 + 1 = L_t by omega] at hv
            rw [Nat.mod_self] at hv
            omega
          rw [Nat.mod_eq_of_lt hvlt] at hv
          omega
        exact hsucc hc.symm
      have hw_ne : lat.tCoord w ≠ tStar := by
        dsimp [w, v', σ]
        exact htStar (σ (Fin.last r))
      let e : LatLink lat := (lat.stepSite w dir0, dir1)
      have hne_of_lt (j : Fin r) :
          (v' j.castSucc, dir0) ≠ e ∧
          (lat.stepSite (v' j.castSucc) dir0, dir1) ≠ e ∧
          (lat.stepSite (v' j.castSucc) dir1, dir0) ≠ e ∧
          (v' j.castSucc, dir1) ≠ e := by
        have hvw : v' j.castSucc ≠ w := by
          intro h
          have heq : j.castSucc = Fin.last r := hv'inj h
          have hval := congrArg Fin.val heq
          change j.1 = r at hval
          omega
        constructor
        · intro h; have := congrArg Prod.snd h; exact hd01 this
        constructor
        · intro h
          have hs := congrArg Prod.fst h
          have : v' j.castSucc = w := lat.step0_inj hs
          exact hvw this
        constructor
        · intro h
          have hs := congrArg Prod.snd h
          change dir0 = dir1 at hs
          exact hd01 hs
        · intro h
          have hs := congrArg Prod.fst h
          apply hvw
          have ht : lat.tCoord (v' j.castSucc) = lat.tCoord (lat.stepSite w dir0) := congrArg lat.tCoord hs
          rw [lat.tCoord_step0] at ht
          have hle := hmax j.castSucc
          rw [ht] at hle
          have hstepord : tOrder lat tStar (lat.tCoord w + 1) =
              tOrder lat tStar (lat.tCoord w) + 1 := by
            rw [← lat.tCoord_step0 w]
            exact tOrder_step0_lt lat tStar hw_ne
          rw [hstepord] at hle
          change tOrder lat tStar (lat.tCoord w) + 1 ≤
            tOrder lat tStar (lat.tCoord w) at hle
          omega
      let Ubase : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) →
          LatLink lat → specialUnitaryGroup (Fin N) ℂ :=
        fun uRest l => if h : l = e then 1 else uRest ⟨l, h⟩
      let A : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) →
          specialUnitaryGroup (Fin N) ℂ := fun uRest => Ubase uRest (w, dir0)
      let B : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) →
          specialUnitaryGroup (Fin N) ℂ := fun uRest =>
        (Ubase uRest (lat.stepSite w dir1, dir0))⁻¹ * (Ubase uRest (w, dir1))⁻¹
      let Y : (LatLink lat → specialUnitaryGroup (Fin N) ℂ) → (Fin r → ℝ) :=
        fun U j => plaquetteObs lat N (v' j.castSucc) U
      have hYmeas : Measurable Y := by
        rw [measurable_pi_iff]; intro j
        exact plaquetteObs_measurable lat N (v' j.castSucc)
      have hYindep : ∀ (U : LatLink lat → specialUnitaryGroup (Fin N) ℂ)
          (g : specialUnitaryGroup (Fin N) ℂ), Y (Function.update U e g) = Y U := by
        intro U g
        funext j
        exact plaquetteObs_update_eq_of_ne lat N (v' j.castSucc) e
          (hne_of_lt j).1 (hne_of_lt j).2.1 (hne_of_lt j).2.2.1 (hne_of_lt j).2.2.2 U g
      let μrest : Measure ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) :=
        Measure.pi (fun _ => suHaar)
      let νprod : Measure (({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
          specialUnitaryGroup (Fin N) ℂ) := μrest.prod suHaar
      let Φ : (({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
          specialUnitaryGroup (Fin N) ℂ) → (Fin r → ℝ) × ℝ :=
        fun p => (Y (Ubase p.1), f0 N (A p.1 * p.2 * B p.1))
      -- transfer IH null set from haarConfigMeasure to μrest
      have hcast_inj : Function.Injective (fun j : Fin r => σ j.castSucc) := by
        intro a b h
        have hh := congrArg σ.symm h
        exact Fin.castSucc_injective r (by simpa using hh)
      have hih := ih hsize' (fun j : Fin r => v' j.castSucc) (hinj.comp hcast_inj)
      have htransfer := haarConfigMeasure_preimage_Ubase suHaar lat e Y hYmeas hYindep
      have hUbase_meas : Measurable Ubase := by
        rw [measurable_pi_iff]
        intro l
        by_cases hl : l = e
        · subst l
          simp [Ubase]
        · simp [Ubase, hl]
          exact measurable_pi_apply (⟨l, hl⟩ : {l : LatLink lat // l ≠ e})
      letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := by
        change SecondCountableTopology (Fin N → Fin N → ℂ)
        infer_instance
      letI : SecondCountableTopology (specialUnitaryGroup (Fin N) ℂ) :=
        TopologicalSpace.secondCountableTopology_induced (specialUnitaryGroup (Fin N) ℂ)
          (Matrix (Fin N) (Fin N) ℂ) (fun A => (A : Matrix (Fin N) (Fin N) ℂ))
      have hAmeas : Measurable A := by
        dsimp [A]
        exact (measurable_pi_apply (w, dir0)).comp hUbase_meas
      have hBmeas : Measurable B := by
        dsimp [B]
        exact (((measurable_pi_apply (lat.stepSite w dir1, dir0)).comp hUbase_meas).inv).mul
          ((measurable_pi_apply (w, dir1)).comp hUbase_meas).inv
      have hΦmeas : Measurable Φ := by
        dsimp [Φ]
        exact (measurable_Y_Ubase Y hYmeas Ubase hUbase_meas).prod
          (measurable_f0_two_sided N A B hAmeas hBmeas)
      have hΦac : (νprod.map Φ) ≪ (volume : Measure ((Fin r → ℝ) × ℝ)) := by
        refine Measure.AbsolutelyContinuous.mk ?_
        intro S hS hSvol
        have hΦslice : MeasurableSet
            {p : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
                  specialUnitaryGroup (Fin N) ℂ | Φ p ∈ S} := hS.preimage hΦmeas
        rw [Measure.map_apply hΦmeas hS]
        let B₀ : Set (Fin r → ℝ) := {y | volume (Prod.mk y ⁻¹' S) ≠ 0}
        have hB₀meas : MeasurableSet B₀ := by
          exact (measurable_measure_prodMk_left hS) (isClosed_singleton.measurableSet.compl)
        have hB₀vol : volume B₀ = 0 := by
          exact ae_iff.mp ((Measure.measure_prod_null hS).mp hSvol)
        have hih_null : haarConfigMeasure suHaar lat {U | Y U ∈ B₀} = 0 := by
          have hh := hih.1 hB₀vol
          rw [Measure.map_apply hYmeas hB₀meas] at hh
          exact hh
        have hrest_null : μrest {uRest | Y (Ubase uRest) ∈ B₀} = 0 := by
          rw [htransfer B₀ hB₀meas]
          exact hih_null
        change (μrest.prod suHaar) {p | Φ p ∈ S} = 0
        rw [Measure.measure_prod_null hΦslice]
        have hae : ∀ᵐ uRest ∂μrest, Y (Ubase uRest) ∉ B₀ := by
          exact ae_iff.mpr (by simpa only [not_not] using hrest_null)
        filter_upwards [hae] with uRest huRest
        have hSyvol : volume {x : ℝ | (Y (Ubase uRest), x) ∈ S} = 0 := by
          exact not_not.mp huRest
        have hSymeas : MeasurableSet {x : ℝ | (Y (Ubase uRest), x) ∈ S} := by
          exact hS.preimage (measurable_const.prodMk measurable_id)
        have hacg := f0_twosided_pushforward_absolutelyContinuous suHaar hN'
          submersion_1d (A uRest) (B uRest)
        have hz := hacg hSyvol
        have hmeasfunc : Measurable (fun U : specialUnitaryGroup (Fin N) ℂ =>
            f0 N (A uRest * U * B uRest)) :=
          (f0_continuous N).measurable.comp
            (((measurable_const.mul measurable_id).mul measurable_const))
        rw [Measure.map_apply hmeasfunc hSymeas] at hz
        simpa [Φ, Y] using hz
      let fRest : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) →
          Fin r → ℝ := fun uRest => Y (Ubase uRest)
      have hfRest : Measurable fRest := by
        change Measurable (fun uRest => Y (Ubase uRest))
        exact hYmeas.comp (hUbase_meas.comp measurable_id)
      have hRestlaw : μrest.map fRest =
          Measure.pi (fun _ : Fin r => suHaar.map (f0 N)) := by
        calc
          μrest.map fRest = (haarConfigMeasure suHaar lat).map Y := by
            apply Measure.ext
            intro S hS
            calc
              μrest.map fRest S = μrest {uRest | Y (Ubase uRest) ∈ S} := by
                rw [Measure.map_apply hfRest hS]
                rfl
              _ = haarConfigMeasure suHaar lat {U | Y U ∈ S} :=
                haarConfigMeasure_preimage_Ubase suHaar lat e Y hYmeas hYindep S hS
              _ = (haarConfigMeasure suHaar lat).map Y S := by
                rw [Measure.map_apply hYmeas hS]
                rfl
          _ = Measure.pi (fun _ : Fin r => suHaar.map (f0 N)) := hih.2
      let T : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
          specialUnitaryGroup (Fin N) ℂ →
          ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
            specialUnitaryGroup (Fin N) ℂ :=
        fun p => (p.1, A p.1 * p.2 * B p.1)
      have hTmeas : Measurable T := by
        dsimp [T]
        exact measurable_fst.prodMk
          (((hAmeas.comp measurable_fst).mul measurable_snd).mul
            (hBmeas.comp measurable_fst))
      have htrans (a b : specialUnitaryGroup (Fin N) ℂ) :
          suHaar.map (fun g => a * g * b) = suHaar := by
        have hleft : suHaar.map (fun g : specialUnitaryGroup (Fin N) ℂ => a * g) = suHaar := by
          simpa using map_mul_left_eq_self suHaar a
        have hright : suHaar.map (fun g : specialUnitaryGroup (Fin N) ℂ => g * b) = suHaar := by
          simpa using map_mul_right_eq_self suHaar b
        have hcomp : (fun g : specialUnitaryGroup (Fin N) ℂ => a * g * b) =
            (fun g => g * b) ∘ (fun g => a * g) := rfl
        rw [hcomp, ← Measure.map_map (continuous_mul_right b).measurable
          (continuous_mul_left a).measurable, hleft, hright]
      have hTpres := measurePreserving_parametricHaarMul suHaar μrest A B hTmeas htrans
      let ψ : ({l : LatLink lat // l ≠ e} → specialUnitaryGroup (Fin N) ℂ) ×
          specialUnitaryGroup (Fin N) ℂ → (Fin r → ℝ) × ℝ :=
        fun p => (fRest p.1, f0 N p.2)
      have hψmeas : Measurable ψ := by
        dsimp [ψ]
        exact hfRest.comp measurable_fst |>.prod
          ((f0_continuous N).measurable.comp measurable_snd)
      have hΦcomp : Φ = ψ ∘ T := by
        funext p
        rfl
      have hΦlaw : νprod.map Φ =
          (Measure.pi (fun _ : Fin r => suHaar.map (f0 N))).prod
            (suHaar.map (f0 N)) := by
        calc
          νprod.map Φ = (νprod.map T).map ψ := by
            rw [hΦcomp, Measure.map_map hψmeas hTmeas]
          _ = νprod.map ψ := by
            rw [hTpres.map_eq]
          _ = (μrest.map fRest).prod (suHaar.map (f0 N)) := by
            exact (Measure.map_prod_map μrest suHaar hfRest
              (f0_continuous N).measurable).symm
          _ = _ := by rw [hRestlaw]
      let E : (Fin (r + 1) → ℝ) ≃ᵐ (Fin r → ℝ) × ℝ :=
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).trans
          MeasurableEquiv.prodComm
      have hEvol : Measure.map E (volume : Measure (Fin (r + 1) → ℝ)) =
          (volume : Measure ((Fin r → ℝ) × ℝ)) := by
        exact (Measure.measurePreserving_swap.comp
          (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r))).map_eq
      have hsplitfun_mp : MeasurePreserving
          (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
            (fun l : {l : LatLink lat // l ≠ e} => U l.1, U e))
          (haarConfigMeasure suHaar lat) νprod := by
        simpa [νprod, μrest] using splitLinkEquiv_measurePreserving suHaar lat e
      have hcomp : (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
          E (fun i => plaquetteObs lat N (v' i) U)) =
          (fun U => Φ (fun l : {l : LatLink lat // l ≠ e} => U l.1, U e)) := by
        funext U
        ext
        · rename_i j
          dsimp [E, Φ]
          dsimp [MeasurableEquiv.prodComm, Fin.removeNth]
          have hsucc : (Fin.last r).succAbove j = j.castSucc := by simp
          rw [hsucc]
          change Y U j = Y (Ubase (fun l : {l : LatLink lat // l ≠ e} => U l.1)) j
          have hU : Ubase (fun l : {l : LatLink lat // l ≠ e} => U l.1) =
              Function.update U e 1 := by
            funext l
            by_cases hl : l = e
            · subst l
              simp [Ubase]
            · simp [Ubase, hl]
          rw [hU, hYindep U 1]
        · have he0 : (w, dir0) ≠ e := by
            intro h; have := congrArg Prod.snd h; exact hd01 this
          have he1 : (lat.stepSite w dir1, dir0) ≠ e := by
            intro h; have := congrArg Prod.snd h; exact hd01 this
          have he2 : (w, dir1) ≠ e := by
            intro h; have hs := congrArg Prod.fst h; exact hstep_ne hs.symm
          have hA : A (fun l : {l : LatLink lat // l ≠ e} => U l.1) = U (w, dir0) := by
            dsimp [A, Ubase]
            simp [he0]
          have hB : B (fun l : {l : LatLink lat // l ≠ e} => U l.1) =
              (U (lat.stepSite w dir1, dir0))⁻¹ * (U (w, dir1))⁻¹ := by
            dsimp [B, Ubase]
            simp [he1, he2]
          change plaquetteObs lat N w U =
            f0 N (A (fun l : {l : LatLink lat // l ≠ e} => U l.1) * U e *
              B (fun l : {l : LatLink lat // l ≠ e} => U l.1))
          rw [hA, hB]
          dsimp [plaquetteObs, e, w, dir0, dir1]
          rw [mul_assoc]
      have hF'comp : Measure.map E
          ((haarConfigMeasure suHaar lat).map
            (fun U i => plaquetteObs lat N (v' i) U)) = (νprod.map Φ) := by
        have hFmeas : Measurable (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
            (fun i => plaquetteObs lat N (v' i) U)) := by
          rw [measurable_pi_iff]
          intro i
          exact plaquetteObs_measurable lat N (v' i)
        rw [Measure.map_map E.measurable hFmeas]
        change Measure.map (fun U => E (fun i => plaquetteObs lat N (v' i) U))
          (haarConfigMeasure suHaar lat) = Measure.map Φ νprod
        rw [hcomp]
        change Measure.map (Φ ∘ (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
          (fun l : {l : LatLink lat // l ≠ e} => U l.1, U e)))
          (haarConfigMeasure suHaar lat) = Measure.map Φ νprod
        rw [← Measure.map_map hΦmeas hsplitfun_mp.measurable, hsplitfun_mp.map_eq]
      have hF'ac : (haarConfigMeasure suHaar lat).map
          (fun U i => plaquetteObs lat N (v' i) U) ≪ (volume : Measure (Fin (r + 1) → ℝ)) := by
        have hmapped : (Measure.map E
            ((haarConfigMeasure suHaar lat).map
              (fun U i => plaquetteObs lat N (v' i) U))) ≪
            (volume : Measure ((Fin r → ℝ) × ℝ)) := by
          rw [hF'comp]
          exact hΦac
        have ht := ac_of_map_ac_equiv E (volume : Measure (Fin (r + 1) → ℝ))
          (volume : Measure ((Fin r → ℝ) × ℝ)) hEvol _ hmapped
        simpa [Measure.map_map E.symm.measurable E.measurable] using ht
      let μ0 : Measure ℝ := suHaar.map (f0 N)
      have hF'law : Measure.map E
          ((haarConfigMeasure suHaar lat).map
            (fun U i => plaquetteObs lat N (v' i) U)) =
          (Measure.pi (fun _ : Fin r => μ0)).prod μ0 := by
        rw [hF'comp, hΦlaw]
      have hEpi : (Measure.pi (fun _ : Fin (r + 1) => μ0)).map E =
          (Measure.pi (fun _ : Fin r => μ0)).prod μ0 := by
        exact (Measure.measurePreserving_swap.comp
          (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ0)
            (Fin.last r))).map_eq
      have hF'law' : (haarConfigMeasure suHaar lat).map
          (fun U i => plaquetteObs lat N (v' i) U) =
          Measure.pi (fun _ : Fin (r + 1) => μ0) := by
        apply E.measurableEmbedding.map_injective
        rw [hF'law, hEpi]
      let π : (Fin (r + 1) → ℝ) ≃ᵐ (Fin (r + 1) → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin (r + 1) => ℝ) σ
      have hπvol : Measure.map π (volume : Measure (Fin (r + 1) → ℝ)) =
          (volume : Measure (Fin (r + 1) → ℝ)) :=
        (volume_measurePreserving_piCongrLeft (fun _ : Fin (r + 1) => ℝ) σ).map_eq
      have hπcomp : (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
          π (fun i => plaquetteObs lat N (v' i) U)) =
          (fun U i => plaquetteObs lat N (v i) U) := by
        funext U i
        dsimp [π]
        rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
        simp [v']
      have hFmeas' : Measurable (fun U : LatLink lat → specialUnitaryGroup (Fin N) ℂ =>
          (fun i => plaquetteObs lat N (v' i) U)) := by
        rw [measurable_pi_iff]
        intro i
        exact plaquetteObs_measurable lat N (v' i)
      have hπlaw : (Measure.pi (fun _ : Fin (r + 1) => μ0)).map π =
          Measure.pi (fun _ : Fin (r + 1) => μ0) := by
        simpa [π, μ0] using
          (Measure.pi_map_piCongrLeft σ (fun _ : Fin (r + 1) => suHaar.map (f0 N)))
      have hF'π : (haarConfigMeasure suHaar lat).map
          (fun U => π (fun i => plaquetteObs lat N (v' i) U)) =
          Measure.pi (fun _ : Fin (r + 1) => μ0) := by
        calc
          _ = ((haarConfigMeasure suHaar lat).map
              (fun U i => plaquetteObs lat N (v' i) U)).map π := by
                simpa [Function.comp_def] using
                  (Measure.map_map π.measurable hFmeas').symm
          _ = (Measure.pi (fun _ : Fin (r + 1) => μ0)).map π := by rw [hF'law']
          _ = Measure.pi (fun _ : Fin (r + 1) => μ0) := hπlaw
      have hres : (haarConfigMeasure suHaar lat).map
          (fun U => π (fun i => plaquetteObs lat N (v' i) U)) ≪
          (volume : Measure (Fin (r + 1) → ℝ)) := by
        simpa only [Measure.map_map π.measurable hFmeas'] using
          (ac_map_measurePreserving π (volume : Measure (Fin (r + 1) → ℝ))
            (volume : Measure (Fin (r + 1) → ℝ))
            (volume_measurePreserving_piCongrLeft (fun _ : Fin (r + 1) => ℝ) σ)
            _ hF'ac)
      constructor
      · rw [← hπcomp]
        exact hres
      · calc
          (haarConfigMeasure suHaar lat).map
              (fun U i => plaquetteObs lat N (v i) U) =
              (haarConfigMeasure suHaar lat).map
                (fun U => π (fun i => plaquetteObs lat N (v' i) U)) := by
                  rw [hπcomp]
          _ = Measure.pi (fun _ : Fin (r + 1) => μ0) := hF'π
lemma exists_unused_tslice (lat : LatticeSetup d L_t) (r : ℕ)
    (hsize : r + 2 ≤ L_t) (v : Fin (r + 1) → lat.Site) :
    ∃ tStar : Fin L_t, ∀ i : Fin (r + 1), lat.tCoord (v i) ≠ tStar := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Fin L_t)) ⊆
      Finset.univ.image (fun i : Fin (r + 1) => lat.tCoord (v i)) := by
    intro t ht
    obtain ⟨i, hi⟩ := h t
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hcard := Finset.card_le_card hsub
  have himg : (Finset.univ.image (fun i : Fin (r + 1) => lat.tCoord (v i))).card ≤
      (Finset.univ : Finset (Fin (r + 1))).card := Finset.card_image_le
  simp only [Finset.card_univ, Fintype.card_fin] at hcard himg
  omega

/-- A site of maximal tOrder. -/
lemma max_torder_site (lat : LatticeSetup d L_t) (tStar : Fin L_t)
    (r : ℕ) (v : Fin (r + 1) → lat.Site) :
    ∃ i0 : Fin (r + 1), ∀ i : Fin (r + 1),
      tOrder lat tStar (lat.tCoord (v i)) ≤ tOrder lat tStar (lat.tCoord (v i0)) := by
  let fOrd : Fin (r + 1) → ℕ := fun i => tOrder lat tStar (lat.tCoord (v i))
  obtain ⟨i0, hi0mem, hi0⟩ := Finset.exists_max_image Finset.univ fOrd Finset.univ_nonempty
  exact ⟨i0, fun i => hi0 i (Finset.mem_univ _)⟩
end YangMills
