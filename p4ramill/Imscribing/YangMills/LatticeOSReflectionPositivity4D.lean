
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Imscribing.YangMills.WilsonHaarCompactness4D
import Imscribing.YangMills.LatticeReflectionPositivity4D

/-!
# 4D SU(N) Wilson Lattice Cut-Splitting & Osterwalder–Seiler Reflection Positivity
-/

noncomputable section

namespace Imscribing.YangMills.LatticeCutSplit4D

open Imscribing.YangMills.WilsonLattice4D

def IsPosLink (M : ℕ) (x : Lat4 (2 * M)) (μ : Fin 4) : Prop :=
  (x 0).val < M ∧ (μ = 0 → (x 0).val ≠ M - 1)

def IsCutLinkMid (M : ℕ) (x : Lat4 (2 * M)) (μ : Fin 4) : Prop :=
  μ = 0 ∧ (x 0).val = M - 1

def IsCutLinkTop (M : ℕ) (x : Lat4 (2 * M)) (μ : Fin 4) : Prop :=
  μ = 0 ∧ (x 0).val = 2 * M - 1

def IsNegLink (M : ℕ) (x : Lat4 (2 * M)) (μ : Fin 4) : Prop :=
  M ≤ (x 0).val ∧ (μ = 0 → (x 0).val ≠ 2 * M - 1)

end Imscribing.YangMills.LatticeCutSplit4D

namespace Imscribing.YangMills.LatticeOSRP4D

open MeasureTheory
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D
open Imscribing.YangMills.LatticeRP4D
open Imscribing.YangMills.LatticeCutSplit4D

/-- Half-lattice link + cut auxiliary gauge variables. -/
abbrev HalfVar (N M : ℕ) : Type :=
  LinkConfig N (2 * M) × (Lat4 (2 * M) → GaugeGroup N)

/-- Glued gauge configuration on the `2 * M` torus built from `p, q : HalfVar N M`. -/
noncomputable def glueConfig {N M : ℕ} (p q : HalfVar N M) : LinkConfig N (2 * M) :=
  letI := Classical.propDecidable
  fun x μ =>
    if IsPosLink M x μ then p.1 x μ
    else if IsCutLinkMid M x μ then (p.2 x)⁻¹ * q.2 x
    else if IsCutLinkTop M x μ then (q.2 x)⁻¹ * p.2 x
    else linkReflect q.1 x μ

private lemma gaugeGroup_coe_inv {N : ℕ} (A : GaugeGroup N) :
    ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = star (A : Matrix (Fin N) (Fin N) ℂ) := by
  have h1 : (A : Matrix (Fin N) (Fin N) ℂ) * ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    change ((A * A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1
    simp
  have h2 : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp A.prop).1
  calc
    ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)
        = (star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ)) *
            ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) := by rw [h2, Matrix.one_mul]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) *
          ((A : Matrix (Fin N) (Fin N) ℂ) * ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)) := by
          rw [Matrix.mul_assoc]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) := by rw [h1, Matrix.mul_one]

private lemma realTrace_mul_comm {N : ℕ} (A B : GaugeGroup N) :
    realTrace (A * B) = realTrace (B * A) := by
  simp only [realTrace]
  change (Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ))).re =
    (Matrix.trace ((B : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ))).re
  rw [Matrix.trace_mul_comm]

private lemma realTrace_inv {N : ℕ} (A : GaugeGroup N) :
    realTrace A⁻¹ = realTrace A := by
  simp only [realTrace]
  change (Matrix.trace ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)).re =
    (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re
  rw [gaugeGroup_coe_inv]
  change (∑ i : Fin N, (star (A : Matrix (Fin N) (Fin N) ℂ)) i i).re =
    (∑ i : Fin N, (A : Matrix (Fin N) (Fin N) ℂ) i i).re
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Complex.conj_re _

private lemma realTrace_mul_inv_eq {N : ℕ} (A B : GaugeGroup N) :
    realTrace (A * B⁻¹) =
      ∑ i : Fin N, ∑ j : Fin N,
        (((A : Matrix (Fin N) (Fin N) ℂ) i j).re * ((B : Matrix (Fin N) (Fin N) ℂ) i j).re +
        ((A : Matrix (Fin N) (Fin N) ℂ) i j).im * ((B : Matrix (Fin N) (Fin N) ℂ) i j).im) := by
  simp only [realTrace]
  change (Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ) *
      ((B⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))).re = _
  rw [gaugeGroup_coe_inv]
  change (∑ i : Fin N, ∑ j : Fin N,
      (A : Matrix (Fin N) (Fin N) ℂ) i j * (star (B : Matrix (Fin N) (Fin N) ℂ)) j i).re = _
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ((A : Matrix (Fin N) (Fin N) ℂ) i j * star ((B : Matrix (Fin N) (Fin N) ℂ) i j)).re = _
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

private lemma zmod_2m_neZero (M : ℕ) [NeZero M] : NeZero (2 * M) :=
  ⟨Nat.mul_ne_zero (by decide) (NeZero.ne M)⟩

private lemma zmod_2m_self {M : ℕ} (n : ℕ) (h : n = 2 * M) :
    (n : ZMod (2 * M)) = 0 := by
  subst h; exact ZMod.natCast_self (2 * M)

private lemma reflectSite_zero_val {M : ℕ} [NeZero M] (x : Lat4 (2 * M)) :
    ((reflectSite (2 * M) x) 0).val = 2 * M - 1 - (x 0).val := by
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hM : 0 < M := NeZero.pos M
  have hx_lt : (x 0).val < 2 * M := ZMod.val_lt (x 0)
  simp only [reflectSite, ↓reduceIte]
  have hsub : ((x 0).val + (2 * M - 1 - (x 0).val) + 1 : ℕ) = 2 * M := by omega
  have hz : (((x 0).val + (2 * M - 1 - (x 0).val) + 1 : ℕ) : ZMod (2 * M)) = 0 :=
    zmod_2m_self _ hsub
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at hz
  have heq : -(x 0 + 1) = (((2 * M - 1 - (x 0).val : ℕ) : ZMod (2 * M))) := by
    linear_combination -hz
  rw [heq, ZMod.val_natCast_of_lt (by omega)]

private lemma reflectSite_sub_step0_zero_val {M : ℕ} [NeZero M] (x : Lat4 (2 * M))
    (hx : (x 0).val < 2 * M - 1) :
    ((reflectSite (2 * M) x - stepDir (2 * M) 0) 0).val = 2 * M - 2 - (x 0).val := by
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hM : 0 < M := NeZero.pos M
  simp only [reflectSite, stepDir, Pi.sub_apply, ↓reduceIte]
  have hsub : ((x 0).val + (2 * M - 2 - (x 0).val) + 2 : ℕ) = 2 * M := by omega
  have hz : (((x 0).val + (2 * M - 2 - (x 0).val) + 2 : ℕ) : ZMod (2 * M)) = 0 :=
    zmod_2m_self _ hsub
  simp only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val] at hz
  have heq : -(x 0 + 1) - 1 = (((2 * M - 2 - (x 0).val : ℕ) : ZMod (2 * M))) := by
    linear_combination -hz
  rw [heq, ZMod.val_natCast_of_lt (by omega)]

private lemma spatial_step_zero_eq {M : ℕ} (x : Lat4 (2 * M)) {ν : Fin 4} (hν : ν ≠ 0) :
    (x + stepDir (2 * M) ν) 0 = x 0 := by
  simp [stepDir, hν.symm]

private lemma reflectSite_add_step0_cutMid {M : ℕ} [NeZero M] (x : Lat4 (2 * M))
    (hx : (x 0).val = M - 1) :
    reflectSite (2 * M) (x + stepDir (2 * M) 0) = x := by
  have hM : 0 < M := NeZero.pos M
  ext ν
  by_cases hν : ν = 0
  · subst hν
    simp only [reflectSite, stepDir, Pi.add_apply, ↓reduceIte]
    have hsub : 2 * ((x 0).val + 1) = 2 * M := by omega
    have hz : ((2 * ((x 0).val + 1) : ℕ) : ZMod (2 * M)) = 0 := zmod_2m_self _ hsub
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      ZMod.natCast_zmod_val] at hz
    linear_combination -hz
  · simp [reflectSite, stepDir, hν]

private lemma reflectSite_cutTop {M : ℕ} [NeZero M] (x : Lat4 (2 * M))
    (hx : (x 0).val = 2 * M - 1) :
    reflectSite (2 * M) x = x + stepDir (2 * M) 0 := by
  have hM : 0 < M := NeZero.pos M
  ext ν
  by_cases hν : ν = 0
  · subst hν
    simp only [reflectSite, stepDir, Pi.add_apply, ↓reduceIte]
    have hsub : (x 0).val + 1 = 2 * M := by omega
    have hz : (((x 0).val + 1 : ℕ) : ZMod (2 * M)) = 0 := zmod_2m_self _ hsub
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at hz
    linear_combination -2 * hz
  · simp [reflectSite, stepDir, hν]

private lemma reflectSite_invol {M : ℕ} (x : Lat4 (2 * M)) :
    reflectSite (2 * M) (reflectSite (2 * M) x) = x := by
  ext ν
  by_cases hν : ν = 0
  · subst hν; simp [reflectSite]
  · simp [reflectSite, hν]

private lemma reflectSite_sub_step0_invol {M : ℕ} (x : Lat4 (2 * M)) :
    reflectSite (2 * M) (reflectSite (2 * M) x - stepDir (2 * M) 0) - stepDir (2 * M) 0 = x := by
  ext ν
  by_cases hν : ν = 0
  · subst hν; simp [reflectSite, stepDir]
  · simp [reflectSite, stepDir, hν]

private lemma reflectSite_add_step_spatial {M : ℕ} (x : Lat4 (2 * M)) {ν : Fin 4} (hν : ν ≠ 0) :
    reflectSite (2 * M) (x + stepDir (2 * M) ν) = reflectSite (2 * M) x + stepDir (2 * M) ν := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ; simp [reflectSite, stepDir, hν.symm]
  · simp [reflectSite, stepDir, hμ]

private lemma reflectSite_add_step0_sub {M : ℕ} (x : Lat4 (2 * M)) :
    reflectSite (2 * M) (x + stepDir (2 * M) 0) = reflectSite (2 * M) x - stepDir (2 * M) 0 := by
  ext ν
  by_cases hν : ν = 0
  · subst hν; simp [reflectSite, stepDir]; ring
  · simp [reflectSite, stepDir, hν]

private def isCutPlaq (M : ℕ) (t : Lat4 (2 * M) × Fin 4 × Fin 4) : Prop :=
  ((t.2.1 = 0 ∧ t.2.2 ≠ 0) ∨ (t.2.2 = 0 ∧ t.2.1 ≠ 0)) ∧
    ((t.1 0).val = M - 1 ∨ (t.1 0).val = 2 * M - 1)

private def isPosPlaq (M : ℕ) (t : Lat4 (2 * M) × Fin 4 × Fin 4) : Prop :=
  ¬ isCutPlaq M t ∧ (t.1 0).val < M

private def isNegPlaq (M : ℕ) (t : Lat4 (2 * M) × Fin 4 × Fin 4) : Prop :=
  ¬ isCutPlaq M t ∧ M ≤ (t.1 0).val

private def reflectPlaq (M : ℕ) (t : Lat4 (2 * M) × Fin 4 × Fin 4) :
    Lat4 (2 * M) × Fin 4 × Fin 4 :=
  if t.2.1 = 0 ∧ t.2.2 ≠ 0 then (reflectSite (2 * M) t.1 - stepDir (2 * M) 0, 0, t.2.2)
  else if t.2.2 = 0 ∧ t.2.1 ≠ 0 then (reflectSite (2 * M) t.1 - stepDir (2 * M) 0, t.2.1, 0)
  else (reflectSite (2 * M) t.1, t.2.1, t.2.2)

private lemma reflectPlaq_invol (M : ℕ) (t : Lat4 (2 * M) × Fin 4 × Fin 4) :
    reflectPlaq M (reflectPlaq M t) = t := by
  rcases t with ⟨x, μ, ν⟩
  dsimp [reflectPlaq]
  by_cases h1 : μ = 0 ∧ ν ≠ 0
  · simp [h1, reflectSite_sub_step0_invol]
  · by_cases h2 : ν = 0 ∧ μ ≠ 0
    · have h1' : ¬ (μ = 0 ∧ ν ≠ 0) := fun h => h2.2 h.1
      simp [h1, h2, h1', reflectSite_sub_step0_invol]
    · simp [h1, h2, reflectSite_invol]

private lemma reflectSite_sub_step0_cutTop_val {M : ℕ} [NeZero M] (x : Lat4 (2 * M))
    (htop : (x 0).val = 2 * M - 1) :
    ((reflectSite (2 * M) x - stepDir (2 * M) 0) 0).val = 2 * M - 1 := by
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hM : 0 < M := NeZero.pos M
  have h1 : x 0 + 1 = 0 := by
    have hsub : (x 0).val + 1 = 2 * M := by omega
    have hz : (((x 0).val + 1 : ℕ) : ZMod (2 * M)) = 0 := zmod_2m_self _ hsub
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at hz
    exact hz
  simp only [reflectSite, stepDir, Pi.sub_apply, ↓reduceIte]
  have hsub2 : (2 * M - 1 + 1 : ℕ) = 2 * M := by omega
  have hz2 : (((2 * M - 1 + 1 : ℕ)) : ZMod (2 * M)) = 0 := zmod_2m_self _ hsub2
  simp only [Nat.cast_add, Nat.cast_one] at hz2
  have heq : -(x 0 + 1) - 1 = (((2 * M - 1 : ℕ) : ZMod (2 * M))) := by
    linear_combination -hz2 - h1
  rw [heq, ZMod.val_natCast_of_lt (by omega)]

private lemma reflectPlaq_neg_iff_pos {M : ℕ} [NeZero M] (t : Lat4 (2 * M) × Fin 4 × Fin 4) :
    isNegPlaq M (reflectPlaq M t) ↔ isPosPlaq M t := by
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hM : 0 < M := NeZero.pos M
  rcases t with ⟨x, μ, ν⟩
  have hx_lt : (x 0).val < 2 * M := ZMod.val_lt (x 0)
  by_cases h1 : μ = 0 ∧ ν ≠ 0
  · obtain ⟨rfl, hν⟩ := h1
    have hc_iff : isCutPlaq M (reflectPlaq M (x, 0, ν)) ↔ isCutPlaq M (x, 0, ν) := by
      dsimp [reflectPlaq, isCutPlaq]
      simp only [hν, ne_eq, not_false_eq_true, and_self, ↓reduceIte, true_or, true_and]
      by_cases htop : (x 0).val = 2 * M - 1
      · have h0 := reflectSite_sub_step0_cutTop_val x htop
        simp only [Pi.sub_apply] at h0
        simp [htop, h0]
      · have hval := reflectSite_sub_step0_zero_val x (by omega)
        rw [hval]
        omega
    by_cases hcut : isCutPlaq M (x, 0, ν)
    · have hcut' : isCutPlaq M (reflectPlaq M (x, 0, ν)) := hc_iff.mpr hcut
      simp [isNegPlaq, isPosPlaq, hcut, hcut']
    · have hcut' : ¬ isCutPlaq M (reflectPlaq M (x, 0, ν)) := fun h => hcut (hc_iff.mp h)
      have hx_ne : (x 0).val ≠ 2 * M - 1 := fun h => hcut ⟨Or.inl ⟨rfl, hν⟩, Or.inr h⟩
      have hx_neM : (x 0).val ≠ M - 1 := fun h => hcut ⟨Or.inl ⟨rfl, hν⟩, Or.inl h⟩
      have hval := reflectSite_sub_step0_zero_val x (by omega)
      simp only [isNegPlaq, isPosPlaq, hcut, hcut', not_false_eq_true, true_and]
      dsimp [reflectPlaq]
      simp only [hν, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      rw [hval]
      constructor <;> intro h <;> omega
  · by_cases h2 : ν = 0 ∧ μ ≠ 0
    · obtain ⟨rfl, hμ⟩ := h2
      have h1' : ¬ (μ = 0 ∧ (0 : Fin 4) ≠ 0) := fun h => hμ h.1
      have hc_iff : isCutPlaq M (reflectPlaq M (x, μ, 0)) ↔ isCutPlaq M (x, μ, 0) := by
        dsimp [reflectPlaq, isCutPlaq]
        simp only [h1', false_and, ↓reduceIte, hμ, ne_eq, not_false_eq_true, and_self, or_true, true_and]
        by_cases htop : (x 0).val = 2 * M - 1
        · have h0 := reflectSite_sub_step0_cutTop_val x htop
          simp only [Pi.sub_apply] at h0
          simp [htop, h0]
        · have hval := reflectSite_sub_step0_zero_val x (by omega)
          rw [hval]
          omega
      by_cases hcut : isCutPlaq M (x, μ, 0)
      · have hcut' : isCutPlaq M (reflectPlaq M (x, μ, 0)) := hc_iff.mpr hcut
        simp [isNegPlaq, isPosPlaq, hcut, hcut']
      · have hcut' : ¬ isCutPlaq M (reflectPlaq M (x, μ, 0)) := fun h => hcut (hc_iff.mp h)
        have hx_ne : (x 0).val ≠ 2 * M - 1 := fun h => hcut ⟨Or.inr ⟨rfl, hμ⟩, Or.inr h⟩
        have hx_neM : (x 0).val ≠ M - 1 := fun h => hcut ⟨Or.inr ⟨rfl, hμ⟩, Or.inl h⟩
        have hval := reflectSite_sub_step0_zero_val x (by omega)
        simp only [isNegPlaq, isPosPlaq, hcut, hcut', not_false_eq_true, true_and]
        dsimp [reflectPlaq]
        simp only [h1', false_and, ↓reduceIte, hμ, ne_eq, not_false_eq_true, and_self]
        rw [hval]
        constructor <;> intro h <;> omega
    · have hcut : ¬ isCutPlaq M (x, μ, ν) := by
        rintro ⟨ha | hb, _⟩
        · exact h1 ha
        · exact h2 hb
      have hcut' : ¬ isCutPlaq M (reflectPlaq M (x, μ, ν)) := by
        dsimp [reflectPlaq, isCutPlaq]
        simp only [h1, h2, ↓reduceIte]
        rintro ⟨ha | hb, _⟩
        · exact ha.elim
        · exact hb.elim
      simp only [isNegPlaq, isPosPlaq, hcut, hcut', not_false_eq_true, true_and]
      dsimp [reflectPlaq]
      simp only [h1, h2, ↓reduceIte]
      rw [reflectSite_zero_val]
      constructor <;> intro h <;> omega

private lemma realTrace_plaquette_linkReflect {N M : ℕ} [NeZero N] [NeZero M]
    (U : LinkConfig N (2 * M)) (t : Lat4 (2 * M) × Fin 4 × Fin 4) :
    realTrace (plaquetteHolonomy (linkReflect U) t.1 t.2.1 t.2.2) =
      realTrace (plaquetteHolonomy U (reflectPlaq M t).1 (reflectPlaq M t).2.1 (reflectPlaq M t).2.2) := by
  rcases t with ⟨x, μ, ν⟩
  by_cases h1 : μ = 0 ∧ ν ≠ 0
  · obtain ⟨rfl, hν⟩ := h1
    dsimp [reflectPlaq]
    simp only [hν, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    set y := reflectSite (2 * M) x - stepDir (2 * M) 0
    have hy0 : reflectSite (2 * M) (x + stepDir (2 * M) 0) = y :=
      reflectSite_add_step0_sub x
    have hyν : reflectSite (2 * M) (x + stepDir (2 * M) ν) - stepDir (2 * M) 0 = y + stepDir (2 * M) ν := by
      dsimp [y]
      rw [reflectSite_add_step_spatial x hν]
      abel
    have h_l1 : linkReflect U x 0 = (U y 0)⁻¹ := by simp [linkReflect, y]
    have h_l2 : linkReflect U (x + stepDir (2 * M) 0) ν = U y ν := by
      simp [linkReflect, hν, hy0]
    have h_l3 : linkReflect U (x + stepDir (2 * M) ν) 0 = (U (y + stepDir (2 * M) ν) 0)⁻¹ := by
      simp [linkReflect, hyν]
    have h_l4 : linkReflect U x ν = U (y + stepDir (2 * M) 0) ν := by
      have hy0_eq : y + stepDir (2 * M) 0 = reflectSite (2 * M) x := by simp [y]
      simp [linkReflect, hν, hy0_eq]
    rw [plaquetteHolonomy, h_l1, h_l2, h_l3, h_l4, inv_inv]
    have hinv_p : (plaquetteHolonomy U y 0 ν)⁻¹ =
        U y ν * U (y + stepDir (2 * M) ν) 0 * (U (y + stepDir (2 * M) 0) ν)⁻¹ * (U y 0)⁻¹ := by
      simp only [plaquetteHolonomy, mul_inv_rev, inv_inv, mul_assoc]
    rw [← realTrace_inv (plaquetteHolonomy U y 0 ν), hinv_p]
    have hcomm : (U y 0)⁻¹ * U y ν * U (y + stepDir (2 * M) ν) 0 * (U (y + stepDir (2 * M) 0) ν)⁻¹ =
        (U y 0)⁻¹ * (U y ν * U (y + stepDir (2 * M) ν) 0 * (U (y + stepDir (2 * M) 0) ν)⁻¹) := by
      simp only [mul_assoc]
    rw [hcomm, realTrace_mul_comm]
  · by_cases h2 : ν = 0 ∧ μ ≠ 0
    · obtain ⟨rfl, hμ⟩ := h2
      have h1' : ¬ (μ = 0 ∧ (0 : Fin 4) ≠ 0) := fun h => hμ h.1
      dsimp [reflectPlaq]
      simp only [h1', ↓reduceIte, hμ, ne_eq, not_false_eq_true, and_self]
      set y := reflectSite (2 * M) x - stepDir (2 * M) 0
      have hy0 : reflectSite (2 * M) (x + stepDir (2 * M) 0) = y :=
        reflectSite_add_step0_sub x
      have hyμ : reflectSite (2 * M) (x + stepDir (2 * M) μ) - stepDir (2 * M) 0 = y + stepDir (2 * M) μ := by
        dsimp [y]
        rw [reflectSite_add_step_spatial x hμ]
        abel
      have hy0_eq : y + stepDir (2 * M) 0 = reflectSite (2 * M) x := by simp [y]
      have h_l1 : linkReflect U x μ = U (y + stepDir (2 * M) 0) μ := by simp [linkReflect, hμ, hy0_eq]
      have h_l2 : linkReflect U (x + stepDir (2 * M) μ) 0 = (U (y + stepDir (2 * M) μ) 0)⁻¹ := by
        simp [linkReflect, hyμ]
      have h_l3 : linkReflect U (x + stepDir (2 * M) 0) μ = U y μ := by
        simp [linkReflect, hμ, hy0]
      have h_l4 : linkReflect U x 0 = (U y 0)⁻¹ := by simp [linkReflect, y]
      rw [plaquetteHolonomy, h_l1, h_l2, h_l3, h_l4, inv_inv]
      have hswap : U (y + stepDir (2 * M) 0) μ * (U (y + stepDir (2 * M) μ) 0)⁻¹ * (U y μ)⁻¹ * U y 0 =
          (U (y + stepDir (2 * M) 0) μ * (U (y + stepDir (2 * M) μ) 0)⁻¹ * (U y μ)⁻¹) * U y 0 := by
        simp only [mul_assoc]
      rw [hswap, realTrace_mul_comm]
      have h_eq : U y 0 * (U (y + stepDir (2 * M) 0) μ * (U (y + stepDir (2 * M) μ) 0)⁻¹ * (U y μ)⁻¹) =
          plaquetteHolonomy U y 0 μ := by
        simp only [plaquetteHolonomy, mul_assoc]
      rw [h_eq]
      have hflip : plaquetteHolonomy U y μ 0 = (plaquetteHolonomy U y 0 μ)⁻¹ := by
        simp only [plaquetteHolonomy, mul_inv_rev, inv_inv, mul_assoc]
      simp only [false_and, ↓reduceIte]
      rw [hflip, realTrace_inv]
    · dsimp [reflectPlaq]
      simp only [h1, h2, ↓reduceIte]
      by_cases hμ0 : μ = 0
      · subst hμ0
        have hν0 : ν = 0 := by
          by_contra hne; exact h1 ⟨rfl, hne⟩
        subst hν0
        simp [plaquetteHolonomy]
      · by_cases hν0 : ν = 0
        · subst hν0
          exfalso; exact h2 ⟨rfl, hμ0⟩
        · have h_l1 : linkReflect U x μ = U (reflectSite (2 * M) x) μ := by simp [linkReflect, hμ0]
          have h_l2 : linkReflect U (x + stepDir (2 * M) μ) ν =
              U (reflectSite (2 * M) x + stepDir (2 * M) μ) ν := by
            simp [linkReflect, hν0, reflectSite_add_step_spatial x hμ0]
          have h_l3 : linkReflect U (x + stepDir (2 * M) ν) μ =
              U (reflectSite (2 * M) x + stepDir (2 * M) ν) μ := by
            simp [linkReflect, hμ0, reflectSite_add_step_spatial x hν0]
          have h_l4 : linkReflect U x ν = U (reflectSite (2 * M) x) ν := by simp [linkReflect, hν0]
          simp only [plaquetteHolonomy, h_l1, h_l2, h_l3, h_l4]

private def cutAmp {N M : ℕ} (x : Lat4 (2 * M)) (μ ν : Fin 4) (r : HalfVar N M) : GaugeGroup N :=
  let s : Fin 4 := if μ = 0 then ν else μ
  if (x 0).val = M - 1 then
    r.2 (x + stepDir (2 * M) s) * (r.1 x s)⁻¹ * (r.2 x)⁻¹
  else
    r.2 x * r.1 (x + stepDir (2 * M) 0) s * (r.2 (x + stepDir (2 * M) s))⁻¹

private lemma glueConfig_posPlaq_eq {N M : ℕ} [NeZero N] [NeZero M]
    (p q : HalfVar N M) {t : Lat4 (2 * M) × Fin 4 × Fin 4} (ht : isPosPlaq M t) :
    realTrace (plaquetteHolonomy (glueConfig p q) t.1 t.2.1 t.2.2) =
      realTrace (plaquetteHolonomy p.1 t.1 t.2.1 t.2.2) := by
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hM : 0 < M := NeZero.pos M
  rcases t with ⟨x, μ, ν⟩
  rcases ht with ⟨hncut, hx⟩
  dsimp only at hncut hx
  by_cases hμν : μ = ν
  · subst hμν; simp [plaquetteHolonomy]
  · by_cases h1 : μ = 0 ∧ ν ≠ 0
    · obtain ⟨rfl, hν⟩ := h1
      have hx_lt : (x 0).val < M - 1 := by
        by_contra hge
        apply hncut
        exact ⟨Or.inl ⟨rfl, hν⟩, Or.inl (by dsimp only; omega)⟩
      have h0_lt : ((x + stepDir (2 * M) 0) 0).val < M := by
        simp only [stepDir, Pi.add_apply, ↓reduceIte]
        have hlt : (x 0).val + 1 < 2 * M := by omega
        have heq : x 0 + 1 = (((x 0).val + 1 : ℕ) : ZMod (2 * M)) := by
          push_cast; rw [ZMod.natCast_zmod_val]
        rw [heq, ZMod.val_natCast_of_lt hlt]
        omega
      have hp1 : IsPosLink M x 0 := ⟨hx, fun _ => by omega⟩
      have hp2 : IsPosLink M (x + stepDir (2 * M) 0) ν := ⟨h0_lt, fun h => absurd h hν⟩
      have hp3 : IsPosLink M (x + stepDir (2 * M) ν) 0 := by
        rw [IsPosLink, spatial_step_zero_eq x hν]
        exact ⟨hx, fun _ => by omega⟩
      have hp4 : IsPosLink M x ν := ⟨hx, fun h => absurd h hν⟩
      simp only [plaquetteHolonomy, glueConfig, hp1, hp2, hp3, hp4, ↓reduceIte]
    · by_cases h2 : ν = 0 ∧ μ ≠ 0
      · obtain ⟨rfl, hμ⟩ := h2
        have hx_lt : (x 0).val < M - 1 := by
          by_contra hge
          apply hncut
          exact ⟨Or.inr ⟨rfl, hμ⟩, Or.inl (by dsimp only; omega)⟩
        have h0_lt : ((x + stepDir (2 * M) 0) 0).val < M := by
          simp only [stepDir, Pi.add_apply, ↓reduceIte]
          have hlt : (x 0).val + 1 < 2 * M := by omega
          have heq : x 0 + 1 = (((x 0).val + 1 : ℕ) : ZMod (2 * M)) := by
            push_cast; rw [ZMod.natCast_zmod_val]
          rw [heq, ZMod.val_natCast_of_lt hlt]
          omega
        have hp1 : IsPosLink M x μ := ⟨hx, fun h => absurd h hμ⟩
        have hp2 : IsPosLink M (x + stepDir (2 * M) μ) 0 := by
          rw [IsPosLink, spatial_step_zero_eq x hμ]
          exact ⟨hx, fun _ => by omega⟩
        have hp3 : IsPosLink M (x + stepDir (2 * M) 0) μ := ⟨h0_lt, fun h => absurd h hμ⟩
        have hp4 : IsPosLink M x 0 := ⟨hx, fun _ => by omega⟩
        simp only [plaquetteHolonomy, glueConfig, hp1, hp2, hp3, hp4, ↓reduceIte]
      · have hμ0 : μ ≠ 0 := fun h => h1 ⟨h, fun h0 => hμν (h.trans h0.symm)⟩
        have hν0 : ν ≠ 0 := fun h => h2 ⟨h, fun h0 => hμν (h0.trans h.symm)⟩
        have hp1 : IsPosLink M x μ := ⟨hx, fun h => absurd h hμ0⟩
        have hp2 : IsPosLink M (x + stepDir (2 * M) μ) ν := by
          rw [IsPosLink, spatial_step_zero_eq x hμ0]; exact ⟨hx, fun h => absurd h hν0⟩
        have hp3 : IsPosLink M (x + stepDir (2 * M) ν) μ := by
          rw [IsPosLink, spatial_step_zero_eq x hν0]; exact ⟨hx, fun h => absurd h hμ0⟩
        have hp4 : IsPosLink M x ν := ⟨hx, fun h => absurd h hν0⟩
        simp only [plaquetteHolonomy, glueConfig, hp1, hp2, hp3, hp4, ↓reduceIte]

private lemma glueConfig_negPlaq_eq {N M : ℕ} [NeZero N] [NeZero M]
    (p q : HalfVar N M) {t : Lat4 (2 * M) × Fin 4 × Fin 4} (ht : isNegPlaq M t) :
    realTrace (plaquetteHolonomy (glueConfig p q) t.1 t.2.1 t.2.2) =
      realTrace (plaquetteHolonomy (linkReflect q.1) t.1 t.2.1 t.2.2) := by
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hM : 0 < M := NeZero.pos M
  rcases t with ⟨x, μ, ν⟩
  rcases ht with ⟨hncut, hx⟩
  dsimp only at hncut hx
  have hneg_eval : ∀ y α, IsNegLink M y α → glueConfig p q y α = linkReflect q.1 y α := by
    intro y α hy
    have hnp : ¬ IsPosLink M y α := fun h => absurd h.1 (not_lt.mpr hy.1)
    have hncm : ¬ IsCutLinkMid M y α := fun ⟨_, heq⟩ => by have := hy.1; omega
    have hnct : ¬ IsCutLinkTop M y α := fun ⟨h0, heq⟩ => hy.2 h0 heq
    simp only [glueConfig, hnp, hncm, hnct, ↓reduceIte]
  by_cases hμν : μ = ν
  · subst hμν; simp [plaquetteHolonomy]
  · by_cases h1 : μ = 0 ∧ ν ≠ 0
    · obtain ⟨rfl, hν⟩ := h1
      have hx_lt : (x 0).val < 2 * M - 1 := by
        have hlt := ZMod.val_lt (x 0)
        by_contra hge
        apply hncut
        exact ⟨Or.inl ⟨rfl, hν⟩, Or.inr (by dsimp only; omega)⟩
      have h0_ge : M ≤ ((x + stepDir (2 * M) 0) 0).val := by
        simp only [stepDir, Pi.add_apply, ↓reduceIte]
        have hlt : (x 0).val + 1 < 2 * M := by omega
        have heq : x 0 + 1 = (((x 0).val + 1 : ℕ) : ZMod (2 * M)) := by
          push_cast; rw [ZMod.natCast_zmod_val]
        rw [heq, ZMod.val_natCast_of_lt hlt]
        omega
      have hn1 : IsNegLink M x 0 := ⟨hx, fun _ => by omega⟩
      have hn2 : IsNegLink M (x + stepDir (2 * M) 0) ν := ⟨h0_ge, fun h => absurd h hν⟩
      have hn3 : IsNegLink M (x + stepDir (2 * M) ν) 0 := by
        rw [IsNegLink, spatial_step_zero_eq x hν]
        exact ⟨hx, fun _ => by omega⟩
      have hn4 : IsNegLink M x ν := ⟨hx, fun h => absurd h hν⟩
      rw [plaquetteHolonomy, plaquetteHolonomy,
        hneg_eval _ _ hn1, hneg_eval _ _ hn2, hneg_eval _ _ hn3, hneg_eval _ _ hn4]
    · by_cases h2 : ν = 0 ∧ μ ≠ 0
      · obtain ⟨rfl, hμ⟩ := h2
        have hx_lt : (x 0).val < 2 * M - 1 := by
          have hlt := ZMod.val_lt (x 0)
          by_contra hge
          apply hncut
          exact ⟨Or.inr ⟨rfl, hμ⟩, Or.inr (by dsimp only; omega)⟩
        have h0_ge : M ≤ ((x + stepDir (2 * M) 0) 0).val := by
          simp only [stepDir, Pi.add_apply, ↓reduceIte]
          have hlt : (x 0).val + 1 < 2 * M := by omega
          have heq : x 0 + 1 = (((x 0).val + 1 : ℕ) : ZMod (2 * M)) := by
            push_cast; rw [ZMod.natCast_zmod_val]
          rw [heq, ZMod.val_natCast_of_lt hlt]
          omega
        have hn1 : IsNegLink M x μ := ⟨hx, fun h => absurd h hμ⟩
        have hn2 : IsNegLink M (x + stepDir (2 * M) μ) 0 := by
          rw [IsNegLink, spatial_step_zero_eq x hμ]
          exact ⟨hx, fun _ => by omega⟩
        have hn3 : IsNegLink M (x + stepDir (2 * M) 0) μ := ⟨h0_ge, fun h => absurd h hμ⟩
        have hn4 : IsNegLink M x 0 := ⟨hx, fun _ => by omega⟩
        rw [plaquetteHolonomy, plaquetteHolonomy,
          hneg_eval _ _ hn1, hneg_eval _ _ hn2, hneg_eval _ _ hn3, hneg_eval _ _ hn4]
      · have hμ0 : μ ≠ 0 := fun h => h1 ⟨h, fun h0 => hμν (h.trans h0.symm)⟩
        have hν0 : ν ≠ 0 := fun h => h2 ⟨h, fun h0 => hμν (h0.trans h.symm)⟩
        have hn1 : IsNegLink M x μ := ⟨hx, fun h => absurd h hμ0⟩
        have hn2 : IsNegLink M (x + stepDir (2 * M) μ) ν := by
          rw [IsNegLink, spatial_step_zero_eq x hμ0]; exact ⟨hx, fun h => absurd h hν0⟩
        have hn3 : IsNegLink M (x + stepDir (2 * M) ν) μ := by
          rw [IsNegLink, spatial_step_zero_eq x hν0]; exact ⟨hx, fun h => absurd h hμ0⟩
        have hn4 : IsNegLink M x ν := ⟨hx, fun h => absurd h hν0⟩
        rw [plaquetteHolonomy, plaquetteHolonomy,
          hneg_eval _ _ hn1, hneg_eval _ _ hn2, hneg_eval _ _ hn3, hneg_eval _ _ hn4]

private lemma glueConfig_cutPlaq_eq {N M : ℕ} [NeZero N] [NeZero M]
    (p q : HalfVar N M) {t : Lat4 (2 * M) × Fin 4 × Fin 4} (ht : isCutPlaq M t) :
    realTrace (plaquetteHolonomy (glueConfig p q) t.1 t.2.1 t.2.2) =
      realTrace (cutAmp t.1 t.2.1 t.2.2 p * (cutAmp t.1 t.2.1 t.2.2 q)⁻¹) := by
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hM : 0 < M := NeZero.pos M
  rcases t with ⟨x, μ, ν⟩
  rcases ht with ⟨hdir, htime⟩
  have h_mid : ∀ y, (y 0).val = M - 1 → glueConfig p q y 0 = (p.2 y)⁻¹ * q.2 y := by
    intro y hy
    have hnp : ¬ IsPosLink M y 0 := fun ⟨_, h⟩ => h rfl hy
    have hcm : IsCutLinkMid M y 0 := ⟨rfl, hy⟩
    simp only [glueConfig, hnp, hcm, ↓reduceIte]
  have h_top : ∀ y, (y 0).val = 2 * M - 1 → glueConfig p q y 0 = (q.2 y)⁻¹ * p.2 y := by
    intro y hy
    have hnp : ¬ IsPosLink M y 0 := fun ⟨h, _⟩ => by omega
    have hncm : ¬ IsCutLinkMid M y 0 := fun ⟨_, h⟩ => by omega
    have hct : IsCutLinkTop M y 0 := ⟨rfl, hy⟩
    simp only [glueConfig, hnp, hncm, hct, ↓reduceIte]
  have h_pos_sp : ∀ y s, s ≠ 0 → (y 0).val < M → glueConfig p q y s = p.1 y s := by
    intro y s hs hy
    have hp : IsPosLink M y s := ⟨hy, fun h => absurd h hs⟩
    simp only [glueConfig, hp, ↓reduceIte]
  have h_neg_sp : ∀ y s, s ≠ 0 → M ≤ (y 0).val →
      glueConfig p q y s = q.1 (reflectSite (2 * M) y) s := by
    intro y s hs hy
    have hnp : ¬ IsPosLink M y s := fun ⟨h, _⟩ => by omega
    have hncm : ¬ IsCutLinkMid M y s := fun ⟨h, _⟩ => hs h
    have hnct : ¬ IsCutLinkTop M y s := fun ⟨h, _⟩ => hs h
    simp only [glueConfig, hnp, hncm, hnct, ↓reduceIte, linkReflect, hs]
  have h_0ν : ∀ (ν : Fin 4), ν ≠ 0 → ((x 0).val = M - 1 ∨ (x 0).val = 2 * M - 1) →
      realTrace (plaquetteHolonomy (glueConfig p q) x 0 ν) =
        realTrace (cutAmp x 0 ν p * (cutAmp x 0 ν q)⁻¹) := by
    intro ν hν hx
    rcases hx with hxM | hxT
    · have hxs : ((x + stepDir (2 * M) ν) 0).val = M - 1 := by
        rw [spatial_step_zero_eq x hν, hxM]
      have hx0_val : ((x + stepDir (2 * M) 0) 0).val = M := by
        simp only [stepDir, Pi.add_apply, ↓reduceIte]
        have hlt : (x 0).val + 1 < 2 * M := by omega
        have heq : x 0 + 1 = (((x 0).val + 1 : ℕ) : ZMod (2 * M)) := by
          push_cast; rw [ZMod.natCast_zmod_val]
        rw [heq, ZMod.val_natCast_of_lt hlt]
        omega
      rw [plaquetteHolonomy, h_mid x hxM, h_neg_sp _ ν hν (by omega),
        h_mid _ hxs, h_pos_sp x ν hν (by omega),
        reflectSite_add_step0_cutMid x hxM]
      simp only [cutAmp, ↓reduceIte, hxM, mul_inv_rev, inv_inv]
      have hassoc : (p.2 x)⁻¹ * q.2 x * q.1 x ν * ((q.2 (x + stepDir (2 * M) ν))⁻¹ * p.2 (x + stepDir (2 * M) ν)) *
            (p.1 x ν)⁻¹ =
          (p.2 x)⁻¹ * (q.2 x * q.1 x ν * (q.2 (x + stepDir (2 * M) ν))⁻¹ *
            p.2 (x + stepDir (2 * M) ν) * (p.1 x ν)⁻¹) := by
        simp only [mul_assoc]
      rw [hassoc, realTrace_mul_comm]
      have hassoc2 : (q.2 x * q.1 x ν * (q.2 (x + stepDir (2 * M) ν))⁻¹ *
            p.2 (x + stepDir (2 * M) ν) * (p.1 x ν)⁻¹) * (p.2 x)⁻¹ =
          (q.2 x * q.1 x ν * (q.2 (x + stepDir (2 * M) ν))⁻¹) *
            (p.2 (x + stepDir (2 * M) ν) * (p.1 x ν)⁻¹ * (p.2 x)⁻¹) := by
        simp only [mul_assoc]
      rw [hassoc2, realTrace_mul_comm]
      simp only [mul_assoc]
    · have hxs : ((x + stepDir (2 * M) ν) 0).val = 2 * M - 1 := by
        rw [spatial_step_zero_eq x hν, hxT]
      have hx0_val : ((x + stepDir (2 * M) 0) 0).val = 0 := by
        simp only [stepDir, Pi.add_apply, ↓reduceIte]
        have hsub : (x 0).val + 1 = 2 * M := by omega
        have hz : (((x 0).val + 1 : ℕ) : ZMod (2 * M)) = 0 := zmod_2m_self _ hsub
        simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at hz
        rw [hz, ZMod.val_zero]
      rw [plaquetteHolonomy, h_top x hxT, h_pos_sp _ ν hν (by omega),
        h_top _ hxs, h_neg_sp x ν hν (by omega), reflectSite_cutTop x hxT]
      have hxne : (x 0).val ≠ M - 1 := by omega
      simp only [cutAmp, ↓reduceIte, hxne, mul_inv_rev, inv_inv]
      have hassoc : (q.2 x)⁻¹ * p.2 x * p.1 (x + stepDir (2 * M) 0) ν *
            ((p.2 (x + stepDir (2 * M) ν))⁻¹ * q.2 (x + stepDir (2 * M) ν)) *
            (q.1 (x + stepDir (2 * M) 0) ν)⁻¹ =
          (q.2 x)⁻¹ * (p.2 x * p.1 (x + stepDir (2 * M) 0) ν * (p.2 (x + stepDir (2 * M) ν))⁻¹ *
            q.2 (x + stepDir (2 * M) ν) * (q.1 (x + stepDir (2 * M) 0) ν)⁻¹) := by
        simp only [mul_assoc]
      rw [hassoc, realTrace_mul_comm]
      simp only [mul_assoc]
  rcases hdir with ⟨rfl, hν⟩ | ⟨rfl, hμ⟩
  · exact h_0ν ν hν htime
  · have hμ0 : μ ≠ 0 := hμ
    have hflip : plaquetteHolonomy (glueConfig p q) x μ 0 =
        (plaquetteHolonomy (glueConfig p q) x 0 μ)⁻¹ := by
      simp only [plaquetteHolonomy, mul_inv_rev, inv_inv, mul_assoc]
    rw [hflip, realTrace_inv, h_0ν μ hμ0 htime]
    simp only [cutAmp, hμ0, ↓reduceIte]

private noncomputable def posAction (N M : ℕ) [NeZero N] [NeZero M] (β : ℝ) (p : HalfVar N M) : ℝ :=
  letI := Classical.propDecidable
  β * ∑ t : Lat4 (2 * M) × Fin 4 × Fin 4,
    if isPosPlaq M t then 1 - realTrace (plaquetteHolonomy p.1 t.1 t.2.1 t.2.2) / (N : ℝ) else 0

private lemma posAction_nonneg {N M : ℕ} [NeZero N] [NeZero M] {β : ℝ} (hβ : 0 ≤ β)
    (p : HalfVar N M) :
    0 ≤ posAction N M β p := by
  classical
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  unfold posAction
  refine mul_nonneg hβ (Finset.sum_nonneg fun t _ => ?_)
  split_ifs
  · exact (plaquette_density_bounds _).1
  · exact le_rfl

private lemma wilsonAction_glue_split {N M : ℕ} [NeZero N] [NeZero M] (β : ℝ)
    (p q : HalfVar N M) :
    letI := Classical.propDecidable
    wilsonAction N (2 * M) β (glueConfig p q) =
      posAction N M β p + posAction N M β q +
      β * ((Finset.univ.filter (isCutPlaq M)).card : ℝ) -
      (β / (N : ℝ)) * ∑ t ∈ Finset.univ.filter (isCutPlaq M),
        realTrace (cutAmp t.1 t.2.1 t.2.2 p * (cutAmp t.1 t.2.1 t.2.2 q)⁻¹) := by
  letI := Classical.propDecidable
  let term : LinkConfig N (2 * M) → Lat4 (2 * M) × Fin 4 × Fin 4 → ℝ := fun U t =>
    1 - realTrace (plaquetteHolonomy U t.1 t.2.1 t.2.2) / (N : ℝ)
  have h_w : wilsonAction N (2 * M) β (glueConfig p q) =
      β * ∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, term (glueConfig p q) t := by
    unfold wilsonAction
    congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    convert rfl
  have h_part :
      (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, term (glueConfig p q) t) =
      (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isPosPlaq M t then term (glueConfig p q) t else 0) +
      (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isNegPlaq M t then term (glueConfig p q) t else 0) +
      (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isCutPlaq M t then term (glueConfig p q) t else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hc : isCutPlaq M t
    · have hnp : ¬ isPosPlaq M t := fun h => h.1 hc
      have hnn : ¬ isNegPlaq M t := fun h => h.1 hc
      simp [hc, hnp, hnn]
    · by_cases hp : (t.1 0).val < M
      · have hpos : isPosPlaq M t := ⟨hc, hp⟩
        have hnn : ¬ isNegPlaq M t := fun h => absurd hp (not_lt.mpr h.2)
        simp [hc, hpos, hnn]
      · have hneg : isNegPlaq M t := ⟨hc, not_lt.mp hp⟩
        have hnp : ¬ isPosPlaq M t := fun h => hp h.2
        simp [hc, hneg, hnp]
  have h_pos_mul :
      β * (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isPosPlaq M t then term (glueConfig p q) t else 0) =
      posAction N M β p := by
    unfold posAction
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · simp [term, glueConfig_posPlaq_eq p q ht]
    · rfl
  have h_neg_mul :
      β * (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isNegPlaq M t then term (glueConfig p q) t else 0) =
      posAction N M β q := by
    have h_eq1 :
        (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isNegPlaq M t then term (glueConfig p q) t else 0) =
        ∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isNegPlaq M t then term (linkReflect q.1) t else 0 := by
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs with ht
      · simp [term, glueConfig_negPlaq_eq p q ht]
      · rfl
    let e : (Lat4 (2 * M) × Fin 4 × Fin 4) ≃ (Lat4 (2 * M) × Fin 4 × Fin 4) :=
      { toFun := reflectPlaq M
        invFun := reflectPlaq M
        left_inv := reflectPlaq_invol M
        right_inv := reflectPlaq_invol M }
    have h_eq2 :
        (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isNegPlaq M t then term (linkReflect q.1) t else 0) =
        ∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isPosPlaq M t then term q.1 t else 0 := by
      rw [← Fintype.sum_equiv e _ (fun s => if isPosPlaq M s then term q.1 s else 0)]
      intro t
      have hp_iff : isPosPlaq M (reflectPlaq M t) ↔ isNegPlaq M t := by
        have := reflectPlaq_neg_iff_pos (M := M) (reflectPlaq M t)
        rw [reflectPlaq_invol] at this
        exact this.symm
      dsimp [e]
      by_cases hneg : isNegPlaq M t
      · have hpos : isPosPlaq M (reflectPlaq M t) := hp_iff.mpr hneg
        simp [hneg, hpos, term, realTrace_plaquette_linkReflect]
      · have hnpos : ¬ isPosPlaq M (reflectPlaq M t) := fun h => hneg (hp_iff.mp h)
        simp [hneg, hnpos]
    rw [h_eq1, h_eq2]
    unfold posAction
    convert rfl
  have h_cut_mul :
      β * (∑ t : Lat4 (2 * M) × Fin 4 × Fin 4, if isCutPlaq M t then term (glueConfig p q) t else 0) =
      β * ((Finset.univ.filter (isCutPlaq M)).card : ℝ) -
      (β / (N : ℝ)) * ∑ t ∈ Finset.univ.filter (isCutPlaq M),
        realTrace (cutAmp t.1 t.2.1 t.2.2 p * (cutAmp t.1 t.2.1 t.2.2 q)⁻¹) := by
    rw [← Finset.sum_filter]
    have h_eq :
        (∑ t ∈ Finset.univ.filter (isCutPlaq M), term (glueConfig p q) t) =
        ((Finset.univ.filter (isCutPlaq M)).card : ℝ) -
        (∑ t ∈ Finset.univ.filter (isCutPlaq M),
          realTrace (cutAmp t.1 t.2.1 t.2.2 p * (cutAmp t.1 t.2.1 t.2.2 q)⁻¹)) / (N : ℝ) := by
      have h1 : ∀ t ∈ Finset.univ.filter (isCutPlaq M), term (glueConfig p q) t =
          1 - realTrace (cutAmp t.1 t.2.1 t.2.2 p * (cutAmp t.1 t.2.1 t.2.2 q)⁻¹) / (N : ℝ) := by
        intro t ht
        simp [term, glueConfig_cutPlaq_eq p q (Finset.mem_filter.mp ht).2]
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        ← Finset.sum_div]
    rw [h_eq]
    ring
  rw [h_w, h_part, mul_add, mul_add, h_pos_mul, h_neg_mul, h_cut_mul, ← add_sub_assoc]

private lemma sum_range_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), y ^ k / (k.factorial : ℝ))
      (∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ)) t := by
  have h_eq : (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), y ^ k / (k.factorial : ℝ)) =
      fun y => (1 : ℝ) + ∑ k ∈ Finset.range n, y ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    funext y
    rw [Finset.sum_range_succ']
    simp [add_comm]
  rw [h_eq]
  have hs : HasDerivAt
      (fun y : ℝ => ∑ k ∈ Finset.range n, y ^ (k + 1) / ((k + 1).factorial : ℝ))
      (∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ)) t := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have hk := (hasDerivAt_pow (k + 1) t).div_const (((k + 1).factorial : ℝ))
    convert hk using 1
    rw [Nat.factorial_succ]
    push_cast
    have hne : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hne]
  exact hs.const_add (1 : ℝ)

private lemma exp_rem_nonneg (n : ℕ) :
    ∀ t : ℝ, 0 ≤ t → ∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ) ≤ Real.exp t := by
  induction n with
  | zero => intro t _; simp [(Real.exp_pos t).le]
  | succ n ih =>
    intro t ht
    let R : ℝ → ℝ := fun y => Real.exp y - ∑ k ∈ Finset.range (n + 1), y ^ k / (k.factorial : ℝ)
    have hR0 : R 0 = 0 := by simp [R, Finset.sum_range_succ']
    have hderiv : ∀ y : ℝ,
        HasDerivAt R (Real.exp y - ∑ k ∈ Finset.range n, y ^ k / (k.factorial : ℝ)) y :=
      fun y => (Real.hasDerivAt_exp y).sub (sum_range_hasDerivAt n y)
    have hint : R t = ∫ y in (0 : ℝ)..t,
        (Real.exp y - ∑ k ∈ Finset.range n, y ^ k / (k.factorial : ℝ)) := by
      have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
        (fun y _ => hderiv y) (Continuous.intervalIntegrable (Real.continuous_exp.sub
          (continuous_finset_sum _ fun k _ => (continuous_pow k).div_const _)) 0 t)
      rw [hR0, sub_zero] at hsub
      exact hsub.symm
    have h_nn : 0 ≤ R t := by
      rw [hint]
      exact intervalIntegral.integral_nonneg ht fun y hy => sub_nonneg.mpr (ih y hy.1)
    exact sub_nonneg.mp h_nn

private lemma exp_taylor_remainder_bound :
    ∀ (n : ℕ) (x : ℝ),
      ‖Real.exp x - ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)‖ ≤
        Real.exp |x| * |x| ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro x
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one, Nat.factorial_zero,
      Nat.cast_one, div_one, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (le_abs_self x)
  | succ n ih =>
    intro x
    let R : ℝ → ℝ := fun t => Real.exp t - ∑ k ∈ Finset.range (n + 1), t ^ k / (k.factorial : ℝ)
    have hR0 : R 0 = 0 := by simp [R, Finset.sum_range_succ']
    have hderiv : ∀ t : ℝ,
        HasDerivAt R (Real.exp t - ∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ)) t :=
      fun t => (Real.hasDerivAt_exp t).sub (sum_range_hasDerivAt n t)
    have hint_eq : R x = ∫ t in (0 : ℝ)..x,
        (Real.exp t - ∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ)) := by
      have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
        (fun t _ => hderiv t) (Continuous.intervalIntegrable (Real.continuous_exp.sub
          (continuous_finset_sum _ fun k _ => (continuous_pow k).div_const _)) 0 x)
      rw [hR0, sub_zero] at hsub
      exact hsub.symm
    rw [show Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ) = R x from rfl,
      hint_eq]
    have h_int_pow : ∀ b : ℝ, ∫ t in (0 : ℝ)..b, t ^ n = b ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
      intro b
      have hp : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) (t ^ n) t := by
        intro t
        have := (hasDerivAt_pow (n + 1) t).div_const (((n + 1 : ℕ) : ℝ))
        convert this using 1
        have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        simp only [Nat.add_sub_cancel]
        field_simp [hne]
      have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := b)
        (fun t _ => hp t) (Continuous.intervalIntegrable (continuous_pow n) 0 b)
      rw [hsub, zero_pow (Nat.succ_ne_zero n), zero_div, sub_zero]
    by_cases hx0 : 0 ≤ x
    · have hbound : ∀ t ∈ Set.Icc (0 : ℝ) x,
          ‖Real.exp t - ∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ)‖ ≤
            Real.exp |x| * t ^ n / (n.factorial : ℝ) := by
        intro t ht
        refine le_trans (ih t) ?_
        rw [abs_of_nonneg ht.1]
        have h1 : Real.exp t ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_trans ht.2 (le_abs_self x))
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (pow_nonneg ht.1 n)) (Nat.cast_nonneg _)
      have h_norm : ‖∫ t in (0 : ℝ)..x,
          (Real.exp t - ∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ))‖ ≤
          ∫ t in (0 : ℝ)..x, Real.exp |x| * t ^ n / (n.factorial : ℝ) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hx0 ?_
          (Continuous.intervalIntegrable (by continuity) 0 x)
        refine Filter.Eventually.of_forall fun t ht => ?_
        exact hbound t ⟨ht.1.le, ht.2⟩
      refine le_trans h_norm ?_
      have h_eq : (∫ t in (0 : ℝ)..x, Real.exp |x| * t ^ n / (n.factorial : ℝ)) =
          (Real.exp |x| / (n.factorial : ℝ)) * ∫ t in (0 : ℝ)..x, t ^ n := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => by ring
      rw [h_eq, h_int_pow x, abs_of_nonneg hx0, Nat.factorial_succ, Nat.cast_mul]
      apply le_of_eq; field_simp
    · have hxlt : x < 0 := lt_of_not_ge hx0
      have hbound : ∀ t ∈ Set.Icc x (0 : ℝ),
          ‖Real.exp t - ∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ)‖ ≤
            Real.exp |x| * (-t) ^ n / (n.factorial : ℝ) := by
        intro t ht
        refine le_trans (ih t) ?_
        rw [abs_of_nonpos ht.2]
        have h1 : Real.exp (-t) ≤ Real.exp |x| := by
          rw [abs_of_neg hxlt]
          exact Real.exp_le_exp.mpr (neg_le_neg ht.1)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (pow_nonneg (neg_nonneg.mpr ht.2) n)) (Nat.cast_nonneg _)
      rw [intervalIntegral.integral_symm x 0, norm_neg]
      have h_norm : ‖∫ t in x..(0 : ℝ),
          (Real.exp t - ∑ k ∈ Finset.range n, t ^ k / (k.factorial : ℝ))‖ ≤
          ∫ t in x..(0 : ℝ), Real.exp |x| * (-t) ^ n / (n.factorial : ℝ) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hxlt.le ?_
          (Continuous.intervalIntegrable (by continuity) x 0)
        refine Filter.Eventually.of_forall fun t ht => ?_
        exact hbound t ⟨ht.1.le, ht.2⟩
      refine le_trans h_norm ?_
      have h_int_neg : ∫ t in x..(0 : ℝ), (-t) ^ n = (-x) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
        rw [intervalIntegral.integral_comp_neg (fun u : ℝ => u ^ n), neg_zero, h_int_pow (-x)]
      have h_eq : (∫ t in x..(0 : ℝ), Real.exp |x| * (-t) ^ n / (n.factorial : ℝ)) =
          (Real.exp |x| / (n.factorial : ℝ)) * ∫ t in x..(0 : ℝ), (-t) ^ n := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => by ring
      rw [h_eq, h_int_neg, abs_of_neg hxlt, Nat.factorial_succ, Nat.cast_mul]
      apply le_of_eq; field_simp

private lemma tendsto_const_pow_div_factorial (C : ℝ) (hC : 0 ≤ C) :
    Filter.Tendsto (fun n : ℕ => C ^ n / (n.factorial : ℝ)) Filter.atTop (nhds 0) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * C)
  have h_bound : ∀ n : ℕ, N₀ ≤ n →
      C ^ n / (n.factorial : ℝ) ≤ (C ^ N₀ / (N₀.factorial : ℝ)) * ((1 / 2 : ℝ) ^ (n - N₀)) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_sub_cancel_left]
    induction m with
    | zero => simp
    | succ m ih =>
      have ih' := ih (Nat.le_add_right N₀ m)
      have h1 : C ^ (N₀ + (m + 1)) / ((N₀ + (m + 1)).factorial : ℝ) =
          (C / ((N₀ + m + 1 : ℕ) : ℝ)) * (C ^ (N₀ + m) / ((N₀ + m).factorial : ℝ)) := by
        rw [← add_assoc, pow_succ, Nat.factorial_succ, Nat.cast_mul]
        ring
      have h2 : C / ((N₀ + m + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
        have hpos : (0 : ℝ) < ((N₀ + m + 1 : ℕ) : ℝ) := by positivity
        rw [div_le_div_iff₀ hpos two_pos]
        have hm : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        push_cast; linarith
      rw [h1]
      calc (C / ((N₀ + m + 1 : ℕ) : ℝ)) * (C ^ (N₀ + m) / ((N₀ + m).factorial : ℝ))
          ≤ (1 / 2) * ((C ^ N₀ / (N₀.factorial : ℝ)) * (1 / 2) ^ m) :=
            mul_le_mul h2 ih' (by positivity) (by positivity)
        _ = (C ^ N₀ / (N₀.factorial : ℝ)) * (1 / 2) ^ (m + 1) := by
            rw [pow_succ]; ring
  have h_half : Filter.Tendsto (fun n : ℕ => (C ^ N₀ / (N₀.factorial : ℝ)) * (1 / 2 : ℝ) ^ (n - N₀))
      Filter.atTop (nhds 0) := by
    have ht : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hshift : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n - N₀)) Filter.atTop (nhds 0) :=
      ht.comp (Filter.tendsto_sub_atTop_nat N₀)
    simpa using tendsto_const_nhds.mul hshift
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => by positivity)
    (Filter.eventually_atTop.mpr ⟨N₀, h_bound⟩) h_half

/-- **Finite-Volume 4D SU(N) Reflection Positivity.** -/
theorem wilson4D_reflection_positivity
    {N M : ℕ} [NeZero N] [NeZero M] {β : ℝ} (hβ : 0 ≤ β)
    [MeasurableSpace (GaugeGroup N)] [MeasurableMul₂ (GaugeGroup N)] [MeasurableInv (GaugeGroup N)]
    (hEntry : ∀ i j : Fin N, Measurable (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ) i j))
    (μ : Measure (HalfVar N M)) [IsFiniteMeasure μ]
    (F : HalfVar N M → ℂ) (hF_meas : Measurable F) (BF : ℝ) (hBF : 0 ≤ BF)
    (hF_bound : ∀ p : HalfVar N M, ‖F p‖ ≤ BF) :
    0 ≤ (∫ p, ∫ q, star (F p) * F q *
      (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ).re := by
  classical
  haveI : NeZero (2 * M) := zmod_2m_neZero M
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have h_cutAmp_meas : ∀ (x : Lat4 (2 * M)) (μ_d ν_d : Fin 4),
      Measurable (fun r : HalfVar N M => cutAmp x μ_d ν_d r) := by
    intro x μ_d ν_d
    unfold cutAmp
    have hm_fst : ∀ y α, Measurable (fun r : HalfVar N M => r.1 y α) := fun y α =>
      ((measurable_pi_apply α).comp
        (measurable_pi_apply y : Measurable fun U : LinkConfig N (2 * M) => U y)).comp measurable_fst
    have hm_snd : ∀ y, Measurable (fun r : HalfVar N M => r.2 y) := fun y =>
      (measurable_pi_apply y).comp measurable_snd
    set s : Fin 4 := if μ_d = 0 then ν_d else μ_d
    by_cases hM1 : (x 0).val = M - 1
    · simp only [hM1, ↓reduceIte]
      exact ((hm_snd _).mul (hm_fst _ _).inv).mul (hm_snd _).inv
    · simp only [hM1, ↓reduceIte]
      exact ((hm_snd _).mul (hm_fst _ _)).mul (hm_snd _).inv
  have h_posAct_meas : Measurable (posAction N M β) := by
    unfold posAction
    refine measurable_const.mul (Finset.measurable_sum _ fun t _ => ?_)
    split_ifs
    · refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
      unfold plaquetteHolonomy
      have hm_fst : ∀ y α, Measurable (fun r : HalfVar N M => r.1 y α) := fun y α =>
        ((measurable_pi_apply α).comp
          (measurable_pi_apply y : Measurable fun U : LinkConfig N (2 * M) => U y)).comp measurable_fst
      have ml1 := hm_fst t.1 t.2.1
      have ml2 := hm_fst (t.1 + stepDir (2 * M) t.2.1) t.2.2
      have ml3 := (hm_fst (t.1 + stepDir (2 * M) t.2.2) t.2.1).inv
      have ml4 := (hm_fst t.1 t.2.2).inv
      have mprod := ((ml1.mul ml2).mul ml3).mul ml4
      change Measurable (fun r : HalfVar N M =>
        Matrix.trace ((plaquetteHolonomy r.1 t.1 t.2.1 t.2.2 : GaugeGroup N) :
          Matrix (Fin N) (Fin N) ℂ))
      simp only [Matrix.trace, Matrix.diag_apply]
      exact Finset.measurable_sum _ fun k _ => (hEntry k k).comp mprod
    · exact measurable_const
  let G : HalfVar N M → ℂ := fun p => F p * (Real.exp (-posAction N M β p) : ℂ)
  have hG_meas : Measurable G :=
    hF_meas.mul (Complex.continuous_ofReal.measurable.comp (Real.continuous_exp.measurable.comp h_posAct_meas.neg))
  have hG_bound : ∀ p : HalfVar N M, ‖G p‖ ≤ BF := by
    intro p
    dsimp [G]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hexp_le : Real.exp (-posAction N M β p) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (posAction_nonneg hβ p))
    calc ‖F p‖ * Real.exp (-posAction N M β p)
        ≤ BF * 1 := mul_le_mul (hF_bound p) hexp_le (Real.exp_pos _).le hBF
      _ = BF := mul_one BF
  let sCut := Finset.univ.filter (isCutPlaq M)
  let CutIdx := sCut × Fin N × Fin N × Bool
  let φ : CutIdx → HalfVar N M → ℝ := fun ⟨⟨t, _⟩, i, j, b⟩ r =>
    let Z := (cutAmp t.1 t.2.1 t.2.2 r : Matrix (Fin N) (Fin N) ℂ) i j
    if b then Z.im else Z.re
  have hφ_meas : ∀ α : CutIdx, Measurable (φ α) := by
    rintro ⟨⟨t, _⟩, i, j, b⟩
    dsimp [φ]
    have hE := (hEntry i j).comp (h_cutAmp_meas t.1 t.2.1 t.2.2)
    cases b
    · exact Complex.continuous_re.measurable.comp hE
    · exact Complex.continuous_im.measurable.comp hE
  have hφ_bound : ∀ α : CutIdx, ∀ p : HalfVar N M, |φ α p| ≤ 1 := by
    rintro ⟨⟨t, _⟩, i, j, b⟩ p
    dsimp [φ]
    have hnorm := gaugeGroup_entry_norm_le_one (cutAmp t.1 t.2.1 t.2.2 p) i j
    cases b
    · exact le_trans (Complex.abs_re_le_norm _) hnorm
    · exact le_trans (Complex.abs_im_le_norm _) hnorm
  let K_sum : HalfVar N M → HalfVar N M → ℝ := fun p q =>
    ∑ α : CutIdx, φ α p * φ α q
  have h_cut_eq : ∀ p q : HalfVar N M,
      (∑ t ∈ sCut, realTrace (cutAmp t.1 t.2.1 t.2.2 p * (cutAmp t.1 t.2.1 t.2.2 q)⁻¹)) =
        K_sum p q := by
    intro p q
    dsimp [K_sum]
    rw [← Finset.sum_coe_sort sCut (fun t => realTrace (cutAmp t.1 t.2.1 t.2.2 p * (cutAmp t.1 t.2.1 t.2.2 q)⁻¹))]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [realTrace_mul_inv_eq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    dsimp [φ]
    ring
  let r : ℝ := β / (N : ℝ)
  have hr : 0 ≤ r := div_nonneg hβ hN_pos.le
  let K_cut : HalfVar N M → HalfVar N M → ℝ := fun p q => r * K_sum p q
  let C_bd : ℝ := r * (Fintype.card CutIdx : ℝ)
  have hC_bd : 0 ≤ C_bd := mul_nonneg hr (Nat.cast_nonneg _)
  have hK_cut_meas : Measurable (fun pq : HalfVar N M × HalfVar N M => K_cut pq.1 pq.2) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun α _ => ?_)
    exact ((hφ_meas α).comp measurable_fst).mul ((hφ_meas α).comp measurable_snd)
  have hK_cut_bound : ∀ p q : HalfVar N M, |K_cut p q| ≤ C_bd := by
    intro p q
    dsimp [K_cut, C_bd]
    rw [abs_mul, abs_of_nonneg hr]
    refine mul_le_mul_of_nonneg_left ?_ hr
    calc |∑ α : CutIdx, φ α p * φ α q|
        ≤ ∑ α : CutIdx, |φ α p * φ α q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _α : CutIdx, (1 : ℝ) := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [abs_mul]
          simpa using mul_le_mul (hφ_bound α p) (hφ_bound α q) (abs_nonneg _) zero_le_one
      _ = (Fintype.card CutIdx : ℝ) := by simp [Finset.sum_const]
  have h_pow : ∀ k : ℕ, ∃ (ι_k : Type) (_ : Fintype ι_k) (ψ : ι_k → HalfVar N M → ℝ),
      (∀ i, Measurable (ψ i)) ∧ (∀ i p, |ψ i p| ≤ 1) ∧
      ∀ p q, (K_sum p q) ^ k = ∑ i : ι_k, ψ i p * ψ i q := by
    intro k
    induction k with
    | zero =>
      exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => measurable_const,
        fun _ _ => by norm_num, fun _ _ => by simp⟩
    | succ k ih =>
      obtain ⟨ι_k, _, ψ_k, hm_k, hb_k, hsum_k⟩ := ih
      refine ⟨ι_k × CutIdx, inferInstance, fun ⟨i, α⟩ p => ψ_k i p * φ α p,
        fun ⟨i, α⟩ => (hm_k i).mul (hφ_meas α),
        fun ⟨i, α⟩ p => by
          rw [abs_mul]
          simpa using mul_le_mul (hb_k i p) (hφ_bound α p) (abs_nonneg _) zero_le_one,
        fun p q => ?_⟩
      rw [pow_succ, hsum_k p q, Fintype.sum_prod_type, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => ?_
      ring
  let S_K : ℕ → HalfVar N M → HalfVar N M → ℝ := fun K p q =>
    ∑ k ∈ Finset.range K, (K_cut p q) ^ k / (k.factorial : ℝ)
  have hS_K_nonneg : ∀ K : ℕ,
      0 ≤ (∫ p, ∫ q, star (G p) * G q * (S_K K p q : ℂ) ∂μ ∂μ).re := by
    intro K
    have h_term_int : ∀ (k : ℕ) (p : HalfVar N M),
        Integrable (fun q : HalfVar N M =>
          star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) μ := by
      intro k p
      refine Integrable.of_bound ?_ (BF * BF * (C_bd ^ k / (k.factorial : ℝ)))
        (Filter.Eventually.of_forall fun q => ?_)
      · exact ((measurable_const.mul hG_meas).mul
          (Complex.continuous_ofReal.measurable.comp
            (((hK_cut_meas.comp (measurable_const.prodMk measurable_id)).pow_const k).div_const _))).aestronglyMeasurable
      · rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow]
        rw [abs_of_nonneg (a := (k.factorial : ℝ)) (Nat.cast_nonneg _)]
        have h1 : ‖G p‖ * ‖G q‖ ≤ BF * BF :=
          mul_le_mul (hG_bound p) (hG_bound q) (norm_nonneg _) hBF
        have h2 : |K_cut p q| ^ k / (k.factorial : ℝ) ≤ C_bd ^ k / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hK_cut_bound p q) k)
            (Nat.cast_nonneg _)
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have h_inner_eq : ∀ p : HalfVar N M,
        (∫ q, star (G p) * G q * (S_K K p q : ℂ) ∂μ) =
        ∑ k ∈ Finset.range K, ∫ q, star (G p) * G q *
          (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ := by
      intro p
      have h_eq : (fun q => star (G p) * G q * (S_K K p q : ℂ)) =
          fun q => ∑ k ∈ Finset.range K, star (G p) * G q *
            (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := by
        funext q
        dsimp [S_K]
        push_cast
        rw [Finset.mul_sum]
      rw [h_eq]
      exact integral_finset_sum _ fun k _ => h_term_int k p
    have h_outer_int : ∀ k : ℕ,
        Integrable (fun p : HalfVar N M =>
          ∫ q, star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ) μ := by
      intro k
      have h_meas_outer : Measurable (fun p : HalfVar N M =>
          ∫ q, star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ) := by
        obtain ⟨ι_k, _, ψ, hm, hb, hsum⟩ := h_pow k
        have h_eq : (fun p : HalfVar N M =>
            ∫ q, star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ) =
            fun p => ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
              ∑ i : ι_k, star (G p) * (ψ i p : ℂ) * ∫ q, G q * (ψ i q : ℂ) ∂μ := by
          funext p
          have h_q_eq : (fun q => star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) =
              fun q => ∑ i : ι_k, ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
                (star (G p) * (ψ i p : ℂ) * (G q * (ψ i q : ℂ))) := by
            funext q
            dsimp [K_cut]
            rw [mul_pow, hsum p q]
            push_cast
            rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
          rw [h_q_eq, integral_finset_sum _ fun i _ => ?_, Finset.mul_sum]
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [integral_const_mul, integral_const_mul]
          · refine Integrable.of_bound ?_
              ((r ^ k / (k.factorial : ℝ)) * (BF * 1 * (BF * 1)))
              (Filter.Eventually.of_forall fun q => ?_)
            · exact (measurable_const.mul (measurable_const.mul (hG_meas.mul (Complex.continuous_ofReal.measurable.comp (hm i))))).aestronglyMeasurable
            · simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
              rw [abs_of_nonneg (by positivity)]
              have hGp := hG_bound p; have hGq := hG_bound q
              have hbp := hb i p; have hbq := hb i q
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul (mul_le_mul hGp hbp (abs_nonneg _) hBF)
                (mul_le_mul hGq hbq (abs_nonneg _) hBF) (by positivity) (by positivity)
        rw [h_eq]
        refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
        exact ((continuous_star.measurable.comp hG_meas).mul
          (Complex.continuous_ofReal.measurable.comp (hm i))).mul measurable_const
      refine Integrable.of_bound h_meas_outer.aestronglyMeasurable
        (BF * BF * (C_bd ^ k / (k.factorial : ℝ)) * (μ Set.univ).toReal)
        (Filter.Eventually.of_forall fun p => ?_)
      refine le_trans (norm_integral_le_integral_norm _) ?_
      have h_pt : ∀ q, ‖star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ≤
          BF * BF * (C_bd ^ k / (k.factorial : ℝ)) := by
        intro q
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow]
        rw [abs_of_nonneg (a := (k.factorial : ℝ)) (Nat.cast_nonneg _)]
        have h1 : ‖G p‖ * ‖G q‖ ≤ BF * BF :=
          mul_le_mul (hG_bound p) (hG_bound q) (norm_nonneg _) hBF
        have h2 : |K_cut p q| ^ k / (k.factorial : ℝ) ≤ C_bd ^ k / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hK_cut_bound p q) k)
            (Nat.cast_nonneg _)
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
      calc ∫ q, ‖star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)‖ ∂μ
          ≤ ∫ _q, BF * BF * (C_bd ^ k / (k.factorial : ℝ)) ∂μ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall h_pt)
        _ = BF * BF * (C_bd ^ k / (k.factorial : ℝ)) * (μ Set.univ).toReal := by
            rw [integral_const, Measure.real_def, smul_eq_mul]; ring
    simp_rw [h_inner_eq]
    rw [integral_finset_sum _ fun k _ => h_outer_int k, Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    obtain ⟨ι_k, _, ψ, hm, hb, hsum⟩ := h_pow k
    have h_int_ψ : ∀ i : ι_k, Integrable (fun q : HalfVar N M => G q * (ψ i q : ℂ)) μ := by
      intro i
      refine Integrable.of_bound
        (hG_meas.mul (Complex.continuous_ofReal.measurable.comp (hm i))).aestronglyMeasurable
        BF (Filter.Eventually.of_forall fun q => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖G q‖ * |ψ i q| ≤ BF * 1 := mul_le_mul (hG_bound q) (hb i q) (abs_nonneg _) hBF
        _ = BF := mul_one BF
    have h_k_eq :
        (∫ p, ∫ q, star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ ∂μ) =
        ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
          ∑ i : ι_k, star (∫ p, G p * (ψ i p : ℂ) ∂μ) * (∫ q, G q * (ψ i q : ℂ) ∂μ) := by
      have h_in : ∀ p : HalfVar N M,
          (∫ q, star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ) =
          ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
            ∑ i : ι_k, star (G p) * (ψ i p : ℂ) * ∫ q, G q * (ψ i q : ℂ) ∂μ := by
        intro p
        have h_q_eq : (fun q => star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) =
            fun q => ∑ i : ι_k, ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
              (star (G p) * (ψ i p : ℂ) * (G q * (ψ i q : ℂ))) := by
          funext q
          dsimp [K_cut]
          rw [mul_pow, hsum p q]
          push_cast
          rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [h_q_eq, integral_finset_sum _ fun i _ => ((h_int_ψ i).const_mul _).const_mul _,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_const_mul]
      simp_rw [h_in, integral_const_mul]
      congr 1
      have h_int_conj : ∀ i : ι_k,
          Integrable (fun p : HalfVar N M =>
            star (G p) * (ψ i p : ℂ) * ∫ q, G q * (ψ i q : ℂ) ∂μ) μ := by
        intro i
        have hstar : Integrable (fun p : HalfVar N M => star (G p * (ψ i p : ℂ))) μ :=
          (Complex.conjCLE.toContinuousLinearMap).integrable_comp (h_int_ψ i)
        have h_eq : (fun p : HalfVar N M => star (G p * (ψ i p : ℂ))) =
            fun p => star (G p) * (ψ i p : ℂ) := by
          funext p; rw [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm]
        rw [h_eq] at hstar
        exact hstar.mul_const _
      rw [integral_finset_sum _ fun i _ => h_int_conj i]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
      congr 1
      change (∫ p, star (G p) * (ψ i p : ℂ) ∂μ) =
        Complex.conjCLE.toContinuousLinearMap (∫ q, G q * (ψ i q : ℂ) ∂μ)
      rw [← Complex.conjCLE.toContinuousLinearMap.integral_comp_comm (h_int_ψ i)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      change star (G p) * (ψ i p : ℂ) = star (G p * (ψ i p : ℂ))
      conv_rhs => rw [star_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, mul_comm]
    rw [h_k_eq]
    have hre : (((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
        ∑ i : ι_k, star (∫ p, G p * (ψ i p : ℂ) ∂μ) * (∫ q, G q * (ψ i q : ℂ) ∂μ)).re =
        (r ^ k / (k.factorial : ℝ)) *
          ∑ i : ι_k, Complex.normSq (∫ p, G p * (ψ i p : ℂ) ∂μ) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hz : (star (∫ p, G p * (ψ i p : ℂ) ∂μ) * (∫ q, G q * (ψ i q : ℂ) ∂μ)).re =
          Complex.normSq (∫ p, G p * (ψ i p : ℂ) ∂μ) := by
        rw [mul_comm, show star (∫ p, G p * (ψ i p : ℂ) ∂μ) = starRingEnd ℂ _ from rfl,
          Complex.mul_conj]
        simp
      exact hz
    rw [hre]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  have hS_K_le_exp : ∀ K : ℕ, ∀ p q : HalfVar N M, |S_K K p q| ≤ Real.exp C_bd := by
    intro K p q
    have h_tri : |S_K K p q| ≤ ∑ k ∈ Finset.range K, C_bd ^ k / (k.factorial : ℝ) := by
      dsimp [S_K]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_div, abs_pow]
      rw [abs_of_nonneg (a := (k.factorial : ℝ)) (Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hK_cut_bound p q) k)
        (Nat.cast_nonneg _)
    exact le_trans h_tri (exp_rem_nonneg K C_bd hC_bd)
  have hS_K_lim : ∀ p q : HalfVar N M,
      Filter.Tendsto (fun K : ℕ => S_K K p q) Filter.atTop (nhds (Real.exp (K_cut p q))) := by
    intro p q
    have h_err : ∀ K : ℕ, ‖Real.exp (K_cut p q) - S_K K p q‖ ≤
        Real.exp C_bd * (C_bd ^ K / (K.factorial : ℝ)) := by
      intro K
      refine le_trans (exp_taylor_remainder_bound K (K_cut p q)) ?_
      rw [mul_div_assoc]
      exact mul_le_mul (Real.exp_le_exp.mpr (hK_cut_bound p q))
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hK_cut_bound p q) K)
          (Nat.cast_nonneg _)) (by positivity) (Real.exp_pos _).le
    have h_rhs0 : Filter.Tendsto (fun K : ℕ => Real.exp C_bd * (C_bd ^ K / (K.factorial : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_const_pow_div_factorial C_bd hC_bd)
    have h_diff0 : Filter.Tendsto (fun K : ℕ => S_K K p q - Real.exp (K_cut p q))
        Filter.atTop (nhds 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero (fun _ => norm_nonneg _) (fun K => ?_) h_rhs0)
      rw [norm_sub_rev]
      exact h_err K
    simpa using h_diff0.add (tendsto_const_nhds (x := Real.exp (K_cut p q)))
  let F_K : ℕ → HalfVar N M → ℂ := fun K p =>
    ∫ q, star (G p) * G q * (S_K K p q : ℂ) ∂μ
  let F_inf : HalfVar N M → ℂ := fun p =>
    ∫ q, star (G p) * G q * (Real.exp (K_cut p q) : ℂ) ∂μ
  have hF_K_lim : ∀ p : HalfVar N M,
      Filter.Tendsto (fun K : ℕ => F_K K p) Filter.atTop (nhds (F_inf p)) := by
    intro p
    refine tendsto_integral_of_dominated_convergence (fun _ => BF * BF * Real.exp C_bd)
      (fun K => ((measurable_const.mul hG_meas).mul
        (Complex.continuous_ofReal.measurable.comp
          (Finset.measurable_sum _ fun k _ =>
            (((hK_cut_meas.comp (measurable_const.prodMk measurable_id)).pow_const k).div_const _)))).aestronglyMeasurable)
      (integrable_const _)
      (fun K => Filter.Eventually.of_forall fun q => ?_)
      (Filter.Eventually.of_forall fun q => ?_)
    · rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul (hG_bound p) (hG_bound q) (norm_nonneg _) hBF)
        (hS_K_le_exp K p q) (abs_nonneg _) (by positivity)
    · exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp (hS_K_lim p q))
  have h_outer_lim :
      Filter.Tendsto (fun K : ℕ => ∫ p, F_K K p ∂μ) Filter.atTop (nhds (∫ p, F_inf p ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun _ => BF * BF * Real.exp C_bd * (μ Set.univ).toReal)
      (fun K => ?_) (integrable_const _) (fun K => Filter.Eventually.of_forall fun p => ?_)
      (Filter.Eventually.of_forall hF_K_lim)
    · have hmeas_k : Measurable (F_K K) := by
        have h_eq : F_K K = fun p =>
            ∑ k ∈ Finset.range K, ∫ q, star (G p) * G q *
              (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ := by
          funext p
          dsimp [F_K, S_K]
          simp only [Complex.ofReal_sum, Finset.mul_sum]
          refine integral_finset_sum _ fun k _ => Integrable.of_bound ?_
            (BF * BF * (C_bd ^ k / (k.factorial : ℝ))) (Filter.Eventually.of_forall fun q => ?_)
          · exact ((measurable_const.mul hG_meas).mul
              (Complex.continuous_ofReal.measurable.comp
                (((hK_cut_meas.comp (measurable_const.prodMk measurable_id)).pow_const k).div_const _))).aestronglyMeasurable
          · simp only [norm_mul, norm_star, Complex.norm_conj, Complex.norm_real,
              Real.norm_eq_abs, abs_div, abs_pow]
            rw [abs_of_nonneg (a := (k.factorial : ℝ)) (Nat.cast_nonneg _)]
            exact mul_le_mul (mul_le_mul (hG_bound p) (hG_bound q) (norm_nonneg _) hBF)
              (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hK_cut_bound p q) k)
                (Nat.cast_nonneg _)) (by positivity) (by positivity)
        rw [h_eq]
        refine Finset.measurable_sum _ fun k _ => ?_
        obtain ⟨ι_k, _, ψ, hm, hb, hsum⟩ := h_pow k
        have h_term_eq : (fun p : HalfVar N M =>
            ∫ q, star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) ∂μ) =
            fun p => ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
              ∑ i : ι_k, star (G p) * (ψ i p : ℂ) * ∫ q, G q * (ψ i q : ℂ) ∂μ := by
          funext p
          have h_q_eq : (fun q => star (G p) * G q * (((K_cut p q) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) =
              fun q => ∑ i : ι_k, ((r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
                (star (G p) * (ψ i p : ℂ) * (G q * (ψ i q : ℂ))) := by
            funext q; dsimp [K_cut]; rw [mul_pow, hsum p q]; push_cast
            rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
          rw [h_q_eq, integral_finset_sum _ fun i _ => ?_, Finset.mul_sum]
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [integral_const_mul, integral_const_mul]
          · refine Integrable.of_bound
              (measurable_const.mul (measurable_const.mul (hG_meas.mul (Complex.continuous_ofReal.measurable.comp (hm i))))).aestronglyMeasurable
              ((r ^ k / (k.factorial : ℝ)) * (BF * 1 * (BF * 1)))
              (Filter.Eventually.of_forall fun q => by
                simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
                rw [abs_of_nonneg (by positivity)]
                have hGp := hG_bound p; have hGq := hG_bound q
                have hbp := hb i p; have hbq := hb i q
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul (mul_le_mul hGp hbp (abs_nonneg _) hBF)
                  (mul_le_mul hGq hbq (abs_nonneg _) hBF) (by positivity) (by positivity))
        rw [h_term_eq]
        refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
        exact ((continuous_star.measurable.comp hG_meas).mul
          (Complex.continuous_ofReal.measurable.comp (hm i))).mul measurable_const
      exact hmeas_k.aestronglyMeasurable
    · refine le_trans (norm_integral_le_integral_norm _) ?_
      calc ∫ q, ‖star (G p) * G q * (S_K K p q : ℂ)‖ ∂μ
          ≤ ∫ _q, BF * BF * Real.exp C_bd ∂μ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall fun q => by
                dsimp only
                rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
                exact mul_le_mul (mul_le_mul (hG_bound p) (hG_bound q) (norm_nonneg _) hBF)
                  (hS_K_le_exp K p q) (abs_nonneg _) (by positivity))
        _ = BF * BF * Real.exp C_bd * (μ Set.univ).toReal := by
            rw [integral_const, Measure.real_def, smul_eq_mul]; ring
  have h_re_lim : Filter.Tendsto (fun K : ℕ => (∫ p, F_K K p ∂μ).re) Filter.atTop
      (nhds (∫ p, F_inf p ∂μ).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp h_outer_lim
  have h_inf_nonneg : 0 ≤ (∫ p, F_inf p ∂μ).re :=
    ge_of_tendsto h_re_lim (Filter.Eventually.of_forall fun K => hS_K_nonneg K)
  let c0 : ℝ := Real.exp (-(β * (sCut.card : ℝ)))
  have hc0 : 0 ≤ c0 := (Real.exp_pos _).le
  have h_final_eq :
      (∫ p, ∫ q, star (F p) * F q *
        (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ) =
      (c0 : ℂ) * (∫ p, F_inf p ∂μ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp [F_inf]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    have h_split : wilsonAction N (2 * M) β (glueConfig p q) =
        posAction N M β p + posAction N M β q + β * (sCut.card : ℝ) - r * K_sum p q := by
      have h_wsplit := wilsonAction_glue_split β p q
      have h_flt : ∀ (inst1 : Fintype (Lat4 (2 * M) × Fin 4 × Fin 4))
          (inst2 : DecidablePred (isCutPlaq M)),
          @Finset.filter _ (isCutPlaq M) inst2 (@Finset.univ _ inst1) = sCut := by
        intro inst1 inst2
        ext t
        simp [sCut]
      rw [h_flt _ _] at h_wsplit
      rw [h_wsplit, h_cut_eq p q]
    rw [h_split]
    have hexp_eq : Real.exp (-(posAction N M β p + posAction N M β q +
        β * (sCut.card : ℝ) - r * K_sum p q)) =
        c0 * Real.exp (-posAction N M β p) * Real.exp (-posAction N M β q) *
          Real.exp (K_cut p q) := by
      dsimp [c0, K_cut, r]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    rw [hexp_eq]
    simp only [G, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [h_final_eq]
  have h_mul_re : ((c0 : ℂ) * (∫ p, F_inf p ∂μ)).re = c0 * (∫ p, F_inf p ∂μ).re := by
    simp [Complex.mul_re]
  rw [h_mul_re]
  exact mul_nonneg hc0 h_inf_nonneg

end Imscribing.YangMills.LatticeOSRP4D