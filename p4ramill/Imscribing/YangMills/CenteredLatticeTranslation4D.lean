import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Imscribing.YangMills.ClayStatement
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure
import Imscribing.YangMills.WilsonLattice4D
import Imscribing.YangMills.LatticeRiemannSchwartzBound4D

noncomputable section

namespace Imscribing.YangMills.CenteredLattice4D

/-- Centered integer representative in `[-L/2, L/2)` for `i : ZMod L`. -/
def centeredCoord (L : ℕ) [NeZero L] (i : ZMod L) : ℤ :=
  let v : ℤ := (i.val : ℤ)
  if 2 * v < (L : ℤ) then v else v - (L : ℤ)

lemma centeredCoord_abs_le {L : ℕ} [NeZero L] (i : ZMod L) :
    |centeredCoord L i| ≤ (L : ℤ) / 2 := by
  dsimp [centeredCoord]
  have hL : (0 : ℤ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hi0 : 0 ≤ (i.val : ℤ) := Int.natCast_nonneg _
  have hiL : (i.val : ℤ) < L := Int.ofNat_lt.mpr (ZMod.val_lt i)
  split_ifs with h
  · rw [abs_of_nonneg hi0]; omega
  · rw [abs_of_neg (by omega)]; omega

lemma centeredCoord_sub_exact {L : ℕ} [NeZero L] (i j : ZMod L)
    (hi : |centeredCoord L i| < (L : ℤ) / 4)
    (hj : |centeredCoord L j| < (L : ℤ) / 4) :
    centeredCoord L (i - j) = centeredCoord L i - centeredCoord L j := by
  have hL : (0 : ℤ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have h_mod : ((centeredCoord L (i - j) : ℤ) : ZMod L) =
      (((centeredCoord L i - centeredCoord L j : ℤ)) : ZMod L) := by
    have hc : ∀ k : ZMod L, (centeredCoord L k : ZMod L) = k := by
      intro k
      dsimp [centeredCoord]
      split_ifs <;> simp [ZMod.natCast_zmod_val]
    push_cast [hc]; rfl
  have h_dvd : (L : ℤ) ∣ centeredCoord L (i - j) - (centeredCoord L i - centeredCoord L j) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [h_mod]; simp
  have h_abs_ij : |centeredCoord L (i - j)| ≤ (L : ℤ) / 2 := centeredCoord_abs_le (i - j)
  rcases h_dvd with ⟨q, hq⟩
  have h1 := abs_le.mp h_abs_ij
  have h2 := abs_lt.mp hi
  have h3 := abs_lt.mp hj
  have hdiv : 2 * ((L : ℤ) / 4) + (L : ℤ) / 2 ≤ L := by omega
  have hq0 : q = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : q ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ q := by omega
      nlinarith
  rw [hq0, mul_zero] at hq; linarith

/-- Centered 4D lattice site coordinates `(Fin 4 → ℤ)`. -/
def centeredLatSite (L : ℕ) [NeZero L] (x : Fin 4 → ZMod L) : Fin 4 → ℤ :=
  fun μ => centeredCoord L (x μ)

lemma centeredLatSite_sub_exact {L : ℕ} [NeZero L] (x y : Fin 4 → ZMod L)
    (hx : ∀ μ, |centeredCoord L (x μ)| < (L : ℤ) / 4)
    (hy : ∀ μ, |centeredCoord L (y μ)| < (L : ℤ) / 4) (μ : Fin 4) :
    centeredLatSite L (x - y) μ = centeredLatSite L x μ - centeredLatSite L y μ :=
  centeredCoord_sub_exact (x μ) (y μ) (hx μ) (hy μ)

end Imscribing.YangMills.CenteredLattice4D

namespace Imscribing.YangMills.CenteredTranslation4D

open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.LatticeRiemann4D

abbrev centeredCoord := Imscribing.YangMills.CenteredLattice4D.centeredCoord

/-- Centered embedding `Lat4 L → Spacetime4` at lattice spacing `a`. -/
def centeredLatSite (L : ℕ) [NeZero L] (a : ℝ) (x : Lat4 L) : Spacetime4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm (fun μ => a * (centeredCoord L (x μ) : ℝ))

theorem centeredLatSite_sub_exact (L : ℕ) [NeZero L] (a : ℝ) (x v : Lat4 L)
    (h_small : ∀ μ : Fin 4,
      |centeredCoord L (x μ)| < (L : ℤ) / 4 ∧ |centeredCoord L (v μ)| < (L : ℤ) / 4) :
    centeredLatSite L a (x - v) = centeredLatSite L a x - centeredLatSite L a v := by
  ext μ
  change a * (centeredCoord L (x μ - v μ) : ℝ) =
    a * (centeredCoord L (x μ) : ℝ) - a * (centeredCoord L (v μ) : ℝ)
  dsimp only [centeredCoord]
  rw [Imscribing.YangMills.CenteredLattice4D.centeredCoord_sub_exact (x μ) (v μ)
    (h_small μ).1 (h_small μ).2]
  push_cast; ring

private lemma centeredCoord_coe (L : ℕ) [NeZero L] (v : ZMod L) :
    ((centeredCoord L v : ℤ) : ZMod L) = v := by
  dsimp [centeredCoord, Imscribing.YangMills.CenteredLattice4D.centeredCoord]
  split_ifs <;> simp [ZMod.natCast_zmod_val]

private lemma centeredCoord_eq_zero_iff (L : ℕ) [NeZero L] (v : ZMod L) :
    centeredCoord L v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 := centeredCoord_coe L v
    rw [h, Int.cast_zero] at h1
    exact h1.symm
  · intro h
    subst h
    have hL : (0 : ℤ) < L := Nat.cast_pos.mpr (NeZero.pos L)
    simp [centeredCoord, Imscribing.YangMills.CenteredLattice4D.centeredCoord, hL]

/-- **1D Centered Riemann Sum Bound:**
    `∑ v : ZMod L, a / (1 + a * |centeredCoord L v|)² ≤ 8` for `0 < a ≤ 1`. -/
theorem centered_1d_riemann_le_eight (L : ℕ) [NeZero L] {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∑ v : ZMod L, a / (1 + a * |(centeredCoord L v : ℝ)|) ^ 2 ≤ 8 := by
  classical
  let f : ZMod L → ℝ := fun v => a / (1 + a * |(centeredCoord L v : ℝ)|) ^ 2
  have hf_nn : ∀ v, 0 ≤ f v := fun _ => by positivity
  let S_pos := Finset.univ.filter (fun v : ZMod L => 0 < centeredCoord L v)
  let S_neg := Finset.univ.filter (fun v : ZMod L => centeredCoord L v < 0)
  have h_sum_split : (∑ v : ZMod L, f v) = f 0 + (∑ v ∈ S_pos, f v) + ∑ v ∈ S_neg, f v := by
    have h0_not_pos : (0 : ZMod L) ∉ S_pos := by
      simp [S_pos, (centeredCoord_eq_zero_iff L 0).mpr rfl]
    have h0_not_neg : (0 : ZMod L) ∉ S_neg := by
      simp [S_neg, (centeredCoord_eq_zero_iff L 0).mpr rfl]
    have h_disj1 : Disjoint ({0} : Finset (ZMod L)) S_pos := by
      rw [Finset.disjoint_singleton_left]; exact h0_not_pos
    have h_disj2 : Disjoint ({0} ∪ S_pos) S_neg := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [S_pos, S_neg, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv1 hv2
      rcases hv1 with rfl | hpos
      · rw [(centeredCoord_eq_zero_iff L 0).mpr rfl] at hv2
        exact lt_irrefl 0 hv2
      · omega
    have huniv : (Finset.univ : Finset (ZMod L)) = ({0} ∪ S_pos) ∪ S_neg := by
      ext v
      simp only [S_pos, S_neg, Finset.mem_univ, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_filter, true_and, true_iff]
      rcases lt_trichotomy (centeredCoord L v) 0 with hlt | heq | hgt
      · exact Or.inr hlt
      · exact Or.inl (Or.inl ((centeredCoord_eq_zero_iff L v).mp heq))
      · exact Or.inl (Or.inr hgt)
    rw [huniv, Finset.sum_union h_disj2, Finset.sum_union h_disj1, Finset.sum_singleton]
  have hf0 : f 0 ≤ 1 := by
    dsimp [f]
    rw [(centeredCoord_eq_zero_iff L 0).mpr rfl]
    simp [ha1]
  have h_pos_bound : ∀ n : ℕ, a / (1 + a * (n : ℝ)) ^ 2 ≤ a / (1 + (a * (n : ℝ)) ^ 2) := by
    intro n
    refine div_le_div_of_nonneg_left ha0.le (by positivity) ?_
    have hnn : 0 ≤ a * (n : ℝ) := by positivity
    nlinarith
  have hS_pos_le : (∑ v ∈ S_pos, f v) ≤ 3 := by
    let g : ℕ → ℝ := fun n => a / (1 + a * (n : ℝ)) ^ 2
    have h_eq : (∑ v ∈ S_pos, f v) = ∑ v ∈ S_pos, g (centeredCoord L v).natAbs := by
      refine Finset.sum_congr rfl fun v hv => ?_
      have hpos : 0 < centeredCoord L v := (Finset.mem_filter.mp hv).2
      dsimp [f, g]
      have habs : |(centeredCoord L v : ℝ)| = ((centeredCoord L v).natAbs : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      rw [habs]
    have hinj : ∀ v₁ ∈ S_pos, ∀ v₂ ∈ S_pos,
        (centeredCoord L v₁).natAbs = (centeredCoord L v₂).natAbs → v₁ = v₂ := by
      intro v₁ hv₁ v₂ hv₂ hnat
      have hp1 : 0 < centeredCoord L v₁ := (Finset.mem_filter.mp hv₁).2
      have hp2 : 0 < centeredCoord L v₂ := (Finset.mem_filter.mp hv₂).2
      have heqZ : centeredCoord L v₁ = centeredCoord L v₂ := by omega
      rw [← centeredCoord_coe L v₁, ← centeredCoord_coe L v₂, heqZ]
    have himg : S_pos.image (fun v => (centeredCoord L v).natAbs) ⊆ Finset.Icc 1 L := by
      intro n hn
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
      have hp : 0 < centeredCoord L v := (Finset.mem_filter.mp hv).2
      have hbd : |centeredCoord L v| ≤ (L : ℤ) / 2 :=
        Imscribing.YangMills.CenteredLattice4D.centeredCoord_abs_le v
      rw [abs_of_pos hp] at hbd
      rw [Finset.mem_Icc]
      omega
    rw [h_eq, ← Finset.sum_image hinj]
    calc (∑ n ∈ S_pos.image (fun v => (centeredCoord L v).natAbs), g n)
        ≤ ∑ n ∈ Finset.Icc 1 L, g n :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun n _ _ => by dsimp [g]; positivity
      _ ≤ ∑ n ∈ Finset.Icc 1 L, a / (1 + (a * (n : ℝ)) ^ 2) :=
          Finset.sum_le_sum fun n _ => h_pos_bound n
      _ ≤ 3 := oneD_lattice_riemann_inv_sq_le_four a ha0 ha1 L
  have hS_neg_le : (∑ v ∈ S_neg, f v) ≤ 3 := by
    let g : ℕ → ℝ := fun n => a / (1 + a * (n : ℝ)) ^ 2
    have h_eq : (∑ v ∈ S_neg, f v) = ∑ v ∈ S_neg, g (centeredCoord L v).natAbs := by
      refine Finset.sum_congr rfl fun v hv => ?_
      dsimp [f, g]
      have habs : |(centeredCoord L v : ℝ)| = ((centeredCoord L v).natAbs : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      rw [habs]
    have hinj : ∀ v₁ ∈ S_neg, ∀ v₂ ∈ S_neg,
        (centeredCoord L v₁).natAbs = (centeredCoord L v₂).natAbs → v₁ = v₂ := by
      intro v₁ hv₁ v₂ hv₂ hnat
      have hn1 : centeredCoord L v₁ < 0 := (Finset.mem_filter.mp hv₁).2
      have hn2 : centeredCoord L v₂ < 0 := (Finset.mem_filter.mp hv₂).2
      have heqZ : centeredCoord L v₁ = centeredCoord L v₂ := by omega
      rw [← centeredCoord_coe L v₁, ← centeredCoord_coe L v₂, heqZ]
    have himg : S_neg.image (fun v => (centeredCoord L v).natAbs) ⊆ Finset.Icc 1 L := by
      intro n hn
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
      have hneg : centeredCoord L v < 0 := (Finset.mem_filter.mp hv).2
      have hbd : |centeredCoord L v| ≤ (L : ℤ) / 2 :=
        Imscribing.YangMills.CenteredLattice4D.centeredCoord_abs_le v
      rw [abs_of_neg hneg] at hbd
      rw [Finset.mem_Icc]
      omega
    rw [h_eq, ← Finset.sum_image hinj]
    calc (∑ n ∈ S_neg.image (fun v => (centeredCoord L v).natAbs), g n)
        ≤ ∑ n ∈ Finset.Icc 1 L, g n :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun n _ _ => by dsimp [g]; positivity
      _ ≤ ∑ n ∈ Finset.Icc 1 L, a / (1 + (a * (n : ℝ)) ^ 2) :=
          Finset.sum_le_sum fun n _ => h_pos_bound n
      _ ≤ 3 := oneD_lattice_riemann_inv_sq_le_four a ha0 ha1 L
  rw [h_sum_split]
  linarith

end Imscribing.YangMills.CenteredTranslation4D