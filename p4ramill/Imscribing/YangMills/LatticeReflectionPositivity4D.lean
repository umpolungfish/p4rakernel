import Imscribing.YangMills.WilsonActionBounds4D

/-!
# Osterwalder–Seiler Time-Reflection Symmetry on 4D SU(N) Lattice Gauge Theory

1. Defines the temporal site reflection `reflectSite` (t ↦ -(t + 1)) and link
   reflection involution `linkReflect` (Θ) on `LinkConfig N L`.
2. Proves `reflectSite_involutive`, `reflectSite_ne_self` on every even temporal
   torus `L = 2 * M`, and `linkReflect_involutive` (Θ² = id).
3. Proves `realTrace_inv` and exact plaquette reflection covariance, yielding
   `wilsonAction_linkReflect : wilsonAction N L β (linkReflect U) = wilsonAction N L β U`.
-/

namespace Imscribing.YangMills.LatticeRP4D

open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D

/-- Temporal site reflection across the half-integer cut t = -1/2:
    `(reflectSite L x) 0 = -(x 0 + 1)`, spatial coordinates unchanged. -/
def reflectSite (L : ℕ) (x : Lat4 L) : Lat4 L :=
  fun ν => if ν = 0 then -(x 0 + 1) else x ν

theorem reflectSite_involutive (L : ℕ) (x : Lat4 L) :
    reflectSite L (reflectSite L x) = x := by
  ext ν
  by_cases hν : ν = 0
  · subst hν; simp [reflectSite]
  · simp [reflectSite, hν]

theorem reflectSite_bijective (L : ℕ) : Function.Bijective (reflectSite L) :=
  Function.Involutive.bijective (reflectSite_involutive L)

/-- On an even temporal lattice `L = 2 * M` (M ≠ 0), `reflectSite` has no fixed points,
    partitioning sites cleanly into positive-time (`t.val < M`) and negative-time halves. -/
theorem reflectSite_ne_self (M : ℕ) [NeZero M] (x : Lat4 (2 * M)) :
    reflectSite (2 * M) x ≠ x := by
  intro heq
  have h0 := congrFun heq 0
  simp only [reflectSite, ↓reduceIte] at h0
  have hzero : 2 * (x 0) + 1 = 0 := by
    have h1 : x 0 + (x 0 + 1) = 0 := by
      calc
        x 0 + (x 0 + 1) = -(x 0 + 1) + (x 0 + 1) := by conv_lhs => lhs; rw [← heq]
        _ = 0 := neg_add_cancel _
    linear_combination h1
  have hcast : ((2 * (x 0).val + 1 : ℕ) : ZMod (2 * M)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hzero
  have hdvd : (2 * M) ∣ (2 * (x 0).val + 1) :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨k, hk⟩ := hdvd
  omega

/-- Osterwalder–Seiler link reflection Θ on 4D SU(N) link configurations. -/
def linkReflect {N L : ℕ} (U : LinkConfig N L) : LinkConfig N L :=
  fun x μ =>
    if μ = 0 then (U (reflectSite L x - stepDir L 0) 0)⁻¹
    else U (reflectSite L x) μ

private lemma reflectSite_add_stepDir_zero (L : ℕ) (x : Lat4 L) :
    reflectSite L (x + stepDir L 0) = reflectSite L x - stepDir L 0 := by
  ext ν
  by_cases hν : ν = 0
  · subst hν; simp [reflectSite, stepDir]; ring
  · simp [reflectSite, stepDir, hν]

private lemma reflectSite_sub_stepDir_zero (L : ℕ) (x : Lat4 L) :
    reflectSite L (x - stepDir L 0) = reflectSite L x + stepDir L 0 := by
  ext ν
  by_cases hν : ν = 0
  · subst hν; simp [reflectSite, stepDir]; ring
  · simp [reflectSite, stepDir, hν]

private lemma reflectSite_add_stepDir_spatial (L : ℕ) (x : Lat4 L) {μ : Fin 4} (hμ : μ ≠ 0) :
    reflectSite L (x + stepDir L μ) = reflectSite L x + stepDir L μ := by
  ext ν
  by_cases hν : ν = 0
  · subst hν; simp [reflectSite, stepDir, hμ.symm]
  · simp [reflectSite, stepDir, hν]

/-- **Θ² = id** on 4D SU(N) link configurations. -/
theorem linkReflect_involutive {N L : ℕ} (U : LinkConfig N L) :
    linkReflect (linkReflect U) = U := by
  ext x μ
  · simp only [linkReflect]
    split_ifs with hμ
    · subst hμ
      have harg : reflectSite L (reflectSite L x - stepDir L 0) - stepDir L 0 = x := by
        rw [reflectSite_sub_stepDir_zero, reflectSite_involutive, add_sub_cancel_right]
      simp [harg]
    · simp [reflectSite_involutive]

/-- Unitary inverse preserves `realTrace`: `Re Tr(A⁻¹) = Re Tr(A)` for `A ∈ SU(N)`. -/
theorem realTrace_inv {N : ℕ} (A : GaugeGroup N) :
    realTrace A⁻¹ = realTrace A := by
  have hL : ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) *
      (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    change ((A⁻¹ * A : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1
    simp
  have hR : (A : Matrix (Fin N) (Fin N) ℂ) * star (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp A.prop).1
  have hinv_star : ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) =
      star (A : Matrix (Fin N) (Fin N) ℂ) := by
    calc
      ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)
          = ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) * 1 := (Matrix.mul_one _).symm
      _ = ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) *
            ((A : Matrix (Fin N) (Fin N) ℂ) * star (A : Matrix (Fin N) (Fin N) ℂ)) := by rw [hR]
      _ = (((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) *
            (A : Matrix (Fin N) (Fin N) ℂ)) * star (A : Matrix (Fin N) (Fin N) ℂ) := by
              rw [Matrix.mul_assoc]
      _ = star (A : Matrix (Fin N) (Fin N) ℂ) := by rw [hL, Matrix.one_mul]
  unfold realTrace
  rw [hinv_star, Matrix.trace, Matrix.diag]
  simp only [Matrix.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_re _

theorem plaquetteHolonomy_diag {N L : ℕ} (U : LinkConfig N L) (x : Lat4 L) (μ : Fin 4) :
    plaquetteHolonomy U x μ μ = 1 := by
  unfold plaquetteHolonomy
  group

theorem plaquetteHolonomy_swap {N L : ℕ} (U : LinkConfig N L) (x : Lat4 L) (μ ν : Fin 4) :
    plaquetteHolonomy U x ν μ = (plaquetteHolonomy U x μ ν)⁻¹ := by
  unfold plaquetteHolonomy
  group

/-- Spatial plaquette density is mapped by site reflection `x ↦ reflectSite L x`. -/
theorem realTrace_plaquette_linkReflect_spatial {N L : ℕ} (U : LinkConfig N L)
    (x : Lat4 L) {μ ν : Fin 4} (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    realTrace (plaquetteHolonomy (linkReflect U) x μ ν) =
      realTrace (plaquetteHolonomy U (reflectSite L x) μ ν) := by
  congr 1
  simp only [plaquetteHolonomy, linkReflect, hμ, hν, ↓reduceIte,
    reflectSite_add_stepDir_spatial L x hμ, reflectSite_add_stepDir_spatial L x hν]

/-- Temporal plaquette `(0, ν)` density is mapped by `(x) ↦ reflectSite L x - e₀`. -/
theorem realTrace_plaquette_linkReflect_time_first {N L : ℕ} (U : LinkConfig N L)
    (x : Lat4 L) {ν : Fin 4} (hν : ν ≠ 0) :
    realTrace (plaquetteHolonomy (linkReflect U) x 0 ν) =
      realTrace (plaquetteHolonomy U (reflectSite L x - stepDir L 0) 0 ν) := by
  set y : Lat4 L := reflectSite L x - stepDir L 0
  have h1 : reflectSite L (x + stepDir L 0) = y := by
    rw [reflectSite_add_stepDir_zero]
  have h2 : reflectSite L (x + stepDir L ν) - stepDir L 0 = y + stepDir L ν := by
    rw [reflectSite_add_stepDir_spatial L x hν]
    dsimp [y]; abel
  have h3 : reflectSite L x = y + stepDir L 0 := by
    dsimp [y]; abel
  have hplaq : plaquetteHolonomy (linkReflect U) x 0 ν =
      (U y 0)⁻¹ * (plaquetteHolonomy U y 0 ν)⁻¹ * U y 0 := by
    simp only [plaquetteHolonomy, linkReflect, ↓reduceIte, hν, h1, h2, h3]
    group
  rw [hplaq, show (U y 0)⁻¹ * (plaquetteHolonomy U y 0 ν)⁻¹ * U y 0 =
    (U y 0)⁻¹ * (plaquetteHolonomy U y 0 ν)⁻¹ * ((U y 0)⁻¹)⁻¹ from by simp,
    realTrace_conj, realTrace_inv]

/-- **Exact Osterwalder–Seiler time-reflection invariance of the 4D SU(N) Wilson action.** -/
theorem wilsonAction_linkReflect (N L : ℕ) [NeZero N] (β : ℝ) (U : LinkConfig N L) :
    wilsonAction N L β (linkReflect U) = wilsonAction N L β U := by
  unfold wilsonAction
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hν : ν = 0
    · subst hν
      simp [plaquetteHolonomy_diag]
    · have h_tr : ∀ x : Lat4 L,
          (1 - realTrace (plaquetteHolonomy (linkReflect U) x 0 ν) / (N : ℝ)) =
          (1 - realTrace (plaquetteHolonomy U (reflectSite L x - stepDir L 0) 0 ν) / (N : ℝ)) :=
        fun x => by rw [realTrace_plaquette_linkReflect_time_first U x hν]
      simp_rw [h_tr]
      exact Fintype.sum_bijective (fun x => reflectSite L x - stepDir L 0)
        ((Equiv.subRight (stepDir L 0)).bijective.comp (reflectSite_bijective L))
        _ _ (fun _ => rfl)
  · by_cases hν : ν = 0
    · subst hν
      have h_tr : ∀ x : Lat4 L,
          (1 - realTrace (plaquetteHolonomy (linkReflect U) x μ 0) / (N : ℝ)) =
          (1 - realTrace (plaquetteHolonomy U (reflectSite L x - stepDir L 0) μ 0) / (N : ℝ)) := by
        intro x
        rw [plaquetteHolonomy_swap (linkReflect U) x 0 μ, realTrace_inv,
            realTrace_plaquette_linkReflect_time_first U x hμ,
            plaquetteHolonomy_swap U _ 0 μ, realTrace_inv]
      simp_rw [h_tr]
      exact Fintype.sum_bijective (fun x => reflectSite L x - stepDir L 0)
        ((Equiv.subRight (stepDir L 0)).bijective.comp (reflectSite_bijective L))
        _ _ (fun _ => rfl)
    · have h_tr : ∀ x : Lat4 L,
          (1 - realTrace (plaquetteHolonomy (linkReflect U) x μ ν) / (N : ℝ)) =
          (1 - realTrace (plaquetteHolonomy U (reflectSite L x) μ ν) / (N : ℝ)) :=
        fun x => by rw [realTrace_plaquette_linkReflect_spatial U x hμ hν]
      simp_rw [h_tr]
      exact Fintype.sum_bijective (reflectSite L) (reflectSite_bijective L) _ _ (fun _ => rfl)

end Imscribing.YangMills.LatticeRP4D