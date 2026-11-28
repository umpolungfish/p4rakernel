
import Imscribing.YangMills.WilsonHaarCompactness4D
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure

/-!
# Frobenius-Norm Wilson Action Identity, Large-Field Suppression, & Smeared Schwinger
-/

noncomputable section

namespace Imscribing.YangMills.WilsonFrobenius4D

open MeasureTheory
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D
open Imscribing.YangMills.WilsonMeasure4D

/-- Frobenius norm squared `∑ i j, ‖M i j‖²` on `M_N(ℂ)`. -/
def frobeniusNormSq {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, ‖M i j‖ ^ 2

theorem frobeniusNormSq_nonneg {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ frobeniusNormSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Exact SU(N) Frobenius Identity:** `‖A - 1‖_F² = 2 * (N - realTrace A)`. -/
theorem wilson_plaquette_eq_frobenius_sq {N : ℕ} (A : GaugeGroup N) :
    frobeniusNormSq ((A : Matrix (Fin N) (Fin N) ℂ) - 1) =
      2 * ((N : ℝ) - realTrace A) := by
  unfold frobeniusNormSq realTrace
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Complex.re_sum]
  have h_row : ∀ i : Fin N,
      (∑ j : Fin N, ‖((A : Matrix (Fin N) (Fin N) ℂ) - 1) i j‖ ^ 2) =
        2 - 2 * ((A : Matrix (Fin N) (Fin N) ℂ) i i).re := by
    intro i
    have h_entry : ∀ j : Fin N,
        ‖((A : Matrix (Fin N) (Fin N) ℂ) - 1) i j‖ ^ 2 =
          ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 +
            if i = j then 1 - 2 * ((A : Matrix (Fin N) (Fin N) ℂ) i i).re else 0 := by
      intro j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.sub_apply, Matrix.one_apply_eq, ↓reduceIte]
        have h_sub : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i - 1‖ ^ 2 =
            ((A : Matrix (Fin N) (Fin N) ℂ) i i - 1).re ^ 2 +
            ((A : Matrix (Fin N) (Fin N) ℂ) i i - 1).im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have h_self : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 =
            ((A : Matrix (Fin N) (Fin N) ℂ) i i).re ^ 2 +
            ((A : Matrix (Fin N) (Fin N) ℂ) i i).im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        rw [h_sub, h_self]
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
        ring
      · simp [Matrix.sub_apply, Matrix.one_apply_ne hij, hij]
    simp_rw [h_entry, Finset.sum_add_distrib, gaugeGroup_row_norm_sq_sum A i]
    rw [Finset.sum_ite_eq Finset.univ i]
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [h_row, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- **Wilson Action as Frobenius Plaquette Energy:** -/
theorem wilsonAction_eq_frobenius_sum (N L : ℕ) [NeZero N] [NeZero L] (β : ℝ) (U : LinkConfig N L) :
    wilsonAction N L β U =
      (β / (2 * (N : ℝ))) * ∑ x : Lat4 L, ∑ μ : Fin 4, ∑ ν : Fin 4,
        frobeniusNormSq ((plaquetteHolonomy U x μ ν : Matrix (Fin N) (Fin N) ℂ) - 1) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold wilsonAction
  have h_term : ∀ x μ ν,
      frobeniusNormSq ((plaquetteHolonomy U x μ ν : Matrix (Fin N) (Fin N) ℂ) - 1) =
        2 * (N : ℝ) * (1 - realTrace (plaquetteHolonomy U x μ ν) / (N : ℝ)) := by
    intro x μ ν
    rw [wilson_plaquette_eq_frobenius_sq]
    field_simp [hN]
  simp_rw [h_term, ← Finset.mul_sum]
  field_simp [hN]

/-- **Balaban Large-Field Exponential Suppression:** -/
theorem large_field_gibbs_suppression (N L : ℕ) [NeZero N] [NeZero L] {β : ℝ} (hβ : 0 ≤ β)
    (U : LinkConfig N L) (x₀ : Lat4 L) (μ₀ ν₀ : Fin 4) {δ : ℝ}
    (hlarge : δ ^ 2 ≤ frobeniusNormSq ((plaquetteHolonomy U x₀ μ₀ ν₀ : Matrix (Fin N) (Fin N) ℂ) - 1)) :
    Real.exp (-wilsonAction N L β U) ≤ Real.exp (-(β / (2 * (N : ℝ))) * δ ^ 2) := by
  rw [wilsonAction_eq_frobenius_sum]
  apply Real.exp_le_exp.mpr
  have h_coeff : 0 ≤ β / (2 * (N : ℝ)) := by positivity
  have h_sum_ge :
      frobeniusNormSq ((plaquetteHolonomy U x₀ μ₀ ν₀ : Matrix (Fin N) (Fin N) ℂ) - 1) ≤
        ∑ x : Lat4 L, ∑ μ : Fin 4, ∑ ν : Fin 4,
          frobeniusNormSq ((plaquetteHolonomy U x μ ν : Matrix (Fin N) (Fin N) ℂ) - 1) := by
    let E : Lat4 L → Fin 4 → Fin 4 → ℝ := fun x μ ν =>
      frobeniusNormSq ((plaquetteHolonomy U x μ ν : Matrix (Fin N) (Fin N) ℂ) - 1)
    have hE_nn : ∀ x μ ν, 0 ≤ E x μ ν := fun _ _ _ => frobeniusNormSq_nonneg _
    have h1 : E x₀ μ₀ ν₀ ≤ ∑ ν : Fin 4, E x₀ μ₀ ν :=
      Finset.single_le_sum (f := E x₀ μ₀) (fun ν _ => hE_nn x₀ μ₀ ν) (Finset.mem_univ ν₀)
    have h2 : (∑ ν : Fin 4, E x₀ μ₀ ν) ≤ ∑ μ : Fin 4, ∑ ν : Fin 4, E x₀ μ ν :=
      Finset.single_le_sum (f := fun μ => ∑ ν : Fin 4, E x₀ μ ν)
        (fun μ _ => Finset.sum_nonneg fun ν _ => hE_nn x₀ μ ν) (Finset.mem_univ μ₀)
    have h3 : (∑ μ : Fin 4, ∑ ν : Fin 4, E x₀ μ ν) ≤
        ∑ x : Lat4 L, ∑ μ : Fin 4, ∑ ν : Fin 4, E x μ ν :=
      Finset.single_le_sum (f := fun x => ∑ μ : Fin 4, ∑ ν : Fin 4, E x μ ν)
        (fun x _ => Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => hE_nn x μ ν)
        (Finset.mem_univ x₀)
    exact le_trans h1 (le_trans h2 h3)
  have h_le := mul_le_mul_of_nonneg_left (le_trans hlarge h_sum_ge) h_coeff
  rw [neg_mul]
  exact neg_le_neg h_le

/-- Local gauge-invariant plaquette energy density `∑_{μ, ν} (1 - Re Tr(U_p) / N)`. -/
noncomputable def localPlaqDensity (N L : ℕ) [NeZero N] [NeZero L] (U : LinkConfig N L) (x : Lat4 L) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, (1 - realTrace (plaquetteHolonomy U x μ ν) / (N : ℝ))

theorem localPlaqDensity_gaugeInvariant (N L : ℕ) [NeZero N] [NeZero L]
    (g : GaugeTransform N L) (U : LinkConfig N L) (x : Lat4 L) :
    localPlaqDensity N L (applyGauge g U) x = localPlaqDensity N L U x := by
  unfold localPlaqDensity
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [plaquetteHolonomy_applyGauge, realTrace_conj]

theorem localPlaqDensity_bounds (N L : ℕ) [NeZero N] [NeZero L] (U : LinkConfig N L) (x : Lat4 L) :
    0 ≤ localPlaqDensity N L U x ∧ localPlaqDensity N L U x ≤ 32 := by
  unfold localPlaqDensity
  refine ⟨Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ =>
    (plaquette_density_bounds _).1, ?_⟩
  calc
    (∑ μ : Fin 4, ∑ ν : Fin 4, (1 - realTrace (plaquetteHolonomy U x μ ν) / (N : ℝ)))
        ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4, (2 : ℝ) :=
          Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => (plaquette_density_bounds _).2
    _ = 32 := by simp [Finset.sum_const]; norm_num

/-- Physical lattice coordinate embedding `Lat4 L → Spacetime4` at spacing `a`. -/
def latSiteToSpacetime (L : ℕ) (a : ℝ) (x : Lat4 L) : Spacetime4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm (fun μ => a * ((x μ).val : ℝ))

/-- Renormalized smeared `n`-point Wilson plaquette Schwinger functional on `EuclideanSchwartz n`. -/
noncomputable def smearedPlaqSchwinger (N L n : ℕ) [NeZero N] [NeZero L]
    (a β Z_ren : ℝ) [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L)) :
    EuclideanSchwartz n →ₗ[ℂ] ℂ where
  toFun f :=
    (Z_ren ^ n * a ^ (4 * n) : ℂ) *
      ∑ xs : Fin n → Lat4 L,
        f (fun k => latSiteToSpacetime L a (xs k)) *
          wilsonExpectation N L β μ (fun U => (∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ))
  map_add' f g := by
    simp only [SchwartzMap.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    ring

/-- **Gauge invariance of the smeared lattice observable inside `smearedPlaqSchwinger`.** -/
theorem smearedPlaq_observable_gaugeInvariant (N L n : ℕ) [NeZero N] [NeZero L]
    (g : GaugeTransform N L) (U : LinkConfig N L) (xs : Fin n → Lat4 L) :
    (∏ k : Fin n, localPlaqDensity N L (applyGauge g U) (xs k)) =
      ∏ k : Fin n, localPlaqDensity N L U (xs k) := by
  refine Finset.prod_congr rfl fun k _ => localPlaqDensity_gaugeInvariant N L g U (xs k)

/-- **Uniform Lattice-Sum Schwartz Estimate on `smearedPlaqSchwinger`.** -/
theorem smearedPlaqSchwinger_norm_le (N L n : ℕ) [NeZero N] [NeZero L]
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (Z_ren : ℝ)
    [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L)) [IsProbabilityMeasure μ]
    (h_act_meas : Measurable (fun U : LinkConfig N L => wilsonAction N L β U))
    (h_prod_meas : ∀ xs : Fin n → Lat4 L,
      Measurable (fun U : LinkConfig N L => (∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ)))
    (f : EuclideanSchwartz n) :
    ‖smearedPlaqSchwinger N L n a β Z_ren μ f‖ ≤
      (|Z_ren| * 32 * a ^ 4) ^ n *
        ∑ xs : Fin n → Lat4 L, ‖f (fun k => latSiteToSpacetime L a (xs k))‖ := by
  unfold smearedPlaqSchwinger
  simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_mul]
  have h_pref : ‖(Z_ren ^ n * a ^ (4 * n) : ℂ)‖ = |Z_ren| ^ n * a ^ (4 * n) := by
    rw [show (Z_ren ^ n * a ^ (4 * n) : ℂ) = ((Z_ren ^ n * a ^ (4 * n) : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (pow_nonneg ha (4 * n))]
  rw [← norm_mul, h_pref]
  have h_term : ∀ xs : Fin n → Lat4 L,
      ‖f (fun k => latSiteToSpacetime L a (xs k)) *
          wilsonExpectation N L β μ (fun U => (∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ))‖ ≤
        32 ^ n * ‖f (fun k => latSiteToSpacetime L a (xs k))‖ := by
    intro xs
    rw [norm_mul]
    have h_exp_bd :
        ‖wilsonExpectation N L β μ (fun U => (∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ))‖ ≤
          32 ^ n := by
      refine wilsonExpectation_norm_le hβ μ h_act_meas _ (h_prod_meas xs) (32 ^ n) (by positivity)
        fun U => ?_
      have h_prod_real :
          ((∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ)) =
            ((∏ k : Fin n, localPlaqDensity N L U (xs k) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [h_prod_real, Complex.norm_real, Real.norm_of_nonneg
        (Finset.prod_nonneg fun k _ => (localPlaqDensity_bounds N L U (xs k)).1)]
      calc
        (∏ k : Fin n, localPlaqDensity N L U (xs k))
            ≤ ∏ _k : Fin n, (32 : ℝ) :=
              Finset.prod_le_prod (fun k _ => (localPlaqDensity_bounds N L U (xs k)).1)
                (fun k _ => (localPlaqDensity_bounds N L U (xs k)).2)
        _ = 32 ^ n := by simp [Finset.prod_const]
    have h1 := mul_le_mul_of_nonneg_left h_exp_bd (norm_nonneg (f (fun k => latSiteToSpacetime L a (xs k))))
    linarith
  have h_sum_le :
      ‖∑ xs : Fin n → Lat4 L, f (fun k => latSiteToSpacetime L a (xs k)) *
          wilsonExpectation N L β μ (fun U => (∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ))‖ ≤
        32 ^ n * ∑ xs : Fin n → Lat4 L, ‖f (fun k => latSiteToSpacetime L a (xs k))‖ := by
    calc
      ‖∑ xs : Fin n → Lat4 L, _‖ ≤ ∑ xs : Fin n → Lat4 L, ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ xs : Fin n → Lat4 L, 32 ^ n * ‖f (fun k => latSiteToSpacetime L a (xs k))‖ :=
          Finset.sum_le_sum fun xs _ => h_term xs
      _ = 32 ^ n * ∑ xs : Fin n → Lat4 L, ‖f (fun k => latSiteToSpacetime L a (xs k))‖ := by
          rw [← Finset.mul_sum]
  have h_fac : (|Z_ren| ^ n * a ^ (4 * n)) * (32 ^ n *
      ∑ xs : Fin n → Lat4 L, ‖f (fun k => latSiteToSpacetime L a (xs k))‖) =
      (|Z_ren| * 32 * a ^ 4) ^ n *
        ∑ xs : Fin n → Lat4 L, ‖f (fun k => latSiteToSpacetime L a (xs k))‖ := by
    rw [mul_pow, mul_pow, pow_mul]
    ring
  calc
    |Z_ren| ^ n * a ^ (4 * n) * ‖∑ xs, _‖
        ≤ |Z_ren| ^ n * a ^ (4 * n) *
            (32 ^ n * ∑ xs : Fin n → Lat4 L, ‖f (fun k => latSiteToSpacetime L a (xs k))‖) :=
          mul_le_mul_of_nonneg_left h_sum_le (by positivity)
    _ = (|Z_ren| * 32 * a ^ 4) ^ n *
          ∑ xs : Fin n → Lat4 L, ‖f (fun k => latSiteToSpacetime L a (xs k))‖ := h_fac

end Imscribing.YangMills.WilsonFrobenius4D