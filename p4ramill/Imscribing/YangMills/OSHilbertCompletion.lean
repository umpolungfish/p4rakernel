import Mathlib.Analysis.InnerProductSpace.Completion
import Imscribing.YangMills.OSContractivityAndGenerator

/-!
# Reflection-Positive Sesquilinear Forms & Completion Lift of OS Semigroups

1. `sesquilinear_cauchy_schwarz` and `sesquilinear_null_submodule`: builds the
   null space N₀ = {x | Re B(x, x) = 0} for any
   reflection-positive sesquilinear form B.
2. Given pre-Hilbert data `(H₀, Ω₀, T₀)` with symmetry, semigroup law, polynomial
   growth, and `Ω₀⊥` decay `Δ > 0`, lifts `T₀` unconditionally to `H = Completion H₀`
   with contractivity, symmetry, semigroup law, and global `Ω⊥` exponential decay.
-/

namespace Imscribing.YangMills.OSCompletion

open scoped InnerProductSpace

section SesquilinearRP

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **Cauchy–Schwarz for any positive semidefinite sesquilinear form B.** -/
theorem sesquilinear_cauchy_schwarz
    (B : E → E → ℂ)
    (h_add_left : ∀ x y z : E, B (x + y) z = B x z + B y z)
    (h_smul_left : ∀ (c : ℂ) (x y : E), B (c • x) y = star c * B x y)
    (h_add_right : ∀ x y z : E, B x (y + z) = B x y + B x z)
    (h_smul_right : ∀ (c : ℂ) (x y : E), B x (c • y) = c * B x y)
    (h_herm : ∀ x y : E, B y x = star (B x y))
    (h_nonneg : ∀ x : E, 0 ≤ (B x x).re)
    (x y : E) :
    ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re := by
  by_cases hxy : B x y = 0
  · rw [hxy, norm_zero, zero_pow (by norm_num)]
    exact mul_nonneg (h_nonneg x) (h_nonneg y)
  · have hnorm_pos : 0 < ‖B x y‖ := norm_pos_iff.mpr hxy
    set u : ℂ := B x y / (‖B x y‖ : ℂ)
    have hu_mul : star u * u = 1 := by
      dsimp [u]
      have h_nz : (‖B x y‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm_pos.ne'
      have h_star_real : star (‖B x y‖ : ℂ) = (‖B x y‖ : ℂ) := Complex.conj_ofReal _
      rw [← Complex.star_def, star_div₀, h_star_real, div_mul_div_comm, ← sq]
      have h_nsq : star (B x y) * B x y = ((‖B x y‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, show star (B x y) = starRingEnd ℂ (B x y) from rfl, Complex.mul_conj]
        norm_cast
        exact Complex.normSq_eq_norm_sq (B x y)
      rw [h_nsq]
      push_cast
      exact div_self (pow_ne_zero 2 h_nz)
    have hu_B : star u * B x y = (‖B x y‖ : ℂ) := by
      dsimp [u]
      have h_nz : (‖B x y‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm_pos.ne'
      have h_star_real : star (‖B x y‖ : ℂ) = (‖B x y‖ : ℂ) := Complex.conj_ofReal _
      rw [← Complex.star_def, star_div₀, h_star_real, div_mul_eq_mul_div]
      have h_nsq : star (B x y) * B x y = ((‖B x y‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, show star (B x y) = starRingEnd ℂ (B x y) from rfl, Complex.mul_conj]
        norm_cast
        exact Complex.normSq_eq_norm_sq (B x y)
      rw [h_nsq, sq]
      push_cast
      rw [mul_div_cancel_right₀ _ h_nz]
    have h_quad : ∀ t : ℝ, 0 ≤ t ^ 2 * (B x x).re + 2 * t * ‖B x y‖ + (B y y).re := by
      intro t
      set a : ℂ := (t : ℂ) * u
      have hnn := h_nonneg (a • x + y)
      have h_expand : B (a • x + y) (a • x + y) =
          (star a * a) * B x x + star a * B x y + a * B y x + B y y := by
        simp only [h_add_left, h_add_right, h_smul_left, h_smul_right]
        ring
      have h_sa_a : star a * a = ((t ^ 2 : ℝ) : ℂ) := by
        dsimp [a]
        rw [← Complex.star_def, star_mul, show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]
        calc
          (star u * (t : ℂ)) * ((t : ℂ) * u) = ((t : ℂ) * (t : ℂ)) * (star u * u) := by ring
          _ = ((t : ℂ) * (t : ℂ)) * 1 := by rw [hu_mul]
          _ = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have h_sa_B : star a * B x y = ((t * ‖B x y‖ : ℝ) : ℂ) := by
        dsimp [a]
        rw [← Complex.star_def, star_mul, show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]
        calc
          (star u * (t : ℂ)) * B x y = (t : ℂ) * (star u * B x y) := by ring
          _ = (t : ℂ) * (‖B x y‖ : ℂ) := by rw [hu_B]
          _ = ((t * ‖B x y‖ : ℝ) : ℂ) := by push_cast; rfl
      have h_a_Byx : a * B y x = ((t * ‖B x y‖ : ℝ) : ℂ) := by
        rw [h_herm x y]
        have h1 : star (star a * B x y) = a * star (B x y) := by
          rw [star_mul, star_star, mul_comm]
        rw [← h1, h_sa_B, Complex.star_def, Complex.conj_ofReal]
      rw [h_expand, h_sa_a, h_sa_B, h_a_Byx] at hnn
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hnn
      linarith
    by_cases hxx : (B x x).re = 0
    · have h_bad := h_quad (-((B y y).re + 1) / (2 * ‖B x y‖))
      rw [hxx, mul_zero, zero_add] at h_bad
      have h_eq : 2 * (-((B y y).re + 1) / (2 * ‖B x y‖)) * ‖B x y‖ + (B y y).re = -1 := by
        field_simp [hnorm_pos.ne']
        ring
      linarith
    · have hxx_pos : 0 < (B x x).re := lt_of_le_of_ne (h_nonneg x) (Ne.symm hxx)
      have h_min := h_quad (-‖B x y‖ / (B x x).re)
      have h_eq : (-‖B x y‖ / (B x x).re) ^ 2 * (B x x).re +
          2 * (-‖B x y‖ / (B x x).re) * ‖B x y‖ + (B y y).re =
          (B y y).re - ‖B x y‖ ^ 2 / (B x x).re := by
        field_simp [hxx_pos.ne']
        ring
      rw [h_eq] at h_min
      have h_le : ‖B x y‖ ^ 2 / (B x x).re ≤ (B y y).re := sub_nonneg.mp h_min
      exact ((div_le_iff₀ hxx_pos).mp h_le).trans_eq (mul_comm _ _)

/-- Null-space kernel N₀ = { x | Re B(x, x) = 0 } as a ℂ-submodule of E. -/
def sesquilinearNullSubmodule
    (B : E → E → ℂ)
    (h_add_left : ∀ x y z : E, B (x + y) z = B x z + B y z)
    (h_smul_left : ∀ (c : ℂ) (x y : E), B (c • x) y = star c * B x y)
    (h_add_right : ∀ x y z : E, B x (y + z) = B x y + B x z)
    (h_smul_right : ∀ (c : ℂ) (x y : E), B x (c • y) = c * B x y)
    (h_herm : ∀ x y : E, B y x = star (B x y))
    (h_nonneg : ∀ x : E, 0 ≤ (B x x).re) : Submodule ℂ E where
  carrier := { x : E | (B x x).re = 0 }
  zero_mem' := by
    have h0 : B 0 0 = 0 := by
      have := h_smul_right 0 0 0
      simpa using this
    simp [h0]
  add_mem' := by
    intro x y hx hy
    have hxy : B x y = 0 := by
      have hcs := sesquilinear_cauchy_schwarz B h_add_left h_smul_left h_add_right
        h_smul_right h_herm h_nonneg x y
      rw [hx, zero_mul] at hcs
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (B x y)])
    have hyx : B y x = 0 := by rw [h_herm, hxy, star_zero]
    have hsum : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
      rw [h_add_left, h_add_right, h_add_right]; ring
    change (B (x + y) (x + y)).re = 0
    change (B x x).re = 0 at hx
    change (B y y).re = 0 at hy
    rw [hsum, hxy, hyx]
    simp [hx, hy]
  smul_mem' := by
    intro c x hx
    have hsc : B (c • x) (c • x) = (star c * c) * B x x := by
      rw [h_smul_left, h_smul_right]; ring
    have h_cs := sesquilinear_cauchy_schwarz B h_add_left h_smul_left h_add_right
      h_smul_right h_herm h_nonneg x x
    rw [hx, zero_mul] at h_cs
    have hxx0 : B x x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (B x x)])
    change (B (c • x) (c • x)).re = 0
    rw [hsc, hxx0, mul_zero, Complex.zero_re]

end SesquilinearRP

section CompletionLift

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]

/-- Package a contractive linear map on `H₀` as a `UniformSpace.Completion H₀ →L[ℂ] ...`. -/
noncomputable def liftContractionToCompletion
    (f₀ : H₀ →ₗ[ℂ] H₀) (h_contr : ∀ v : H₀, ‖f₀ v‖ ≤ ‖v‖) :
    UniformSpace.Completion H₀ →L[ℂ] UniformSpace.Completion H₀ :=
  let fCLM : H₀ →L[ℂ] H₀ := LinearMap.mkContinuous f₀ 1 (fun v => by simpa using h_contr v)
  let rawMap : UniformSpace.Completion H₀ → UniformSpace.Completion H₀ :=
    UniformSpace.Completion.map fCLM
  have h_cont : Continuous rawMap := UniformSpace.Completion.continuous_map
  have h_add : ∀ x y : UniformSpace.Completion H₀, rawMap (x + y) = rawMap x + rawMap y := by
    intro x y
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp =>
        refine isClosed_eq (h_cont.comp continuous_add) ?_
        exact (h_cont.comp continuous_fst).add (h_cont.comp continuous_snd)
    | ih x y =>
        change UniformSpace.Completion.map fCLM (↑x + ↑y) =
          UniformSpace.Completion.map fCLM ↑x + UniformSpace.Completion.map fCLM ↑y
        rw [← UniformSpace.Completion.coe_add,
            UniformSpace.Completion.map_coe fCLM.uniformContinuous,
            UniformSpace.Completion.map_coe fCLM.uniformContinuous,
            UniformSpace.Completion.map_coe fCLM.uniformContinuous,
            map_add, UniformSpace.Completion.coe_add]
  have h_smul : ∀ (c : ℂ) (x : UniformSpace.Completion H₀), rawMap (c • x) = c • rawMap x := by
    intro c x
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
        refine isClosed_eq (h_cont.comp (continuous_const_smul c)) ?_
        exact (continuous_const_smul c).comp h_cont
    | ih x =>
        change UniformSpace.Completion.map fCLM (c • ↑x) =
          c • UniformSpace.Completion.map fCLM ↑x
        rw [← UniformSpace.Completion.coe_smul,
            UniformSpace.Completion.map_coe fCLM.uniformContinuous,
            UniformSpace.Completion.map_coe fCLM.uniformContinuous,
            map_smul, UniformSpace.Completion.coe_smul]
  have h_norm : ∀ x : UniformSpace.Completion H₀, ‖rawMap x‖ ≤ 1 * ‖x‖ := by
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (continuous_norm.comp h_cont) (continuous_const.mul continuous_norm)
    | ih x =>
        change ‖UniformSpace.Completion.map fCLM ↑x‖ ≤ 1 * ‖(x : UniformSpace.Completion H₀)‖
        rw [UniformSpace.Completion.map_coe fCLM.uniformContinuous,
            UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, one_mul]
        exact h_contr x
  LinearMap.mkContinuous
    { toFun := rawMap
      map_add' := h_add
      map_smul' := h_smul }
    1 h_norm

theorem liftContractionToCompletion_coe
    (f₀ : H₀ →ₗ[ℂ] H₀) (h_contr : ∀ v : H₀, ‖f₀ v‖ ≤ ‖v‖) (v : H₀) :
    liftContractionToCompletion f₀ h_contr (v : UniformSpace.Completion H₀) =
      (f₀ v : UniformSpace.Completion H₀) := by
  unfold liftContractionToCompletion
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [UniformSpace.Completion.map_coe
      (LinearMap.mkContinuous f₀ 1 (fun w => by simpa using h_contr w)).uniformContinuous]
  rfl

/-- **Full OS Completion Semigroup Theorem.** -/
theorem os_completion_semigroup_bridge
    (Ω₀ : H₀) (hΩ₀ : ‖Ω₀‖ = 1)
    (T₀ : ℝ → H₀ →ₗ[ℂ] H₀)
    (hT₀_vac : ∀ t : ℝ, 0 ≤ t → T₀ t Ω₀ = Ω₀)
    (hT₀_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H₀, ⟪x, T₀ t y⟫_ℂ = ⟪T₀ t x, y⟫_ℂ)
    (hT₀_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : H₀, T₀ (s + t) x = T₀ s (T₀ t x))
    (hT₀_poly : ∀ x : H₀, ∃ C r : ℝ, 0 < C ∧ 0 ≤ r ∧ ∀ t ≥ 0, ‖T₀ t x‖ ≤ C * (1 + t) ^ r)
    (Δ : ℝ)
    (hT₀_decay : ∀ t : ℝ, 0 ≤ t → ∀ φ : H₀, ⟪Ω₀, φ⟫_ℂ = 0 →
      ‖T₀ t φ‖ ≤ Real.exp (-Δ * t) * ‖φ‖) :
    let H := UniformSpace.Completion H₀
    let Ω : H := (Ω₀ : H)
    ∃ T : ℝ → H →L[ℂ] H,
      ‖Ω‖ = 1 ∧
      (∀ t : ℝ, 0 ≤ t → T t Ω = Ω) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : H, T (s + t) x = T s (T t x)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ φ : H, ⟪Ω, φ⟫_ℂ = 0 →
        ‖T t φ‖ ≤ Real.exp (-Δ * t) * ‖φ‖) := by
  have h_contr : ∀ t : ℝ, 0 ≤ t → ∀ v : H₀, ‖T₀ t v‖ ≤ ‖v‖ :=
    OSGenerator.os_repeated_squaring_contraction T₀ hT₀_symm hT₀_add hT₀_poly
  let T : ℝ → UniformSpace.Completion H₀ →L[ℂ] UniformSpace.Completion H₀ := fun t =>
    if ht : 0 ≤ t then liftContractionToCompletion (T₀ t) (h_contr t ht) else 0
  have hT_coe : ∀ t : ℝ, 0 ≤ t → ∀ v : H₀,
      T t (v : UniformSpace.Completion H₀) = (T₀ t v : UniformSpace.Completion H₀) := by
    intro t ht v
    dsimp [T]
    rw [dif_pos ht]
    exact liftContractionToCompletion_coe (T₀ t) (h_contr t ht) v
  refine ⟨T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [UniformSpace.Completion.norm_coe] using hΩ₀
  · intro t ht
    rw [hT_coe t ht Ω₀, hT₀_vac t ht]
  · intro t ht x y
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          (continuous_fst.inner ((T t).continuous.comp continuous_snd))
          (((T t).continuous.comp continuous_fst).inner continuous_snd)
    | ih x y =>
        rw [hT_coe t ht x, hT_coe t ht y,
            UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
            hT₀_symm t ht x y]
  · intro s t hs ht x
    have hst : 0 ≤ s + t := add_nonneg hs ht
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
        exact isClosed_eq (T (s + t)).continuous ((T s).continuous.comp (T t).continuous)
    | ih x =>
        rw [hT_coe (s + t) hst x, hT_coe t ht x, hT_coe s hs (T₀ t x), hT₀_add s t hs ht x]
  · intro t ht x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (continuous_norm.comp (T t).continuous) continuous_norm
    | ih x =>
        rw [hT_coe t ht x, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
        exact h_contr t ht x
  · intro t ht φ hφ
    have h_all : ∀ x : UniformSpace.Completion H₀,
        ‖T t (x - ⟪(Ω₀ : UniformSpace.Completion H₀), x⟫_ℂ • (Ω₀ : UniformSpace.Completion H₀))‖ ≤
          Real.exp (-Δ * t) *
            ‖x - ⟪(Ω₀ : UniformSpace.Completion H₀), x⟫_ℂ • (Ω₀ : UniformSpace.Completion H₀)‖ := by
      intro x
      have h_proj_cont : Continuous (fun z : UniformSpace.Completion H₀ =>
          z - ⟪(Ω₀ : UniformSpace.Completion H₀), z⟫_ℂ • (Ω₀ : UniformSpace.Completion H₀)) :=
        continuous_id.sub ((continuous_const.inner continuous_id).smul continuous_const)
      induction x using UniformSpace.Completion.induction_on with
      | hp =>
          exact isClosed_le
            (continuous_norm.comp ((T t).continuous.comp h_proj_cont))
            (continuous_const.mul (continuous_norm.comp h_proj_cont))
      | ih v =>
        have hv_orth : ⟪Ω₀, v - ⟪Ω₀, v⟫_ℂ • Ω₀⟫_ℂ = 0 := by
          rw [inner_sub_right, inner_smul_right]
          have h1 : ⟪Ω₀, Ω₀⟫_ℂ = (1 : ℂ) := by
            rw [inner_self_eq_norm_sq_to_K, hΩ₀]; norm_num
          rw [h1]; ring
        have h_coe_eq : (v : UniformSpace.Completion H₀) -
            ⟪(Ω₀ : UniformSpace.Completion H₀), (v : UniformSpace.Completion H₀)⟫_ℂ •
              (Ω₀ : UniformSpace.Completion H₀) =
            ((v - ⟪Ω₀, v⟫_ℂ • Ω₀ : H₀) : UniformSpace.Completion H₀) := by
          rw [UniformSpace.Completion.inner_coe, UniformSpace.Completion.coe_sub,
              UniformSpace.Completion.coe_smul]
        rw [h_coe_eq, hT_coe t ht, UniformSpace.Completion.norm_coe,
            UniformSpace.Completion.norm_coe]
        exact hT₀_decay t ht _ hv_orth
    have h_sub := h_all φ
    simpa [hφ] using h_sub

end CompletionLift

end Imscribing.YangMills.OSCompletion