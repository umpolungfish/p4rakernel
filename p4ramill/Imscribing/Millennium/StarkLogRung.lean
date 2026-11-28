import Mathlib
import Imscribing.Millennium.BoundaryLog

/-!
# StarkLogRung: roots of unity meet the boundary logarithm

Instantiate the BoundaryBrick root-of-unity harmonic at the Fourier root
`rootExp r f = exp(2πi·r/f)` and split its modulus trigonometrically:
`|1 - e^{iθ}| = 2·sin(θ/2)`. Together these give the real part of the
boundary limit: `re(-log(1 - exp(2πi·r/f))) = -log(2·sin(π·r/f))`,
the summand of `L'(0,χ)`.
-/

open scoped ComplexConjugate
open scoped Topology
open Filter Finset

noncomputable section

namespace StarkLogRung

/-- The Fourier root at ratio `r/f`: `exp(2πi·r/f)`. -/
def rootExp (r f : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) / (f : ℂ)))

/-! ## Folded computation lemmas -/

/-- `rootExp r f` raised to `f` is `1`. -/
private theorem expRoot_pow {f : ℕ} (hf : 0 < f) (r : ℕ) :
    (rootExp r f) ^ f = 1 := by
  unfold rootExp
  rw [← Complex.exp_nat_mul (n := f)]
  rw [Complex.exp_eq_one_iff]
  refine ⟨(r : ℤ), ?_⟩
  have hfc : (f : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  field_simp
  push_cast
  ring

/-- `rootExp r f` is a nontrivial root of unity when `0 < r < f`. -/
private theorem expRoot_ne_one {f : ℕ} (hf : 0 < f) {r : ℕ} (hr : 0 < r) (hrf : r < f) :
    rootExp r f ≠ 1 := by
  unfold rootExp
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hq : ((r : ℂ) / (f : ℂ)) = ((n : ℤ) : ℂ) := by
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [hn]
    ring
  have hcf : (f : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  have hrC : (r : ℂ) = ((n : ℤ) : ℂ) * (f : ℂ) := by
    rw [← hq]
    field_simp
  have hre : (r : ℝ) = ((n : ℤ) : ℝ) * (f : ℝ) := by
    have hc := congrArg Complex.re hrC
    simpa using hc
  have hfr : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have hdiv : (n : ℝ) = (r : ℝ) / (f : ℝ) := by
    rw [hre]
    field_simp
  have hlt : (0:ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := by
    constructor
    · rw [hdiv]
      exact div_pos (by exact_mod_cast hr) (by exact_mod_cast hf)
    · rw [hdiv]
      exact (div_lt_one (by exact_mod_cast hf)).2 (by exact_mod_cast hrf)
  rcases lt_trichotomy n 0 with hneg | h0 | hpn
  · have hnn : (n : ℝ) < 0 := by exact_mod_cast hneg
    linarith [hlt.1]
  · rw [h0] at hlt
    norm_num at hlt
  · have hone : (1:ℤ) ≤ n := by omega
    have h1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hone
    exact absurd hlt.2 (not_lt.2 h1)

/-- The conjugate of `1 - exp(θi)` is `1 - exp(-θi)`. -/
private theorem conj_one_sub_exp_mul_I (θ : ℝ) :
    conj ((1:ℂ) - Complex.exp (θ * Complex.I))
      = (1:ℂ) - Complex.exp (-θ * Complex.I) := by
  have hsub : (starRingEnd ℂ) ((1:ℂ) - Complex.exp (θ * Complex.I))
      = (starRingEnd ℂ) (1:ℂ) - (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) :=
    map_sub _ _ _
  have h1 : (starRingEnd ℂ) (1:ℂ) = 1 := map_one _
  have he : (starRingEnd ℂ) (Complex.exp (θ * Complex.I))
      = Complex.exp ((starRingEnd ℂ) (θ * Complex.I)) := (Complex.exp_conj _).symm
  rw [hsub, h1, he]
  rw [show (starRingEnd ℂ) (θ * Complex.I) = -θ * Complex.I from by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring]

/-- The unit-circle product: `exp(θi)·exp(-θi) = 1`. -/
private theorem exp_mul_exp_neg (θ : ℝ) :
    Complex.exp (θ * Complex.I) * Complex.exp (-θ * Complex.I) = 1 := by
  rw [← Complex.exp_add, show θ * Complex.I + -θ * Complex.I = 0 from by ring]
  exact Complex.exp_zero

/-- Euler split: `exp(θi) + exp(-θi) = 2·cos θ` (as a complex coercion). -/
private theorem exp_add_exp_neg_eq_cos (θ : ℝ) :
    (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I))
      = ((2 * Real.cos θ : ℝ) : ℂ) := by
  have hcd : (2:ℂ) * Complex.cos ((θ : ℝ) : ℂ)
      = Complex.exp ((θ : ℝ) * Complex.I) + Complex.exp ((-(θ : ℝ)) * Complex.I) := by
    unfold Complex.cos
    ring
  have hoc : ((Real.cos θ : ℝ) : ℂ) = Complex.cos ((θ : ℝ) : ℂ) := Complex.ofReal_cos θ
  rw [← hcd, ← hoc, Complex.ofReal_mul]
  norm_num

/-- Squared norm of `1 - exp(θi)` is `2 - 2·cos θ`. -/
private theorem normSq_one_sub_exp_mul_I (θ : ℝ) :
    ‖((1:ℂ) - Complex.exp (θ * Complex.I))‖ ^ 2 = 2 - 2 * Real.cos θ := by
  have hprod : ((1:ℂ) - Complex.exp (θ * Complex.I)) * conj ((1:ℂ) - Complex.exp (θ * Complex.I))
      = ((2 - 2 * Real.cos θ : ℝ) : ℂ) := by
    rw [conj_one_sub_exp_mul_I]
    have hex : ((1:ℂ) - Complex.exp (θ * Complex.I)) * ((1:ℂ) - Complex.exp (-θ * Complex.I))
        = 2 - (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I)) := by
      have h1 : ((1:ℂ) - Complex.exp (θ * Complex.I)) * ((1:ℂ) - Complex.exp (-θ * Complex.I))
          = 1 - Complex.exp (θ * Complex.I) - Complex.exp (-θ * Complex.I)
              + Complex.exp (θ * Complex.I) * Complex.exp (-θ * Complex.I) := by ring
      rw [h1, exp_mul_exp_neg]
      ring
    rw [hex, exp_add_exp_neg_eq_cos]
    push_cast
    ring
  have hns : Complex.normSq ((1:ℂ) - Complex.exp (θ * Complex.I)) = 2 - 2 * Real.cos θ := by
    have h2 := Complex.mul_conj ((1:ℂ) - Complex.exp (θ * Complex.I))
    rw [hprod] at h2
    exact Complex.ofReal_injective h2.symm
  rw [← Complex.normSq_eq_norm_sq]
  exact hns

/-! ## The trigonometric modulus split -/

/-- The modulus split: `|1 - e^{iθ}| = 2·sin(θ/2)` for `0 < θ < 2π`. -/
theorem norm_one_sub_exp_mul_I {θ : ℝ} (h0 : 0 < θ) (h2π : θ < 2 * Real.pi) :
    ‖((1:ℂ) - Complex.exp (θ * Complex.I))‖ = 2 * Real.sin (θ / 2) := by
  have hsq := normSq_one_sub_exp_mul_I θ
  have hpos : 0 < θ / 2 := by linarith
  have hsinpos : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
  have hsq2 : (2 * Real.sin (θ / 2)) ^ 2 = 2 - 2 * Real.cos θ := by
    have hsh := Real.sin_half_eq_sqrt h0.le h2π.le
    have hge : (0:ℝ) ≤ (1 - Real.cos θ) / 2 := by
      have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
      linarith
    rw [hsh, mul_pow, Real.sq_sqrt hge]
    ring
  have hnn : (0:ℝ) ≤ 2 * Real.sin (θ / 2) := by linarith
  have hsqeq : ‖((1:ℂ) - Complex.exp (θ * Complex.I))‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 :=
    hsq.trans hsq2.symm
  have habs := (sq_eq_sq_iff_abs_eq_abs ..).1 hsqeq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hnn] at habs

/-- The real part of the boundary limit: `re(-log(1 - e^{iθ})) = -log(2·sin(θ/2))`. -/
theorem re_neg_log_one_sub_exp_mul_I {θ : ℝ} (h0 : 0 < θ) (h2π : θ < 2 * Real.pi) :
    (-(Complex.log ((1:ℂ) - Complex.exp (θ * Complex.I)))).re
      = -(Real.log (2 * Real.sin (θ / 2))) := by
  have h2 := norm_one_sub_exp_mul_I h0 h2π
  have h3 : (0:ℝ) < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h4 : ‖((1:ℂ) - Complex.exp (θ * Complex.I))‖ > 0 := by rw [h2]; linarith
  have hne : ((1:ℂ) - Complex.exp (θ * Complex.I)) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at h4
    norm_num at h4
  have hlog := Complex.log_re ((1:ℂ) - Complex.exp (θ * Complex.I))
  simp only [Complex.neg_re]
  rw [hlog, h2]

/-! ## Instantiating the boundary logarithm at exp(2πi·r/f) -/

/-- The BoundaryBrick harmonic at a nontrivial `f`-th root of unity. -/
theorem boundaryAtRootUnity {f : ℕ} (hf : 0 < f) {r : ℕ} (hr : 0 < r) (hrf : r < f) :
    Filter.Tendsto (fun K : ℕ => ∑ n ∈ range K, (rootExp r f) ^ (n + 1) / (n + 1 : ℂ))
      Filter.atTop
      (𝓝 (-(Complex.log (1 - rootExp r f)))) :=
  BoundaryBrick.tendsto_rootUnityHarmonic hf (expRoot_pow hf r) (expRoot_ne_one hf hr hrf)

/-- Its real part: the partial sums converge in real part to `-log|1 - u|`. -/
theorem re_boundaryAtRootUnity {f : ℕ} (hf : 0 < f) {r : ℕ} (hr : 0 < r) (hrf : r < f) :
    Filter.Tendsto (fun K : ℕ => Complex.reCLM (∑ n ∈ range K, (rootExp r f) ^ (n + 1) / (n + 1 : ℂ)))
      Filter.atTop
      (𝓝 (Complex.reCLM (-(Complex.log (1 - rootExp r f))))) := by
  have hg : ContinuousAt Complex.reCLM (-(Complex.log (1 - rootExp r f))) :=
    (Complex.reCLM.continuous).continuousAt
  exact Filter.Tendsto.comp hg.tendsto (boundaryAtRootUnity hf hr hrf)

/-- The `L'(0,χ)` summand: the real-part limit equals `-log(2·sin(π·r/f))`. -/
theorem lprimeSummand {f : ℕ} (hf : 0 < f) {r : ℕ} (hr : 0 < r) (hrf : r < f) :
    Filter.Tendsto (fun K : ℕ => Complex.reCLM (∑ n ∈ range K, (rootExp r f) ^ (n + 1) / (n + 1 : ℂ)))
      Filter.atTop
      (𝓝 (-(Real.log (2 * Real.sin (Real.pi * (r : ℝ) / (f : ℝ)))))) := by
  have h1 := re_boundaryAtRootUnity hf hr hrf
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have h2π0 : (0:ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hp : 0 < 2 * Real.pi * (r : ℝ) / (f : ℝ) :=
    div_pos (mul_pos h2π0 (by exact_mod_cast hr)) (by exact_mod_cast hf)
  have hrRf : ((r : ℕ) : ℝ) < (f : ℝ) := by exact_mod_cast hrf
  have hlt : 2 * Real.pi * (r : ℝ) / (f : ℝ) < 2 * Real.pi := by
    rw [div_lt_iff₀ (by exact_mod_cast hf)]
    nlinarith [h2π0, hrRf]
  have hexp : rootExp r f
      = Complex.exp ((2 * Real.pi * (r : ℝ) / (f : ℝ) : ℝ) * Complex.I) := by
    unfold rootExp
    rw [show (2 * Real.pi * Complex.I : ℂ) * ((r : ℂ) / (f : ℂ))
        = ((2 * Real.pi * (r : ℝ) / (f : ℝ) : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring]
  have hhalf : (2 * Real.pi * (r : ℝ) / (f : ℝ)) / 2 = Real.pi * (r : ℝ) / (f : ℝ) := by
    field_simp
  have hval : Complex.reCLM (-(Complex.log (1 - rootExp r f)))
      = -(Real.log (2 * Real.sin (Real.pi * (r : ℝ) / (f : ℝ)))) := by
    have hcoe : ∀ z : ℂ, Complex.reCLM z = z.re := fun _ => rfl
    rw [hcoe, hexp, re_neg_log_one_sub_exp_mul_I hp hlt, hhalf]
  rw [hval] at h1
  exact h1

end StarkLogRung
