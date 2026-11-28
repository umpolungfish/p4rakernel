import Mathlib
import Imscribing.Millennium.BoundaryLog
import Imscribing.Millennium.StarkLogRung

/-!
# StarkCharFilter: the character filter over the roots of unity

Assemble the per-root boundary limits into the character-twisted sum. For any
real function `χ` on `ZMod f` with `χ 0 = 0`, the real part of the twisted
partial sums converges to `-∑_j χ(j)·log(2·sin(π·j/f))` — the Dirichlet
`L′(0,χ)` summand structure. The exchanged (sum-over-n first) form is recorded
for the Gauss-sum brick.
-/

open scoped ComplexConjugate
open scoped Topology
open Filter Finset

noncomputable section

namespace StarkCharFilter

open StarkLogRung

/-! ## Folded helper lemmas -/

/-- Finite sums of convergent sequences converge to the sum of the limits. -/
private theorem tendsto_finset_sum {ι : Type*} {α : Type*} [TopologicalSpace α]
    [AddCommMonoid α] [ContinuousAdd α] (s : Finset ι) (F : ι → ℕ → α) (x : ι → α)
    (h : ∀ i ∈ s, Filter.Tendsto (F i) Filter.atTop (𝓝 (x i))) :
    Filter.Tendsto (fun K => ∑ i ∈ s, F i K) Filter.atTop (𝓝 (∑ i ∈ s, x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Real part of the boundary limit at a nontrivial root of unity, as a value. -/
private theorem reLogRootExp {f : ℕ} (hf : 0 < f) {r : ℕ} (hr : 0 < r) (hrf : r < f) :
    (-(Complex.log (1 - rootExp r f))).re
      = -(Real.log (2 * Real.sin (Real.pi * (r : ℝ) / (f : ℝ)))) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have h2π0 : (0:ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hrRf : ((r : ℕ) : ℝ) < (f : ℝ) := by exact_mod_cast hrf
  have hp : 0 < 2 * Real.pi * (r : ℝ) / (f : ℝ) :=
    div_pos (mul_pos h2π0 (by exact_mod_cast hr)) (by exact_mod_cast hf)
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
  rw [hexp, re_neg_log_one_sub_exp_mul_I hp hlt, hhalf]

/-- Real part of a real-scalar multiple. -/
private theorem reCLM_const_mul (a : ℝ) (z : ℂ) :
    Complex.reCLM ((a : ℂ) * z) = a * Complex.reCLM z := by
  have hcoe : ∀ w : ℂ, Complex.reCLM w = w.re := fun _ => rfl
  rw [hcoe, hcoe]
  show ((a : ℂ) * z).re = a * z.re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp

/-! ## The character filter -/

/-- The character-twisted boundary logarithm: for any real `χ` on `ZMod f`
    with `χ 0 = 0`, the twisted partial sums converge to
    `∑_j χ(j)·(-log(1 - exp(2πi·j/f)))`. -/
theorem charFilterLimit {f : ℕ} [NeZero f] (hf : 0 < f) (χ : ZMod f → ℝ) (hχ0 : χ 0 = 0) :
    Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) *
        (∑ n ∈ Finset.range K, (rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ)))
      Filter.atTop
      (𝓝 (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) * -(Complex.log (1 - rootExp j.val f)))) := by
  refine tendsto_finset_sum Finset.univ _ _ fun j hj => ?_
  rcases eq_or_ne j 0 with h0 | hne
  · subst h0
    simp [hχ0]
  · have hT : Filter.Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K,
        (rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ))
        Filter.atTop (𝓝 (-(Complex.log (1 - rootExp j.val f)))) :=
      StarkLogRung.boundaryAtRootUnity hf (ZMod.val_pos.2 hne) (ZMod.val_lt j)
    exact hT.const_mul ((χ j : ℝ) : ℂ)

/-- The real-part form: the twisted partial sums converge in real part to
    `-∑_j χ(j)·log(2·sin(π·j/f))` — the `L'(0,χ)` summand structure. -/
theorem charFilterRealLimit {f : ℕ} [NeZero f] (hf : 0 < f) (χ : ZMod f → ℝ) (hχ0 : χ 0 = 0) :
    Filter.Tendsto (fun K : ℕ => Complex.reCLM (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) *
        (∑ n ∈ Finset.range K, (rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ))))
      Filter.atTop
      (𝓝 (∑ j ∈ Finset.univ, (χ j) *
        -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (f : ℝ)))))) := by
  have hg : ContinuousAt Complex.reCLM (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) *
      -(Complex.log (1 - rootExp j.val f))) := (Complex.reCLM.continuous).continuousAt
  have h1 : Filter.Tendsto (fun K : ℕ => Complex.reCLM (∑ j ∈ Finset.univ,
      ((χ j : ℝ) : ℂ) *
        (∑ n ∈ Finset.range K, (rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ))))
      Filter.atTop
      (𝓝 (Complex.reCLM (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) *
        -(Complex.log (1 - rootExp j.val f))))) := by
    simpa only [Function.comp_apply] using
      Filter.Tendsto.comp hg.tendsto (charFilterLimit hf χ hχ0)
  have hval : ∀ j ∈ (Finset.univ : Finset (ZMod f)),
      Complex.reCLM (((χ j : ℝ) : ℂ) * -(Complex.log (1 - rootExp j.val f)))
        = (χ j) * -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (f : ℝ)))) := by
    intro j _
    rcases eq_or_ne j 0 with h0 | hne
    · subst h0
      simp [hχ0]
    · rw [reCLM_const_mul, (show ∀ w : ℂ, Complex.reCLM w = w.re from fun _ => rfl),
        reLogRootExp hf (ZMod.val_pos.2 hne) (ZMod.val_lt j)]
  have hval2 : (Complex.reCLM (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) *
        -(Complex.log (1 - rootExp j.val f))))
      = (∑ j ∈ Finset.univ, (χ j) *
        -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (f : ℝ))))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j hj => hval j hj
  rw [← hval2]
  exact h1

/-! ## The exchanged form (Gauss-sum brick input) -/

/-- Exchanging the order of summation: the character-twisted partial sums are
    the normalized twisted exponential sums — the input to the Gauss-sum brick. -/
theorem twistedSumForm {f : ℕ} [NeZero f] (χ : ZMod f → ℝ) (K : ℕ) :
    (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) *
        (∑ n ∈ Finset.range K, (rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ)))
      = ∑ n ∈ Finset.range K,
          (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) * (rootExp j.val f) ^ (n + 1))
            / (n + 1 : ℂ) := by
  calc (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) *
          (∑ n ∈ Finset.range K, (rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ)))
      _ = ∑ j ∈ Finset.univ, ∑ n ∈ Finset.range K,
            ((χ j : ℝ) : ℂ) * ((rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
      _ = ∑ n ∈ Finset.range K, ∑ j ∈ Finset.univ,
            ((χ j : ℝ) : ℂ) * ((rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ)) :=
          Finset.sum_comm
      _ = ∑ n ∈ Finset.range K, ∑ j ∈ Finset.univ,
            ((χ j : ℝ) : ℂ) * (rootExp j.val f) ^ (n + 1) / (n + 1 : ℂ) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_div_assoc' ((χ j : ℝ) : ℂ) ((rootExp j.val f) ^ (n + 1)) (↑n + 1)]
      _ = ∑ n ∈ Finset.range K,
            (∑ j ∈ Finset.univ, ((χ j : ℝ) : ℂ) * (rootExp j.val f) ^ (n + 1))
              / (n + 1 : ℂ) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← Finset.sum_div]

end StarkCharFilter
