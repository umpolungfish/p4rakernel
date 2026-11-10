import Imscribing.Classical.ErdosStrausDecomposition

namespace Imscribing

/-- A main-term-plus-remainder decomposition transfers a vanishing
normalized remainder to the normalized main expression. -/
theorem tendsto_normalized_main_of_remainder
    {ψ R : ℝ → ℝ}
    (hdecomp : ∀ x : ℝ, ψ x / x = 1 + R x / x)
    (hR : Filter.Tendsto (fun x : ℝ => R x / x)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => ψ x / x)
      Filter.atTop (nhds 1) := by
  have hsum :
      Filter.Tendsto (fun x : ℝ => (1 : ℝ) + R x / x)
        Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hR
  have htarget :
      Filter.Tendsto (fun x : ℝ => 1 + R x / x)
        Filter.atTop (nhds 1) := by
    simpa using hsum
  apply htarget.congr'
  filter_upwards with x
  exact (hdecomp x).symm

/-- The explicit-formula form of the transfer, with the decomposition
required only eventually. -/
theorem tendsto_normalized_chebyshev_of_remainder
    {ψ R : ℝ → ℝ}
    (hdecomp : ∀ᶠ x : ℝ in Filter.atTop, ψ x = x + R x)
    (hR : Filter.Tendsto (fun x : ℝ => R x / x)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => ψ x / x)
      Filter.atTop (nhds 1) := by
  have hnorm :
      (fun x : ℝ => ψ x / x) =ᶠ[Filter.atTop]
        (fun x : ℝ => 1 + R x / x) := by
    filter_upwards
        [hdecomp, Filter.eventually_gt_atTop (0 : ℝ)]
        with x hx hxpos
    rw [hx]
    field_simp [ne_of_gt hxpos]
  have hsum :
      Filter.Tendsto (fun x : ℝ => (1 : ℝ) + R x / x)
        Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hR
  have htarget :
      Filter.Tendsto (fun x : ℝ => 1 + R x / x)
        Filter.atTop (nhds 1) := by
    simpa using hsum
  exact htarget.congr' hnorm.symm

/-- An error bounded by every positive multiple of `x` is negligible
after division by `x`. -/
theorem tendsto_normalized_remainder_of_linear_error
    {R : ℝ → ℝ}
    (hbound : ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop,
      |R x| ≤ ε * x) :
    Filter.Tendsto (fun x : ℝ => R x / x)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by
    linarith
  filter_upwards
      [hbound (ε / 2) hε2, Filter.eventually_gt_atTop (0 : ℝ)]
      with x hx hxpos
  have hdiv : |R x| / x ≤ ε / 2 := by
    apply (div_le_iff₀ hxpos).2
    nlinarith
  have habs : |R x| / |x| < ε := by
    rw [abs_of_pos hxpos]
    exact lt_of_le_of_lt hdiv (by linarith)
  simpa [dist_eq_norm, Real.norm_eq_abs, abs_div] using habs

/-- The triangle inequality for three real error contributions. -/
theorem abs_add_three_le (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  have h₁ : |a + b + c| ≤ |a + b| + |c| := by
    simpa only [Real.norm_eq_abs] using (norm_add_le (a + b) c)
  have h₂ : |a + b| ≤ |a| + |b| := by
    simpa only [Real.norm_eq_abs] using (norm_add_le a b)
  calc
    |a + b + c| ≤ |a + b| + |c| := h₁
    _ ≤ (|a| + |b|) + |c| := by
      linarith [h₂]

/-- Three separately negligible contributions give a negligible total
remainder. -/
theorem tendsto_normalized_remainder_of_three_error_bounds
    {R Ezero Edyadic Eaux : ℝ → ℝ}
    (hsplit : ∀ x : ℝ,
      R x = Ezero x + Edyadic x + Eaux x)
    (hzero : ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop,
      |Ezero x| ≤ (ε / 3) * x)
    (hdyadic : ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop,
      |Edyadic x| ≤ (ε / 3) * x)
    (haux : ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop,
      |Eaux x| ≤ (ε / 3) * x) :
    Filter.Tendsto (fun x : ℝ => R x / x)
      Filter.atTop (nhds 0) := by
  apply tendsto_normalized_remainder_of_linear_error
  intro ε hε
  filter_upwards
      [hzero ε hε, hdyadic ε hε, haux ε hε]
      with x hzero' hdyadic' haux'
  rw [hsplit x]
  calc
    |Ezero x + Edyadic x + Eaux x|
        ≤ |Ezero x| + |Edyadic x| + |Eaux x| :=
          abs_add_three_le (Ezero x) (Edyadic x) (Eaux x)
    _ ≤ ((ε / 3) * x + (ε / 3) * x) + (ε / 3) * x :=
      add_le_add (add_le_add hzero' hdyadic') haux'
    _ = ε * x := by ring

/-- Complete transfer theorem: an eventually valid explicit formula and
three `o(x)` remainder estimates imply the Chebyshev main-term limit. -/
theorem tendsto_normalized_chebyshev_of_three_error_bounds
    {ψ R Ezero Edyadic Eaux : ℝ → ℝ}
    (hdecomp : ∀ᶠ x : ℝ in Filter.atTop, ψ x = x + R x)
    (hsplit : ∀ x : ℝ,
      R x = Ezero x + Edyadic x + Eaux x)
    (hzero : ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop,
      |Ezero x| ≤ (ε / 3) * x)
    (hdyadic : ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop,
      |Edyadic x| ≤ (ε / 3) * x)
    (haux : ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop,
      |Eaux x| ≤ (ε / 3) * x) :
    Filter.Tendsto (fun x : ℝ => ψ x / x)
      Filter.atTop (nhds 1) :=
  tendsto_normalized_chebyshev_of_remainder hdecomp
    (tendsto_normalized_remainder_of_three_error_bounds
      hsplit hzero hdyadic haux)

end Imscribing