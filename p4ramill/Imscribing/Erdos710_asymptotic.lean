import Imscribing.Erdos710_unified

open scoped BigOperators Topology
open Filter Asymptotics

noncomputable section

namespace Erdos710

/-!
Erdős #710: rigorous asymptotic consequences of the already-verified
combinatorial core, and a precise proof interface for a sharp equivalent.

This module uses exactly `Erdos710.f`, the least L admitting distinct
multiples in the OPEN interval (n,n+L).

Unified imscription: ⟨𐑦𐑸𐑑𐑿𐑐𐑧𐑲𐑝⊙𐑖𐑳𐑴⟩
IMASM: ⊢∈≻⋈∋⊡⊣   Full carrier: SIXTEEN₃ = P({T,F,t,f}).

The lower-asymptotic theorem below is unconditional. The sharp result is
an implication whose assumptions are the explicit, still-open, analytic
upper and lower estimates. No custom axioms, proof placeholders, by_contra, or False.elim.
-/

/-- A quantitative asymptotic lower envelope, valid for every `n ≥ 1`.
    It makes the O(1/n) error explicit. -/
theorem ratio_lower_envelope (n : ℕ) (hn : 0 < n) :
    (5 / 4 : ℝ) - 23 / (4 * (n : ℝ)) ≤ (f n : ℝ) / (n : ℝ) := by
  have hbound := linear_lower_bound n
  have hreal : (5 : ℝ) * (n : ℝ) ≤
      (4 : ℝ) * (f n : ℝ) + 23 := by exact_mod_cast hbound
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hpos).2
  have hmul : (4 : ℝ) * (n : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Direct asymptotic consequence: the normalized length is eventually
    at least `5/4 - ε`, for every positive ε.

    This DOES NOT assert that f(n)/n converges to 5/4. -/
theorem eventually_ratio_ge_five_fourths_sub (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (5 / 4 : ℝ) - ε ≤ (f n : ℝ) / (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((23 : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  have hnpos : 0 < n := by omega
  have hNle : N ≤ n := by omega
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNle
  have hNlarge : (23 : ℝ) < ε * (N : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hεn : (23 : ℝ) ≤ ε * (n : ℝ) :=
    le_trans (le_of_lt hNlarge)
      (mul_le_mul_of_nonneg_left hnreal (le_of_lt hε))
  have hnat := linear_lower_bound n
  have hreal : (5 : ℝ) * (n : ℝ) ≤
      (4 : ℝ) * (f n : ℝ) + 23 := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- The general sharp-asymptotic squeeze lemma. It does not require any
    classical reductio: its assumptions are two directly checkable
    eventually-valid inequalities and positivity of the scale. -/
theorem tendsto_ratio_of_eventual_bounds
    (g : ℕ → ℝ)
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n)
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (1 - ε) * g n ≤ (f n : ℝ))
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (1 + ε) * g n) :
    Tendsto (fun n : ℕ => (f n : ℝ) / g n) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hlower (ε / 2) hε2)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hupper (ε / 2) hε2)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hg
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have hn₃ : N₃ ≤ n := by omega
  have hgn : 0 < g n := hN₃ n hn₃
  have hlo : (1 : ℝ) - ε / 2 ≤ (f n : ℝ) / g n := by
    apply (le_div_iff₀ hgn).2
    exact hN₁ n hn₁
  have hhi : (f n : ℝ) / g n ≤ (1 : ℝ) + ε / 2 := by
    apply (div_le_iff₀ hgn).2
    exact hN₂ n hn₂
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

/-- The proposed sharp scale, stated without asserting an unverified
    leading constant. -/
def sharpScale (c : ℝ) (n : ℕ) : ℝ :=
  c * (n : ℝ) * Real.sqrt (Real.log (n : ℝ))

/-- The sharp scale is eventually positive whenever c > 0. -/
theorem sharpScale_eventually_pos (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < sharpScale c n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hsqrt : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.2 hlog
  unfold sharpScale
  positivity

/-- The precise final step for any proposed coefficient c.

    IMPORTANT: This is a proved implication. Its two mathematical
    hypotheses are the missing sharp *analytic estimates*, not axioms
    and not theorems claimed in this file. -/
theorem sharp_asymptotic_of_two_sided_estimates
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (1 - ε) * sharpScale c n ≤ (f n : ℝ))
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (f n : ℝ) ≤ (1 + ε) * sharpScale c n) :
    Tendsto (fun n : ℕ => (f n : ℝ) / sharpScale c n)
      atTop (𝓝 1) := by
  exact tendsto_ratio_of_eventual_bounds (sharpScale c)
    (sharpScale_eventually_pos c hc) hlower hupper

#print axioms ratio_lower_envelope
#print axioms eventually_ratio_ge_five_fourths_sub
#print axioms sharp_asymptotic_of_two_sided_estimates

end Erdos710
