import Imscribing.Erdos710_limit_envelope
import Imscribing.Millennium.HornTorusGeometry

open Filter

noncomputable section

namespace Erdos710

/-- The finite-scale slope whose supremum is the extended constant. -/
def erdos710Slope (n : ℕ) : ℝ := ((f n : ℝ) - 1) / (n : ℝ)

/-- A nonnegative slope is placed on the radius-two horn torus. -/
def slopeOnHorn (x : ℝ) : Imscribing.HornTorus.Point :=
  Imscribing.HornTorus.horn 2 (2 * Real.arctan (Real.sqrt x)) 0

private theorem cos_slope_angle (x : ℝ) (hx : 0 ≤ x) :
    Real.cos (2 * Real.arctan (Real.sqrt x)) = (1 - x) / (1 + x) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  rw [hsx]
  have hden : 1 + x ≠ 0 := by linarith
  field_simp [hden]
  <;> ring

private theorem sin_slope_angle (x : ℝ) (hx : 0 ≤ x) :
    Real.sin (2 * Real.arctan (Real.sqrt x)) =
      2 * Real.sqrt x / (1 + x) := by
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  rw [hsx]
  have hden : Real.sqrt (1 + x) ≠ 0 := by positivity
  field_simp [hden]
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + x)]
  <;> ring

private theorem slopeOnHorn_first (x : ℝ) (hx : 0 ≤ x) :
    (slopeOnHorn x).1 = 4 / (1 + x) := by
  rw [slopeOnHorn, Imscribing.HornTorus.horn]
  simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
  rw [cos_slope_angle x hx]
  have hden : 1 + x ≠ 0 := by linarith
  field_simp [hden]
  <;> ring

/-- The squared distance to the horn pinch is the reciprocal slope coordinate.
Thus infinite slope is represented by arrival at the pinched point. -/
theorem slopeOnHorn_distance_sq (x : ℝ) (hx : 0 ≤ x) :
    Imscribing.HornTorus.sqDist (slopeOnHorn x) Imscribing.HornTorus.origin =
      16 / (1 + x) := by
  rw [show slopeOnHorn x =
      Imscribing.HornTorus.horn 2 (2 * Real.arctan (Real.sqrt x)) 0 by rfl]
  rw [show Imscribing.HornTorus.origin = (0, 0, 0) by rfl]
  rw [Imscribing.HornTorus.sqDist]
  rw [Imscribing.HornTorus.horn]
  simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
  rw [cos_slope_angle x hx, sin_slope_angle x hx]
  have hden : 1 + x ≠ 0 := by linarith
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  field_simp [hden]
  <;> nlinarith [hsx]

/-- Every finite nonnegative slope maps to the radius-two horn torus. -/
theorem slopeOnHorn_mem_horn (x : ℝ) (hx : 0 ≤ x) :
    Imscribing.HornTorus.OnHorn 2 (slopeOnHorn x) := by
  rw [Imscribing.HornTorus.OnHorn]
  rw [slopeOnHorn_distance_sq x hx, slopeOnHorn_first x hx]
  simp only [slopeOnHorn, Imscribing.HornTorus.horn,
    Real.sin_zero, mul_zero, add_zero, Real.cos_zero, mul_one,
    Imscribing.HornTorus.origin]
  have hden : 1 + x ≠ 0 := by linarith
  field_simp [hden]
  <;> ring

/-- Unbounded nonnegative slopes are equivalent to their horn images
approaching the pinch. The compactified formulation turns an infinite
endpoint into the ordinary zero-distance boundary value. -/
theorem unbounded_iff_horn_pinching (s : ℕ → ℝ)
    (hs : ∀ n, 0 ≤ s n) :
    (∀ B : ℝ, ∃ n, B < s n) ↔
      ∀ ε : ℝ, 0 < ε → ∃ n,
        Imscribing.HornTorus.sqDist (slopeOnHorn (s n))
          Imscribing.HornTorus.origin < ε := by
  constructor
  · intro hunbounded ε hε
    obtain ⟨n, hn⟩ := hunbounded (16 / ε)
    refine ⟨n, ?_⟩
    rw [slopeOnHorn_distance_sq (s n) (hs n)]
    have hden : 0 < 1 + s n := by linarith [hs n]
    apply (div_lt_iff₀ hden).2
    have hmul0 : 16 < s n * ε := (div_lt_iff₀ hε).mp hn
    have hmul : 16 < ε * s n := by simpa [mul_comm] using hmul0
    nlinarith
  · intro hpinch B
    let D := max B 0 + 2
    have hD : B + 2 ≤ D := by
      dsimp [D]
      linarith [le_max_left B 0]
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hε : 0 < 16 / D := div_pos (by norm_num) hDpos
    obtain ⟨n, hn⟩ := hpinch (16 / D) hε
    refine ⟨n, ?_⟩
    rw [slopeOnHorn_distance_sq (s n) (hs n)] at hn
    have hden : 0 < 1 + s n := by linarith [hs n]
    have hcmp := (div_lt_div_iff₀ hden hDpos).mp hn
    have hcmp' : D < 1 + s n := by nlinarith [hcmp]
    linarith

/-- For Erdős #710, divergence of the normalized lengths is equivalent to
the finite-scale slopes arriving at the horn pinch. -/
theorem erdos710_divergence_iff_horn_pinching :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop atTop ↔
      ∀ ε : ℝ, 0 < ε → ∃ n,
        Imscribing.HornTorus.sqDist (slopeOnHorn (erdos710Slope n))
          Imscribing.HornTorus.origin < ε := by
  rw [normalized_ratio_atTop_iff_unbounded_slopes]
  have hslope : ∀ n, 0 ≤ erdos710Slope n := by
    intro n
    by_cases hn : n = 0
    · simp [erdos710Slope, hn]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hf : 0 < f n := f_pos_of_pos n hnpos
      have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hfreal : (1 : ℝ) ≤ (f n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hf)
      unfold erdos710Slope
      exact div_nonneg (by linarith) (le_of_lt hnreal)
  constructor
  · intro hunbounded
    apply (unbounded_iff_horn_pinching erdos710Slope hslope).mp
    intro B
    obtain ⟨m, hm, hBm⟩ := hunbounded B
    exact ⟨m, hBm⟩
  · intro hpinch B
    have hunbounded := (unbounded_iff_horn_pinching erdos710Slope hslope).mpr hpinch
    by_cases hB : B < 0
    · refine ⟨1, by norm_num, ?_⟩
      exact lt_of_lt_of_le hB (hslope 1)
    · obtain ⟨m, hBm⟩ := hunbounded B
      have hm : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        have : B < 0 := by simpa [erdos710Slope] using hBm
        exact hB this
      exact ⟨m, hm, hBm⟩

#print axioms slopeOnHorn_mem_horn
#print axioms slopeOnHorn_distance_sq
#print axioms unbounded_iff_horn_pinching
#print axioms erdos710_divergence_iff_horn_pinching

end Erdos710
