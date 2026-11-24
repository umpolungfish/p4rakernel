import Imscribing.Millennium.Erdos.SchutteTournament
import Mathlib.Tactic

namespace Imscribing.Millennium.Erdos

open Filter Topology Asymptotics

def szekeresBound (n : ℕ) : ℕ := (n + 2) * 2 ^ (n - 1) - 1
def probabilisticUpperBound (n : ℕ) : ℕ := 3 * n ^ 2 * 2 ^ n

theorem natCast_szekeresBound {n : ℕ} (hn : 1 ≤ n) :
    (szekeresBound n : ℝ) = ((n : ℝ) + 2) * 2 ^ (n - 1) - 1 := by
  have h1 : 1 ≤ (n + 2) * 2 ^ (n - 1) := by
    have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    nlinarith
  unfold szekeresBound
  push_cast [Nat.cast_sub h1]
  ring

theorem two_pow_pred {n : ℕ} (hn : 1 ≤ n) : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  ring

theorem n_mul_two_pow_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) * 2 ^ n) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have h : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- §25.3b.1  The lower bound is asymptotically (n/2)·2ⁿ. -/
theorem lower_bound_asymptotic_order :
    Tendsto (fun n : ℕ => (szekeresBound n : ℝ) / ((n : ℝ) * 2 ^ n)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have key : (fun n : ℕ => (szekeresBound n : ℝ) / ((n : ℝ) * 2 ^ n))
      =ᶠ[atTop] (fun n : ℕ => (1 + 2 / (n : ℝ)) / 2 - 1 / ((n : ℝ) * 2 ^ n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hp : (0 : ℝ) < 2 ^ (n - 1) := by positivity

    rw [natCast_szekeresBound hn, two_pow_pred hn]
    field_simp
  refine Tendsto.congr' key.symm ?_
  have h2n : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hA : Tendsto (fun n : ℕ => (1 + 2 / (n : ℝ)) / 2) atTop (𝓝 ((1 + 0) / 2)) :=
    ((tendsto_const_nhds.add h2n).div_const 2)
  have hB : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * 2 ^ n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop n_mul_two_pow_atTop
  simpa using hA.sub hB

/-- §25.3b.1b  The lower bound is Θ(n·2ⁿ). -/
theorem lower_bound_is_Theta_n_mul_2_pow_n :
    (fun n : ℕ => (szekeresBound n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ) * 2 ^ n) := by
  constructor
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hp : (0 : ℝ) < 2 ^ (n - 1) := by positivity
    have hs : (szekeresBound n : ℝ) = ((n : ℝ) + 2) * 2 ^ (n - 1) - 1 :=
      natCast_szekeresBound (by omega)
    have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := two_pow_pred (by omega)
    have h0 : (0 : ℝ) ≤ (szekeresBound n : ℝ) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) * 2 ^ n), hs, hpow]
    nlinarith
  · refine IsBigO.of_bound 4 ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hp1 : (1 : ℝ) ≤ 2 ^ (n - 1) := one_le_pow₀ (by norm_num)
    have hp : (0 : ℝ) < 2 ^ (n - 1) := by positivity
    have hs : (szekeresBound n : ℝ) = ((n : ℝ) + 2) * 2 ^ (n - 1) - 1 :=
      natCast_szekeresBound (by omega)
    have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := two_pow_pred (by omega)
    have h0 : (0 : ℝ) ≤ (szekeresBound n : ℝ) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) * 2 ^ n), hs, hpow]
    nlinarith

/-- §25.3b.2  The upper bound is O(n²·2ⁿ) — immediate from the definition. -/
theorem upper_bound_is_O_n_squared_mul_2_pow_n :
    (fun n : ℕ => (probabilisticUpperBound n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * 2 ^ n) := by
  refine IsBigO.of_bound 3 (Eventually.of_forall fun n => ?_)
  have h : (probabilisticUpperBound n : ℝ) = 3 * (n : ℝ) ^ 2 * 2 ^ n := by
    unfold probabilisticUpperBound; push_cast; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, h,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * (n:ℝ) ^ 2 * 2 ^ n),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) ^ 2 * 2 ^ n)]
  ring_nf
  exact le_refl _

theorem szekeresBound_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (szekeresBound n : ℝ) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ 2 ^ (n - 1) := one_le_pow₀ (by norm_num)
  rw [natCast_szekeresBound (by omega)]
  nlinarith

/-- §25.3b.3  The gap between the two classical bounds is Θ(n). -/
theorem asymptotic_gap_is_Theta_n :
    (fun n : ℕ => (probabilisticUpperBound n : ℝ) / (szekeresBound n : ℝ))
      =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  constructor
  · refine IsBigO.of_bound 12 ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsz : (0 : ℝ) < (szekeresBound n : ℝ) := szekeresBound_pos (by omega)
    have hs : (szekeresBound n : ℝ) = ((n : ℝ) + 2) * 2 ^ (n - 1) - 1 :=
      natCast_szekeresBound (by omega)
    have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := two_pow_pred (by omega)
    have hp4 : (4 : ℝ) ≤ 2 ^ (n - 1) := by
      calc (4:ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := by
            apply pow_le_pow_right₀ (by norm_num); omega
    have hu : (probabilisticUpperBound n : ℝ) = 3 * (n : ℝ) ^ 2 * 2 ^ n := by
      unfold probabilisticUpperBound; push_cast; ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (probabilisticUpperBound n : ℝ) / (szekeresBound n : ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ)), hu,
        div_le_iff₀ hsz, hs, hpow]
    nlinarith [sq_nonneg ((n:ℝ) - 3), mul_pos (by linarith : (0:ℝ) < (n:ℝ)) (by linarith : (0:ℝ) < 2 ^ (n-1))]
  · refine IsBigO.of_bound (1 / 3) ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsz : (0 : ℝ) < (szekeresBound n : ℝ) := szekeresBound_pos (by omega)
    have hs : (szekeresBound n : ℝ) = ((n : ℝ) + 2) * 2 ^ (n - 1) - 1 :=
      natCast_szekeresBound (by omega)
    have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := two_pow_pred (by omega)
    have hp1 : (1 : ℝ) ≤ 2 ^ (n - 1) := one_le_pow₀ (by norm_num)
    have hu : (probabilisticUpperBound n : ℝ) = 3 * (n : ℝ) ^ 2 * 2 ^ n := by
      unfold probabilisticUpperBound; push_cast; ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (probabilisticUpperBound n : ℝ) / (szekeresBound n : ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ)), hu,
        show (1:ℝ)/3 * (3 * (n:ℝ)^2 * 2^n / (szekeresBound n : ℝ))
             = ((n:ℝ)^2 * 2^n) / (szekeresBound n : ℝ) by field_simp,
        le_div_iff₀ hsz, hs, hpow]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ))
      (le_of_lt (show (0:ℝ) < 2 ^ (n-1) by positivity))) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2)]

/-- §25.3b.3b  The precise slope: R(n)/(6n) → 1. -/
theorem asymptotic_gap_precise_slope :
    Tendsto (fun n : ℕ =>
        ((probabilisticUpperBound n : ℝ) / (szekeresBound n : ℝ)) / (6 * (n : ℝ)))
      atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => 1 + 2 / (n : ℝ) - 1 / ((n : ℝ) * 2 ^ (n - 1)))
      atTop (𝓝 1) := by
    have h2n : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hbig : Tendsto (fun n : ℕ => (n : ℝ) * 2 ^ (n - 1)) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have h : (1 : ℝ) ≤ 2 ^ (n - 1) := one_le_pow₀ (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h3 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * 2 ^ (n - 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hbig
    simpa using (tendsto_const_nhds.add h2n).sub h3
  have key : (fun n : ℕ =>
        ((probabilisticUpperBound n : ℝ) / (szekeresBound n : ℝ)) / (6 * (n : ℝ)))
      =ᶠ[atTop] (fun n : ℕ => (1 + 2 / (n : ℝ) - 1 / ((n : ℝ) * 2 ^ (n - 1)))⁻¹) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hp : (0 : ℝ) < 2 ^ (n - 1) := by positivity
    have hp1 : (1 : ℝ) ≤ 2 ^ (n - 1) := one_le_pow₀ (by norm_num)
    have hsz : (0 : ℝ) < (szekeresBound n : ℝ) := szekeresBound_pos (by omega)
    have hs : (szekeresBound n : ℝ) = ((n : ℝ) + 2) * 2 ^ (n - 1) - 1 :=
      natCast_szekeresBound (by omega)
    have hS : ((n : ℝ) + 2) * 2 ^ (n - 1) - 1 ≠ 0 := hs ▸ (ne_of_gt hsz)
    have hS' : (-1 + (n : ℝ) * 2 ^ (n - 1) + 2 ^ (n - 1) * 2) ≠ 0 := by
      intro h; apply hS; linarith [h]
    have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := two_pow_pred (by omega)
    have hu : (probabilisticUpperBound n : ℝ) = 3 * (n : ℝ) ^ 2 * 2 ^ n := by
      unfold probabilisticUpperBound; push_cast; ring
    have hD : (1 : ℝ) + 2 / (n : ℝ) - 1 / ((n : ℝ) * 2 ^ (n - 1)) ≠ 0 := by
      have hge : (2 : ℝ) ≤ (n : ℝ) * 2 ^ (n - 1) := by nlinarith
      have h1 : 1 / ((n : ℝ) * 2 ^ (n - 1)) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hge
      have h2 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
      exact ne_of_gt (by linarith)
    rw [hu, hpow, hs, inv_eq_one_div, eq_div_iff hD]
    field_simp [hS']
    linear_combination (6 : ℝ) * inv_mul_cancel₀ hS'
  exact Tendsto.congr' key.symm (by simpa using hden.inv₀ one_ne_zero)

/-- §25.3b.4  The four asymptotic statements, together. Every one of them is
about the two BOUND functions; none of them is about `f` itself, which is why
this closes the statistical branch and leaves the obstructional branch at B. -/
theorem complete_asymptotic_closure :
    ((fun n : ℕ => (szekeresBound n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ) * 2 ^ n)) ∧
    ((fun n : ℕ => (probabilisticUpperBound n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * 2 ^ n)) ∧
    ((fun n : ℕ => (probabilisticUpperBound n : ℝ) / (szekeresBound n : ℝ))
      =Θ[atTop] (fun n : ℕ => (n : ℝ))) ∧
    (Tendsto (fun n : ℕ =>
        ((probabilisticUpperBound n : ℝ) / (szekeresBound n : ℝ)) / (6 * (n : ℝ)))
      atTop (𝓝 1)) :=
  ⟨lower_bound_is_Theta_n_mul_2_pow_n, upper_bound_is_O_n_squared_mul_2_pow_n,
   asymptotic_gap_is_Theta_n, asymptotic_gap_precise_slope⟩

/-! ### §25.5  Why the exact-determination section does not close

The claimed construction doubles a tournament: `f(n+1) = 2·f(n) + 1` from
`f(1) = 3`. That recurrence has a closed form, and it is NOT `(n+2)·2ⁿ⁻¹ − 1`.
The document's own line

    f(n) = 2ⁿ⁻¹·f(1) + (2ⁿ⁻¹ − 1) = 3·2ⁿ⁻¹ + 2ⁿ⁻¹ − 1 = (n+2)·2ⁿ⁻¹ − 1

is false at its last step: `3·2ⁿ⁻¹ + 2ⁿ⁻¹ − 1 = 2ⁿ⁺¹ − 1`. The two agree only
at n = 2. -/

/-- The count the doubling construction actually produces: `doublingCount k`
is the size after `k` doublings from the 3-cycle, i.e. the claimed `f(k+1)`. -/
def doublingCount : ℕ → ℕ
  | 0 => 3
  | (k + 1) => 2 * doublingCount k + 1

theorem doublingCount_closed_form (k : ℕ) : doublingCount k = 2 ^ (k + 2) - 1 := by
  induction k with
  | zero => rfl
  | succ m ih =>
      have h1 : 1 ≤ 2 ^ (m + 2) := Nat.one_le_two_pow
      have h2 : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
      simp only [doublingCount, ih]
      omega

/-- The document's algebra step is false for every n ≥ 3: what the recurrence
gives is strictly smaller than what the formula claims. -/
theorem claimed_closed_form_false {n : ℕ} (hn : 3 ≤ n) :
    3 * 2 ^ (n - 1) + 2 ^ (n - 1) - 1 < (n + 2) * 2 ^ (n - 1) - 1 := by
  have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have hp : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
  have h2 : 4 * 2 ^ (n - 1) < (n + 2) * 2 ^ (n - 1) :=
    (Nat.mul_lt_mul_right hp).mpr (by omega)
  omega

/-- The refutation, in one line the kernel checks: the doubling construction
would give a tournament with property S₃ on 15 vertices, but f(3) = 19 is
already carried in this directory (Reid–Parker, `schutte_tournament_known_results`).
A 15-vertex witness would contradict a value the file records as true, so
`doubleTournament_preserves_S` cannot hold as stated. -/
theorem doubling_construction_refuted :
    doublingCount 2 = 15 ∧ szekeresBound 3 = 19 ∧ doublingCount 2 < szekeresBound 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- And the formula does not even reproduce the base value it starts from:
`f(1) = 3`, while the claimed closed form gives 2 at n = 1. -/
theorem claimed_form_misses_base : szekeresBound 1 = 2 := by decide

#print axioms doublingCount_closed_form
#print axioms claimed_closed_form_false
#print axioms doubling_construction_refuted
#print axioms claimed_form_misses_base

#print axioms lower_bound_asymptotic_order
#print axioms lower_bound_is_Theta_n_mul_2_pow_n
#print axioms upper_bound_is_O_n_squared_mul_2_pow_n
#print axioms asymptotic_gap_is_Theta_n
#print axioms asymptotic_gap_precise_slope
#print axioms complete_asymptotic_closure

end Imscribing.Millennium.Erdos