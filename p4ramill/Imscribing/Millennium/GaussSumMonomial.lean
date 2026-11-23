import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Imscribing.Millennium.GaussSumMonomial

open Complex Real

/-! ## Part 1: Universal Closed-Form Monomial and Non-Cancellation -/

def m_d (d : ℤ) : ℤ := (d - 3) * (d + 1)

def coeffA (N : ℤ) : ℤ :=
  -N^6 + N^5 + 8*N^4 - 7*N^3 - 18*N^2 + 12*N + 8

def coeffB (N : ℤ) : ℤ :=
  N^5 - N^4 - 6*N^3 + 5*N^2 + 8*N - 4

def normMonomial (d : ℤ) : ℤ :=
  -(d - 3)^3 * (d + 1)^2

lemma coeffA_shifted (k : ℤ) :
    -coeffA (k + 3) = k^6 + 17*k^5 + 112*k^4 + 361*k^3 + 594*k^2 + 474*k + 145 := by
  unfold coeffA; ring

lemma coeffB_shifted (k : ℤ) :
    coeffB (k + 3) = k^5 + 14*k^4 + 72*k^3 + 167*k^2 + 173*k + 65 := by
  unfold coeffB; ring

theorem coeffA_neg {d : ℤ} (hd : 4 ≤ d) : coeffA (d - 1) < 0 := by
  set k : ℤ := d - 4
  have hk : 0 ≤ k := by omega
  have hN : d - 1 = k + 3 := by omega
  rw [hN]
  have hpos : 0 < -coeffA (k + 3) := by
    rw [coeffA_shifted]
    positivity
  linarith

theorem coeffB_pos {d : ℤ} (hd : 4 ≤ d) : 0 < coeffB (d - 1) := by
  set k : ℤ := d - 4
  have hk : 0 ≤ k := by omega
  have hN : d - 1 = k + 3 := by omega
  rw [hN, coeffB_shifted]
  positivity

/-- Exact norm identity A(d-1)² - m_d(d) * B(d-1)² = 4 * N(M_d) for every d : ℤ. -/
theorem monomial_norm_identity (d : ℤ) :
    (coeffA (d - 1))^2 - m_d d * (coeffB (d - 1))^2 = 4 * normMonomial d := by
  unfold coeffA coeffB m_d normMonomial
  ring

structure RationalizedMonomial (d : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  normM : ℤ
  hc : c ≠ 0
  norm_spec : a^2 - m_d d * b^2 = c^2 * normM
  same_sign_denom : 0 < a * (-b)

def makeRationalizedMonomial (d : ℤ) (hd : 4 ≤ d) : RationalizedMonomial d where
  a := coeffA (d - 1)
  b := coeffB (d - 1)
  c := 2
  normM := normMonomial d
  hc := by decide
  norm_spec := by
    have h := monomial_norm_identity d
    linarith
  same_sign_denom := by
    have ha := coeffA_neg hd
    have hb := coeffB_pos hd
    nlinarith

/-- Cancellation-free rationalized evaluation for all d ≥ 4. -/
theorem rationalized_eval_eq {d : ℤ} (hd : 4 ≤ d) (r : ℝ)
    (hr : r^2 = (m_d d : ℝ)) (hr_nonneg : 0 ≤ r) :
    let R := makeRationalizedMonomial d hd
    ((R.a : ℝ) + (R.b : ℝ) * r) / (R.c : ℝ) =
      ((R.c : ℝ) * (R.normM : ℝ)) / ((R.a : ℝ) - (R.b : ℝ) * r) := by
  intro R
  have ha : (R.a : ℝ) < 0 := by exact_mod_cast coeffA_neg hd
  have hb : (0 : ℝ) < (R.b : ℝ) := by exact_mod_cast coeffB_pos hd
  have hdenom : (R.a : ℝ) - (R.b : ℝ) * r < 0 := by nlinarith
  have hc : (R.c : ℝ) ≠ 0 := by norm_num [R, makeRationalizedMonomial]
  have hspec : ((R.a : ℝ))^2 - (m_d d : ℝ) * ((R.b : ℝ))^2 =
      ((R.c : ℝ))^2 * (R.normM : ℝ) := by
    exact_mod_cast R.norm_spec
  field_simp [hc, ne_of_lt hdenom]
  calc
    ((R.a : ℝ) + (R.b : ℝ) * r) * ((R.a : ℝ) - (R.b : ℝ) * r)
        = (R.a : ℝ)^2 - (R.b : ℝ)^2 * r^2 := by ring
    _   = (R.a : ℝ)^2 - (m_d d : ℝ) * (R.b : ℝ)^2 := by rw [hr]; ring
    _   = (R.c : ℝ)^2 * (R.normM : ℝ) := hspec

/-- Exact expansion of M_d = σ (1 - σ)³ (1 + σ)² for σ = ((d - 1) - s)/2. -/
theorem monomial_sigma_expansion (d : ℤ) (s : ℝ) (hs : s^2 = (m_d d : ℝ)) :
    let N : ℝ := (d : ℝ) - 1
    let σ : ℝ := (N - s) / 2
    σ * (1 - σ)^3 * (1 + σ)^2 =
      ((coeffA (d - 1) : ℝ) + (coeffB (d - 1) : ℝ) * s) / 2 := by
  intro N σ
  have hmd : (m_d d : ℝ) = N^2 - 4 := by
    unfold m_d; push_cast; dsimp [N]; ring
  have hσ2 : σ^2 = N * σ - 1 := by
    dsimp [σ]
    calc
      ((N - s) / 2)^2 = (N^2 - 2*N*s + s^2) / 4 := by ring
      _ = (N^2 - 2*N*s + (N^2 - 4)) / 4 := by rw [hs, hmd]
      _ = N * ((N - s) / 2) - 1 := by ring
  have h1 : σ * (1 - σ) = 1 - (N - 1) * σ := by
    calc
      σ * (1 - σ) = σ - σ^2 := by ring
      _ = σ - (N * σ - 1) := by rw [hσ2]
      _ = 1 - (N - 1) * σ := by ring
  have h2 : (1 - σ^2)^2 = (4 - N^2) + (N^3 - 4*N) * σ := by
    calc
      (1 - σ^2)^2 = (1 - (N * σ - 1))^2 := by rw [hσ2]
      _ = (2 - N * σ)^2 := by ring
      _ = 4 - 4*N*σ + N^2 * σ^2 := by ring
      _ = 4 - 4*N*σ + N^2 * (N * σ - 1) := by rw [hσ2]
      _ = (4 - N^2) + (N^3 - 4*N) * σ := by ring
  have h3 : σ * (1 - σ)^3 * (1 + σ)^2 = (σ * (1 - σ)) * (1 - σ^2)^2 := by ring
  rw [h3, h1, h2]
  set A0 : ℝ := 4 - N^2
  set A1 : ℝ := N^3 - 4*N
  have h4 : (1 - (N - 1) * σ) * (A0 + A1 * σ) =
      (A0 + (N - 1) * A1) + (A1 - (N - 1) * A0 - N * (N - 1) * A1) * σ := by
    calc
      (1 - (N - 1) * σ) * (A0 + A1 * σ)
          = A0 + (A1 - (N - 1) * A0) * σ - (N - 1) * A1 * σ^2 := by ring
      _   = A0 + (A1 - (N - 1) * A0) * σ - (N - 1) * A1 * (N * σ - 1) := by rw [hσ2]
      _   = (A0 + (N - 1) * A1) + (A1 - (N - 1) * A0 - N * (N - 1) * A1) * σ := by ring
  rw [h4]
  dsimp [A0, A1, σ, N]
  unfold coeffA coeffB
  push_cast
  ring

theorem d2048_exact_data :
    m_d 2048 = 4190205 ∧
    coeffA 2047 = -73534985899138338825 ∧
    coeffB 2047 = 35923312651511805 ∧
    normMonomial 2048 = -35905737691441125 := by
  unfold m_d coeffA coeffB normMonomial
  decide

/-! ## Part 2: Quadratic Gauss-Sum Radical Extraction Over ℂ -/

noncomputable def zeta (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

noncomputable def gaussSum (m : ℕ) [NeZero m] : ℂ :=
  ∑ k : ZMod m, zeta m ^ (k.val ^ 2)

lemma zeta_pow_m (m : ℕ) [NeZero m] : zeta m ^ m = 1 := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [mul_div_cancel₀ _ hm]
  exact Complex.exp_two_pi_mul_I

lemma zeta_pow_eq_of_modEq {m : ℕ} [NeZero m] {a b : ℕ} (h : a ≡ b [MOD m]) :
    zeta m ^ a = zeta m ^ b := by
  have h1 : ∀ k : ℕ, zeta m ^ k = zeta m ^ (k % m) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k m]
    rw [pow_add, pow_mul, zeta_pow_m, one_pow, one_mul]
  rw [h1 a, h1 b, h]

lemma zeta_ne_one {m : ℕ} (hm : 1 < m) : zeta m ≠ 1 := by
  unfold zeta
  rw [ne_eq, Complex.exp_eq_one_iff]
  rintro ⟨k, hk⟩
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hci : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hk' : (2 * Real.pi * Complex.I) =
      ((k : ℤ) * (m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    calc (2 * Real.pi * Complex.I)
        = (2 * Real.pi * Complex.I / (m : ℂ)) * (m : ℂ) := by field_simp [hm0]
      _ = ((k : ℂ) * (2 * Real.pi * Complex.I)) * (m : ℂ) := by rw [hk]
      _ = ((k : ℤ) * (m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  have h3 : (1 : ℂ) = ((k : ℤ) * (m : ℤ) : ℂ) := by
    apply mul_right_cancel₀ hci
    simpa using hk'
  have hk_int : (1 : ℤ) = k * (m : ℤ) := by exact_mod_cast h3
  have hm_int : (1 : ℤ) < m := by exact_mod_cast hm
  have hdiv : (m : ℤ) ∣ 1 := ⟨k, by linarith⟩
  have hle : (m : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one hdiv
  omega

lemma sum_zeta_zmod_eq_zero {m : ℕ} [NeZero m] (hm : 1 < m) :
    ∑ w : ZMod m, zeta m ^ w.val = 0 := by
  have hsum : ∑ w : ZMod m, zeta m ^ w.val = ∑ i ∈ Finset.range m, zeta m ^ i := by
    refine Finset.sum_bij (fun w _ => w.val) ?_ ?_ ?_ ?_
    · intro w _; exact Finset.mem_range.mpr (ZMod.val_lt w)
    · intro a _ b _ hab; exact ZMod.val_injective m hab
    · intro i hi
      refine ⟨(i : ZMod m), Finset.mem_univ _, ?_⟩
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
    · intro _ _; rfl
  rw [hsum]
  have hgeom : (∑ i ∈ Finset.range m, zeta m ^ i) * (zeta m - 1) = zeta m ^ m - 1 :=
    geom_sum_mul (zeta m) m
  rw [zeta_pow_m, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr (zeta_ne_one hm))

lemma star_zeta_pow (m : ℕ) [NeZero m] (k : ℕ) :
    starRingEnd ℂ (zeta m ^ k) = zeta m ^ ((m - k % m) % m) := by
  have hm1 : 1 ≤ m := NeZero.pos m
  have hconj : starRingEnd ℂ (zeta m) = zeta m ^ (m - 1) := by
    have hmul : zeta m * zeta m ^ (m - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hm1, zeta_pow_m]
    have hinv : (zeta m)⁻¹ = zeta m ^ (m - 1) := inv_eq_of_mul_eq_one_right hmul
    rw [← hinv]
    unfold zeta
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, map_natCast, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [map_pow, hconj, ← pow_mul]
  apply zeta_pow_eq_of_modEq
  have hlt : k % m ≤ m := Nat.le_of_lt (Nat.mod_lt k hm1)
  have hmod : (m - 1) * k ≡ m - k % m [MOD m] := by
    change ((m - 1) * k) ≡ (m - k % m) [MOD m]
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast [hm1, hlt]
    have hk_mod : ((k % m : ℕ) : ZMod m) = (k : ZMod m) := ZMod.natCast_mod k m
    rw [hk_mod, ZMod.natCast_self]
    ring
  exact hmod.trans (Nat.mod_modEq (m - k % m) m).symm

lemma zmod_mul_left_bijective {p : ℕ} [Fact p.Prime] {u : ZMod p} (hu : u ≠ 0) :
    Function.Bijective (fun v : ZMod p => u * v) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun w => u⁻¹ * w, ?_, ?_⟩
  · intro v; calc u⁻¹ * (u * v) = (u⁻¹ * u) * v := by ring
      _ = 1 * v := by rw [inv_mul_cancel₀ hu]
      _ = v := one_mul v
  · intro w; calc u * (u⁻¹ * w) = (u * u⁻¹) * w := by ring
      _ = 1 * w := by rw [mul_inv_cancel₀ hu]
      _ = w := one_mul w

/-- For every odd prime p, |gaussSum p|² = p. -/
theorem gaussSum_mul_conj_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    gaussSum p * starRingEnd ℂ (gaussSum p) = p := by
  have hp_prime : Nat.Prime p := Fact.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  have hp1 : 1 < p := hp_prime.one_lt
  unfold gaussSum
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have hterm : ∀ a b : ZMod p,
      zeta p ^ (a.val ^ 2) * starRingEnd ℂ (zeta p ^ (b.val ^ 2)) =
        zeta p ^ (((a - b) * (a + b)).val) := by
    intro a b
    rw [star_zeta_pow, ← pow_add]
    apply zeta_pow_eq_of_modEq
    change (a.val ^ 2 + (p - b.val ^ 2 % p) % p) ≡ ((a - b) * (a + b)).val [MOD p]
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    have hcast : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val
    have hsub : (((p - b.val ^ 2 % p) % p : ℕ) : ZMod p) = -(b * b) := by
      rw [ZMod.natCast_mod, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ hp_prime.pos))]
      simp [ZMod.natCast_mod, hcast, sq]
    rw [hsub, hcast a, hcast ((a - b) * (a + b))]
    ring
  simp_rw [hterm]
  have hprod : (∑ a : ZMod p, ∑ b : ZMod p, zeta p ^ ((a - b) * (a + b)).val) =
      ∑ x : ZMod p × ZMod p, zeta p ^ ((x.1 - x.2) * (x.1 + x.2)).val :=
    (Fintype.sum_prod_type
      (fun x : ZMod p × ZMod p => zeta p ^ ((x.1 - x.2) * (x.1 + x.2)).val)).symm
  rw [hprod]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  let inv2 : ZMod p := (2 : ZMod p)⁻¹
  have h2inv : (2 : ZMod p) * inv2 = 1 := mul_inv_cancel₀ h2ne
  let φ : ZMod p × ZMod p → ZMod p × ZMod p := fun x => (x.1 - x.2, x.1 + x.2)
  have hφ_bij : Function.Bijective φ := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun y => ((y.1 + y.2) * inv2, (y.2 - y.1) * inv2), ?_, ?_⟩
    · intro ⟨a, b⟩
      ext <;> dsimp [φ]
      · calc ((a - b) + (a + b)) * inv2 = a * (2 * inv2) := by ring
          _ = a := by rw [h2inv, mul_one]
      · calc ((a + b) - (a - b)) * inv2 = b * (2 * inv2) := by ring
          _ = b := by rw [h2inv, mul_one]
    · intro ⟨u, v⟩
      ext <;> dsimp [φ]
      · calc (u + v) * inv2 - (v - u) * inv2 = u * (2 * inv2) := by ring
          _ = u := by rw [h2inv, mul_one]
      · calc (u + v) * inv2 + (v - u) * inv2 = v * (2 * inv2) := by ring
          _ = v := by rw [h2inv, mul_one]
  have hsum_eq : ∑ x : ZMod p × ZMod p, zeta p ^ ((x.1 - x.2) * (x.1 + x.2)).val =
      ∑ y : ZMod p × ZMod p, zeta p ^ (y.1 * y.2).val :=
    Fintype.sum_bijective φ hφ_bij _ _ (fun _ => rfl)
  rw [hsum_eq, Fintype.sum_prod_type]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (ZMod p))
    (fun u : ZMod p => ∑ v : ZMod p, zeta p ^ ((u, v).1 * (u, v).2).val)
    (Finset.mem_univ (0 : ZMod p))]
  dsimp only
  have hzero : ∑ v : ZMod p, zeta p ^ ((0 : ZMod p) * v).val = p := by simp
  have honz : ∑ u ∈ Finset.univ.erase (0 : ZMod p), ∑ v : ZMod p, zeta p ^ (u * v).val = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have hmul_bij : Function.Bijective (fun v : ZMod p => u * v) := zmod_mul_left_bijective hu0
    rw [Fintype.sum_bijective (fun v : ZMod p => u * v) hmul_bij _ (fun w => zeta p ^ w.val) (fun _ => rfl)]
    exact sum_zeta_zmod_eq_zero hp1
  rw [hzero, honz, add_zero]

/-- For prime p ≡ 1 [MOD 4], gaussSum p is real and (Re(gaussSum p))² = p. -/
theorem gaussSum_sq_prime_mod1 (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    (gaussSum p).im = 0 ∧ ((gaussSum p).re)^2 = p := by
  have hp_prime : Nat.Prime p := Fact.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hmul := gaussSum_mul_conj_prime p hp2
  have hex : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  rcases hex with ⟨c, hc⟩
  have hc_sq : c^2 = -1 := by rw [sq, ← hc]
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [zero_mul] at hc
    have h10 : (1 : ZMod p) = 0 := by simpa using congrArg Neg.neg hc.symm
    exact one_ne_zero h10
  have hconj : starRingEnd ℂ (gaussSum p) = gaussSum p := by
    unfold gaussSum
    rw [map_sum]
    have hbij : Function.Bijective (fun b : ZMod p => c * b) := zmod_mul_left_bijective hc0
    have hstep : ∀ b : ZMod p,
        starRingEnd ℂ (zeta p ^ (b.val ^ 2)) = zeta p ^ ((c * b).val ^ 2) := by
      intro b
      rw [star_zeta_pow]
      apply zeta_pow_eq_of_modEq
      change (p - b.val ^ 2 % p) % p ≡ (c * b).val ^ 2 [MOD p]
      rw [← ZMod.natCast_eq_natCast_iff]
      have hcast : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val
      have hsub : (((p - b.val ^ 2 % p) % p : ℕ) : ZMod p) = -(b * b) := by
        rw [ZMod.natCast_mod, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ hp_prime.pos))]
        simp [ZMod.natCast_mod, hcast, sq]
      push_cast
      rw [hsub, hcast]
      calc -(b * b) = c^2 * (b * b) := by rw [hc_sq]; ring
        _ = (c * b)^2 := by ring
    simp_rw [hstep]
    exact Fintype.sum_bijective (fun b : ZMod p => c * b) hbij _ _ (fun _ => rfl)
  rw [hconj] at hmul
  have him : (gaussSum p).im = 0 := by
    have h := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h
    linarith
  have hre : ((gaussSum p).re)^2 = p := by
    have h := congrArg Complex.re hmul
    simp [sq, him] at h ⊢
    exact h
  exact ⟨him, hre⟩

/-- For prime p ≡ 3 [MOD 4], gaussSum p is purely imaginary and (gaussSum p)² = -p. -/
theorem gaussSum_sq_prime_mod3 (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    starRingEnd ℂ (gaussSum p) = - gaussSum p ∧ (gaussSum p)^2 = -(p : ℂ) := by
  have hp_prime : Nat.Prime p := Fact.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hp1 : 1 < p := hp_prime.one_lt
  have hmul := gaussSum_mul_conj_prime p hp2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    omega
  set k : ℕ := (p - 1) / 2
  have hk_mul : 2 * k = p - 1 := by omega
  have hk_pos : 0 < k := by omega
  have hk_odd : Odd k := by rw [Nat.odd_iff]; omega
  have hsq_iff : ∀ y : ZMod p, y ≠ 0 → (IsSquare y ↔ y ^ k = 1) := by
    intro y hy
    constructor
    · rintro ⟨a, ha⟩
      have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hy ha
      calc y ^ k = (a * a) ^ k := by rw [← ha]
        _ = (a ^ 2) ^ k := by ring
        _ = a ^ (2 * k) := by rw [← pow_mul]
        _ = a ^ (p - 1) := by rw [hk_mul]
        _ = 1 := ZMod.pow_card_sub_one_eq_one ha0
    · intro hyk
      let S : Finset (ZMod p) := (Finset.univ.erase 0).image (fun x : ZMod p => x^2)
      let R : Finset (ZMod p) := Finset.univ.filter (fun x : ZMod p => x^k = 1)
      have hSR : S ⊆ R := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        calc (x^2)^k = x^(2*k) := by rw [← pow_mul]
          _ = x^(p - 1) := by rw [hk_mul]
          _ = 1 := ZMod.pow_card_sub_one_eq_one hx0
      have hS_card : S.card = k := by
        have hfib : ∀ z ∈ S, (Finset.filter (fun x : ZMod p => x^2 = z) (Finset.univ.erase 0)).card = 2 := by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
          have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
          have ha_ne : a ≠ -a := by
            intro heq
            have : (2 : ZMod p) * a = 0 := by linear_combination heq
            exact ha0 ((mul_eq_zero.mp this).resolve_left h2ne)
          have hset : Finset.filter (fun x : ZMod p => x^2 = a^2) (Finset.univ.erase 0) = {a, -a} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
              Finset.mem_insert, Finset.mem_singleton]
            rw [sq_eq_sq_iff_eq_or_eq_neg]
            constructor
            · exact fun h => h.2
            · rintro (rfl | rfl)
              · exact ⟨ha0, Or.inl rfl⟩
              · exact ⟨neg_ne_zero.mpr ha0, Or.inr rfl⟩
          rw [hset, Finset.card_pair ha_ne]
        have hsum_card := Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod p => x^2)
          (s := Finset.univ.erase 0) (t := S) (fun x hx => Finset.mem_image_of_mem _ hx)
        have herase : (Finset.univ.erase (0 : ZMod p)).card = 2 * k := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, hk_mul]
        rw [herase, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum_card
        omega
      have hR_card : R.card ≤ k := by
        let poly : Polynomial (ZMod p) := Polynomial.X ^ k - 1
        have hpoly_ne : poly ≠ 0 := by
          intro h0
          have hev := congrArg (Polynomial.eval 0) h0
          simp [poly, hk_pos.ne'] at hev
        have hsub : R.val ⊆ poly.roots := by
          intro x hx
          have hxR : x^k = 1 := (Finset.mem_filter.mp (Finset.mem_val.mp hx)).2
          rw [Polynomial.mem_roots hpoly_ne]
          simp [poly, hxR]
        have hle1 : R.card ≤ poly.roots.card :=
          Multiset.card_le_card ((Multiset.le_iff_subset R.nodup).mpr hsub)
        have hle2 : poly.roots.card ≤ poly.natDegree := Polynomial.card_roots' poly
        have hdeg : poly.natDegree ≤ k :=
          (Polynomial.natDegree_sub_le _ _).trans (max_le (Polynomial.natDegree_X_pow_le k) (by simp))
        omega
      have hSR_eq : S = R := Finset.eq_of_subset_of_card_le hSR (by omega)
      have hyR : y ∈ R := by simp [R, hyk]
      rw [← hSR_eq] at hyR
      rcases Finset.mem_image.mp hyR with ⟨x, _, rfl⟩
      exact ⟨x, sq x⟩
  have hcount : ∀ y : ZMod p,
      (Finset.univ.filter (fun x : ZMod p => x^2 = y)).card +
      (Finset.univ.filter (fun x : ZMod p => x^2 = -y)).card = 2 := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have h0 : Finset.univ.filter (fun x : ZMod p => x^2 = 0) = {0} := by
        ext x; simp [sq_eq_zero_iff]
      simp only [neg_zero, h0, Finset.card_singleton]
    · have hcard_sq : ∀ z : ZMod p, z ≠ 0 → IsSquare z →
          (Finset.univ.filter (fun x : ZMod p => x^2 = z)).card = 2 := by
        intro z hz ⟨a, ha⟩
        have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hz ha
        have ha_ne : a ≠ -a := by
          intro heq
          have : (2 : ZMod p) * a = 0 := by linear_combination heq
          exact ha0 ((mul_eq_zero.mp this).resolve_left h2ne)
        have hset : Finset.univ.filter (fun x : ZMod p => x^2 = z) = {a, -a} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          rw [ha, ← sq, sq_eq_sq_iff_eq_or_eq_neg]
        rw [hset, Finset.card_pair ha_ne]
      have hcard_nsq : ∀ z : ZMod p, ¬ IsSquare z →
          (Finset.univ.filter (fun x : ZMod p => x^2 = z)).card = 0 := by
        intro z hns
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ hx
        exact hns ⟨x, by rw [← hx, sq]⟩
      have hleg : IsSquare y ↔ ¬ IsSquare (-y) := by
        rw [hsq_iff y hy, hsq_iff (-y) (neg_ne_zero.mpr hy)]
        have hpow2 : (y ^ k)^2 = 1 := by
          calc (y ^ k)^2 = y ^ (2 * k) := by ring
            _ = y ^ (p - 1) := by rw [hk_mul]
            _ = 1 := ZMod.pow_card_sub_one_eq_one hy
        have hnegk : (-y) ^ k = -(y ^ k) := by
          rw [neg_pow, hk_odd.neg_one_pow, neg_one_mul]
        rw [hnegk]
        rcases sq_eq_one_iff.mp hpow2 with h1 | h1 <;> rw [h1]
        · constructor
          · intro _ hneg
            have : (1 : ZMod p) + 1 = 0 := by linear_combination -hneg
            exact h2ne (by linear_combination this)
          · intro _; rfl
        · constructor
          · intro h1; exfalso
            have : (1 : ZMod p) + 1 = 0 := by linear_combination -h1
            exact h2ne (by linear_combination this)
          · intro hneg; exfalso; apply hneg; norm_num
      by_cases hsq : IsSquare y
      · rw [hcard_sq y hy hsq, hcard_nsq (-y) (hleg.mp hsq)]
      · have hsq_neg : IsSquare (-y) := by_contra fun hn => hsq (hleg.mpr hn)
        rw [hcard_nsq y hsq, hcard_sq (-y) (neg_ne_zero.mpr hy) hsq_neg]
  have hanti : gaussSum p + starRingEnd ℂ (gaussSum p) = 0 := by
    have hsum1 : gaussSum p = ∑ y : ZMod p,
        ((Finset.univ.filter (fun x : ZMod p => x^2 = y)).card : ℂ) * zeta p ^ y.val := by
      unfold gaussSum
      rw [← Finset.sum_fiberwise (g := fun x : ZMod p => x^2) Finset.univ (fun x => zeta p ^ (x.val ^ 2))]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hconst : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => x^2 = y),
          zeta p ^ (x.val ^ 2) = zeta p ^ y.val := by
        intro x hx
        have hx' : x^2 = y := (Finset.mem_filter.mp hx).2
        apply zeta_pow_eq_of_modEq
        change x.val ^ 2 ≡ y.val [MOD p]
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        simp [ZMod.natCast_zmod_val, ← hx', sq]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hsum2 : starRingEnd ℂ (gaussSum p) = ∑ y : ZMod p,
        ((Finset.univ.filter (fun x : ZMod p => x^2 = -y)).card : ℂ) * zeta p ^ y.val := by
      unfold gaussSum
      rw [map_sum]
      have hre : ∑ x : ZMod p, starRingEnd ℂ (zeta p ^ (x.val ^ 2)) =
          ∑ x : ZMod p, zeta p ^ ((-(x^2)).val) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [star_zeta_pow]
        apply zeta_pow_eq_of_modEq
        change (p - x.val ^ 2 % p) % p ≡ (-(x^2)).val [MOD p]
        rw [← ZMod.natCast_eq_natCast_iff]
        have hcast : ∀ z : ZMod p, ((z.val : ℕ) : ZMod p) = z := ZMod.natCast_zmod_val
        have hsub : (((p - x.val ^ 2 % p) % p : ℕ) : ZMod p) = -(x^2) := by
          rw [ZMod.natCast_mod, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ hp_prime.pos))]
          simp [ZMod.natCast_mod, hcast, sq]
        rw [hsub, hcast]
      rw [hre, ← Finset.sum_fiberwise (g := fun x : ZMod p => -(x^2)) Finset.univ]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hconst : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => -(x^2) = y),
          zeta p ^ ((-(x^2)).val) = zeta p ^ y.val := by
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      have hflt : Finset.univ.filter (fun x : ZMod p => -(x^2) = y) =
          Finset.univ.filter (fun x : ZMod p => x^2 = -y) := by
        ext x; simp [neg_eq_iff_eq_neg]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hflt]
    rw [hsum2, hsum1, ← Finset.sum_add_distrib]
    have hcoeff2 : ∀ y : ZMod p,
        (((Finset.univ.filter (fun x : ZMod p => x^2 = y)).card : ℂ) * zeta p ^ y.val +
         ((Finset.univ.filter (fun x : ZMod p => x^2 = -y)).card : ℂ) * zeta p ^ y.val) =
        2 * zeta p ^ y.val := by
      intro y
      rw [← add_mul]
      have hc2 : ((Finset.univ.filter (fun x : ZMod p => x^2 = y)).card : ℂ) +
          ((Finset.univ.filter (fun x : ZMod p => x^2 = -y)).card : ℂ) = 2 := by
        exact_mod_cast hcount y
      rw [hc2]
    simp_rw [hcoeff2, ← Finset.mul_sum, sum_zeta_zmod_eq_zero hp1, mul_zero]
  have hconj : starRingEnd ℂ (gaussSum p) = - gaussSum p := eq_neg_of_add_eq_zero_right hanti
  refine ⟨hconj, ?_⟩
  calc (gaussSum p)^2 = -(gaussSum p * (-gaussSum p)) := by ring
    _ = -(gaussSum p * starRingEnd ℂ (gaussSum p)) := by rw [← hconj]
    _ = -(p : ℂ) := by rw [hmul]

/-- CRT factorization and radical extraction at m = 4*p for prime p ≡ 3 [MOD 4]:
    (Re(gaussSum (4*p)) / 2)² = p. -/
theorem gaussSum_four_mul_prime_mod3 (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    ((gaussSum (4 * p)).re / 2)^2 = p := by
  have hp_prime : Nat.Prime p := Fact.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  haveI : NeZero (4 * p) := ⟨mul_ne_zero (by decide) hp_prime.ne_zero⟩
  have hcop : Nat.Coprime 4 p := by
    rw [Nat.Coprime]
    rcases hp_prime.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right 4 p) with h1 | hp4
    · exact h1
    · have hd4 : p ∣ 2 * 2 := by simpa using (hp4 ▸ Nat.gcd_dvd_left 4 p)
      have hd2 : p ∣ 2 := (hp_prime.dvd_mul.mp hd4).elim id id
      have hle2 : p ≤ 2 := Nat.le_of_dvd (by decide) hd2
      have hge2 : 2 ≤ p := hp_prime.two_le
      omega
  have hcrt : gaussSum (4 * p) = 2 * (1 - Complex.I) * gaussSum p := by
    let ψ : ZMod 4 × ZMod p → ZMod (4 * p) := fun ⟨a, b⟩ =>
      (p : ZMod (4 * p)) * (a.val : ZMod (4 * p)) + (4 : ZMod (4 * p)) * (b.val : ZMod (4 * p))
    have hψ_inj : Function.Injective ψ := by
      intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      have h4p : ((4 * p : ℕ) : ℤ) ∣
          ((p * a1.val + 4 * b1.val : ℤ) - (p * a2.val + 4 * b2.val)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        exact sub_eq_zero.mpr (by simpa [ψ] using h)
      have ha : (4 : ℤ) ∣ p * ((a1.val : ℤ) - a2.val) := by
        rcases h4p with ⟨k, hk⟩
        push_cast at hk
        refine ⟨(b2.val : ℤ) - b1.val + p * k, ?_⟩
        linarith
      have ha_nat : 4 ∣ ((a1.val : ℤ) - a2.val).natAbs := by
        have h1 : 4 ∣ p * ((a1.val : ℤ) - a2.val).natAbs := by
          have := Int.natCast_dvd.mp (by simpa [Int.natAbs_mul] using ha)
          simpa [Int.natAbs_mul] using this
        exact hcop.dvd_of_dvd_mul_left h1
      have ha_lt : ((a1.val : ℤ) - a2.val).natAbs < 4 := by
        have h1 := a1.val_lt; have h2 := a2.val_lt
        rcases Int.natAbs_eq ((a1.val : ℤ) - a2.val) with habs | habs <;> omega
      have ha_zero : ((a1.val : ℤ) - a2.val).natAbs = 0 :=
        Nat.eq_zero_of_dvd_of_lt ha_nat ha_lt
      have hb : (p : ℤ) ∣ 4 * ((b1.val : ℤ) - b2.val) := by
        rcases h4p with ⟨k, hk⟩
        push_cast at hk
        refine ⟨(a2.val : ℤ) - a1.val + 4 * k, ?_⟩
        linarith
      have hb_nat : p ∣ ((b1.val : ℤ) - b2.val).natAbs := by
        have h1 : p ∣ 4 * ((b1.val : ℤ) - b2.val).natAbs := by
          have := Int.natCast_dvd.mp (by simpa [Int.natAbs_mul] using hb)
          simpa [Int.natAbs_mul] using this
        exact hcop.symm.dvd_of_dvd_mul_left h1
      have hb_lt : ((b1.val : ℤ) - b2.val).natAbs < p := by
        have h1 := b1.val_lt; have h2 := b2.val_lt
        rcases Int.natAbs_eq ((b1.val : ℤ) - b2.val) with habs | habs <;> omega
      have hb_zero : ((b1.val : ℤ) - b2.val).natAbs = 0 :=
        Nat.eq_zero_of_dvd_of_lt hb_nat hb_lt
      have ha_eq : a1 = a2 := ZMod.val_injective 4 (by
        have := Int.natAbs_eq_zero.mp ha_zero; omega)
      have hb_eq : b1 = b2 := ZMod.val_injective p (by
        have := Int.natAbs_eq_zero.mp hb_zero; omega)
      exact Prod.ext ha_eq hb_eq
    have hψ_bij : Function.Bijective ψ :=
      (Fintype.bijective_iff_injective_and_card ψ).mpr ⟨hψ_inj, by simp [ZMod.card]⟩
    unfold gaussSum
    rw [(Fintype.sum_bijective ψ hψ_bij
      (fun ab => zeta (4 * p) ^ ((ψ ab).val ^ 2))
      (fun z => zeta (4 * p) ^ (z.val ^ 2))
      (fun _ => rfl)).symm]
    rw [Fintype.sum_prod_type]
    have hfactor : ∀ a : ZMod 4, ∀ b : ZMod p,
        zeta (4 * p) ^ ((ψ (a, b)).val ^ 2) =
          (zeta 4 ^ (p * a.val ^ 2)) * (zeta p ^ (4 * b.val ^ 2)) := by
      intro a b
      have hmod1 : (ψ (a, b)).val ^ 2 ≡ p^2 * a.val^2 + 16 * b.val^2 [MOD 4 * p] := by
        change (ψ (a, b)).val ^ 2 ≡ p^2 * a.val^2 + 16 * b.val^2 [MOD 4 * p]
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        simp only [ψ, ZMod.natCast_zmod_val]
        calc ((p : ZMod (4*p)) * a.val + 4 * b.val)^2
            = (p : ZMod (4*p))^2 * a.val^2 +
                2 * ((4 * p : ℕ) : ZMod (4*p)) * (a.val * b.val) + 16 * b.val^2 := by
              push_cast; ring
          _ = (p : ZMod (4*p))^2 * a.val^2 + 16 * b.val^2 := by
            rw [ZMod.natCast_self]; ring
      rw [zeta_pow_eq_of_modEq hmod1, pow_add]
      have hz4 : zeta (4 * p) ^ p = zeta 4 := by
        unfold zeta
        rw [← Complex.exp_nat_mul]
        congr 1
        have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
        push_cast; field_simp [hp0]
      have hzp : zeta (4 * p) ^ 4 = zeta p := by
        unfold zeta
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast; field_simp
      congr 1
      · calc zeta (4 * p) ^ (p ^ 2 * a.val ^ 2)
            = (zeta (4 * p) ^ p) ^ (p * a.val ^ 2) := by rw [← pow_mul]; congr 1; ring
          _ = zeta 4 ^ (p * a.val ^ 2) := by rw [hz4]
      · calc zeta (4 * p) ^ (16 * b.val ^ 2)
            = (zeta (4 * p) ^ 4) ^ (4 * b.val ^ 2) := by rw [← pow_mul]; congr 1; ring
          _ = zeta p ^ (4 * b.val ^ 2) := by rw [hzp]
    simp_rw [hfactor, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    have hzeta4 : zeta 4 = Complex.I := by
      unfold zeta
      rw [show 2 * Real.pi * Complex.I / ((4 : ℕ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two,
        Complex.ofReal_zero, Complex.ofReal_one, zero_add, one_mul]
    have hsum4 : ∑ a : ZMod 4, zeta 4 ^ (p * a.val ^ 2) = 2 * (1 - Complex.I) := by
      rw [hzeta4]
      have hp_mod4 : ∀ k : ℕ, Complex.I ^ (p * k) = (-Complex.I) ^ k := by
        intro k
        rw [pow_mul]
        have hi_p : Complex.I ^ p = -Complex.I := by
          have : p = 4 * (p / 4) + 3 := by omega
          rw [this, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
          norm_num [pow_succ, Complex.I_sq]
        rw [hi_p]
      simp_rw [hp_mod4]
      change ∑ a : Fin 4, (-Complex.I) ^ (a.val ^ 2) = 2 * (1 - Complex.I)
      rw [Fin.sum_univ_four]
      have hI9 : (-Complex.I) ^ 9 = -Complex.I := by
        calc (-Complex.I) ^ 9
            = ((-Complex.I) ^ 2) ^ 4 * (-Complex.I) := by ring
          _ = (-1) ^ 4 * (-Complex.I) := by rw [neg_sq, Complex.I_sq]
          _ = -Complex.I := by norm_num
      norm_num [Complex.I_sq]
      rw [hI9]
      ring
    have hsump : ∑ b : ZMod p, zeta p ^ (4 * b.val ^ 2) = gaussSum p := by
      have hbij2 : Function.Bijective (fun b : ZMod p => 2 * b) := by
        have h2ne : (2 : ZMod p) ≠ 0 := by
          intro h
          have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
          have : p ≤ 2 := Nat.le_of_dvd (by decide) hd
          omega
        exact zmod_mul_left_bijective h2ne
      unfold gaussSum
      rw [← Fintype.sum_bijective (fun b : ZMod p => 2 * b) hbij2 _ (fun b => zeta p ^ (b.val ^ 2)) (fun _ => rfl)]
      refine Finset.sum_congr rfl fun b _ => ?_
      apply zeta_pow_eq_of_modEq
      change 4 * b.val ^ 2 ≡ (2 * b).val ^ 2 [MOD p]
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      have hcast : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val
      rw [hcast b, hcast (2 * b)]; ring
    rw [hsum4, hsump]
    rfl
  have ⟨hconj, hsq⟩ := gaussSum_sq_prime_mod3 p hp
  have hre_formula : ((gaussSum (4 * p)).re : ℂ) = -2 * Complex.I * gaussSum p := by
    have hre2 : (2 : ℂ) * (gaussSum (4 * p)).re =
        gaussSum (4 * p) + starRingEnd ℂ (gaussSum (4 * p)) := by
      simpa [mul_comm] using (Complex.add_conj (gaussSum (4 * p))).symm
    have hconj4p : starRingEnd ℂ (gaussSum (4 * p)) = 2 * (1 + Complex.I) * (-gaussSum p) := by
      rw [hcrt, map_mul, map_mul, map_sub, map_one, Complex.conj_I, hconj]
      simp only [map_ofNat]
      ring
    have hsum_eq : gaussSum (4 * p) + starRingEnd ℂ (gaussSum (4 * p)) =
        -4 * Complex.I * gaussSum p := by
      rw [hconj4p, hcrt]; ring
    rw [hsum_eq] at hre2
    linear_combination hre2 / 2
  have hsq_c : (((gaussSum (4 * p)).re / 2 : ℂ))^2 = p := by
    calc (((gaussSum (4 * p)).re / 2 : ℂ))^2
        = (-Complex.I * gaussSum p)^2 := by
          rw [show (gaussSum (4 * p)).re / 2 = -Complex.I * gaussSum p by linear_combination hre_formula / 2]
      _ = Complex.I^2 * (gaussSum p)^2 := by ring
      _ = (-1) * (-(p : ℂ)) := by rw [Complex.I_sq, hsq]
      _ = p := by ring
  exact_mod_cast hsq_c

/-! ## Part 3: Instantiation at d = 2048 Factors {5, 12, 409, 2732} -/

theorem d2048_gauss_radicals :
    ((gaussSum 5).re)^2 = 5 ∧
    ((gaussSum 12).re / 2)^2 = 3 ∧
    ((gaussSum 409).re)^2 = 409 ∧
    ((gaussSum 2732).re / 2)^2 = 683 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 409) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 683) := ⟨by norm_num⟩
  refine ⟨(gaussSum_sq_prime_mod1 5 (by decide)).2,
          ?_,
          (gaussSum_sq_prime_mod1 409 (by decide)).2,
          ?_⟩
  · simpa using gaussSum_four_mul_prime_mod3 3 (by decide)
  · simpa using gaussSum_four_mul_prime_mod3 683 (by decide)

theorem d2048_discriminant_product :
    (((gaussSum 5).re * ((gaussSum 12).re / 2) *
      (gaussSum 409).re * ((gaussSum 2732).re / 2))^2) = (4190205 : ℝ) := by
  rcases d2048_gauss_radicals with ⟨h5, h3, h409, h683⟩
  calc (((gaussSum 5).re * ((gaussSum 12).re / 2) *
         (gaussSum 409).re * ((gaussSum 2732).re / 2))^2)
      = ((gaussSum 5).re)^2 * ((gaussSum 12).re / 2)^2 *
        ((gaussSum 409).re)^2 * ((gaussSum 2732).re / 2)^2 := by ring
    _ = 5 * 3 * 409 * 683 := by rw [h5, h3, h409, h683]
    _ = 4190205 := by norm_num

end Imscribing.Millennium.GaussSumMonomial