import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Imscribing.YangMills.WilsonFrobeniusAndSmeared4D

noncomputable section

namespace Imscribing.YangMills.LatticeRiemann4D

open scoped BigOperators

/-- One-dimensional Riemann bound for `(1 + (a * n)^2)⁻¹` over positive integers:
`∑_{n=1}^N a / (1 + (a * n)^2) ≤ 3` for `0 < a ≤ 1`. -/
lemma oneD_lattice_riemann_inv_sq_le_four (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, a / (1 + (a * (n : ℝ)) ^ 2) ≤ 3 := by
  let M : ℕ := Nat.floor (1 / a) + 1
  have hM_pos : 0 < M := Nat.succ_pos _
  have hMa : 1 < a * (M : ℝ) := by
    have h1 : 1 / a < (M : ℝ) := by exact_mod_cast Nat.lt_floor_add_one (1 / a)
    calc 1 = a * (1 / a) := (mul_one_div_cancel ha.ne').symm
      _ < a * (M : ℝ) := mul_lt_mul_of_pos_left h1 ha
  have h_head : ∑ n ∈ Finset.Icc 1 (min N M), a / (1 + (a * (n : ℝ)) ^ 2) ≤ 2 := by
    calc ∑ n ∈ Finset.Icc 1 (min N M), a / (1 + (a * (n : ℝ)) ^ 2)
        ≤ ∑ _n ∈ Finset.Icc 1 (min N M), a :=
          Finset.sum_le_sum fun _ _ => div_le_self ha.le (le_add_of_nonneg_right (sq_nonneg _))
      _ = ((min N M : ℕ) : ℝ) * a := by simp [Nat.card_Icc, nsmul_eq_mul]
      _ ≤ (M : ℝ) * a := by gcongr; exact min_le_right _ _
      _ = ((Nat.floor (1 / a) : ℝ) + 1) * a := by push_cast [M]; rfl
      _ ≤ (1 / a + 1) * a := by gcongr; exact Nat.floor_le (by positivity)
      _ = 1 + a := by field_simp [ha.ne']
      _ ≤ 2 := by linarith
  by_cases hNM : N ≤ M
  · have : min N M = N := min_eq_left hNM
    rw [this] at h_head
    linarith
  · have hMN : M < N := lt_of_not_ge hNM
    have hsplit : Finset.Icc 1 N = Finset.Icc 1 M ∪ Finset.Icc (M + 1) N := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    rw [hsplit, Finset.sum_union (Finset.disjoint_iff_ne.mpr (fun x hx y hy => by
      simp only [Finset.mem_Icc] at hx hy; omega))]
    have h_head' : ∑ n ∈ Finset.Icc 1 M, a / (1 + (a * (n : ℝ)) ^ 2) ≤ 2 := by
      simpa [min_eq_right hMN.le] using h_head
    have h_tail : ∑ n ∈ Finset.Icc (M + 1) N, a / (1 + (a * (n : ℝ)) ^ 2) ≤ 1 := by
      have h_eq : ∑ n ∈ Finset.Icc (M + 1) N, a / (1 + (a * (n : ℝ)) ^ 2) =
          ∑ k ∈ Finset.range (N - M), a / (1 + (a * ((M + k + 1 : ℕ) : ℝ)) ^ 2) := by
        have hIcc : Finset.Icc (M + 1) N = Finset.Ico (M + 1) (N + 1) := by
          ext n; simp [Finset.mem_Icc, Finset.mem_Ico]
        rw [hIcc, Finset.sum_Ico_eq_sum_range, show N + 1 - (M + 1) = N - M by omega]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show M + 1 + k = M + k + 1 by omega]
      rw [h_eq]
      have h_le : ∀ k ∈ Finset.range (N - M),
          a / (1 + (a * ((M + k + 1 : ℕ) : ℝ)) ^ 2) ≤
          1 / (a * ((M + k : ℕ) : ℝ)) - 1 / (a * ((M + (k + 1) : ℕ) : ℝ)) := by
        intro k _
        have hpos1 : 0 < a * ((M + k : ℕ) : ℝ) := by positivity
        have hpos2 : 0 < a * ((M + (k + 1) : ℕ) : ℝ) := by positivity
        have h1 : (1 : ℝ) < a * ((M + k : ℕ) : ℝ) := by
          have : (M : ℝ) ≤ ((M + k : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_add_right _ _)
          linarith [mul_le_mul_of_nonneg_left this ha.le]
        rw [div_sub_div _ _ hpos1.ne' hpos2.ne', div_le_div_iff₀ (by positivity) (mul_pos hpos1 hpos2)]
        have hcast1 : ((M + (k + 1) : ℕ) : ℝ) = ((M + k : ℕ) : ℝ) + 1 := by push_cast; ring
        have hcast2 : ((M + k + 1 : ℕ) : ℝ) = ((M + k : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hcast1, hcast2]
        nlinarith [sq_nonneg a]
      calc ∑ k ∈ Finset.range (N - M), a / (1 + (a * ((M + k + 1 : ℕ) : ℝ)) ^ 2)
          ≤ ∑ k ∈ Finset.range (N - M),
              (1 / (a * ((M + k : ℕ) : ℝ)) - 1 / (a * ((M + (k + 1) : ℕ) : ℝ))) :=
            Finset.sum_le_sum h_le
        _ = 1 / (a * ((M + 0 : ℕ) : ℝ)) - 1 / (a * ((M + (N - M) : ℕ) : ℝ)) :=
            Finset.sum_range_sub' (fun k => 1 / (a * ((M + k : ℕ) : ℝ))) (N - M)
        _ ≤ 1 / (a * (M : ℝ)) := by simp; positivity
        _ ≤ 1 := div_le_one_of_le₀ hMa.le (by positivity)
    linarith

end Imscribing.YangMills.LatticeRiemann4D

namespace Imscribing.YangMills.LatticeRiemannBound4D

open MeasureTheory
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonFrobenius4D
open Imscribing.YangMills.LatticeRiemann4D

private lemma zmod_1d_riemann_le_four (L : ℕ) [NeZero L] {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∑ v : ZMod L, a / (1 + a * (v.val : ℝ)) ^ 2 ≤ 4 := by
  classical
  let g : ℕ → ℝ := fun n => a / (1 + a * (n : ℝ)) ^ 2
  have hg_nn : ∀ n, 0 ≤ g n := fun _ => by positivity
  have h_pos_bound : ∀ n : ℕ, g n ≤ a / (1 + (a * (n : ℝ)) ^ 2) := by
    intro n
    refine div_le_div_of_nonneg_left ha0.le (by positivity) ?_
    have hnn : 0 ≤ a * (n : ℝ) := by positivity
    nlinarith
  have h_eq : (∑ v : ZMod L, g v.val) = ∑ n ∈ Finset.range L, g n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
    change (∑ v : Fin (m + 1), g v.val) = ∑ n ∈ Finset.range (m + 1), g n
    rw [Fin.sum_univ_eq_sum_range]
  rw [h_eq]
  have hL : 0 < L := NeZero.pos L
  have hsplit : Finset.range L = insert 0 (Finset.Icc 1 (L - 1)) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0_mem : (0 : ℕ) ∉ Finset.Icc 1 (L - 1) := by simp
  rw [hsplit, Finset.sum_insert h0_mem]
  have hg0 : g 0 ≤ 1 := by simp [g, ha1]
  have h_tail : (∑ n ∈ Finset.Icc 1 (L - 1), g n) ≤ 3 :=
    le_trans (Finset.sum_le_sum fun n _ => h_pos_bound n)
      (oneD_lattice_riemann_inv_sq_le_four a ha0 ha1 (L - 1))
  linarith

/-- **Uniform Schwartz Bound on `smearedPlaqSchwinger` (`O((|Z_ren| * 8192)^n)`).** -/
theorem smearedPlaqSchwinger_uniform_schwartz_bound
    (N L n : ℕ) [NeZero N] [NeZero L]
    {a β : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hβ : 0 ≤ β) (Z_ren : ℝ)
    [MeasurableSpace (LinkConfig N L)] (μ : Measure (LinkConfig N L)) [IsProbabilityMeasure μ]
    (h_act_meas : Measurable (fun U : LinkConfig N L => wilsonAction N L β U))
    (h_prod_meas : ∀ xs : Fin n → Lat4 L,
      Measurable (fun U : LinkConfig N L => (∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ)))
    (f : EuclideanSchwartz n) :
    ‖smearedPlaqSchwinger N L n a β Z_ren μ f‖ ≤
      (|Z_ren| * 8192) ^ n *
        ∑ j ∈ Finset.range (8 * n + 1),
          ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f := by
  have h_1d := zmod_1d_riemann_le_four L ha0 ha1
  have h_4d : ∑ x : Lat4 L, ∏ μ : Fin 4, (a / (1 + a * ((x μ).val : ℝ)) ^ 2) ≤ 256 := by
    have h_prod_sum :
        (∑ x : Lat4 L, ∏ μ : Fin 4, (a / (1 + a * ((x μ).val : ℝ)) ^ 2)) =
        ∏ _μ : Fin 4, ∑ v : ZMod L, a / (1 + a * (v.val : ℝ)) ^ 2 :=
      (Fintype.prod_sum (fun (_ : Fin 4) (v : ZMod L) =>
        a / (1 + a * (v.val : ℝ)) ^ 2)).symm
    rw [h_prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h_nn : 0 ≤ ∑ v : ZMod L, a / (1 + a * (v.val : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    calc (∑ v : ZMod L, a / (1 + a * (v.val : ℝ)) ^ 2) ^ 4 ≤ 4 ^ 4 :=
          pow_le_pow_left₀ h_nn h_1d 4
      _ = 256 := by norm_num
  have h_nd :
      (∑ xs : Fin n → Lat4 L, ∏ k : Fin n, ∏ μ : Fin 4,
          (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) ≤ (256 : ℝ) ^ n := by
    have h_prod_sum :
        (∑ xs : Fin n → Lat4 L, ∏ k : Fin n, ∏ μ : Fin 4,
          (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) =
        ∏ _k : Fin n, ∑ x : Lat4 L, ∏ μ : Fin 4,
          (a / (1 + a * ((x μ).val : ℝ)) ^ 2) :=
      (Fintype.prod_sum (fun (_ : Fin n) (x : Lat4 L) =>
        ∏ μ : Fin 4, (a / (1 + a * ((x μ).val : ℝ)) ^ 2))).symm
    rw [h_prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h_nn : 0 ≤ ∑ x : Lat4 L, ∏ μ : Fin 4, (a / (1 + a * ((x μ).val : ℝ)) ^ 2) :=
      Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity
    exact pow_le_pow_left₀ h_nn h_4d n
  let S_semi : ℝ := ∑ j ∈ Finset.range (8 * n + 1),
    ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f
  have hS_nn : 0 ≤ S_semi := Finset.sum_nonneg fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  have h_pt : ∀ xs : Fin n → Lat4 L,
      a ^ (4 * n) * ‖f (fun k => latSiteToSpacetime L a (xs k))‖ ≤
        S_semi * (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) := by
    intro xs
    let x_phys : Fin n → Spacetime4 := fun k => latSiteToSpacetime L a (xs k)
    have h_coord_le : ∀ k : Fin n, ∀ μ : Fin 4,
        1 + a * ((xs k μ).val : ℝ) ≤ 1 + ‖x_phys‖ := by
      intro k μ
      have h1 : a * ((xs k μ).val : ℝ) = ‖(x_phys k) μ‖ := by
        change a * ((xs k μ).val : ℝ) = ‖a * ((xs k μ).val : ℝ)‖
        rw [Real.norm_of_nonneg (mul_nonneg ha0.le (Nat.cast_nonneg _))]
      have h2 : ‖(x_phys k) μ‖ ≤ ‖x_phys k‖ := PiLp.norm_apply_le (x_phys k) μ
      have h3 : ‖x_phys k‖ ≤ ‖x_phys‖ := norm_le_pi_norm x_phys k
      linarith
    have h_prod_den :
        (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * ((xs k μ).val : ℝ)) ^ 2) ≤
          (1 + ‖x_phys‖) ^ (8 * n) := by
      calc (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * ((xs k μ).val : ℝ)) ^ 2)
          ≤ ∏ _k : Fin n, ∏ _μ : Fin 4, (1 + ‖x_phys‖) ^ 2 := by
            refine Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
              fun k _ => Finset.prod_le_prod (fun _ _ => by positivity) fun μ _ =>
                pow_le_pow_left₀ (by positivity) (h_coord_le k μ) 2
        _ = (1 + ‖x_phys‖) ^ (8 * n) := by
            simp [Finset.prod_const, ← pow_mul]
    have h_f_bound : (1 + ‖x_phys‖) ^ (8 * n) * ‖f x_phys‖ ≤ S_semi := by
      rw [add_comm, add_pow, Finset.sum_mul]
      dsimp [S_semi]
      refine Finset.sum_le_sum fun j _ => ?_
      have h_le_s : ‖x_phys‖ ^ j * ‖f x_phys‖ ≤ SchwartzMap.seminorm ℂ j 0 f := by
        simpa [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ j 0 f x_phys
      calc ‖x_phys‖ ^ j * 1 ^ (8 * n - j) * ((8 * n).choose j : ℝ) * ‖f x_phys‖
          = ((8 * n).choose j : ℝ) * (‖x_phys‖ ^ j * ‖f x_phys‖) := by ring
        _ ≤ ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f :=
            mul_le_mul_of_nonneg_left h_le_s (Nat.cast_nonneg _)
    have h_a_eq : a ^ (4 * n) =
        (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * ((xs k μ).val : ℝ)) ^ 2) *
        (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) := by
      have ha4 : a ^ (4 * n) = ∏ _k : Fin n, ∏ _μ : Fin 4, a := by
        simp [Finset.prod_const, ← pow_mul, mul_comm]
      rw [ha4, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun μ _ => ?_
      have hne : (1 + a * ((xs k μ).val : ℝ)) ^ 2 ≠ 0 := by positivity
      field_simp [hne]
    rw [h_a_eq, mul_assoc]
    calc (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * ((xs k μ).val : ℝ)) ^ 2) *
          ((∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) * ‖f x_phys‖)
        = ((∏ k : Fin n, ∏ μ : Fin 4, (1 + a * ((xs k μ).val : ℝ)) ^ 2) * ‖f x_phys‖) *
          (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) := by ring
      _ ≤ S_semi * (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right h_prod_den (norm_nonneg _)) h_f_bound)
            (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
  have h_base := smearedPlaqSchwinger_norm_le N L n ha0.le hβ Z_ren μ h_act_meas h_prod_meas f
  have h_split : (|Z_ren| * 32 * a ^ 4) ^ n = (|Z_ren| * 32) ^ n * a ^ (4 * n) := by
    rw [mul_pow, ← pow_mul, mul_comm 4 n]
  rw [h_split, mul_assoc, Finset.mul_sum] at h_base
  refine le_trans h_base ?_
  calc (|Z_ren| * 32) ^ n *
        ∑ xs : Fin n → Lat4 L, a ^ (4 * n) * ‖f (fun k => latSiteToSpacetime L a (xs k))‖
      ≤ (|Z_ren| * 32) ^ n *
          ∑ xs : Fin n → Lat4 L, S_semi *
            (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun xs _ => h_pt xs) (by positivity)
    _ = (|Z_ren| * 32) ^ n * (S_semi * ∑ xs : Fin n → Lat4 L,
          ∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * ((xs k μ).val : ℝ)) ^ 2)) := by
        rw [← Finset.mul_sum]
    _ ≤ (|Z_ren| * 32) ^ n * (S_semi * (256 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_nd hS_nn) (by positivity)
    _ = (|Z_ren| * 8192) ^ n * S_semi := by
        have h81 : (8192 : ℝ) = 32 * 256 := by norm_num
        rw [h81]
        simp only [mul_pow]
        ring

end Imscribing.YangMills.LatticeRiemannBound4D