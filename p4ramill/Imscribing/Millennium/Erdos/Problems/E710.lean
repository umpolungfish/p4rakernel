import Mathlib

/-!
# Erdős #710 — divisible distinct tuples
-/

namespace Erdos710

open Finset

def Adm (n : ℕ) (L : ℤ) (a : Fin n → ℤ) : Prop :=
  (∀ i : Fin n, (n : ℤ) < a i ∧ a i < (n : ℤ) + L) ∧
  Function.Injective a ∧
  (∀ i : Fin n, ((i.val + 1 : ℕ) : ℤ) ∣ a i)

def Lam (n : ℕ) : Set ℤ :=
  {L : ℤ | 0 ≤ L ∧ ∃ a : Fin n → ℤ, Adm n L a}

noncomputable def f (n : ℕ) : ℤ := sInf (Lam n)

def witness (n : ℕ) (k : Fin n) : ℤ :=
  ((k.val + 1 : ℕ) : ℤ) * ((n : ℤ) + 1)

theorem witness_adm (n : ℕ) : Adm n ((n : ℤ)^2 + 1) (witness n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hk1 : (1 : ℤ) ≤ ((k.val + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k.val)
    have hkn : ((k.val + 1 : ℕ) : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast Nat.succ_le_of_lt k.isLt
    constructor
    · have hle : (n : ℤ) + 1 ≤ witness n k := by
        unfold witness
        calc (n : ℤ) + 1 = 1 * ((n : ℤ) + 1) := by ring
          _ ≤ ((k.val + 1 : ℕ) : ℤ) * ((n : ℤ) + 1) :=
              mul_le_mul_of_nonneg_right hk1 (by linarith)
      linarith
    · have hle :
          ((k.val + 1 : ℕ) : ℤ) * ((n : ℤ) + 1) ≤ (n : ℤ) * ((n : ℤ) + 1) :=
        mul_le_mul_of_nonneg_right hkn (by linarith)
      have hlt : (n : ℤ) * ((n : ℤ) + 1) < (n : ℤ) + ((n : ℤ)^2 + 1) := by
        nlinarith
      unfold witness
      linarith
  · intro i j hij
    unfold witness at hij
    have hn : ((n : ℤ) + 1) ≠ 0 := by positivity
    have h : ((i.val + 1 : ℕ) : ℤ) = ((j.val + 1 : ℕ) : ℤ) :=
      mul_right_cancel₀ hn hij
    exact Fin.ext (by omega)
  · intro k
    exact dvd_mul_right _ _

theorem mem_Lam_sq_add_one (n : ℕ) : ((n : ℤ)^2 + 1) ∈ Lam n :=
  ⟨by nlinarith [Int.natCast_nonneg n, sq_nonneg (n : ℤ)], witness n, witness_adm n⟩

theorem Lam_nonempty (n : ℕ) : (Lam n).Nonempty :=
  ⟨_, mem_Lam_sq_add_one n⟩

theorem Lam_bddBelow (n : ℕ) : BddBelow (Lam n) :=
  ⟨0, fun _ hL => hL.1⟩

theorem f_le_sq_add_one (n : ℕ) : f n ≤ (n : ℤ)^2 + 1 := by
  unfold f
  exact csInf_le (Lam_bddBelow n) (mem_Lam_sq_add_one n)

theorem Lam_zero : Lam 0 = Set.Ici (0 : ℤ) := by
  ext L
  simp only [Lam, Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro x y _; exact Subsingleton.elim x y
    · intro i; exact Fin.elim0 i

theorem f_zero : f 0 = 0 := by
  unfold f
  rw [Lam_zero, csInf_Ici]

theorem le_of_mem_Lam {n : ℕ} {L : ℤ} (h : L ∈ Lam n) : (n : ℤ) ≤ L := by
  obtain ⟨hL0, a, ha⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hL0
  · have hinj : Function.Injective a := ha.2.1
    have hsub : Finset.univ.image a ⊆ Finset.Ico ((n : ℤ) + 1) ((n : ℤ) + L) := by
      intro m hm
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨h1, h2⟩ := ha.1 i
      rw [Finset.mem_Ico]
      exact ⟨by linarith, by linarith⟩
    have hcard : n ≤ (Finset.Ico ((n : ℤ) + 1) ((n : ℤ) + L)).card := by
      calc n = (Finset.univ.image a).card := by
              rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    rw [Int.card_Ico] at hcard
    have heq : (n : ℤ) + L - ((n : ℤ) + 1) = L - 1 := by ring
    rw [heq] at hcard
    by_cases hLm1 : (0 : ℤ) ≤ L - 1
    · have hcast : (n : ℤ) ≤ (((L - 1).toNat : ℕ) : ℤ) := by exact_mod_cast hcard
      rw [Int.toNat_of_nonneg hLm1] at hcast
      linarith
    · push_neg at hLm1
      have hzero : ((L - 1).toNat : ℕ) = 0 := by
        rw [Int.toNat_eq_zero]; omega
      rw [hzero] at hcard
      omega

theorem le_f (n : ℕ) : (n : ℤ) ≤ f n := by
  unfold f
  exact le_csInf (Lam_nonempty n) (fun _ hL => le_of_mem_Lam hL)

def multIn (n : ℕ) (L : ℤ) (k : Fin n) : Finset ℤ :=
  (Finset.Ico ((n : ℤ) + 1) ((n : ℤ) + L)).filter (fun m => ((k.val + 1 : ℕ) : ℤ) ∣ m)

theorem hall_criterion (n : ℕ) (L : ℤ) :
    (∃ a : Fin n → ℤ, Adm n L a) ↔
    (∀ S : Finset (Fin n), S.card ≤ (S.biUnion (multIn n L)).card) := by
  classical
  have key := Finset.all_card_le_biUnion_card_iff_exists_injective (multIn n L)
  constructor
  · rintro ⟨a, ha⟩
    have hmem : ∀ k : Fin n, a k ∈ multIn n L k := by
      intro k
      simp only [multIn, Finset.mem_filter, Finset.mem_Ico]
      obtain ⟨h1, h2⟩ := ha.1 k
      exact ⟨⟨by linarith, by linarith⟩, ha.2.2 k⟩
    intro S
    exact key.mpr ⟨a, ha.2.1, hmem⟩ S
  · intro h
    obtain ⟨a, hinj, hmem⟩ := key.mp h
    refine ⟨a, ?_, hinj, ?_⟩
    · intro k
      have hk := hmem k
      simp only [multIn, Finset.mem_filter, Finset.mem_Ico] at hk
      exact ⟨by linarith [hk.1.1], by linarith [hk.1.2]⟩
    · intro k
      have hk := hmem k
      simp only [multIn, Finset.mem_filter] at hk
      exact hk.2

def AsymptoticClaim : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ᶠ (n : ℕ) in Filter.atTop,
      Real.exp (c₁ * n) ≤ (f n : ℝ) ∧ (f n : ℝ) ≤ Real.exp (c₂ * n)

theorem exp_dominates_quadratic (c : ℝ) (hc : 0 < c) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      (n : ℝ)^2 + 1 < Real.exp (c * n) := by
  have hcn : Filter.Tendsto (fun n : ℕ => c * (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have h_cube : Filter.Tendsto (fun t : ℝ => Real.exp t / t^3) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_div_pow_atTop 3
  have h_comp : Filter.Tendsto
      (fun n : ℕ => Real.exp (c * n) / (c * n)^3) Filter.atTop Filter.atTop :=
    h_cube.comp hcn
  have h_linT : Filter.Tendsto (fun n : ℕ => (2 * c^3) * (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2 * c^3)
  have h_ge2 : ∀ᶠ (n : ℕ) in Filter.atTop,
      Real.exp (c * n) / (c * n)^3 ≥ 2 :=
    h_comp.eventually (Filter.eventually_atTop.2 ⟨2, fun _ hy => hy⟩)
  have h_lin : ∀ᶠ (n : ℕ) in Filter.atTop, (2 * c^3 * (n : ℝ)) ≥ 2 :=
    h_linT.eventually (Filter.eventually_atTop.2 ⟨2, fun _ hy => hy⟩)
  have h_ge2n : ∀ᶠ (n : ℕ) in Filter.atTop, (2 : ℕ) ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩
  filter_upwards [h_ge2, h_lin, h_ge2n] with n h2 h3 hn2
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hcn_pos : (0 : ℝ) < c * (n : ℝ) := mul_pos hc (by linarith)
  have hcube_pos : (0 : ℝ) < (c * n)^3 := by positivity
  have h2_mul : 2 * (c * n)^3 ≤ Real.exp (c * n) := by
    have h2' : 2 ≤ Real.exp (c * n) / (c * n)^3 := h2
    have key : 2 * (c * n)^3 ≤ Real.exp (c * n) / (c * n)^3 * (c * n)^3 :=
      mul_le_mul_of_nonneg_right h2' (le_of_lt hcube_pos)
    have heq : Real.exp (c * n) / (c * n)^3 * (c * n)^3 = Real.exp (c * n) :=
      div_mul_cancel₀ _ (ne_of_gt hcube_pos)
    rw [heq] at key
    exact key
  have h_goal : (n : ℝ)^2 + 1 < 2 * (c * n)^3 := by
    have h_expand : 2 * (c * n)^3 = (2 * c^3 * (n : ℝ)) * (n : ℝ)^2 := by ring
    rw [h_expand]
    have hsq : (4 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
    nlinarith
  linarith

theorem not_AsymptoticClaim : ¬ AsymptoticClaim := by
  rintro ⟨c₁, c₂, hc₁, -, hbound⟩
  have hle : ∀ᶠ (n : ℕ) in Filter.atTop,
      Real.exp (c₁ * (n : ℝ)) ≤ (n : ℝ)^2 + 1 := by
    filter_upwards [hbound] with n hn
    have h3 : (f n : ℝ) ≤ (n : ℝ)^2 + 1 := by
      exact_mod_cast f_le_sq_add_one n
    linarith [hn.1, hn.2]
  have hgt := exp_dominates_quadratic c₁ hc₁
  have h_and : ∀ᶠ (n : ℕ) in Filter.atTop,
      Real.exp (c₁ * (n : ℝ)) ≤ (n : ℝ)^2 + 1 ∧
      (n : ℝ)^2 + 1 < Real.exp (c₁ * (n : ℝ)) := hle.and hgt
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_and
  obtain ⟨hP, hQ⟩ := hN N le_rfl
  linarith

end Erdos710