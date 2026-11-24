import Mathlib

/-!
# Uniform sector states (Definition 5.1)

Register of `m` coordinates, each `T` (`true`) or `F` (`false`).
Basis state = string `x : Fin m → Bool`. Weight = number of `T` coordinates.
`dicke m k` = `(m choose k)^(-1/2) ∑_{wt x = k} |x⟩`, as an amplitude function `(Fin m → Bool) → ℂ`.
`ip` is the standard ℓ² inner product (conjugate-linear in the first slot).
-/

open Finset

namespace Dicke

/-- weight: number of coordinates equal to `T`. -/
def wt {m : ℕ} (x : Fin m → Bool) : ℕ := (univ.filter fun i => x i = true).card

/-- the weight-`k` sector. -/
def sector (m k : ℕ) : Finset (Fin m → Bool) := univ.filter fun x => wt x = k

/-- the weight-`k` sector has `(m choose k)` strings. -/
theorem card_sector (m k : ℕ) : (sector m k).card = m.choose k := by
  have h : (sector m k).card = (powersetCard k (univ : Finset (Fin m))).card := by
    refine Finset.card_bij (fun x _ => univ.filter fun i => x i = true) ?_ ?_ ?_
    · intro x hx
      rw [mem_powersetCard]
      refine ⟨subset_univ _, ?_⟩
      simpa [sector, wt] using hx
    · intro x _ y _ hxy
      funext i
      have h1 := congrArg (fun s => i ∈ s) hxy
      simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at h1
      cases hx : x i <;> cases hy : y i <;> simp_all
    · intro s hs
      rw [mem_powersetCard] at hs
      have hs' : (univ.filter fun i => decide (i ∈ s) = true) = s := by
        ext i; simp
      refine ⟨fun i => decide (i ∈ s), ?_, hs'⟩
      simp only [sector, wt, mem_filter, mem_univ, true_and]
      rw [hs']
      exact hs.2
  rw [h, card_powersetCard, card_univ, Fintype.card_fin]

/-- Definition 5.1: `|k⟩ = (m choose k)^(-1/2) ∑_{wt x = k} |x⟩`. -/
noncomputable def dicke (m k : ℕ) : (Fin m → Bool) → ℂ :=
  fun x => if wt x = k then (((Real.sqrt (m.choose k) : ℝ)) : ℂ)⁻¹ else 0

/-- standard ℓ² inner product. -/
noncomputable def ip {m : ℕ} (ψ φ : (Fin m → Bool) → ℂ) : ℂ :=
  ∑ x, (starRingEnd ℂ) (ψ x) * φ x

theorem inv_sqrt_mul_self (n : ℕ) :
    (((Real.sqrt n : ℝ)) : ℂ)⁻¹ * (((Real.sqrt n : ℝ)) : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

/-- orthonormality of the `|k⟩`, `0 ≤ k ≤ m`. -/
theorem ip_dicke (m j k : ℕ) (hj : j ≤ m) (hk : k ≤ m) :
    ip (dicke m j) (dicke m k) = if j = k then 1 else 0 := by
  unfold ip
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    have key : ∀ x : Fin m → Bool,
        (starRingEnd ℂ) (dicke m j x) * dicke m j x
          = if wt x = j then ((m.choose j : ℕ) : ℂ)⁻¹ else 0 := by
      intro x
      unfold dicke
      split_ifs
      · rw [map_inv₀, Complex.conj_ofReal]
        exact inv_sqrt_mul_self _
      · simp
    rw [Finset.sum_congr rfl (fun x _ => key x), ← Finset.sum_filter, Finset.sum_const]
    show (sector m j).card • (((m.choose j : ℕ) : ℂ)⁻¹) = 1
    rw [card_sector, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Nat.choose_pos hj).ne')
  · rw [if_neg hjk]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h2 : wt x = k
    · by_cases h1 : wt x = j
      · exact absurd (h1.symm.trans h2) hjk
      · simp [dicke, h1]
    · simp [dicke, h2]

/-! ## Symmetric subspace -/

/-- invariant under permuting coordinates. -/
def IsSymm {m : ℕ} (ψ : (Fin m → Bool) → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin m)) (x : Fin m → Bool), ψ (fun i => x (σ i)) = ψ x

/-- the symmetric subspace. -/
def symmSubspace (m : ℕ) : Submodule ℂ ((Fin m → Bool) → ℂ) where
  carrier := {ψ | IsSymm ψ}
  add_mem' := by
    intro a b ha hb σ x
    simp [ha σ x, hb σ x]
  zero_mem' := by
    intro σ x
    rfl
  smul_mem' := by
    intro c a ha σ x
    simp [ha σ x]

theorem wt_perm {m : ℕ} (x : Fin m → Bool) (σ : Equiv.Perm (Fin m)) :
    wt (fun i => x (σ i)) = wt x := by
  unfold wt
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro a ha
    simpa using ha
  · intro a _ b _ h
    exact σ.injective h
  · intro b hb
    exact ⟨σ.symm b, by simpa using hb, by simp⟩

theorem dicke_symm (m k : ℕ) : IsSymm (dicke m k) := by
  intro σ x
  unfold dicke
  rw [wt_perm]

/-- two strings of equal weight differ by a permutation of coordinates. -/
theorem exists_perm {m : ℕ} (x y : Fin m → Bool) (h : wt x = wt y) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i, y i = x (σ i) := by
  classical
  have h1 : Fintype.card {i // y i = true} = Fintype.card {i // x i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert h.symm
  have h2 : Fintype.card {i // ¬ y i = true} = Fintype.card {i // ¬ x i = true} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let e1 : {i // y i = true} ≃ {i // x i = true} := Fintype.equivOfCardEq h1
  let e2 : {i // ¬ y i = true} ≃ {i // ¬ x i = true} := Fintype.equivOfCardEq h2
  let σ : Equiv.Perm (Fin m) :=
    (Equiv.sumCompl (fun i => y i = true)).symm.trans
      ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (fun i => x i = true)))
  refine ⟨σ, fun i => ?_⟩
  by_cases hy : y i = true
  · have hσ : σ i = (e1 ⟨i, hy⟩ : Fin m) := by
      simp [σ, Equiv.sumCompl_symm_apply_of_pos hy]
    rw [hσ, hy, (e1 ⟨i, hy⟩).2]
  · have hσ : σ i = (e2 ⟨i, hy⟩ : Fin m) := by
      simp [σ, Equiv.sumCompl_symm_apply_of_neg hy]
    have hy' : y i = false := by simpa using hy
    have hx' : x (e2 ⟨i, hy⟩ : Fin m) = false := by simpa using (e2 ⟨i, hy⟩).2
    rw [hσ, hy', hx']

/-- a symmetric amplitude depends only on the weight. -/
theorem IsSymm.eq_of_wt {m : ℕ} {ψ : (Fin m → Bool) → ℂ} (hψ : IsSymm ψ)
    (x y : Fin m → Bool) (h : wt x = wt y) : ψ x = ψ y := by
  obtain ⟨σ, hσ⟩ := exists_perm x y h
  have : y = fun i => x (σ i) := funext hσ
  rw [this, hψ σ x]

/-- **The `|k⟩`, `0 ≤ k ≤ m`, span the symmetric subspace.** -/
theorem span_dicke_eq_symm (m : ℕ) :
    Submodule.span ℂ {φ : (Fin m → Bool) → ℂ | ∃ k, k ≤ m ∧ φ = dicke m k}
      = symmSubspace m := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro φ ⟨k, _, rfl⟩
    exact dicke_symm m k
  · intro ψ hψ
    have hψ' : IsSymm ψ := hψ
    let c : ℕ → ℂ := fun k => (∑ y ∈ sector m k, ψ y) * (((Real.sqrt (m.choose k) : ℝ)) : ℂ)⁻¹
    have hrepr : ψ = ∑ k ∈ Finset.range (m + 1), c k • dicke m k := by
      funext x
      have hwt : wt x ≤ m := by
        calc wt x ≤ (univ : Finset (Fin m)).card := card_le_card (filter_subset _ _)
          _ = m := by simp
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, dicke, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq (range (m + 1)) (wt x),
        if_pos (mem_range.mpr (Nat.lt_succ_of_le hwt))]
      have hconst : ∑ y ∈ sector m (wt x), ψ y = ∑ y ∈ sector m (wt x), ψ x := by
        refine Finset.sum_congr rfl fun y hy => ?_
        have hwy : wt y = wt x := by simpa [sector] using hy
        exact (hψ'.eq_of_wt x y hwy.symm).symm
      have hC : ((m.choose (wt x) : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hwt).ne'
      simp only [c]
      rw [hconst, Finset.sum_const, card_sector, nsmul_eq_mul]
      have hs := inv_sqrt_mul_self (m.choose (wt x))
      calc ψ x = ((m.choose (wt x) : ℕ) : ℂ) * ψ x * ((m.choose (wt x) : ℕ) : ℂ)⁻¹ := by
            field_simp
        _ = _ := by
            rw [← hs]; ring
    rw [hrepr]
    exact Submodule.sum_mem _ fun k hk =>
      Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), rfl⟩)

end Dicke
