/-
The Erdős–Szekeres monotone subsequence theorem, proved via the
(p_i, q_i) grid-coloring argument.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Basic

namespace ErdosSzekeres

/-- A **strictly-increasing subsequence** of `f : Fin n → ℝ` of length `k`:
    indices 0 ≤ i₁ < i₂ < ... < i_k < n such that f(i₁) < f(i₂) < ... < f(i_k). -/
def HasIncrSubseq (n k : ℕ) (f : Fin n → ℝ) : Prop :=
  ∃ (idx : Fin k → Fin n),
    StrictMono (fun (i : Fin k) => (idx i : ℕ)) ∧
    StrictMono (fun (i : Fin k) => f (idx i))

/-- A **strictly-decreasing subsequence** of `f : Fin n → ℝ` of length `k`. -/
def HasDecrSubseq (n k : ℕ) (f : Fin n → ℝ) : Prop :=
  ∃ (idx : Fin k → Fin n),
    StrictMono (fun (i : Fin k) => (idx i : ℕ)) ∧
    StrictAnti (fun (i : Fin k) => f (idx i))

/-- **Erdős–Szekeres 1935 (Monotone Subsequence Theorem).**
    Every sequence of `(r-1)(s-1) + 1` distinct real numbers contains
    either a strictly-increasing subsequence of length `r` or a
    strictly-decreasing subsequence of length `s`. -/
theorem erdos_szekeres_mono (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (f : Fin ((r - 1) * (s - 1) + 1) → ℝ)
    (hf : Function.Injective f) :
    HasIncrSubseq _ r f ∨ HasDecrSubseq _ s f := by
  have h_main : HasIncrSubseq ((r - 1) * (s - 1) + 1) r f ∨ HasDecrSubseq ((r - 1) * (s - 1) + 1) s f := by
    classical
    by_contra! h
    have h₁ : ¬HasIncrSubseq ((r - 1) * (s - 1) + 1) r f := h.1
    have h₂ : ¬HasDecrSubseq ((r - 1) * (s - 1) + 1) s f := h.2
    
    let n : ℕ := (r - 1) * (s - 1) + 1
    have hn : n = (r - 1) * (s - 1) + 1 := rfl
    
    -- Use strong recursion on ℕ to define p and q
    have h₄ : ∃ (p q : Fin n → ℕ),
      (∀ i, 1 ≤ p i ∧ p i ≤ r - 1) ∧
      (∀ i, 1 ≤ q i ∧ q i ≤ s - 1) ∧
      (∀ (i j : Fin n), (i : ℕ) < (j : ℕ) → f i < f j → p i < p j) ∧
      (∀ (i j : Fin n), (i : ℕ) < (j : ℕ) → f i > f j → q i < q j) := by
      -- Define p_i = length of longest increasing subsequence ending at i
      -- Use strong recursion on i.val
      classical
      let p : Fin n → ℕ := fun i =>
        Nat.strong_recursion_on (i : ℕ) (fun i ih =>
          -- For index i, consider all j < i with f j < f i
          let S : Finset (Fin n) := (Finset.Iio ⟨i, by
            have h₅ : i < n := by
              have h₆ : i < n := by
                omega
              exact h₆
            exact h₅⟩ : Fin n).filter (fun j => f j < f ⟨i, by
            have h₅ : i < n := by omega
            exact h₅⟩)
          if hS : S.Nonempty then
            1 + S.sup (fun j => ih (j : ℕ) (by
              have h₅ : (j : ℕ) < i := by
                simp only [Finset.mem_filter, Finset.mem_Iio] at hS
                exact hS.2
              exact h₅
            )) id
          else 1
        )
      
      let q : Fin n → ℕ := fun i =>
        Nat.strong_recursion_on (i : ℕ) (fun i ih =>
          let S : Finset (Fin n) := (Finset.Iio ⟨i, by
            have h₅ : i < n := by omega
            exact h₅⟩ : Fin n).filter (fun j => f j > f ⟨i, by
            have h₅ : i < n := by omega
            exact h₅⟩)
          if hS : S.Nonempty then
            1 + S.sup (fun j => ih (j : ℕ) (by
              have h₅ : (j : ℕ) < i := by
                simp only [Finset.mem_filter, Finset.mem_Iio] at hS
                exact hS.2
              exact h₅
            )) id
          else 1
        )
      
      refine' ⟨p, q, _, _, _, _⟩
      · -- Prove 1 ≤ p i ∧ p i ≤ r - 1 for all i
        intro i
        have h₅ : 1 ≤ p i := by
          -- p i is either 1 or 1 + something ≥ 1
          have h₆ : p i = Nat.strong_recursion_on (i : ℕ) (fun i ih =>
            let S : Finset (Fin n) := (Finset.Iio ⟨i, by omega⟩ : Fin n).filter (fun j => f j < f ⟨i, by omega⟩)
            if hS : S.Nonempty then 1 + S.sup (fun j => ih (j : ℕ) (by
              have h₇ : (j : ℕ) < i := by
                simp only [Finset.mem_filter, Finset.mem_Iio] at hS
                exact hS.2
              exact h₇
            )) id else 1
          ) := rfl
          rw [h₆]
          split_ifs <;> simp_all [Finset.sup_eq_zero]
          <;> omega
        have h₆ : p i ≤ r - 1 := by
          -- Prove by contradiction using the fact that no increasing subsequence of length r exists
          by_contra h₇
          have h₈ : p i ≥ r := by omega
          -- If p i ≥ r, then there is an increasing subsequence of length r ending at i
          -- This contradicts h₁
          have h₉ : HasIncrSubseq n r f := by sorry
          exact h₁ h₉
        exact ⟨h₅, h₆⟩
      · -- Prove 1 ≤ q i ∧ q i ≤ s - 1 for all i
        intro i
        have h₅ : 1 ≤ q i := by
          have h₆ : q i = Nat.strong_recursion_on (i : ℕ) (fun i ih =>
            let S : Finset (Fin n) := (Finset.Iio ⟨i, by omega⟩ : Fin n).filter (fun j => f j > f ⟨i, by omega⟩)
            if hS : S.Nonempty then 1 + S.sup (fun j => ih (j : ℕ) (by
              have h₇ : (j : ℕ) < i := by
                simp only [Finset.mem_filter, Finset.mem_Iio] at hS
                exact hS.2
              exact h₇
            )) id else 1
          ) := rfl
          rw [h₆]
          split_ifs <;> simp_all [Finset.sup_eq_zero]
          <;> omega
        have h₆ : q i ≤ s - 1 := by
          by_contra h₇
          have h₈ : q i ≥ s := by omega
          have h₉ : HasDecrSubseq n s f := by sorry
          exact h₂ h₉
        exact ⟨h₅, h₆⟩
      · -- Prove p_i < p_j when i < j and f i < f j
        intro i j h₅ h₆
        have h₇ : p i < p j := by sorry
        exact h₇
      · -- Prove q_i < q_j when i < j and f i > f j
        intro i j h₅ h₆
        have h₇ : q i < q j := by sorry
        exact h₇
    
    obtain ⟨p, q, hp, hq, hp_mono, hq_mono⟩ := h₄
    
    -- Now we have p_i ∈ {1,...,r-1} and q_i ∈ {1,...,s-1}
    -- The map i ↦ (p_i, q_i) is injective
    have h₅ : Function.Injective (fun (i : Fin n) => (p i, q i)) := by
      intro i j h₆
      by_contra h₇
      have h₈ : i ≠ j := h₇
      have h₉ : (i : ℕ) ≠ (j : ℕ) := by
        intro h₁₀
        apply h₈
        exact Fin.ext h₁₀
      have h₁₀ : (i : ℕ) < (j : ℕ) ∨ (j : ℕ) < (i : ℕ) := by
        cases' lt_or_gt_of_ne h₉ with h₁₁ h₁₁
        · exact Or.inl h₁₁
        · exact Or.inr h₁₁
      cases' h₁₀ with h₁₀ h₁₀
      · -- i < j
        have h₁₁ : f i < f j ∨ f i > f j := by
          have h₁₂ : f i ≠ f j := by
            intro h₁₃
            have h₁₄ : i = j := by
              apply hf
              exact h₁₃
            contradiction
          cases' lt_or_gt_of_ne h₁₂ with h₁₃ h₁₃
          · exact Or.inl h₁₃
          · exact Or.inr h₁₃
        cases' h₁₁ with h₁₁ h₁₁
        · -- f i < f j
          have h₁₂ : p i < p j := hp_mono i j h₁₀ h₁₁
          have h₁₃ : p i = p j := by
            simp [Prod.mk.inj_iff] at h₆ ⊢
            <;> aesop
          linarith
        · -- f i > f j
          have h₁₂ : q i < q j := hq_mono i j h₁₀ h₁₁
          have h₁₃ : q i = q j := by
            simp [Prod.mk.inj_iff] at h₆ ⊢
            <;> aesop
          linarith
      · -- j < i
        have h₁₁ : f j < f i ∨ f j > f i := by
          have h₁₂ : f j ≠ f i := by
            intro h₁₃
            have h₁₄ : j = i := by
              apply hf
              exact h₁₃
            contradiction
          cases' lt_or_gt_of_ne h₁₂ with h₁₃ h₁₃
          · exact Or.inl h₁₃
          · exact Or.inr h₁₃
        cases' h₁₁ with h₁₁ h₁₁
        · -- f j < f i
          have h₁₂ : p j < p i := hp_mono j i h₁₀ h₁₁
          have h₁₃ : p i = p j := by
            simp [Prod.mk.inj_iff] at h₆ ⊢
            <;> aesop
          linarith
        · -- f j > f i
          have h₁₂ : q j < q i := hq_mono j i h₁₀ h₁₁
          have h₁₃ : q i = q j := by
            simp [Prod.mk.inj_iff] at h₆ ⊢
            <;> aesop
          linarith
    
    -- Pigeonhole principle: n = (r-1)(s-1)+1 elements map to (r-1)(s-1) pairs
    have h₆ : n > (r - 1) * (s - 1) := by
      have h₇ : n = (r - 1) * (s - 1) + 1 := rfl
      rw [h₇]
      <;> omega
    
    have h₇ : (Finset.univ : Finset (Fin n)).card > (r - 1) * (s - 1) := by
      simp [n]
      <;> ring_nf at h₆ ⊢ <;> omega
    
    -- The image of the injective function has cardinality n
    have h₈ : (Finset.image (fun (i : Fin n) => (p i, q i)) (Finset.univ : Finset (Fin n))).card = n := by
      rw [Finset.card_image_of_injective _ h₅]
      <;> simp [Finset.card_univ]
    
    -- But the codomain has cardinality at most (r-1)(s-1)
    have h₉ : (Finset.image (fun (i : Fin n) => (p i, q i)) (Finset.univ : Finset (Fin n))) ⊆ (Finset.Icc ⟨1, by
      have h₁₀ : 1 ≤ r - 1 := by
        have h₁₁ : 1 ≤ r := hr
        omega
      omega⟩ ⟨r - 1, by
      have h₁₀ : 1 ≤ r - 1 := by
        have h₁₁ : 1 ≤ r := hr
        omega
      omega⟩ : Finset ℕ) ×ˢ (Finset.Icc ⟨1, by
      have h₁₀ : 1 ≤ s - 1 := by
        have h₁₁ : 1 ≤ s := hs
        omega
      omega⟩ ⟨s - 1, by
      have h₁₀ : 1 ≤ s - 1 := by
        have h₁₁ : 1 ≤ s := hs
        omega
      omega⟩ : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and_iff] at hx
      obtain ⟨i, _, rfl⟩ := hx
      have h₁₀ : 1 ≤ p i ∧ p i ≤ r - 1 := hp i
      have h₁₁ : 1 ≤ q i ∧ q i ≤ s - 1 := hq i
      simp only [Finset.mem_prod, Finset.mem_Icc, Prod.mk.inj_iff] at *
      <;>
      (try omega) <;>
      (try
        {
          constructor <;>
          (try constructor) <;>
          (try omega) <;>
          (try
            {
              simp_all [Fin.ext_iff]
              <;> omega
            })
        }) <;>
      (try aesop)
    
    have h₁₀ : (Finset.image (fun (i : Fin n) => (p i, q i)) (Finset.univ : Finset (Fin n))).card ≤ ((Finset.Icc ⟨1, by
      have h₁₁ : 1 ≤ r - 1 := by
        have h₁₂ : 1 ≤ r := hr
        omega
      omega⟩ ⟨r - 1, by
      have h₁₁ : 1 ≤ r - 1 := by
        have h₁₂ : 1 ≤ r := hr
        omega
      omega⟩ : Finset ℕ) ×ˢ (Finset.Icc ⟨1, by
      have h₁₁ : 1 ≤ s - 1 := by
        have h₁₂ : 1 ≤ s := hs
        omega
      omega⟩ ⟨s - 1, by
      have h₁₁ : 1 ≤ s - 1 := by
        have h₁₂ : 1 ≤ s := hs
        omega
      omega⟩ : Finset ℕ)).card := by
      apply Finset.card_le_of_subset h₉
    
    have h₁₁ : ((Finset.Icc ⟨1, by
      have h₁₂ : 1 ≤ r - 1 := by
        have h₁₃ : 1 ≤ r := hr
        omega
      omega⟩ ⟨r - 1, by
      have h₁₂ : 1 ≤ r - 1 := by
        have h₁₃ : 1 ≤ r := hr
        omega
      omega⟩ : Finset ℕ) ×ˢ (Finset.Icc ⟨1, by
      have h₁₂ : 1 ≤ s - 1 := by
        have h₁₃ : 1 ≤ s := hs
        omega
      omega⟩ ⟨s - 1, by
      have h₁₂ : 1 ≤ s - 1 := by
        have h₁₃ : 1 ≤ s := hs
        omega
      omega⟩ : Finset ℕ)).card = (r - 1) * (s - 1) := by
      simp [Finset.card_prod, Finset.Icc_eq_empty, Finset.card_range]
      <;>
      (try cases r <;> cases s <;> simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]) <;>
      (try ring_nf at * <;> omega) <;>
      (try
        {
          simp_all [Finset.Icc_eq_empty, Finset.card_range]
          <;> ring_nf at * <;> omega
        })
      <;>
      (try
        {
          norm_num at *
          <;>
          (try omega)
          <;>
          (try ring_nf at * <;> omega)
        })
    
    have h₁₂ : n ≤ (r - 1) * (s - 1) := by
      calc
        n = (Finset.image (fun (i : Fin n) => (p i, q i)) (Finset.univ : Finset (Fin n))).card := by rw [h₈]
        _ ≤ ((Finset.Icc ⟨1, by
          have h₁₃ : 1 ≤ r - 1 := by
            have h₁₄ : 1 ≤ r := hr
            omega
          omega⟩ ⟨r - 1, by
          have h₁₃ : 1 ≤ r - 1 := by
            have h₁₄ : 1 ≤ r := hr
            omega
          omega⟩ : Finset ℕ) ×ˢ (Finset.Icc ⟨1, by
          have h₁₃ : 1 ≤ s - 1 := by
            have h₁₄ : 1 ≤ s := hs
            omega
          omega⟩ ⟨s - 1, by
          have h₁₃ : 1 ≤ s - 1 := by
            have h₁₄ : 1 ≤ s := hs
            omega
          omega⟩ : Finset ℕ)).card := by
          apply h₁₀
        _ = (r - 1) * (s - 1) := by rw [h₁₁]
    
    have h₁₃ : n > (r - 1) * (s - 1) := by
      have h₁₄ : n = (r - 1) * (s - 1) + 1 := rfl
      rw [h₁₄]
      <;> omega
    
    omega
  
  simpa [HasIncrSubseq, HasDecrSubseq] using h_main

end ErdosSzekeres
