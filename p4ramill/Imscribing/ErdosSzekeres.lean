import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic

open Classical

namespace ErdosSzekeres

def HasIncrSubseq (n k : ℕ) (f : Fin n → ℝ) : Prop :=
  ∃ (idx : Fin k → Fin n),
    StrictMono (fun (i : Fin k) => (idx i : ℕ)) ∧
    StrictMono (fun (i : Fin k) => f (idx i))

def HasDecrSubseq (n k : ℕ) (f : Fin n → ℝ) : Prop :=
  ∃ (idx : Fin k → Fin n),
    StrictMono (fun (i : Fin k) => (idx i : ℕ)) ∧
    StrictAnti (fun (i : Fin k) => f (idx i))

def IsIncrSubseqEndingAt {n : ℕ} (f : Fin n → ℝ) (i : Fin n) (len : ℕ) : Prop :=
  ∃ (idx : Fin len → Fin n),
    (∀ a, (idx a).val ≤ i.val) ∧
    StrictMono (fun a => (idx a).val) ∧
    StrictMono (fun a => f (idx a)) ∧
    (∃ a, idx a = i)

def IsDecrSubseqEndingAt {n : ℕ} (f : Fin n → ℝ) (i : Fin n) (len : ℕ) : Prop :=
  ∃ (idx : Fin len → Fin n),
    (∀ a, (idx a).val ≤ i.val) ∧
    StrictMono (fun a => (idx a).val) ∧
    StrictAnti (fun a => f (idx a)) ∧
    (∃ a, idx a = i)

noncomputable def lisAt {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.Icc 1 (i.val + 1)).sup
    (fun len => if IsIncrSubseqEndingAt f i len then len else 0)

noncomputable def ldsAt {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.Icc 1 (i.val + 1)).sup
    (fun len => if IsDecrSubseqEndingAt f i len then len else 0)

/-! ## Basic facts -/

lemma isIncr_one {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    IsIncrSubseqEndingAt f i 1 := by
  refine ⟨fun _ => i, ?_, ?_, ?_, ⟨⟨0, Nat.one_pos⟩, rfl⟩⟩
  · intro a; exact Nat.le_refl _
  · intro a b hab; exact absurd hab (by omega)
  · intro a b hab; exact absurd hab (by omega)

lemma isDecr_one {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    IsDecrSubseqEndingAt f i 1 := by
  refine ⟨fun _ => i, ?_, ?_, ?_, ⟨⟨0, Nat.one_pos⟩, rfl⟩⟩
  · intro a; exact Nat.le_refl _
  · intro a b hab; exact absurd hab (by omega)
  · intro a b hab; exact absurd hab (by omega)

lemma lisAt_ge_one {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : 1 ≤ lisAt f i := by
  unfold lisAt
  have h1 : 1 ∈ Finset.Icc 1 (i.val + 1) :=
    Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩
  have hv : (if IsIncrSubseqEndingAt f i 1 then (1 : ℕ) else 0) = 1 := by
    simp [isIncr_one f i]
  calc (1 : ℕ) = _ := hv.symm
    _ ≤ _ := Finset.le_sup
      (f := fun l => if IsIncrSubseqEndingAt f i l then l else 0) h1

lemma ldsAt_ge_one {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : 1 ≤ ldsAt f i := by
  unfold ldsAt
  have h1 : 1 ∈ Finset.Icc 1 (i.val + 1) :=
    Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩
  have hv : (if IsDecrSubseqEndingAt f i 1 then (1 : ℕ) else 0) = 1 := by
    simp [isDecr_one f i]
  calc (1 : ℕ) = _ := hv.symm
    _ ≤ _ := Finset.le_sup
      (f := fun l => if IsDecrSubseqEndingAt f i l then l else 0) h1

lemma exists_isIncr_of_lisAt {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∃ len, len ∈ Finset.Icc 1 (i.val + 1) ∧
           IsIncrSubseqEndingAt f i len ∧ lisAt f i = len := by
  unfold lisAt
  have hne : (Finset.Icc 1 (i.val + 1)).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩
  obtain ⟨len, hmem, heq⟩ :=
    Finset.exists_mem_eq_sup (Finset.Icc 1 (i.val + 1)) hne
      (fun len => if IsIncrSubseqEndingAt f i len then len else 0)
  have hvalid : IsIncrSubseqEndingAt f i len := by
    by_contra h
    rw [if_neg h] at heq
    have h1 : 1 ≤ (Finset.Icc 1 (i.val + 1)).sup
        (fun l => if IsIncrSubseqEndingAt f i l then l else 0) := by
      have hv : (if IsIncrSubseqEndingAt f i 1 then (1 : ℕ) else 0) = 1 := by
        simp [isIncr_one f i]
      calc (1 : ℕ) = _ := hv.symm
        _ ≤ _ := Finset.le_sup
            (f := fun l => if IsIncrSubseqEndingAt f i l then l else 0)
            (Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩)
    omega
  refine ⟨len, hmem, hvalid, ?_⟩
  rw [if_pos hvalid] at heq
  exact heq

lemma exists_isDecr_of_ldsAt {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∃ len, len ∈ Finset.Icc 1 (i.val + 1) ∧
           IsDecrSubseqEndingAt f i len ∧ ldsAt f i = len := by
  unfold ldsAt
  have hne : (Finset.Icc 1 (i.val + 1)).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩
  obtain ⟨len, hmem, heq⟩ :=
    Finset.exists_mem_eq_sup (Finset.Icc 1 (i.val + 1)) hne
      (fun len => if IsDecrSubseqEndingAt f i len then len else 0)
  have hvalid : IsDecrSubseqEndingAt f i len := by
    by_contra h
    rw [if_neg h] at heq
    have h1 : 1 ≤ (Finset.Icc 1 (i.val + 1)).sup
        (fun l => if IsDecrSubseqEndingAt f i l then l else 0) := by
      have hv : (if IsDecrSubseqEndingAt f i 1 then (1 : ℕ) else 0) = 1 := by
        simp [isDecr_one f i]
      calc (1 : ℕ) = _ := hv.symm
        _ ≤ _ := Finset.le_sup
            (f := fun l => if IsDecrSubseqEndingAt f i l then l else 0)
            (Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩)
    omega
  refine ⟨len, hmem, hvalid, ?_⟩
  rw [if_pos hvalid] at heq
  exact heq

/-! ## The extension lemmas -/

lemma lisAt_incr_step {n : ℕ} (f : Fin n → ℝ) {i j : Fin n}
    (hij : j.val < i.val) (hfi : f j < f i) :
    lisAt f i ≥ lisAt f j + 1 := by
  obtain ⟨L, hLmem, hL_valid, hL_eq⟩ := exists_isIncr_of_lisAt f j
  rw [hL_eq]
  obtain ⟨idx, hle, hidx, hf_mono, ⟨a₀, ha₀⟩⟩ := hL_valid
  have h_fidx_le : ∀ a : Fin L, f (idx a) ≤ f j := by
    intro a
    rcases lt_trichotomy a a₀ with h | h | h
    · have hlt : f (idx a) < f (idx a₀) := hf_mono h
      rw [ha₀] at hlt
      exact le_of_lt hlt
    · rw [h, ha₀]
    · exfalso
      have hlt : (idx a₀).val < (idx a).val := hidx h
      rw [ha₀] at hlt
      have := hle a
      omega
  let idx' : Fin (L + 1) → Fin n := fun a =>
    if ha : a.val < L then idx ⟨a.val, ha⟩ else i
  have hidx'_mono : StrictMono (fun a : Fin (L + 1) => (idx' a).val) := by
    intro a b hab
    simp only [idx']
    by_cases ha : a.val < L <;> by_cases hb : b.val < L
    · simp only [dif_pos ha, dif_pos hb]; exact hidx hab
    · simp only [dif_pos ha, dif_neg hb]
      have hle_ab : (idx ⟨a.val, ha⟩).val ≤ j.val := hle _
      have : b.val = L := by have := b.isLt; omega
      omega
    · exfalso; have := a.isLt; omega
    · exfalso; have := a.isLt; have := b.isLt; omega
  have hf'_mono : StrictMono (fun a : Fin (L + 1) => f (idx' a)) := by
    intro a b hab
    simp only [idx']
    by_cases ha : a.val < L <;> by_cases hb : b.val < L
    · simp only [dif_pos ha, dif_pos hb]; exact hf_mono hab
    · simp only [dif_pos ha, dif_neg hb]
      have h1 := h_fidx_le ⟨a.val, ha⟩
      exact lt_of_le_of_lt h1 hfi
    · exfalso; have := a.isLt; omega
    · exfalso; have := a.isLt; have := b.isLt; omega
  have h_ext_valid : IsIncrSubseqEndingAt f i (L + 1) := by
    refine ⟨idx', ?_, hidx'_mono, hf'_mono, ⟨⟨L, Nat.lt_succ_self L⟩, ?_⟩⟩
    · intro a
      simp only [idx']
      split_ifs with h
      · exact le_trans (hle ⟨a.val, h⟩) (le_of_lt hij)
      · exact le_refl _
    · simp only [idx']
      rw [dif_neg (Nat.lt_irrefl L)]
  have h_mem : L + 1 ∈ Finset.Icc 1 (i.val + 1) := by
    rw [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    have hL_le : L ≤ j.val + 1 := (Finset.mem_Icc.mp hLmem).2
    omega
  unfold lisAt
  calc L + 1
      = (if IsIncrSubseqEndingAt f i (L + 1) then (L + 1 : ℕ) else 0) := by
        rw [if_pos h_ext_valid]
    _ ≤ (Finset.Icc 1 (i.val + 1)).sup
          (fun l => if IsIncrSubseqEndingAt f i l then l else 0) :=
        Finset.le_sup
          (f := fun l => if IsIncrSubseqEndingAt f i l then l else 0) h_mem

lemma ldsAt_decr_step {n : ℕ} (f : Fin n → ℝ) {i j : Fin n}
    (hij : j.val < i.val) (hfi : f j > f i) :
    ldsAt f i ≥ ldsAt f j + 1 := by
  obtain ⟨L, hLmem, hL_valid, hL_eq⟩ := exists_isDecr_of_ldsAt f j
  rw [hL_eq]
  obtain ⟨idx, hle, hidx, hf_anti, ⟨a₀, ha₀⟩⟩ := hL_valid
  have h_fidx_le : ∀ a : Fin L, f j ≤ f (idx a) := by
    intro a
    rcases lt_trichotomy a a₀ with h | h | h
    · have hlt : f (idx a₀) < f (idx a) := hf_anti h
      rw [ha₀] at hlt
      exact le_of_lt hlt
    · rw [h, ha₀]
    · exfalso
      have hlt : (idx a₀).val < (idx a).val := hidx h
      rw [ha₀] at hlt
      have := hle a
      omega
  let idx' : Fin (L + 1) → Fin n := fun a =>
    if ha : a.val < L then idx ⟨a.val, ha⟩ else i
  have hidx'_mono : StrictMono (fun a : Fin (L + 1) => (idx' a).val) := by
    intro a b hab
    simp only [idx']
    by_cases ha : a.val < L <;> by_cases hb : b.val < L
    · simp only [dif_pos ha, dif_pos hb]; exact hidx hab
    · simp only [dif_pos ha, dif_neg hb]
      have hle_ab : (idx ⟨a.val, ha⟩).val ≤ j.val := hle _
      have : b.val = L := by have := b.isLt; omega
      omega
    · exfalso; have := a.isLt; omega
    · exfalso; have := a.isLt; have := b.isLt; omega
  have hf'_mono : StrictAnti (fun a : Fin (L + 1) => f (idx' a)) := by
    intro a b hab
    simp only [idx']
    by_cases ha : a.val < L <;> by_cases hb : b.val < L
    · simp only [dif_pos ha, dif_pos hb]; exact hf_anti hab
    · simp only [dif_pos ha, dif_neg hb]
      have h1 := h_fidx_le ⟨a.val, ha⟩
      exact lt_of_lt_of_le hfi h1
    · exfalso; have := a.isLt; omega
    · exfalso; have := a.isLt; have := b.isLt; omega
  have h_ext_valid : IsDecrSubseqEndingAt f i (L + 1) := by
    refine ⟨idx', ?_, hidx'_mono, hf'_mono, ⟨⟨L, Nat.lt_succ_self L⟩, ?_⟩⟩
    · intro a
      simp only [idx']
      split_ifs with h
      · exact le_trans (hle ⟨a.val, h⟩) (le_of_lt hij)
      · exact le_refl _
    · simp only [idx']
      rw [dif_neg (Nat.lt_irrefl L)]
  have h_mem : L + 1 ∈ Finset.Icc 1 (i.val + 1) := by
    rw [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    have hL_le : L ≤ j.val + 1 := (Finset.mem_Icc.mp hLmem).2
    omega
  unfold ldsAt
  calc L + 1
      = (if IsDecrSubseqEndingAt f i (L + 1) then (L + 1 : ℕ) else 0) := by
        rw [if_pos h_ext_valid]
    _ ≤ (Finset.Icc 1 (i.val + 1)).sup
          (fun l => if IsDecrSubseqEndingAt f i l then l else 0) :=
        Finset.le_sup
          (f := fun l => if IsDecrSubseqEndingAt f i l then l else 0) h_mem

lemma lisAt_bound {n r : ℕ} (hr : 1 ≤ r) (f : Fin n → ℝ)
    (h : ¬ HasIncrSubseq n r f) (i : Fin n) : lisAt f i ≤ r - 1 := by
  by_contra hlt
  have hrle : r ≤ lisAt f i := by omega
  obtain ⟨L, hLmem, hL_valid, hL_eq⟩ := exists_isIncr_of_lisAt f i
  have hL_ge : r ≤ L := by omega
  obtain ⟨idx, _, hidx, hf_mono, _⟩ := hL_valid
  apply h
  refine ⟨fun a : Fin r => idx ⟨a.val, lt_of_lt_of_le a.isLt hL_ge⟩, ?_, ?_⟩
  · intro a b hab; exact hidx hab
  · intro a b hab; exact hf_mono hab

lemma ldsAt_bound {n s : ℕ} (hs : 1 ≤ s) (f : Fin n → ℝ)
    (h : ¬ HasDecrSubseq n s f) (i : Fin n) : ldsAt f i ≤ s - 1 := by
  by_contra hlt
  have hsle : s ≤ ldsAt f i := by omega
  obtain ⟨L, hLmem, hL_valid, hL_eq⟩ := exists_isDecr_of_ldsAt f i
  have hL_ge : s ≤ L := by omega
  obtain ⟨idx, _, hidx, hf_anti, _⟩ := hL_valid
  apply h
  refine ⟨fun a : Fin s => idx ⟨a.val, lt_of_lt_of_le a.isLt hL_ge⟩, ?_, ?_⟩
  · intro a b hab; exact hidx hab
  · intro a b hab; exact hf_anti hab

/-! ## Injectivity of the (p, q) map -/

lemma pair_injective {n : ℕ} (f : Fin n → ℝ) (hf : Function.Injective f) :
    Function.Injective (fun i : Fin n => (lisAt f i, ldsAt f i)) := by
  intro i j hij
  by_contra hne
  have hfij : f i ≠ f j := fun h => hne (hf h)
  have h1 : lisAt f i = lisAt f j := congrArg Prod.fst hij
  have h2 : ldsAt f i = ldsAt f j := congrArg Prod.snd hij
  rcases lt_trichotomy i.val j.val with hlt | heq | hlt
  · rcases lt_or_gt_of_ne hfij with hltf | hltf
    · have := lisAt_incr_step f hlt hltf; omega
    · have := ldsAt_decr_step f hlt hltf; omega
  · exact hne (Fin.ext heq)
  · rcases lt_or_gt_of_ne (Ne.symm hfij) with hltf | hltf
    · have := lisAt_incr_step f hlt hltf; omega
    · have := ldsAt_decr_step f hlt hltf; omega

/-! ## Main theorem -/

theorem erdos_szekeres_mono (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (f : Fin ((r - 1) * (s - 1) + 1) → ℝ)
    (hf : Function.Injective f) :
    HasIncrSubseq _ r f ∨ HasDecrSubseq _ s f := by
  rcases eq_or_lt_of_le hr with hr1 | hr2
  · subst hr1
    left
    refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
    · intro a b hab; exact absurd hab (by omega)
    · intro a b hab; exact absurd hab (by omega)
  rcases eq_or_lt_of_le hs with hs1 | hs2
  · subst hs1
    right
    refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
    · intro a b hab; exact absurd hab (by omega)
    · intro a b hab; exact absurd hab (by omega)
  by_contra h
  push_neg at h
  obtain ⟨h_no_incr, h_no_decr⟩ := h
  have h_image_sub :
      (Finset.univ.image
        (fun i : Fin ((r - 1) * (s - 1) + 1) =>
          (lisAt f i, ldsAt f i)))
        ⊆ Finset.Icc 1 (r - 1) ×ˢ Finset.Icc 1 (s - 1) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨lisAt_ge_one f i, lisAt_bound hr2.le f h_no_incr i⟩,
           ⟨ldsAt_ge_one f i, ldsAt_bound hs2.le f h_no_decr i⟩⟩
  have h_image_card :
      (Finset.univ.image
        (fun i : Fin ((r - 1) * (s - 1) + 1) =>
          (lisAt f i, ldsAt f i))).card
        = (r - 1) * (s - 1) + 1 := by
    rw [Finset.card_image_of_injective _ (pair_injective f hf)]
    simp
  have hS_card :
      (Finset.Icc 1 (r - 1) ×ˢ Finset.Icc 1 (s - 1)).card
        = (r - 1) * (s - 1) := by
    rw [Finset.card_product]
    have h1 : (Finset.Icc 1 (r - 1)).card = r - 1 := by
      rw [Nat.card_Icc]; omega
    have h2 : (Finset.Icc 1 (s - 1)).card = s - 1 := by
      rw [Nat.card_Icc]; omega
    rw [h1, h2]
  have hle : (r - 1) * (s - 1) + 1 ≤ (r - 1) * (s - 1) := by
    calc (r - 1) * (s - 1) + 1
        = _ := h_image_card.symm
      _ ≤ (Finset.Icc 1 (r - 1) ×ˢ Finset.Icc 1 (s - 1)).card :=
          Finset.card_le_card h_image_sub
      _ = (r - 1) * (s - 1) := hS_card
  omega

end ErdosSzekeres

#print axioms ErdosSzekeres.erdos_szekeres_mono