/-
The Erdős–Szekeres monotone subsequence theorem, proved via the
(p_i, q_i) grid-coloring argument.

Import note: `Mathlib.Data.Finset.Lattice` was split into `Lattice/`.
We import `Lattice.Lemmas` (transitively pulls in Basic/Fold/Pi/Prod/Union)
so that `Finset.sup` is available.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Lemmas

namespace ErdosSzekeres

/-- A strictly-increasing subsequence of `f : Fin n → ℝ` of length `k`. -/
def HasIncrSubseq (n k : ℕ) (f : Fin n → ℝ) : Prop :=
  ∃ (idx : Fin k → Fin n),
    StrictMono (fun (i : Fin k) => (idx i : ℕ)) ∧
    StrictMono (fun (i : Fin k) => f (idx i))

/-- A strictly-decreasing subsequence of `f : Fin n → ℝ` of length `k`. -/
def HasDecrSubseq (n k : ℕ) (f : Fin n → ℝ) : Prop :=
  ∃ (idx : Fin k → Fin n),
    StrictMono (fun (i : Fin k) => (idx i : ℕ)) ∧
    StrictAnti (fun (i : Fin k) => f (idx i))

/-- Length of the longest strictly-increasing subsequence ending at `i`. -/
noncomputable def incrLen {n : ℕ} (f : Fin n → ℝ) : Fin n → ℕ
  | i => 1 + ((Finset.univ.filter (fun j : Fin n => j < i ∧ f j < f i)).attach).sup
           (fun j => incrLen f j.1)
termination_by i => i.val
decreasing_by
  rename_i j
  have h := j.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact Fin.lt_def.mp h.1

/-- Length of the longest strictly-decreasing subsequence ending at `i`. -/
noncomputable def decrLen {n : ℕ} (f : Fin n → ℝ) : Fin n → ℕ
  | i => 1 + ((Finset.univ.filter (fun j : Fin n => j < i ∧ f j > f i)).attach).sup
           (fun j => decrLen f j.1)
termination_by i => i.val
decreasing_by
  rename_i j
  have h := j.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact Fin.lt_def.mp h.1

lemma incrLen_pos {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : 1 ≤ incrLen f i := by
  rw [incrLen]; omega

lemma decrLen_pos {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : 1 ≤ decrLen f i := by
  rw [decrLen]; omega

lemma incrLen_lt_of_lt {n : ℕ} (f : Fin n → ℝ) {i j : Fin n}
    (hij : j < i) (hfj : f j < f i) : incrLen f j < incrLen f i := by
  have hmem : j ∈ Finset.univ.filter (fun k : Fin n => k < i ∧ f k < f i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hij, hfj⟩
  have hle : incrLen f j ≤
      ((Finset.univ.filter (fun k : Fin n => k < i ∧ f k < f i)).attach).sup
        (fun k => incrLen f k.1) := by
    apply Finset.le_sup; simp
  have h_i : incrLen f i = 1 +
      ((Finset.univ.filter (fun k : Fin n => k < i ∧ f k < f i)).attach).sup
        (fun k => incrLen f k.1) := by rw [incrLen]
  rw [h_i]; omega

lemma decrLen_lt_of_lt {n : ℕ} (f : Fin n → ℝ) {i j : Fin n}
    (hij : j < i) (hfj : f j > f i) : decrLen f j < decrLen f i := by
  have hmem : j ∈ Finset.univ.filter (fun k : Fin n => k < i ∧ f k > f i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hij, hfj⟩
  have hle : decrLen f j ≤
      ((Finset.univ.filter (fun k : Fin n => k < i ∧ f k > f i)).attach).sup
        (fun k => decrLen f k.1) := by
    apply Finset.le_sup; simp
  have h_i : decrLen f i = 1 +
      ((Finset.univ.filter (fun k : Fin n => k < i ∧ f k > f i)).attach).sup
        (fun k => decrLen f k.1) := by rw [decrLen]
  rw [h_i]; omega

/-- For every `i`, there is an increasing subsequence of length `incrLen f i`
    whose last index is exactly `i`. -/
lemma exists_incr_subseq_ending {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∃ idx : Fin (incrLen f i) → Fin n,
      StrictMono (fun k => (idx k : ℕ)) ∧
      StrictMono (fun k => f (idx k)) ∧
      idx ⟨incrLen f i - 1, by have := incrLen_pos f i; omega⟩ = i := by
  suffices H : ∀ m, ∀ i : Fin n, i.val = m →
      ∃ idx : Fin (incrLen f i) → Fin n,
        StrictMono (fun k => (idx k : ℕ)) ∧
        StrictMono (fun k => f (idx k)) ∧
        idx ⟨incrLen f i - 1, by have := incrLen_pos f i; omega⟩ = i from
    H i.val i rfl
  intro m
  refine Nat.strongRec m ?_
  intro m' ih i hi
  by_cases hk : incrLen f i = 1
  · refine ⟨fun _ => i, ?_, ?_, ?_⟩
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
    · simp [hk]
  · have hk2 : 2 ≤ incrLen f i := by have := incrLen_pos f i; omega
    have hsup : 1 ≤ ((Finset.univ.filter (fun j : Fin n => j < i ∧ f j < f i)).attach).sup
        (fun j => incrLen f j.1) := by
      have h := incrLen_pos f i
      rw [incrLen] at h; omega
    have hne : (Finset.univ.filter (fun j : Fin n => j < i ∧ f j < f i)).attach.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro hemp
      rw [hemp] at hsup; simp at hsup
    obtain ⟨j, _, hj_eq⟩ := Finset.exists_mem_eq_sup _ hne (fun j => incrLen f j.1)
    have hji : j.1 < i := by
      have := j.2; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.1
    have hfj : f j.1 < f i := by
      have := j.2; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.2
    have hjsup : incrLen f j.1 = incrLen f i - 1 := by
      rw [hj_eq]
      have : incrLen f i = 1 + incrLen f j.1 := by rw [incrLen, hj_eq]
      omega
    have hjlt : j.1.val < m' := by rw [← hi]; exact Fin.lt_def.mp hji
    obtain ⟨idx', hmono', hfmono', hend'⟩ := ih j.1.val hjlt j.1 rfl
    let last' : Fin (incrLen f j.1) :=
      ⟨incrLen f j.1 - 1, by have := incrLen_pos f j.1; omega⟩
    let idx : Fin (incrLen f i) → Fin n := fun k =>
      if h : (k : ℕ) < incrLen f j.1 then idx' ⟨(k : ℕ), h⟩ else i
    refine ⟨idx, ?_, ?_, ?_⟩
    · intro a b hab
      by_cases ha : (a : ℕ) < incrLen f j.1
      · by_cases hb : (b : ℕ) < incrLen f j.1
        · show (idx' ⟨(a : ℕ), ha⟩ : ℕ) < (idx' ⟨(b : ℕ), hb⟩ : ℕ)
          exact hmono' (by simp only [Fin.lt_iff_val_lt_val]; exact hab)
        · show (idx' ⟨(a : ℕ), ha⟩ : ℕ) < (i : ℕ)
          have hle' : (⟨(a : ℕ), ha⟩ : Fin (incrLen f j.1)) ≤ last' := by
            simp only [Fin.le_iff_val_le_val]; omega
          have h1 : (idx' ⟨(a : ℕ), ha⟩ : ℕ) ≤ (idx' last' : ℕ) := hmono'.monotone hle'
          rw [hend'] at h1; omega
      · exfalso; have hb' : (b : ℕ) < incrLen f i := b.isLt; omega
    · intro a b hab
      by_cases ha : (a : ℕ) < incrLen f j.1
      · by_cases hb : (b : ℕ) < incrLen f j.1
        · show f (idx' ⟨(a : ℕ), ha⟩) < f (idx' ⟨(b : ℕ), hb⟩)
          exact hfmono' (by simp only [Fin.lt_iff_val_lt_val]; exact hab)
        · show f (idx' ⟨(a : ℕ), ha⟩) < f i
          have hle' : (⟨(a : ℕ), ha⟩ : Fin (incrLen f j.1)) ≤ last' := by
            simp only [Fin.le_iff_val_le_val]; omega
          have h1 : f (idx' ⟨(a : ℕ), ha⟩) ≤ f (idx' last') := hfmono'.monotone hle'
          rw [hend'] at h1; omega
      · exfalso; have hb' : (b : ℕ) < incrLen f i := b.isLt; omega
    · simp only [idx]
      have : ¬((⟨incrLen f i - 1, by have := incrLen_pos f i; omega⟩ : Fin (incrLen f i) : ℕ)
          < incrLen f j.1) := by
        simp only [Fin.val_mk]; omega
      simp [this]

lemma hasIncrSubseq_of_incrLen_ge {n r : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hr : 1 ≤ r) (h : r ≤ incrLen f i) : HasIncrSubseq n r f := by
  obtain ⟨idx, hmono, hfmono, _⟩ := exists_incr_subseq_ending f i
  refine ⟨fun k => idx (Fin.castLE h k), ?_, ?_⟩
  · intro a b hab; exact hmono (by simpa using hab)
  · intro a b hab; exact hfmono (by simpa using hab)

/-- Mirror of `exists_incr_subseq_ending` for decreasing subsequences. -/
lemma exists_decr_subseq_ending {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∃ idx : Fin (decrLen f i) → Fin n,
      StrictMono (fun k => (idx k : ℕ)) ∧
      StrictAnti (fun k => f (idx k)) ∧
      idx ⟨decrLen f i - 1, by have := decrLen_pos f i; omega⟩ = i := by
  suffices H : ∀ m, ∀ i : Fin n, i.val = m →
      ∃ idx : Fin (decrLen f i) → Fin n,
        StrictMono (fun k => (idx k : ℕ)) ∧
        StrictAnti (fun k => f (idx k)) ∧
        idx ⟨decrLen f i - 1, by have := decrLen_pos f i; omega⟩ = i from
    H i.val i rfl
  intro m
  refine Nat.strongRec m ?_
  intro m' ih i hi
  by_cases hk : decrLen f i = 1
  · refine ⟨fun _ => i, ?_, ?_, ?_⟩
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
    · simp [hk]
  · have hk2 : 2 ≤ decrLen f i := by have := decrLen_pos f i; omega
    have hsup : 1 ≤ ((Finset.univ.filter (fun j : Fin n => j < i ∧ f j > f i)).attach).sup
        (fun j => decrLen f j.1) := by
      have h := decrLen_pos f i
      rw [decrLen] at h; omega
    have hne : (Finset.univ.filter (fun j : Fin n => j < i ∧ f j > f i)).attach.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro hemp
      rw [hemp] at hsup; simp at hsup
    obtain ⟨j, _, hj_eq⟩ := Finset.exists_mem_eq_sup _ hne (fun j => decrLen f j.1)
    have hji : j.1 < i := by
      have := j.2; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.1
    have hfj : f j.1 > f i := by
      have := j.2; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.2
    have hjsup : decrLen f j.1 = decrLen f i - 1 := by
      rw [hj_eq]
      have : decrLen f i = 1 + decrLen f j.1 := by rw [decrLen, hj_eq]
      omega
    have hjlt : j.1.val < m' := by rw [← hi]; exact Fin.lt_def.mp hji
    obtain ⟨idx', hmono', hfmono', hend'⟩ := ih j.1.val hjlt j.1 rfl
    let last' : Fin (decrLen f j.1) :=
      ⟨decrLen f j.1 - 1, by have := decrLen_pos f j.1; omega⟩
    let idx : Fin (decrLen f i) → Fin n := fun k =>
      if h : (k : ℕ) < decrLen f j.1 then idx' ⟨(k : ℕ), h⟩ else i
    refine ⟨idx, ?_, ?_, ?_⟩
    · intro a b hab
      by_cases ha : (a : ℕ) < decrLen f j.1
      · by_cases hb : (b : ℕ) < decrLen f j.1
        · show (idx' ⟨(a : ℕ), ha⟩ : ℕ) < (idx' ⟨(b : ℕ), hb⟩ : ℕ)
          exact hmono' (by simp only [Fin.lt_iff_val_lt_val]; exact hab)
        · show (idx' ⟨(a : ℕ), ha⟩ : ℕ) < (i : ℕ)
          have hle' : (⟨(a : ℕ), ha⟩ : Fin (decrLen f j.1)) ≤ last' := by
            simp only [Fin.le_iff_val_le_val]; omega
          have h1 : (idx' ⟨(a : ℕ), ha⟩ : ℕ) ≤ (idx' last' : ℕ) := hmono'.monotone hle'
          rw [hend'] at h1; omega
      · exfalso; have hb' : (b : ℕ) < decrLen f i := b.isLt; omega
    · intro a b hab
      by_cases ha : (a : ℕ) < decrLen f j.1
      · by_cases hb : (b : ℕ) < decrLen f j.1
        · show f (idx' ⟨(a : ℕ), ha⟩) > f (idx' ⟨(b : ℕ), hb⟩)
          exact hfmono' (by simp only [Fin.lt_iff_val_lt_val]; exact hab)
        · show f (idx' ⟨(a : ℕ), ha⟩) > f i
          have hle' : (⟨(a : ℕ), ha⟩ : Fin (decrLen f j.1)) ≤ last' := by
            simp only [Fin.le_iff_val_le_val]; omega
          have h1 : f (idx' ⟨(a : ℕ), ha⟩) ≥ f (idx' last') := hfmono'.monotone hle'
          rw [hend'] at h1; omega
      · exfalso; have hb' : (b : ℕ) < decrLen f i := b.isLt; omega
    · simp only [idx]
      have : ¬((⟨decrLen f i - 1, by have := decrLen_pos f i; omega⟩ : Fin (decrLen f i) : ℕ)
          < decrLen f j.1) := by
        simp only [Fin.val_mk]; omega
      simp [this]

lemma hasDecrSubseq_of_decrLen_ge {n s : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hs : 1 ≤ s) (h : s ≤ decrLen f i) : HasDecrSubseq n s f := by
  obtain ⟨idx, hmono, hfmono, _⟩ := exists_decr_subseq_ending f i
  refine ⟨fun k => idx (Fin.castLE h k), ?_, ?_⟩
  · intro a b hab; exact hmono (by simpa using hab)
  · intro a b hab; exact hfmono (by simpa using hab)

/-- **Erdős–Szekeres 1935 (Monotone Subsequence Theorem).**
    Every sequence of `(r-1)(s-1) + 1` distinct real numbers contains
    either a strictly-increasing subsequence of length `r` or a
    strictly-decreasing subsequence of length `s`. -/
theorem erdos_szekeres_mono (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (f : Fin ((r - 1) * (s - 1) + 1) → ℝ)
    (hf : Function.Injective f) :
    HasIncrSubseq _ r f ∨ HasDecrSubseq _ s f := by
  by_cases hr1 : r = 1
  · subst hr1
    left
    refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
  by_cases hs1 : s = 1
  · subst hs1
    right
    refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
    · intro a b hab; have ha := a.isLt; have hb := b.isLt; omega
  by_contra h
  push_neg at h
  obtain ⟨h₁, h₂⟩ := h
  have hp_bound : ∀ i, incrLen f i ≤ r - 1 := by
    intro i
    by_contra hlt
    push_neg at hlt
    exact h₁ (hasIncrSubseq_of_incrLen_ge f i hr (by omega))
  have hq_bound : ∀ i, decrLen f i ≤ s - 1 := by
    intro i
    by_contra hlt
    push_neg at hlt
    exact h₂ (hasDecrSubseq_of_decrLen_ge f i hs (by omega))
  let φ : Fin ((r - 1) * (s - 1) + 1) → Fin (r - 1) × Fin (s - 1) := fun i =>
    (⟨incrLen f i - 1, by have := incrLen_pos f i; have := hp_bound i; omega⟩,
     ⟨decrLen f i - 1, by have := decrLen_pos f i; have := hq_bound i; omega⟩)
  have hφ_inj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    have hpq : incrLen f i = incrLen f j ∧ decrLen f i = decrLen f j := by
      simp only [φ, Prod.mk.injEq, Fin.mk.injEq] at hij
      exact ⟨by omega, by omega⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hfne : f i ≠ f j := fun heq => hne (hf heq)
      rcases lt_or_gt_of_ne hfne with hfij | hfij
      · have := incrLen_lt_of_lt f hlt hfij; omega
      · have := decrLen_lt_of_lt f hlt hfij; omega
    · have hfne : f j ≠ f i := fun heq => hne (hf heq).symm
      rcases lt_or_gt_of_ne hfne with hfji | hfji
      · have := incrLen_lt_of_lt f hlt hfji; omega
      · have := decrLen_lt_of_lt f hlt hfji; omega
  have hcard := Fintype.card_le_of_injective φ hφ_inj
  simp [Fintype.card_fin, Fintype.card_prod] at hcard
  omega

end ErdosSzekeres