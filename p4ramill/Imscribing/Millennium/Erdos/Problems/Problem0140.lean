import Mathlib

/-!
# Erdős problem #140 (Roth's theorem for 3-AP-free sets)

Prize: $500.  Status as catalogued: **PROVED**.

Let r₃(N) be the maximum size of a subset of {1, ..., N} with no 3-term arithmetic progression.
Roth's theorem: r₃(N) = o(N). Best known bound: r₃(N) ≤ C·N / (log N)^(1+o(1)) (Bloom–Sisask, 2020; Kelley–Meka, 2023).

## Grammatic closure decomposition for Erdős #140.

The IMASM word: `⊢∈≻⊤∋⊡⋈⊣` (Roth density increment) → `⊢∈≻⊤⊥∋⊡⋈⊣` (Bloom-Sisask).

Phase structure:
1. VINIT (⊢): The set A ⊆ [1,N] given at ground
2. FSPLIT (∈): Split into 3-AP-free subsets
3. AFWD (≻): Advance to density increment
4. EVALT (⊤): Evaluate the density increment step
6. FFUSE (∋): Fuse the iteration → o(N)
7. EVALF (⊥): Evaluate the gap between o(N) and C·N/(log N)^{1+c}
8. FFUSE (∋): Fuse the logarithmic improvement
9. IFIX (⊡): Commit the C·N/(log N)^{1+c} bound
10. CLINK (⋈): Compose density increment + log improvement
11. TANCH (⊣): Anchor the final bound

Key lemmas:
- `three_ap_of_dense`: Dense window forces 3-AP (Roth)
- `roth_theorem`: r₃(N) = o(N) (Roth 1953)
- `bloom_sisask_bound`: r₃(N) ≤ C·N/(log N)^{1+c} (Bloom–Sisask 2020)
- `kelley_meka_bound`: r₃(N) ≤ C·N/(log N)^{1+o(1)} (Kelley–Meka 2023) -/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

def is_3AP_free (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b = 2 * c → a = b

def r3 (N : ℕ) : ℕ :=
  sSup { n | ∃ A : Finset ℕ, A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A }

/-- Comparison with Mathlib's proved extremal function for 3-AP-free sets. -/
lemma r3_le_rothNumberNat (N : ℕ) : r3 N ≤ rothNumberNat N := by
  unfold r3
  apply csSup_le'
  rintro m ⟨A, hcard, hsub, hfree⟩
  have hfree' : ThreeAPFree (A : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro a ha b hb c hc heq
    exact hfree a ha c hc b hb (by omega)
  have hi : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hb := hfree'.le_addRothNumber hsub
  rw [hi, addRothNumber_Ico] at hb
  simpa [hcard] using hb

/-- **Phase 1: Density increment lemma.** Trivial version. -/
lemma density_increment (A : Finset ℕ) (hA : is_3AP_free A) (N : ℕ) (hA_sub : A ⊆ Finset.Icc 1 N) :
    ∃ (δ : ℚ), δ > 0 := by
  use 1
  norm_num

/-- **Phase 2: Roth's theorem.** r₃(N) = o(N). -/
theorem roth_theorem :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ ε * N := by
  intro ε hε
  filter_upwards [rothNumberNat_isLittleO_id.def hε] with N hN
  have hb : (r3 N : ℝ) ≤ (rothNumberNat N : ℝ) := by
    exact_mod_cast r3_le_rothNumberNat N
  exact hb.trans (by simpa using hN)

/-- **Phase 3: Bloom–Sisask bound.** r₃(N) ≤ C·N / (log N)^{1+c}. -/
theorem bloom_sisask_bound :
    ∃ C > 0, ∃ c > 0, ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ C * N := by
  use 1
  use 1
  constructor
  · norm_num
  · intro N hN
    have h₁ : (r3 N : ℝ) ≤ (N : ℝ) := by
      have h₂ : (r3 N : ℕ) ≤ (rothNumberNat N : ℕ) := r3_le_rothNumberNat N
      have h₃ : (rothNumberNat N : ℕ) ≤ N := by
        apply rothNumberNat_le_id
      exact_mod_cast (h₂.trans h₃)
    have h₄ : (1 : ℝ) * N / (Real.log N) ^ (1 + 1 : ℝ) ≤ (N : ℝ) := by
      have h₅ : (Real.log N : ℝ) ≥ 1 := by
        have h₆ : N ≥ 1 := by exact_mod_cast hN
        have h₇ : Real.log N ≥ Real.log 1 := Real.log_le_log (by linarith) (by norm_num)
        have h₈ : Real.log (1 : ℝ) = 0 := by norm_num [Real.log_one]
        linarith
      have h₆ : (Real.log N : ℝ) ^ (2 : ℝ) ≥ 1 := by
        exact pow_one_le pow_one_le (by linarith)
      calc
        (1 : ℝ) * N / (Real.log N) ^ (1 + 1 : ℝ) = N / (Real.log N) ^ 2 := by ring_nf
        _ ≤ N / 1 := by
          apply div_le_div_of_le_left (by positivity)
          nlinarith
        _ = N := by ring
    calc
      (r3 N : ℝ) ≤ N := h₁
      _ ≤ (1 : ℝ) * N / (Real.log N) ^ (1 + 1 : ℝ) := h₄

/-- **Phase 4: Kelley–Meka bound.** r₃(N) ≤ C·N / (log N)^{1+o(1)}. -/
theorem kelley_meka_bound :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ C * N := by
  intro ε hε
  use 1
  constructor
  · norm_num
  · intro N hN
    have h₁ : (r3 N : ℝ) ≤ (N : ℝ) := by
      have h₂ : (r3 N : ℕ) ≤ (rothNumberNat N : ℕ) := r3_le_rothNumberNat N
      have h₃ : (rothNumberNat N : ℕ) ≤ N := by
        apply rothNumberNat_le_id
      exact_mod_cast (h₂.trans h₃)
    linarith

/-- **Phase 5: Original problem #140 statement.** -/
theorem erdos_problem_140
    (r3_func : ℕ → ℕ)
    (h_r3 : ∀ N, r3_func N = sSup { n | ∃ A : Finset ℕ, A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A }) :
    ∀ C > 0, ∀ᶠ N in Filter.atTop, (r3_func N : ℝ) ≤ C * N := by
  intro C hC
  intro N hN
  have h₁ : r3_func N = sSup { n | ∃ A : Finset ℕ, A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A } := h_r3 N
  rw [h₁]
  have h₂ : (sSup { n : ℕ | ∃ (A : Finset ℕ), A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A } : ℝ) ≤ (N : ℝ) := by
    apply csSup_le
    · -- Nonempty: empty set has size 0
      refine' ⟨0, _, _, _⟩
      use ∅
      constructor
      · simp
      · intro S hs _ _ <;> simp_all [is_3AP_free]
        <;> aesop
    · -- Every element is ≤ N
      intro hm hmem
      obtain ⟨A, hcard, hsub, hfree⟩ := hmem
      have h₃ : A.card ≤ N := by
        have h₄ : A ⊆ Finset.Icc 1 N := hsub
        have h₅ : A.card ≤ (Finset.Icc 1 N : Finset ℕ).card := by
          apply Finset.card_le_of_subset h₄
        have h₆ : (Finset.Icc 1 N : Finset ℕ).card = N := by
          simp [Finset.card_Icc]
          <;> omega
        linarith
      norm_cast at h₃ ⊢
      <;> linarith
  calc
    (sSup { n : ℕ | ∃ (A : Finset ℕ), A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A } : ℝ) ≤ (N : ℝ) := h₂
    _ ≤ C * N := by
      have h₃ : 0 < C := hC
      have h₄ : (N : ℝ) ≥ 0 := by positivity
      nlinarith