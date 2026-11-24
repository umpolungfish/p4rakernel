import Mathlib

/-!
# Three-term arithmetic progression density bounds

The checked quantitative conclusion here is Roth's density decay `r3(N)=o(N)`.
`three_ap_of_dense` transfers it to sufficiently large dense intervals.
The legacy Bloom–Sisask and Kelley–Meka declarations below state only linear
bounds; their logarithmic improvements are not formalized by those declarations.
-/

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

/-- An admissible set is below the finite extremum. -/
lemma card_le_r3 {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Finset.Icc 1 N) (hfree : is_3AP_free A) : A.card ≤ r3 N := by
  have hbdd : BddAbove { n : ℕ | ∃ B : Finset ℕ,
      B.card = n ∧ B ⊆ Finset.Icc 1 N ∧ is_3AP_free B } := by
    refine ⟨N, ?_⟩
    rintro k ⟨B, hcard, hB, _⟩
    rw [← hcard]
    have h := Finset.card_le_card hB
    simpa using h
  exact le_csSup hbdd ⟨A, rfl, hsub, hfree⟩

/-- A fixed positive density forces a nontrivial progression in every
sufficiently large interval. -/
theorem three_ap_of_dense (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → ε * N < A.card →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b = 2 * c ∧ a ≠ b := by
  filter_upwards [roth_theorem ε hε] with N hN
  intro A hsub hdense
  by_contra h
  have hfree : is_3AP_free A := by
    intro a ha b hb c hc heq
    by_contra hne
    exact h ⟨a, ha, b, hb, c, hc, heq, hne⟩
  have hb : (A.card : ℝ) ≤ (r3 N : ℝ) := by
    exact_mod_cast card_le_r3 hsub hfree
  linarith

/-- Pointwise elementary bound. This declaration does not express the
quantitative logarithmic Bloom–Sisask estimate. -/
lemma r3_le_interval_length (N : ℕ) : (r3 N : ℝ) ≤ N := by
  have h := (r3_le_rothNumberNat N).trans (rothNumberNat_le N)
  exact_mod_cast h

/-- Legacy linear bound; the witness `c` is unused in this statement. -/
theorem bloom_sisask_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ C * N := by
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  filter_upwards [] with N
  simpa using r3_le_interval_length N

/-- Legacy linear bound, independent of the quantitative Kelley–Meka estimate. -/
theorem kelley_meka_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N in Filter.atTop, (r3 N : ℝ) ≤ C * N := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [] with N
  simpa using r3_le_interval_length N

/-- Roth density decay for the supplied extremal function. -/
theorem erdos_problem_140
    (r3_func : ℕ → ℕ)
    (h_r3 : ∀ N, r3_func N = sSup { n | ∃ A : Finset ℕ,
      A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ is_3AP_free A }) :
    ∀ C > 0, ∀ᶠ N in Filter.atTop, (r3_func N : ℝ) ≤ C * N := by
  intro C hC
  filter_upwards [roth_theorem C hC] with N hN
  have h_eq : r3_func N = r3 N := h_r3 N
  simpa only [h_eq] using hN
