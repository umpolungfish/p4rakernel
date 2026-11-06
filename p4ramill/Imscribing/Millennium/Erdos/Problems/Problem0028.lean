import Mathlib

/-!
# Erdős problem #28

Prize: $500.  Status as catalogued: **OPEN**.

If A+A has finite complement, the representation counts are unbounded.
The referenced problem asks for unbounded limsup, not convergence to infinity:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/28.lean

The finite counting lemmas below are proved. The actual open assertion is
recorded as a proposition and is not introduced as an axiom.
-/

open scoped BigOperators
open Finset
open Classical

def sumset (A : Set ℕ) : Set ℕ :=
  { n : ℕ | ∃ a ∈ A, ∃ b ∈ A, a + b = n }

/-- The representation function r_A(n) = number of ways to write n as a+b with a,b ∈ A.
This is a function on ℕ that we define using the finite approximation A ∩ [0, n]. -/
noncomputable def r (A : Set ℕ) (n : ℕ) : ℕ :=
  let A_n : Finset ℕ := (Finset.Icc 0 n).filter (fun x => x ∈ A)
  (A_n ×ˢ A_n).filter (fun p => p.1 + p.2 = n) |>.card

/-- The finite approximation A ∩ [0, n] -/
noncomputable def A_n (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 0 n).filter (fun x => x ∈ A)

/-- Representation count whose two summands remain in the fixed finite frame. -/
noncomputable def finite_r (A : Set ℕ) (n k : ℕ) : ℕ :=
  ((((A_n A n) ×ˢ (A_n A n))).filter (fun p => p.1 + p.2 = k)).card

lemma finite_r_sum (A : Set ℕ) (n B : ℕ) :
    (∑ k ∈ Finset.range (B + 1), finite_r A n k) =
      ((((A_n A n) ×ˢ (A_n A n))).filter (fun p => p.1 + p.2 ≤ B)).card := by
  classical
  unfold finite_r
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨hp, h⟩ <;> exact ⟨hp, by omega⟩

lemma r_eq_finite_r_of_le (A : Set ℕ) {k n : ℕ} (hkn : k ≤ n) :
    r A k = finite_r A n k := by
  classical
  dsimp only [r, finite_r, A_n]
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor <;> rintro ⟨⟨⟨⟨ha0, han⟩, ha⟩, ⟨⟨hb0, hbn⟩, hb⟩⟩, hs⟩ <;>
    exact ⟨⟨⟨⟨by omega, by omega⟩, ha⟩, ⟨⟨by omega, by omega⟩, hb⟩⟩, hs⟩

lemma finite_r_le_r (A : Set ℕ) (n k : ℕ) : finite_r A n k ≤ r A k := by
  classical
  dsimp only [finite_r, r, A_n]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  rcases hp with ⟨⟨⟨⟨ha0, han⟩, ha⟩, ⟨⟨hb0, hbn⟩, hb⟩⟩, hs⟩
  exact ⟨⟨⟨⟨by omega, by omega⟩, ha⟩, ⟨⟨by omega, by omega⟩, hb⟩⟩, hs⟩

/-- Summing fibres retains exactly the pairs below the sum boundary. -/
theorem sum_r_eq_filtered_card (A : Set ℕ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), r A k) =
      ((((A_n A n) ×ˢ (A_n A n))).filter (fun p => p.1 + p.2 ≤ n)).card := by
  calc
    (∑ k ∈ Finset.range (n + 1), r A k) =
        ∑ k ∈ Finset.range (n + 1), finite_r A n k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact r_eq_finite_r_of_le A (by have := Finset.mem_range.mp hk; omega)
    _ = _ := finite_r_sum A n n

/-- Summing the fixed-frame count through `2n` counts each retained pair once.
The unrestricted `r A k` cannot replace `finite_r A n k` in this identity. -/
theorem sum_finite_r_eq_card_sq (A : Set ℕ) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1), finite_r A n k) = (A_n A n).card ^ 2 := by
  classical
  rw [finite_r_sum]
  have hf : ((((A_n A n) ×ˢ (A_n A n))).filter (fun p => p.1 + p.2 ≤ 2 * n)) =
      ((A_n A n) ×ˢ (A_n A n)) := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    simp only [A_n, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
    omega
  rw [hf, Finset.card_product]
  ring

/-- The rejected unrestricted identity already fails for `{0,2}` at `n=1`. -/
theorem unrestricted_sum_identity_counterexample :
    (∑ k ∈ Finset.range 3, r ({0, 2} : Set ℕ) k) ≠
      (A_n ({0, 2} : Set ℕ) 1).card ^ 2 := by
  norm_num [r, A_n, Finset.sum_range_succ, Finset.product_eq_sprod,
    ← Nat.range_succ_eq_Icc_zero, Finset.range_add_one,
    Finset.filter_insert, Finset.filter_singleton, Finset.product,
    Finset.singleton_product]

/-! The exact Erdős–Turán assertion, matching the formalized problem: a cofinite
sumset makes the limsup of the ordered representation counts infinite. -/
def ErdosProblem28Statement : Prop :=
  ∀ A : Set ℕ, Set.Finite { n : ℕ | n ∉ sumset A } →
    Filter.limsup (fun n : ℕ => (r A n : ℕ∞)) Filter.atTop = ⊤

/-- Eventual growth above every bound is the filter definition of divergence. -/
theorem unbounded_representation_counts_tendsto (A : Set ℕ)
    (h : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, r A n > M) :
    Filter.Tendsto (fun n : ℕ => r A n) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro M
  obtain ⟨N, hN⟩ := h M
  exact Filter.eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).le⟩

/-- The sum of r_A(k) for k ≤ n is at most |A_n|² -/
lemma sum_r_le_card_sq {A : Set ℕ} {n : ℕ} :
    (Finset.sum (Finset.range (n + 1)) (fun k => r A k)) ≤ (A_n A n).card ^ 2 := by
  classical
  have h₁ : (Finset.sum (Finset.range (n + 1)) (fun k => r A k)) = (((((A_n A n) ×ˢ (A_n A n))).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card :=
    sum_r_eq_filtered_card A n
  rw [h₁]
  have h₂ : (((((A_n A n) ×ˢ (A_n A n))).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)) ⊆ ((A_n A n) ×ˢ (A_n A n)) := by
    apply Finset.filter_subset
  have h₃ : (((((A_n A n) ×ˢ (A_n A n))).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card ≤ (((A_n A n) ×ˢ (A_n A n))).card := by
    apply Finset.card_mono h₂
  have h₄ : (((A_n A n) ×ˢ (A_n A n))).card = (A_n A n).card * (A_n A n).card := by
    simp [Finset.card_product]
  have h₅ : (A_n A n).card * (A_n A n).card = (A_n A n).card ^ 2 := by
    ring
  have h₆ : (((A_n A n) ×ˢ (A_n A n))).card = (A_n A n).card ^ 2 := by
    rw [h₄, h₅]
  have h₇ : (((((A_n A n) ×ˢ (A_n A n))).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card ≤ (A_n A n).card ^ 2 := by
    calc
      (((((A_n A n) ×ˢ (A_n A n))).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n)) : Finset (ℕ × ℕ)).card ≤ (((A_n A n) ×ˢ (A_n A n))).card := h₃
      _ = (A_n A n).card ^ 2 := by rw [h₆]
  exact h₇

/-- The square identity applies to the fixed finite-frame representation count. -/
lemma sum_r_eq_card_sq {A : Set ℕ} {n : ℕ} :
    (∑ k ∈ Finset.range (2 * n + 1), finite_r A n k) = (A_n A n).card ^ 2 :=
  sum_finite_r_eq_card_sq A n

lemma card_sq_le_sum_r (A : Set ℕ) (n : ℕ) :
    (A_n A n).card ^ 2 ≤ ∑ k ∈ Finset.range (2 * n + 1), r A k := by
  rw [← sum_finite_r_eq_card_sq A n]
  exact Finset.sum_le_sum (fun k _ => finite_r_le_r A n k)

/-- A bound on the unrestricted representation counts bounds the retained pairs. -/
lemma card_sq_le_of_r_bounded {A : Set ℕ} {n M : ℕ}
    (h : ∀ k ≤ 2 * n, r A k ≤ M) :
    (A_n A n).card ^ 2 ≤ M * (2 * n + 1) := by
  calc
    (A_n A n).card ^ 2 ≤ ∑ k ∈ Finset.range (2 * n + 1), r A k := card_sq_le_sum_r A n
    _ ≤ ∑ k ∈ Finset.range (2 * n + 1), M := by
      apply Finset.sum_le_sum
      intro k hk
      exact h k (by have := Finset.mem_range.mp hk; omega)
    _ = M * (2 * n + 1) := by simp [Nat.mul_comm]

lemma r_positive_iff (A : Set ℕ) (n : ℕ) : 0 < r A n ↔ n ∈ sumset A := by
  classical
  dsimp only [r, sumset]
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨a, b⟩, hp⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    exact ⟨a, hp.1.1.2, b, hp.1.2.2, hp.2⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨(a, b), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨⟨by omega, by omega⟩, ha⟩, ⟨⟨by omega, by omega⟩, hb⟩⟩, hab⟩

/-- A cofinite sumset forces a square-root counting lower bound. This follows
from the finite pair partition, independently of the unboundedness conjecture. -/
theorem cofinite_sumset_counting_lower_bound (A : Set ℕ)
    (hA : Set.Finite {n : ℕ | n ∉ sumset A}) :
    ∃ B : ℕ, ∀ N : ℕ, N - B ≤ (A_n A N).card ^ 2 := by
  classical
  obtain ⟨B, hB⟩ := hA.exists_le
  refine ⟨B, ?_⟩
  intro N
  have hpos : ∀ k ∈ Finset.Icc (B + 1) N, 1 ≤ r A k := by
    intro k hk
    have hsum : k ∈ sumset A := by
      by_contra h
      have hb := hB k h
      have := (Finset.mem_Icc.mp hk).1
      omega
    exact (r_positive_iff A k).mpr hsum
  have hsub : Finset.Icc (B + 1) N ⊆ Finset.range (N + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hk).2; omega)
  calc
    N - B = (Finset.Icc (B + 1) N).card := by rw [Nat.card_Icc]; omega
    _ = ∑ k ∈ Finset.Icc (B + 1) N, 1 := by simp
    _ ≤ ∑ k ∈ Finset.Icc (B + 1) N, r A k := Finset.sum_le_sum hpos
    _ ≤ ∑ k ∈ Finset.range (N + 1), r A k := Finset.sum_le_sum_of_subset hsub
    _ ≤ (A_n A N).card ^ 2 := sum_r_le_card_sq

/-- Under a bounded-representation counterassumption, a cofinite sumset pins
the square of the counting function between linear bounds. This records the
scale forced by the elementary pair count; it does not prove the open
unboundedness conclusion. -/
theorem cofinite_bounded_representations_counting_scale (A : Set ℕ)
    (h_cofinite : Set.Finite {n : ℕ | n ∉ sumset A}) (M : ℕ)
    (h_bounded : ∀ k : ℕ, r A k ≤ M) :
    ∃ B : ℕ, ∀ N : ℕ,
      N - B ≤ (A_n A N).card ^ 2 ∧
      (A_n A N).card ^ 2 ≤ M * (2 * N + 1) := by
  obtain ⟨B, h_lower⟩ := cofinite_sumset_counting_lower_bound A h_cofinite
  refine ⟨B, fun N => ⟨h_lower N, ?_⟩⟩
  apply card_sq_le_of_r_bounded
  intro k _
  exact h_bounded k
