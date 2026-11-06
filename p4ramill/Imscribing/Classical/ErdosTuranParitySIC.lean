import Mathlib
import Imscribing.Classical.RepresentationParity
import Imscribing.Millennium.Erdos.Problems.Problem0028
import Imscribing.Millennium.ZetaSICDualFrame

/-!
Finite coefficient form of the parity identity used in the Erdős–Turán
generating-function argument. The odd representation coefficients are exactly
the doubled elements of the source set. The coefficient vector can be carried
through the established ZetaSIC Gram/dual pair without loss.
-/

namespace Imscribing.Classical.ErdosTuranParitySIC

open Finset
open Imscribing.Classical
open Imscribing.Millennium.ZetaSICDualFrame

/-- The odd representation coefficients up to the maximal sum `2N`. -/
def oddRepresentationSums (B : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => Odd (reps B n).card)

/-- Doubling is injective on the finite source set. -/
theorem double_injective_on (B : Finset ℕ) :
    Set.InjOn (fun a : ℕ => 2 * a) (B : Set ℕ) := by
  intro a ha b hb hab
  exact Nat.mul_left_cancel (by decide : 0 < 2) hab

/-- For a source set in `[0,N]`, the odd coefficients of its sum polynomial
are exactly the doubles of its elements. -/
theorem odd_representation_sums_eq_doubles (B : Finset ℕ) (N : ℕ)
    (hB : ∀ a ∈ B, a ≤ N) :
    oddRepresentationSums B N = (B.image (fun a => 2 * a)) := by
  classical
  ext n
  simp only [oddRepresentationSums, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro ⟨hn, hodd⟩
    obtain ⟨a, ha, rfl⟩ := (reps_card_odd_iff B n).mp hodd
    exact ⟨a, ha, by omega⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have := hB a ha
      omega
    · exact (reps_card_odd_iff B (2 * a)).mpr ⟨a, ha, by omega⟩

/-- The odd-coefficient support has precisely one index per source element. -/
theorem card_odd_representation_sums (B : Finset ℕ) (N : ℕ)
    (hB : ∀ a ∈ B, a ≤ N) :
    (oddRepresentationSums B N).card = B.card := by
  rw [odd_representation_sums_eq_doubles B N hB]
  exact Finset.card_image_iff.mpr (double_injective_on B)

/-- Place the odd-coefficient indicator into a square SIC coordinate space.
Coordinates beyond the coefficient interval are zero. -/
noncomputable def paritySICDimension (N : ℕ) : ℕ+ :=
  ⟨2 * N + 2, by omega⟩

/-- Put the complete ordered representation function on `[0,2N]` into the
same square SIC coordinate space used for the parity signal. Coordinates past
the sum range are zero. -/
noncomputable def representationCoefficientPayload (B : Finset ℕ) (N : ℕ) :
    Fin (((paritySICDimension N : ℕ)) ^ 2) → ℂ := by
  classical
  intro j
  exact if hj : j.val ≤ 2 * N then (reps B j.val).card else 0

/-- Every in-range SIC coordinate is exactly the corresponding ordered
representation count, with its natural-number value embedded in `ℂ`. -/
theorem representation_coefficient_payload_coordinate (B : Finset ℕ) (N k : ℕ)
    (hk : k ≤ 2 * N) :
    representationCoefficientPayload B N ⟨k, by
      have hdim : 2 * N + 2 ≤ ((paritySICDimension N : ℕ) ^ 2) := by
        simp [paritySICDimension]
        nlinarith
      omega⟩ = ((reps B k).card : ℂ) := by
  simp [representationCoefficientPayload, hk]

/-- ZetaSIC analysis followed by the exact zeta-derived dual recovers every
ordered representation coefficient simultaneously. -/
theorem zeta_sic_recovers_representation_coefficients (B : Finset ℕ) (N : ℕ) :
    (sicDualGeneral (paritySICDimension N)).mulVec
      ((sicGramGeneral (paritySICDimension N)).mulVec
        (representationCoefficientPayload B N)) =
      representationCoefficientPayload B N := by
  rw [Matrix.mulVec_mulVec, (sic_inverse_general (paritySICDimension N)).1,
    Matrix.one_mulVec]

/-- On the complete finite sum window, the ZetaSIC coordinate is the actual
representation function of the ambient set. The summands of a target at most
`N` are automatically in `A_n A N`, so this identifies the finite SIC payload
with the coefficients in Erdős problem #28, rather than with a truncated
surrogate. -/
theorem zeta_sic_recovers_basis_window_counts (A : Set ℕ) (N k : ℕ)
    (hk : k ≤ N) :
    (sicDualGeneral (paritySICDimension N)).mulVec
      ((sicGramGeneral (paritySICDimension N)).mulVec
        (representationCoefficientPayload (A_n A N) N))
        ⟨k, by
          have hdim : 2 * N + 2 ≤ ((paritySICDimension N : ℕ) ^ 2) := by
            simp [paritySICDimension]
            nlinarith
          omega⟩ = (r A k : ℂ) := by
  rw [zeta_sic_recovers_representation_coefficients]
  rw [representation_coefficient_payload_coordinate (A_n A N) N k (by omega)]
  have hframe : (reps (A_n A N) k).card = r A k := by
    rw [r_eq_finite_r_of_le A hk]
    rfl
  exact_mod_cast hframe

/-- A hypothetical bounded asymptotic basis becomes a positive, uniformly
bounded coefficient block in the exact ZetaSIC readout. This carries the
problem's tail-coverage and global-cap hypotheses onto the same coefficients
used by the finite square-series arguments. -/
theorem zeta_sic_basis_window_constraints (A : Set ℕ) (N N₀ M : ℕ)
    (h_basis : ∀ n ≥ N₀, n ∈ sumset A)
    (h_bound : ∀ n : ℕ, r A n ≤ M) (hN : N₀ ≤ N) :
    ∀ k : ℕ, ∀ (_ : N₀ ≤ k), ∀ (hkN : k ≤ N),
      0 < Complex.re ((sicDualGeneral (paritySICDimension N)).mulVec
        ((sicGramGeneral (paritySICDimension N)).mulVec
          (representationCoefficientPayload (A_n A N) N))
          ⟨k, by
            have hdim : 2 * N + 2 ≤ ((paritySICDimension N : ℕ) ^ 2) := by
              simp [paritySICDimension]
              nlinarith
            omega⟩) ∧
      Complex.re ((sicDualGeneral (paritySICDimension N)).mulVec
        ((sicGramGeneral (paritySICDimension N)).mulVec
          (representationCoefficientPayload (A_n A N) N))
          ⟨k, by
            have hdim : 2 * N + 2 ≤ ((paritySICDimension N : ℕ) ^ 2) := by
              simp [paritySICDimension]
              nlinarith
            omega⟩) ≤ (M : ℝ) := by
  intro k hk₀ hkN
  rw [zeta_sic_recovers_basis_window_counts A N k hkN]
  have hrepresented : k ∈ sumset A := h_basis k (by omega)
  have hpos : 0 < r A k := (r_positive_iff A k).2 hrepresented
  constructor
  · simpa using (show 0 < (r A k : ℝ) by exact_mod_cast hpos)
  · simpa using (show (r A k : ℝ) ≤ (M : ℝ) by exact_mod_cast h_bound k)

/-- The parity coordinate recovered by ZetaSIC is exactly the diagonal
condition in the ambient set: an odd ordered-representation coefficient occurs
precisely at a doubled element. The finite frame is lossless on `k ≤ N`. -/
theorem zeta_sic_basis_window_parity (A : Set ℕ) (N k : ℕ) (hk : k ≤ N) :
    Odd (r A k) ↔ ∃ a ∈ A, k = a + a := by
  classical
  have hframe : (reps (A_n A N) k).card = r A k := by
    rw [r_eq_finite_r_of_le A hk]
    rfl
  rw [← hframe, reps_card_odd_iff]
  constructor
  · rintro ⟨a, ha, hk⟩
    exact ⟨a, (Finset.mem_filter.mp ha).2, hk⟩
  · rintro ⟨a, ha, hk⟩
    have ha_le : a ≤ N := by omega
    refine ⟨a, ?_, hk⟩
    simp [A_n, Finset.mem_filter, Finset.mem_Icc, ha, ha_le]

/-- A covered finite target family forces a parity-refined pair count. Each
target has at least one ordered representation, and each target outside the
doubled image has at least two by the swap involution. The doubled image has at
most one point per source element. -/
theorem covered_targets_pair_square_lower_bound (B S : Finset ℕ)
    (hcover : ∀ k ∈ S, ∃ a ∈ B, ∃ b ∈ B, a + b = k) :
    2 * S.card ≤ B.card ^ 2 + B.card := by
  classical
  let isDouble : ℕ → Prop := fun k => ∃ a ∈ B, k = a + a
  let D := S.filter isDouble
  let T := S.filter (fun k => ¬ isDouble k)
  have hDsub : D ⊆ B.image (fun a => 2 * a) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨_, ⟨a, ha, hka⟩⟩
    exact Finset.mem_image.mpr ⟨a, ha, by omega⟩
  have hDle : D.card ≤ B.card :=
    (Finset.card_le_card hDsub).trans Finset.card_image_le
  have hsplitCard : D.card + T.card = S.card := by
    simpa [D, T] using
      (Finset.card_filter_add_card_filter_not (s := S) isDouble)
  have hsumFibers :
      (∑ k ∈ S, (reps B k).card) =
        ((B ×ˢ B).filter (fun p => p.1 + p.2 ∈ S)).card := by
    simpa only [reps, Finset.sum_card_fiberwise_eq_card_filter] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (s := B ×ˢ B) (t := S) (g := fun p : ℕ × ℕ => p.1 + p.2))
  have hsumLe :
      (∑ k ∈ S, (reps B k).card) ≤ B.card ^ 2 := by
    rw [hsumFibers]
    calc
      ((B ×ˢ B).filter (fun p => p.1 + p.2 ∈ S)).card ≤ (B ×ˢ B).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = B.card ^ 2 := by simp [Finset.card_product, pow_two]
  have hpos : ∀ k ∈ S, 1 ≤ (reps B k).card := by
    intro k hk
    obtain ⟨a, ha, b, hb, hab⟩ := hcover k hk
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    refine ⟨(a, b), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
  have hdoubleLower : D.card ≤ ∑ k ∈ D, (reps B k).card := by
    calc
      D.card = ∑ k ∈ D, 1 := by simp
      _ ≤ ∑ k ∈ D, (reps B k).card := by
        apply Finset.sum_le_sum
        intro k hk
        exact hpos k (Finset.mem_filter.mp hk).1
  have htwoLower : 2 * T.card ≤ ∑ k ∈ T, (reps B k).card := by
    calc
      2 * T.card = ∑ k ∈ T, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ k ∈ T, (reps B k).card := by
        apply Finset.sum_le_sum
        intro k hk
        have hnonDouble : ¬ ∃ a ∈ B, k = a + a := by
          simpa [T, isDouble] using (Finset.mem_filter.mp hk).2
        obtain ⟨a, ha, b, hb, hab⟩ := hcover k (Finset.mem_filter.mp hk).1
        have hmem : (a, b) ∈ reps B k := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
        exact Imscribing.Classical.two_le_reps_of_nonempty B k ⟨(a, b), hmem⟩ hnonDouble
  have hsumSplit :
      (∑ k ∈ D, (reps B k).card) +
        (∑ k ∈ T, (reps B k).card) =
          ∑ k ∈ S, (reps B k).card := by
    rw [← Finset.sum_filter_add_sum_filter_not S isDouble
      (fun k => (reps B k).card)]
  have hlow : D.card + 2 * T.card ≤ ∑ k ∈ S, (reps B k).card := by
    rw [← hsumSplit]
    exact Nat.add_le_add hdoubleLower htwoLower
  have hpair : D.card + 2 * T.card ≤ B.card ^ 2 := le_trans hlow hsumLe
  nlinarith [hsplitCard, hDle, hpair]

/-- Apply the parity-refined count to the actual lower window in Erdős–Turán
#28. Eventual basis coverage forces at least twice the window length in
ordered-pair capacity, up to the diagonal budget `|A ∩ [0,N]|`. -/
theorem basis_window_parity_pair_lower_bound (A : Set ℕ) (N N₀ : ℕ)
    (h_basis : ∀ n ≥ N₀, n ∈ sumset A) (hN : N₀ ≤ N) :
    2 * (Finset.Icc N₀ N).card ≤
      (A_n A N).card ^ 2 + (A_n A N).card := by
  apply covered_targets_pair_square_lower_bound (A_n A N) (Finset.Icc N₀ N)
  intro k hk
  have hk_window := Finset.mem_Icc.mp hk
  obtain ⟨a, ha, b, hb, hab⟩ := h_basis k (by omega)
  refine ⟨a, ?_, b, ?_, hab⟩
  · simp [A_n, Finset.mem_filter, Finset.mem_Icc, ha]
    omega
  · simp [A_n, Finset.mem_filter, Finset.mem_Icc, hb]
    omega

noncomputable def paritySICPayload (B : Finset ℕ) (N : ℕ) :
    Fin (((paritySICDimension N : ℕ)) ^ 2) → ℂ := by
  classical
  intro j
  exact if hj : j.val ≤ 2 * N then
    (if Odd (reps B j.val).card then 1 else 0)
  else 0

/-- The Zeta-derived SIC inverse reconstructs the complete odd-coefficient
vector, retaining each parity-marked representation sum. -/
theorem zeta_sic_recovers_parity_payload (B : Finset ℕ) (N : ℕ) :
    (sicDualGeneral (paritySICDimension N)).mulVec
      ((sicGramGeneral (paritySICDimension N)).mulVec
        (paritySICPayload B N)) = paritySICPayload B N := by
  rw [Matrix.mulVec_mulVec, (sic_inverse_general (paritySICDimension N)).1,
    Matrix.one_mulVec]

end Imscribing.Classical.ErdosTuranParitySIC
