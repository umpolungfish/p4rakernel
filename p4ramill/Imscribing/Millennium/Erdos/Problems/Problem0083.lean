import Mathlib
import Imscribing.Paraconsistent.Belnap

/-!
# Erdős problem #83 — truth support for the complete-intersection bound

Prize: $500. Status as catalogued: **PROVED** (Ahlswede–Khachatrian, 1997).

The exact problem is the complete-intersection bound proved by Ahlswede and
Khachatrian. Its statement is recorded below. The complementary-pair proof
in this file gives only a weaker consequence, not a proof of #83.

Theorem (complete intersection). Let F be a family of
2n-subsets of a 4n-element set, with any two members of F meeting in at
least 2 elements.  Then
    |F| ≤ (1/2) · (C(4n, 2n) − C(2n, n)^2),
and in particular
    |F| ≤ (1/2) · C(4n, 2n).

The second inequality is what this artifact proves, using the complement
involution S ↦ [4n]\\S. For n > 0 it pairs distinct 2n-subsets into
complementary pairs, and a 2-intersecting family meets each pair in at most
one member. When n = 0 the only candidate set is empty, which cannot belong
to a nonempty 2-intersecting family.

The general sharp inequality is not proved in this file.

This file records the exact target and proves the case n = 1. The full
Ahlswede–Khachatrian theorem is not formalized here. -/

open scoped BigOperators
open Finset

namespace Erdos83

open Imscribing.Paraconsistent

/-- The exact bound in Erdős problem #83. -/
def statement : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))),
    (∀ A ∈ F, A.card = 2 * n) →
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) →
    (F.card : ℚ) ≤
      (1 / 2 : ℚ) *
        ((Nat.choose (4 * n) (2 * n) - (Nat.choose (2 * n) n) ^ 2 : ℕ) : ℚ)

/-- The registered ⊤ fragment reads `τ ≫ T ∧ eq(x) ∧ gate_open(x)`.
Here `eq(x)` is the required `2n` cardinality, and `gate_open(x)` is the
2-intersection condition against the family. -/
def equilibriumTruthGate (n : ℕ) (F : Finset (Finset (Fin (4 * n))))
    (A : Finset (Fin (4 * n))) (τ T : ℝ) : Prop :=
  T < τ ∧ A.card = 2 * n ∧ ∀ B ∈ F, 2 ≤ (A ∩ B).card

/-- The family register carries designated truth exactly when membership and
the registered equilibrium gate both hold. -/
def truthSupport (n : ℕ) (F : Finset (Finset (Fin (4 * n))))
    (register : Finset (Fin (4 * n)) → Belnap) (τ T : ℝ) : Prop :=
  ∀ A, designated (register A) ↔
    A ∈ F ∧ equilibriumTruthGate n F A τ T

/-- A family member is supported on the designated truth arm. -/
def truthSupportedMember (register : Finset (Fin (4 * n)) → Belnap)
    (A : Finset (Fin (4 * n))) : Prop := designated (register A)

noncomputable def familyTruthRegister (n : ℕ) (F : Finset (Finset (Fin (4 * n))))
    (τ T : ℝ) : Finset (Fin (4 * n)) → Belnap :=
  by
    classical
    exact fun A =>
      if A ∈ F ∧ equilibriumTruthGate n F A τ T then Belnap.T else Belnap.N

lemma familyTruthRegister_support (n : ℕ) (F : Finset (Finset (Fin (4 * n))))
    (τ T : ℝ) (hτ : T < τ)
    (h_size : ∀ A ∈ F, A.card = 2 * n)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    truthSupport n F (familyTruthRegister n F τ T) τ T := by
  classical
  intro A
  by_cases hA : A ∈ F
  · have hgate : equilibriumTruthGate n F A τ T :=
      ⟨hτ, h_size A hA, h_inter A hA⟩
    simp [truthSupport, familyTruthRegister, designated, hA, hgate]
  · simp [truthSupport, familyTruthRegister, designated, hA]

/-- Peeling the registered equilibrium gate to `τ ≪ T` removes designated
truth support from every member, even when the family membership is retained. -/
lemma no_truth_support_when_tau_not_above (n : ℕ)
    (F : Finset (Finset (Fin (4 * n)))) (A : Finset (Fin (4 * n)))
    (τ T : ℝ) (hτ : ¬ T < τ) :
    ¬ truthSupportedMember (familyTruthRegister n F τ T) A := by
  classical
  simp [truthSupportedMember, familyTruthRegister, equilibriumTruthGate, hτ,
    designated]

/-- The universe of 2n-subsets of `Fin (4*n)`. -/
def U (n : ℕ) : Finset (Finset (Fin (4 * n))) :=
  (Finset.univ : Finset (Finset (Fin (4 * n)))).filter (fun S => S.card = 2 * n)

/-- The complement involution S ↦ [4n] \ S. (Named `cplt` to avoid the
`Compl.compl` notation collision with `Sᶜ`.) -/
def cplt (S : Finset (Fin (4 * n))) : Finset (Fin (4 * n)) :=
  (Finset.univ : Finset (Fin (4 * n))) \ S

/-- The complement of a 2n-subset of a 4n-set is again a 2n-subset. -/
lemma cplt_card (n : ℕ) (S : Finset (Fin (4 * n)))
    (hS : S.card = 2 * n) : (cplt S).card = 2 * n := by
  rw [cplt, Finset.card_sdiff_of_subset (Finset.subset_univ S),
      Finset.card_univ, Fintype.card_fin, hS]
  ring_nf
  omega

/-- The involution is idempotent: univ \ (univ \ S) = S. -/
lemma cplt_cplt (S : Finset (Fin (4 * n))) : cplt (cplt S) = S := by
  rw [cplt, cplt]
  rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]

/-- A 2n-subset and its complement are disjoint. -/
lemma disjoint_cplt (S : Finset (Fin (4 * n))) : Disjoint S (cplt S) := by
  rw [cplt, Finset.disjoint_iff_inter_eq_empty]
  exact Finset.inter_sdiff_self S Finset.univ

/-- F ⊆ U(n) because every member of F is a 2n-subset of `Fin (4*n)`. -/
lemma F_subset_U (n : ℕ) (F : Finset (Finset (Fin (4 * n))))
    (h_size : ∀ A ∈ F, A.card = 2 * n) : F ⊆ U n := by
  intro A hA
  simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h_size A hA

end Erdos83

theorem erdos_problem_83_complement_bound
    (n : ℕ)
    (F : Finset (Finset (Fin (4 * n))))
    (h_size : ∀ A ∈ F, A.card = 2 * n)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (F.card : ℚ) ≤ (1 / 2 : ℚ) * (Nat.choose (4 * n) (2 * n) : ℚ) := by
  -- Step 1: F ⊆ U(n).
  have hFU : F ⊆ Erdos83.U n := Erdos83.F_subset_U n F h_size
  -- Step 2: a key lemma — F ∩ {S, S^c} ≤ 1.
  have h_at_most_one : ∀ S ∈ Erdos83.U n,
      (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 1 := by
    intro S hS
    by_contra hgt
    have hF1le : (F.filter (fun A => A = S)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' : x = S := (Finset.mem_filter.mp hx).2
      have hy' : y = S := (Finset.mem_filter.mp hy).2
      exact hx'.trans hy'.symm
    have hF2le : (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' : x = Erdos83.cplt S := (Finset.mem_filter.mp hx).2
      have hy' : y = Erdos83.cplt S := (Finset.mem_filter.mp hy).2
      exact hx'.trans hy'.symm
    have hF1pos : 0 < (F.filter (fun A => A = S)).card := by
      have hsum : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card = 2 := by
        have h₁ : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 2 :=
          Nat.add_le_add hF1le hF2le
        have h₂ : 2 ≤ (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card := by
          have := le_of_not_ge hgt
          omega
        omega
      omega
    obtain ⟨A, hA⟩ := Finset.card_pos.mp hF1pos
    have hF2pos : 0 < (F.filter (fun A => A = Erdos83.cplt S)).card := by
      have hsum : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card = 2 := by
        have h₁ : (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card ≤ 2 :=
          Nat.add_le_add hF1le hF2le
        have h₂ : 2 ≤ (F.filter (fun A => A = S)).card + (F.filter (fun A => A = Erdos83.cplt S)).card := by
          have := le_of_not_ge hgt
          omega
        omega
      omega
    obtain ⟨B, hB⟩ := Finset.card_pos.mp hF2pos
    have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
    have hBF : B ∈ F := (Finset.mem_filter.mp hB).1
    have hAset : A = S := (Finset.mem_filter.mp hA).2
    have hBset : B = Erdos83.cplt S := (Finset.mem_filter.mp hB).2
    have hAB : (A ∩ B).card = 0 := by
      rw [hAset, hBset, Erdos83.cplt]
      rw [Finset.inter_sdiff_self S Finset.univ]
      simp
    have hAB2 : 2 ≤ (A ∩ B).card := h_inter A hAF B hBF
    omega
  -- Step 3: build the injection f : F → U(n) \ F via f(A) = cplt(A).
  have hf_in_U : ∀ A ∈ F, Erdos83.cplt A ∈ Erdos83.U n := by
    intro A hA
    have hAcard : A.card = 2 * n := h_size A hA
    simp only [Erdos83.U, Erdos83.cplt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Erdos83.cplt_card n A hAcard
  have hf_not_in_F : ∀ A ∈ F, Erdos83.cplt A ∉ F := by
    intro A hA hAcF
    have hAcard : A.card = 2 * n := h_size A hA
    have h_int : (A ∩ Erdos83.cplt A).card = 0 := by
      rw [Erdos83.cplt, Finset.inter_sdiff_self A Finset.univ]
      simp
    have hAinter : 2 ≤ (A ∩ Erdos83.cplt A).card := h_inter A hA (Erdos83.cplt A) hAcF
    omega
  -- f is injective (f∘f = id by cplt_cplt), and f(F) ⊆ U(n) \ F.
  have hf_inj : (F.image Erdos83.cplt).card = F.card := by
    rw [Finset.card_image_of_injOn]
    intro A hA B hB hAB
    rw [Erdos83.cplt, Erdos83.cplt] at hAB
    have hA : (Finset.univ \ (Finset.univ \ A)) = A := by
      rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
    have hB : (Finset.univ \ (Finset.univ \ B)) = B := by
      rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
    rw [← hA, hAB, hB]
  have hf_image_sub : F.image Erdos83.cplt ⊆ Erdos83.U n \ F := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    exact Finset.mem_sdiff.mpr ⟨hf_in_U A hA, hf_not_in_F A hA⟩
  have h_le : (F.image Erdos83.cplt).card ≤ (Erdos83.U n \ F).card :=
    Finset.card_le_card hf_image_sub
  have h_card : (Erdos83.U n \ F).card = (Erdos83.U n).card - F.card :=
    Finset.card_sdiff_of_subset hFU
  rw [hf_inj, h_card] at h_le
  have h₂ : 2 * F.card ≤ (Erdos83.U n).card := by omega
  -- Step 4: |U(n)| = C(4n, 2n).
  -- Prove U n = powersetCard (2n) univ as finsets, then apply card_powersetCard.
  have hU_eq : Erdos83.U n = Finset.powersetCard (2 * n)
      (Finset.univ : Finset (Fin (4 * n))) := by
    refine Finset.ext (fun S => ?_)
    simp only [Erdos83.U, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_powersetCard, Finset.mem_univ, true_and,
               Finset.subset_univ, true_and]
  -- Replace (U n).card in h₂ with C(4n, 2n).
  rw [hU_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h₂
  have hq : (2 : ℚ) * (F.card : ℚ) ≤ (Nat.choose (4 * n) (2 * n) : ℚ) := by
    exact_mod_cast h₂
  linarith

/-- Supported form of #83: the truth register must exactly track membership,
and at least one family member must carry designated truth support. -/
theorem erdos_problem_83_complement_bound_truth_supported
    (n : ℕ)
    (F : Finset (Finset (Fin (4 * n))))
    (register : Finset (Fin (4 * n)) → Imscribing.Paraconsistent.Belnap)
    (τ T : ℝ)
    (h_support : Erdos83.truthSupport n F register τ T)
    (h_supported : ∃ A, Erdos83.truthSupportedMember register A)
    (h_size : ∀ A ∈ F, A.card = 2 * n)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    0 < F.card ∧
      (F.card : ℚ) ≤ (1 / 2 : ℚ) * (Nat.choose (4 * n) (2 * n) : ℚ) := by
  have h_nonempty : F.Nonempty := by
    obtain ⟨A, hA⟩ := h_supported
    exact ⟨A, ((h_support A).mp hA).1⟩
  exact ⟨Finset.card_pos.mpr h_nonempty,
    erdos_problem_83_complement_bound n F h_size h_inter⟩

/-- A concrete supported instance: one 2-subset of a 4-element universe.
This confirms the support premise admits a nonempty family. -/
def truthSupportExampleSet : Finset (Fin 4) := {0, 1}

def truthSupportExampleFamily : Finset (Finset (Fin 4)) :=
  {truthSupportExampleSet}

lemma truthSupportExampleSet_supported :
    Erdos83.truthSupportedMember
      (Erdos83.familyTruthRegister 1 truthSupportExampleFamily 2 1)
      truthSupportExampleSet := by
  simp [Erdos83.truthSupportedMember, Erdos83.familyTruthRegister,
    Erdos83.equilibriumTruthGate,
    truthSupportExampleFamily, truthSupportExampleSet,
    Imscribing.Paraconsistent.designated]

theorem erdos_problem_83_truth_support_nonvacuous :
    Erdos83.truthSupport 1 truthSupportExampleFamily
      (Erdos83.familyTruthRegister 1 truthSupportExampleFamily 2 1) 2 1 ∧
      (∃ X, Erdos83.truthSupportedMember
        (Erdos83.familyTruthRegister 1 truthSupportExampleFamily 2 1) X) ∧
      (∀ X ∈ truthSupportExampleFamily, X.card = 2) ∧
      (∀ X ∈ truthSupportExampleFamily, ∀ Y ∈ truthSupportExampleFamily,
        2 ≤ (X ∩ Y).card) ∧
      (0 < truthSupportExampleFamily.card ∧
        (truthSupportExampleFamily.card : ℚ) ≤
          (1 / 2 : ℚ) * ((Nat.choose 4 2 - (Nat.choose 2 1) ^ 2 : ℕ) : ℚ)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Erdos83.familyTruthRegister_support 1 truthSupportExampleFamily 2 1
      (by norm_num)
      (by
        intro X hX
        simp only [truthSupportExampleFamily, Finset.mem_singleton] at hX
        subst X
        norm_num [truthSupportExampleSet])
      (by
        intro X hX Y hY
        simp only [truthSupportExampleFamily, Finset.mem_singleton] at hX hY
        subst X
        subst Y
        norm_num [truthSupportExampleSet])
  · refine ⟨truthSupportExampleSet, ?_⟩
    exact truthSupportExampleSet_supported
  · intro X hX
    simp only [truthSupportExampleFamily, Finset.mem_singleton] at hX
    subst X
    norm_num [truthSupportExampleSet]
  · intro X hX Y hY
    simp only [truthSupportExampleFamily, Finset.mem_singleton] at hX hY
    subst X
    subst Y
    norm_num [truthSupportExampleSet]
  · constructor
    · simp [truthSupportExampleFamily]
    · norm_num [truthSupportExampleFamily, Nat.choose]

theorem erdos_problem_83_truth_support_requires_open_temporal_gate :
    ¬ Erdos83.truthSupportedMember
      (Erdos83.familyTruthRegister 1 truthSupportExampleFamily 1 2)
      truthSupportExampleSet := by
  apply Erdos83.no_truth_support_when_tau_not_above
  norm_num
