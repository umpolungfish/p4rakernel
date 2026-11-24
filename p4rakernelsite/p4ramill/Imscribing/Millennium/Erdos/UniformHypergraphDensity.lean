import Mathlib

/-! Uniform hypergraph deletion: every deletion is retained in the counting fold. -/
namespace Erdos712
open Finset Filter
open scoped BigOperators Topology

/-- An `r`-uniform family with no complete `k`-vertex subfamily. -/
def Admissible {V : Type*} [DecidableEq V] (k r : ℕ) (H : Finset (Finset V)) : Prop :=
  (∀ S ∈ H, S.card = r) ∧
    ¬ ∃ X : Finset V, X.card = k ∧
      ∀ S : Finset V, S ⊆ X → S.card = r → S ∈ H

noncomputable def lift {n : ℕ} (v : Fin (n + 1)) (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.image v.succAbove

lemma lift_card {n : ℕ} (v : Fin (n + 1)) (S : Finset (Fin n)) :
    (lift v S).card = S.card := by
  exact card_image_of_injective S Fin.succAbove_right_injective

lemma lift_injective {n : ℕ} (v : Fin (n + 1)) : Function.Injective (lift v) := by
  exact Finset.image_injective Fin.succAbove_right_injective

lemma not_mem_lift {n : ℕ} (v : Fin (n + 1)) (S : Finset (Fin n)) : v ∉ lift v S := by
  simp only [lift, mem_image]
  rintro ⟨i, hi, heq⟩
  exact Fin.succAbove_ne v i heq

lemma exists_lift {n : ℕ} (v : Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hv : v ∉ T) : ∃ S : Finset (Fin n), lift v S = T := by
  have hsub : T ⊆ Finset.univ.image v.succAbove := by
    intro x hx
    have hxv : x ≠ v := by intro h; subst x; exact hv hx
    have hxrange : x ∈ Set.range v.succAbove := by
      simpa only [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff] using hxv
    obtain ⟨i, rfl⟩ := hxrange
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  exact Finset.subset_univ_image_iff.mp hsub

noncomputable def deletion {n : ℕ} (v : Fin (n + 1))
    (H : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => lift v S ∈ H)

lemma admissible_deletion {n k r : ℕ} {H : Finset (Finset (Fin (n + 1)))}
    (hH : Admissible k r H) (v : Fin (n + 1)) : Admissible k r (deletion v H) := by
  classical
  constructor
  · intro S hS
    have hm : lift v S ∈ H := (mem_filter.mp hS).2
    simpa only [lift_card] using hH.1 (lift v S) hm
  · rintro ⟨X, hX, hclique⟩
    apply hH.2
    refine ⟨lift v X, by simpa only [lift_card] using hX, ?_⟩
    intro T hTX hT
    obtain ⟨S, hSX, hST⟩ := Finset.subset_image_iff.mp hTX
    have hScard : S.card = r := by
      have hc := lift_card v S
      rw [show lift v S = T from hST] at hc
      omega
    have hS := hclique S hSX hScard
    have hm := (mem_filter.mp hS).2
    simpa only [show lift v S = T from hST] using hm

lemma deletion_card {n : ℕ} (v : Fin (n + 1))
    (H : Finset (Finset (Fin (n + 1)))) :
    (deletion v H).card = (H.filter (fun S => v ∉ S)).card := by
  classical
  apply Finset.card_bij (fun S _ => lift v S)
  · intro S hS
    exact mem_filter.mpr ⟨(mem_filter.mp hS).2, not_mem_lift v S⟩
  · intro S hS T hT hST
    exact lift_injective v hST
  · intro T hT
    obtain ⟨hTH, hv⟩ := mem_filter.mp hT
    obtain ⟨S, hS⟩ := exists_lift v T hv
    refine ⟨S, mem_filter.mpr ⟨mem_univ _, ?_⟩, hS⟩
    simpa only [hS] using hTH

noncomputable def extremal (k r n : ℕ) : ℕ :=
  sSup {m | ∃ H : Finset (Finset (Fin n)), H.card = m ∧ Admissible k r H}

lemma admissible_counts_finite (k r n : ℕ) :
    {m | ∃ H : Finset (Finset (Fin n)), H.card = m ∧ Admissible k r H}.Finite := by
  apply (Set.finite_range (fun H : Finset (Finset (Fin n)) => H.card)).subset
  rintro m ⟨H, hH, _⟩
  exact ⟨H, hH⟩

lemma card_le_extremal {k r n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : Admissible k r H) : H.card ≤ extremal k r n :=
  le_csSup (admissible_counts_finite k r n).bddAbove ⟨H, rfl, hH⟩

lemma admissible_empty {V : Type*} [DecidableEq V] {k r : ℕ} (hrk : r ≤ k) :
    Admissible k r (∅ : Finset (Finset V)) := by
  constructor
  · simp
  · rintro ⟨X, hX, hclique⟩
    obtain ⟨S, hSX, hS⟩ := X.exists_subset_card_eq (by omega : r ≤ X.card)
    simpa using hclique S hSX hS

lemma exists_extremal (k r n : ℕ) (hrk : r ≤ k) :
    ∃ H : Finset (Finset (Fin n)), H.card = extremal k r n ∧ Admissible k r H := by
  have hne : Set.Nonempty {m | ∃ H : Finset (Finset (Fin n)), H.card = m ∧ Admissible k r H} :=
    ⟨0, ∅, rfl, admissible_empty hrk⟩
  exact hne.csSup_mem (admissible_counts_finite k r n)

/-- The full deletion sum retains every edge exactly once for each vertex
outside that edge. -/
theorem extremal_deletion_bound (k r n : ℕ) (hrk : r ≤ k) :
    extremal k r (n + 1) * (n + 1 - r) ≤ (n + 1) * extremal k r n := by
  classical
  obtain ⟨H, hcard, hH⟩ := exists_extremal k r (n + 1) hrk
  have hcount : H.card * (n + 1 - r) ≤ (n + 1) * extremal k r n := by
    have hh : H.card • (n + 1 - r) ≤
        (Finset.univ : Finset (Fin (n + 1))).card • extremal k r n := by
      apply Finset.card_nsmul_le_card_nsmul' (r := fun v S => v ∉ S)
      · intro S hS
        have hs := hH.1 S hS
        have hf : (Finset.univ.filter (fun v : Fin (n + 1) => v ∉ S)) = Sᶜ := by
          ext v
          simp
        simp only [Finset.bipartiteBelow, hf, Finset.card_compl,
          Fintype.card_fin, hs, Nat.cast_id, le_refl]
      · intro v hv
        simpa only [Finset.bipartiteAbove, ← deletion_card] using
          card_le_extremal (admissible_deletion hH v)
    simpa only [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] using hh
  simpa only [hcard] using hcount

noncomputable def density (k r n : ℕ) : ℝ :=
  (extremal k r n : ℝ) / (n.choose r : ℝ)

/-- Normalized extremal density decreases under the full deletion average. -/
theorem density_succ_le (k r n : ℕ) (hrk : r ≤ k) (hrn : r ≤ n) :
    density k r (n + 1) ≤ density k r n := by
  have hc := extremal_deletion_bound k r n hrk
  have hp : extremal k r (n + 1) * n.choose r ≤
      extremal k r n * (n + 1).choose r := by
    apply Nat.le_of_mul_le_mul_right (c := n + 1) _ (by omega)
    calc
      (extremal k r (n + 1) * n.choose r) * (n + 1) =
          (extremal k r (n + 1) * (n + 1 - r)) * (n + 1).choose r := by
        rw [Nat.mul_assoc, Nat.choose_mul_succ_eq]
        ring
      _ ≤ ((n + 1) * extremal k r n) * (n + 1).choose r :=
        Nat.mul_le_mul_right _ hc
      _ = (extremal k r n * (n + 1).choose r) * (n + 1) := by ring
  unfold density
  apply (div_le_div_iff₀ ?_ ?_).mpr
  · exact_mod_cast hp
  · exact_mod_cast Nat.choose_pos (by omega : r ≤ n + 1)
  · exact_mod_cast Nat.choose_pos hrn

theorem density_antitone (k r : ℕ) (hrk : r ≤ k) :
    AntitoneOn (density k r) (Set.Ici r) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  exact density_succ_le k r n hrk hn

/-- Existence of uniform hypergraph Turán density. -/
theorem density_limit (k r : ℕ) (hrk : r ≤ k) :
    ∃ L : ℝ, Tendsto (density k r) atTop (𝓝 L) := by
  suffices h : ∃ L : ℝ, Tendsto (fun n => density k r (n + r)) atTop (𝓝 L) by
    simpa only [tendsto_add_atTop_iff_nat r] using h
  refine ⟨⨅ n, density k r (n + r), ?_⟩
  apply tendsto_atTop_ciInf
  · rw [antitone_add_nat_iff_antitoneOn_nat_Ici]
    exact density_antitone k r hrk
  · refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    unfold density
    positivity

end Erdos712
