import Mathlib

/-!
# Erdős problem #113
Reference: https://www.erdosproblems.com/113
The question concerns finite bipartite graphs, 2-degeneracy, and an asymptotic
upper bound. The previous infinite-graph lower-bound formulation was incorrect.
The Janzer disproof remains a proof obligation here.
-/

open SimpleGraph Filter
open scoped Classical Topology
noncomputable section
namespace Erdos113

lemma infinite_graph_free (H : SimpleGraph ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) : H.Free G := by
  rintro ⟨c⟩
  haveI : Finite ℕ := Finite.of_injective c.toHom c.injective
  exact not_finite ℕ
lemma infinite_graph_extremal (H : SimpleGraph ℕ) (n : ℕ) :
    extremalNumber n H = n.choose 2 := by
  apply le_antisymm
  · rw [← Fintype.card_fin n, extremalNumber_le_iff]
    intro G _ _
    simpa using G.card_edgeFinset_le_card_choose_two
  · have h := card_edgeFinset_le_extremalNumber (infinite_graph_free H n (⊤ : SimpleGraph (Fin n)))
    rw [card_edgeFinset_top_eq_card_choose_two] at h
    simpa using h

/-- Every nonempty induced subgraph has a vertex of degree at most two. -/
def TwoDegenerate {q : ℕ} (H : SimpleGraph (Fin q)) : Prop :=
  ∀ S : Finset (Fin q), S.Nonempty → ∃ v : (S : Set (Fin q)),
    ((H.induce (S : Set (Fin q))).neighborSet v).encard ≤ 2

/-- The conjectured equivalence, with a fixed asymptotic upper-bound constant. -/
def Conjecture : Prop :=
  ∀ (q : ℕ) (H : SimpleGraph (Fin q)), H.IsBipartite →
    ((∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (extremalNumber n H : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ)) ↔ TwoDegenerate H)

/-- Unresolved in this module; no result about infinite graphs discharges it. -/
def Disproof : Prop := ¬ Conjecture

end Erdos113
