import Mathlib
set_option maxHeartbeats 1000000

/-!
# Erdős problem #713

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

/-! The literal universal assertion in #713 asks for a positive power-law
asymptotic for every bipartite graph. -/

def HasErdos713PowerLaw {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ α c : ℝ, 1 ≤ α ∧ α < 2 ∧ 0 < c ∧
    Filter.Tendsto
      (fun n : ℕ => (SimpleGraph.extremalNumber n G : ℝ) / (c * (n : ℝ) ^ α))
      Filter.atTop (𝓝 1)

def ErdosProblem713Statement : Prop :=
  ∀ (q : ℕ) (G : SimpleGraph (Fin q)),
    G.IsBipartite → 2 ≤ G.edgeFinset.card → HasErdos713PowerLaw G

abbrev K2 : SimpleGraph (Fin 2) := ⊤

lemma K2_bipartite : K2.IsBipartite := by
  unfold SimpleGraph.IsBipartite SimpleGraph.Colorable
  refine ⟨⟨fun i => i, ?_⟩⟩
  intro a b hab heq
  exact (K2.ne_of_adj hab) heq

lemma K2_has_only_one_edge : K2.edgeFinset.card = 1 := by
  simpa [K2] using
    (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin 2))

theorem K2_is_excluded_from_erdos713 : ¬ 2 ≤ K2.edgeFinset.card := by
  rw [K2_has_only_one_edge]
  omega
