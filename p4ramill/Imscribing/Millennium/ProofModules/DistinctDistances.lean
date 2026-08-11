/-
PROOF MODULE: Guth–Katz distinct distances

The Guth–Katz theorem is `g(n) = Ω(n / log n)`, where `g(n)` is the least
number of distinct pairwise distances among `n` points in the plane. It is
asymptotic and it is a lower bound on a MINIMUM over configurations.

This module previously defined

    g_distinct n = sInf { m | ∀ P, P.card = n → (distances P).card ≥ m }

and that set is downward closed: `m = 0` satisfies the condition for every `P`,
so `0` belongs to it and the infimum is `0` at every `n`. `g_distinct` was
identically zero, and `guth_katz_computable`, which asserted
`g_distinct n ≥ (1/10)·n/log n` for all `n ≥ 2`, was therefore asserting
`0 ≥ (1/10)·n/log n` — false at every `n ≥ 2`, since the right side is
positive there. A `sorry` stood where the contradiction would have surfaced.
`g_distinct_eq_zero` and `guth_katz_computable_is_false` below prove both
halves of that.

The quantity wanted is the SUPREMUM of the same set, or equivalently the
minimum of the distance count over configurations, which is what `distinctG`
is. The Guth–Katz bound is stated as a Prop rather than sorried, since it is
cited here and not formalized.

Author: Lando⊗⊙perator
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped BigOperators
open Asymptotics Filter

namespace Millennium.ProofModules.DistinctDistances

/-- The distinct distances realised by a finite point set. -/
noncomputable def distanceSet (P : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  (((P ×ˢ P).image (fun pq => dist pq.1 pq.2)).erase 0)

/-- The old definition, kept so its defect can be stated. -/
noncomputable def g_distinct (n : ℕ) : ℕ :=
  sInf { m : ℕ | ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n → (distanceSet P).card ≥ m }

/-- **The old definition is identically zero.** The set is downward closed and
`0` is in it, because every cardinality is at least `0`. -/
theorem g_distinct_eq_zero (n : ℕ) : g_distinct n = 0 := by
  unfold g_distinct
  have h0 : (0 : ℕ) ∈ { m : ℕ | ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n → (distanceSet P).card ≥ m } := by
    intro P _
    exact Nat.zero_le _
  exact Nat.sInf_eq_zero.2 (Or.inl h0)

/-- The constant the module carried. -/
noncomputable def guth_katz_constant : ℝ := 1 / 10

/-- **So the effective claim was false, not merely unproved.** With
`g_distinct n = 0` the assertion `g_distinct n ≥ (1/10)·n/log n` fails at every
`n ≥ 2`, since `log n > 0` there makes the right side positive. -/
theorem guth_katz_computable_is_false (n : ℕ) (hn : 2 ≤ n) :
    ¬ ((g_distinct n : ℝ) ≥ guth_katz_constant * (n : ℝ) / Real.log (n : ℝ)) := by
  have hlog : 0 < Real.log (n : ℝ) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact Real.log_pos h1
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hrhs : 0 < guth_katz_constant * (n : ℝ) / Real.log (n : ℝ) := by
    unfold guth_katz_constant
    positivity
  rw [g_distinct_eq_zero]
  push_cast
  linarith

/-- The quantity actually wanted: the least distance count over all
`n`-point configurations, as a supremum of lower bounds. -/
noncomputable def distinctG (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n → (distanceSet P).card ≥ m }

/-- **Guth–Katz, as a statement.** Cited, not formalized here; writing it as a
Prop keeps it out of the trusted base instead of hiding it behind a `sorry`. -/
def GuthKatzBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
    (distinctG n : ℝ) ≥ c * (n : ℝ) / Real.log (n : ℝ)

/-- What is elementary and true at every `n`: one point has no distances, and
two points have exactly one, so the count is at least `1` from `n = 2`. -/
theorem distances_pos_of_two {P : Finset (EuclideanSpace ℝ (Fin 2))}
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    1 ≤ (distanceSet P).card := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨dist p q, ?_⟩
  unfold distanceSet
  rw [Finset.mem_erase]
  refine ⟨?_, ?_⟩
  · exact dist_ne_zero.2 hpq
  · exact Finset.mem_image.2 ⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩, rfl⟩

#print axioms g_distinct_eq_zero
#print axioms guth_katz_computable_is_false
#print axioms distances_pos_of_two

end Millennium.ProofModules.DistinctDistances

end
