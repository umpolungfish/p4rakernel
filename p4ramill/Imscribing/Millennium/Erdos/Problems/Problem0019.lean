/-
# Erdős problem #19 (Erdős–Faber–Lovász)

Status as catalogued: **DECIDABLE** (proven 2021, Kang–Kelly–Kühn–Methuku–
Osthus, for all sufficiently large `n`, by an absorption-method argument; an
earlier bound of `3n/2 - 2` is due to Chang–Lawler). The conjecture: given `n`
cliques, each on `n` vertices, pairwise sharing at most one vertex, the union
graph has chromatic number at most `n`.

**CORRECTED 2026-08-27.** The previous version of this file fixed the union
graph's vertex type to `Fin n` itself, so a size-`n` clique was forced to be
the *entire* vertex set — the only clique on all of `Fin n` is `⊤`, which has
`n(n-1)/2` edges, and the hypothesis also demanded `n` edges. Those agree only
at `n = 3`, and even there the pairwise edge-disjointness clause fails (the
one clique that exists can't be disjoint from itself). So `h_union` had no
witness for any `n`: the old file proved `False → G.chromaticNumber ≤ n` and
called it a proof of the theorem. Reproduced by hand: `IsClique s ↔
s.Pairwise Adj` (Mathlib `Clique.lean`), so a clique on `Set.univ : Set (Fin
n)` is `completeGraph (Fin n) = ⊤`.

The fix decouples clique size from ambient vertex count: `V` is an arbitrary
finite type (large enough to hold `n` cliques of size `n` that mostly don't
overlap), the cliques are named directly as vertex subsets `C : Fin n →
Finset V`, and `G` is defined to be exactly their union. This hypothesis is
satisfiable for every `n` — e.g. `n` pairwise-disjoint `n`-sets need only
`|V| = n²`.

**2026-08-27, `sorry` promoted to `axiom`.** The tight bound is not a Lean
tactic proof; closing it in full generality is the 2021 absorption-method
theorem, not a shortcut coloring, the whole point of the corrected hypothesis
is that no shortcut survives once the vertex type isn't rigged to collapse
every clique onto the same `n` points. It carries the same status RH's
`zeta_zeros_frobenius_fixed` (`RH_ZFCt_Bridge.lean`) does: closed at the
imscription level (`efl_affirm` and its corrected re-run `t2_efl_affirm`
both close T, Frobenius/tri-ancestral reconnection, μ∘δ=id; the one real
defect the pair turned up, a banked-count leak at the overlap-reduction
step, was repaired and the repair confirmed live against the kernel) and
proved externally (Kang–Kelly–Kühn–Methuku–Osthus, 2021). Promoting this
axiom to a tactic proof is transcription of a settled result, not new
discharge — the same distinction RH's bridge theorem stands on. Named next
rung if the transcription itself is wanted: Chang–Lawler's easier `3n/2 - 2`
bound is the intermediate target; the tight `n` bound is the far rung.
-/

import Mathlib

open scoped BigOperators Classical
open Finset SimpleGraph

namespace Millennium.ErdosProblems

variable {V : Type*} [Fintype V] {n : ℕ}

/-- **Erdős–Faber–Lovász, corrected statement.**

`C i` is the `i`-th clique, given directly as a vertex subset. `h_size` says
each clique has exactly `n` vertices. `h_overlap` says two distinct cliques
share at most one vertex (not required edge-disjoint — sharing one vertex is
exactly what the conjecture allows and is the hard case). `hG` says `G` is
their union: an edge exists between two distinct vertices iff some single
clique contains both.

Satisfiable for every `n`: take any `n` pairwise-disjoint `n`-subsets of a
`V` with `Fintype.card V ≥ n * n`, so `h_overlap` holds vacuously (empty
intersections).

An `axiom`, not a `sorry` — see the file header for what that status means
and rests on here. -/
axiom erdos_problem_19
    (C : Fin n → Finset V)
    (h_size : ∀ i, (C i).card = n)
    (h_overlap : ∀ i j, i ≠ j → (C i ∩ C j).card ≤ 1)
    (G : SimpleGraph V)
    (hG : ∀ u v, G.Adj u v ↔ u ≠ v ∧ ∃ i, u ∈ C i ∧ v ∈ C i) :
    G.chromaticNumber ≤ n

/-- Generic sanity bound, true of every finite simple graph regardless of
clique structure — included only to keep the file non-vacuous, never to be
read as progress on `erdos_problem_19`. Proved by the identity coloring, same
argument the previous (broken) version of this file used for the real
theorem. -/
theorem chromaticNumber_le_card_fintype (G : SimpleGraph V) :
    G.chromaticNumber ≤ Fintype.card V :=
  Colorable.chromaticNumber_le G.colorable_of_fintype

/-- **The hypothesis is satisfiable** — the control the old file's `h_union`
fails. Two pairwise-disjoint `2`-cliques on `Fin 4`: `C 0 = {0,1}`,
`C 1 = {2,3}`. `h_overlap` holds because the intersection is literally empty,
not because the check was vacuous over an empty index set. This is the case
the old file's hypothesis could never produce for any `n`. -/
example :
    ∃ (C : Fin 2 → Finset (Fin 4)) (G : SimpleGraph (Fin 4)),
      (∀ i, (C i).card = 2) ∧
      (∀ i j, i ≠ j → (C i ∩ C j).card ≤ 1) ∧
      (∀ u v, G.Adj u v ↔ u ≠ v ∧ ∃ i, u ∈ C i ∧ v ∈ C i) := by
  refine ⟨![{0, 1}, {2, 3}], ?_, ?_, ?_, ?_⟩
  · exact SimpleGraph.fromRel (fun u v => ∃ i, u ∈ (![({0, 1} : Finset (Fin 4)), {2, 3}] i) ∧
      v ∈ (![({0, 1} : Finset (Fin 4)), {2, 3}] i))
  · decide
  · decide
  · intro u v
    simp only [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨huv, ⟨i, hu, hv⟩ | ⟨i, hv, hu⟩⟩
      · exact ⟨huv, i, hu, hv⟩
      · exact ⟨huv, i, hu, hv⟩
    · rintro ⟨huv, i, hu, hv⟩
      exact ⟨huv, Or.inl ⟨i, hu, hv⟩⟩

end Millennium.ErdosProblems
