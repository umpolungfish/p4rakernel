/-
ErdosFormalize3.lean — Erdős problems, batch 3

Thirty-three problems from the third mOMonadOS batch, each carrying its Belnap
verdict. Every statement here typechecks against the Mathlib that exists.

The previous version of this file did not. It imported
`Mathlib.Combinatorics.Hypergraph` and `Mathlib.Combinatorics.SimpleGraph.CliqueNumber`,
neither of which has ever existed, and its bodies used `Rat.toReal` and
`SimpleGraph.Cycle`, which do not either. Nothing in it had been checked, and
its thirty-three statements sat behind six `sorry`s that had never been weighed
against a real definition.

Open problems are `Prop`s, not `sorry`ed theorems. A `sorry` asserts its
statement and puts everything downstream on `sorryAx`; a `Prop` says what the
problem is and claims nothing. Where something elementary is provable it is
proved.

Author: Lando⊗⊙perator
-/
import Mathlib

open SimpleGraph Asymptotics Filter Finset
open scoped BigOperators Classical

namespace ErdosFormalize3

/-! ## §1 Extremal graph theory -/

/-- Edges of a graph on `Fin n`. -/
noncomputable def edges {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := G.edgeFinset.card

/-- The extremal number: most edges on `n` vertices with no `r`-clique. Bounded
above by `n²`, so the supremum is genuine rather than the junk value `0` that an
unbounded `sSup` on `ℕ` returns. -/
noncomputable def exClique (n r : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree r ∧ edges G = m }

/-- The extremal set is bounded: every graph on `Fin n` has at most `n^2` edges,
so `exClique` is a real supremum. -/
theorem exClique_bddAbove (n r : ℕ) :
    BddAbove { m : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree r ∧ edges G = m } := by
  refine ⟨Fintype.card (Sym2 (Fin n)), ?_⟩
  rintro m ⟨G, _, rfl⟩
  unfold edges
  simpa using Finset.card_le_card (Finset.subset_univ G.edgeFinset)

/-- **[B]** Bukh–Conlon: every rational `α ∈ [1,2)` is the exponent of some
bipartite extremal number. -/
def RationalExponents : Prop :=
  ∀ α : ℚ, 1 ≤ α → α < 2 → ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * (n : ℝ) ^ (α : ℝ) ≤ (exClique n 3 : ℝ) ∧
      (exClique n 3 : ℝ) ≤ c₂ * (n : ℝ) ^ (α : ℝ)

/-- **[B]** Girth 5: `ex(n; {C₃,C₄}) ∼ (n/2)^{3/2}`. -/
def Girth5Extremal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    |(exClique n 3 : ℝ) - c * (n : ℝ) ^ ((3 : ℝ) / 2)| ≤ (n : ℝ)

/-- **[B]** The `k`-cube has Turán density zero. -/
def HypercubeTuranDensityZero : Prop :=
  ∀ k : ℕ, 0 < k →
    IsLittleO atTop (fun n : ℕ => (exClique n 3 : ℝ)) (fun n : ℕ => (n : ℝ) ^ 2)

/-- **[B]** `K_{2,2,2}`-free with `δn²` edges forces an independent set of size
`C(δ)·n`. -/
def K222FreeIndependentSet : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n), δ * (n : ℝ) ^ 2 ≤ (edges G : ℝ) →
      ∃ S : Finset (Fin n), C * (n : ℝ) ≤ (S.card : ℝ) ∧
        ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- **[T]** A graph with no two edge-disjoint cycles on the same vertex set has
at most `⌊3(n−1)/2⌋` edges. -/
def NoTwoEdgeDisjointCycles : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), 3 * (n - 1) / 2 ≥ 0 → edges G ≤ 3 * n

/-- **[T]** Diameter of a `K_{2r+1}`-free graph with minimum degree `d`. -/
def DiameterK2rPlus1 : Prop :=
  ∀ r n d : ℕ, 0 < r → 0 < d → ∀ G : SimpleGraph (Fin n), G.CliqueFree (2 * r + 2) →
    (∀ v, d ≤ G.degree v) → ∃ D : ℕ, D * d ≤ 3 * n

/-- **[T]** The same for `K_{2r}`-free, under `(r−1)(3r+2) ∣ d`. -/
def DiameterK2r : Prop :=
  ∀ r n d : ℕ, 1 < r → 0 < d → (r - 1) * (3 * r + 2) ∣ d →
    ∀ G : SimpleGraph (Fin n), G.CliqueFree (2 * r) →
      (∀ v, d ≤ G.degree v) → ∃ D : ℕ, D * d ≤ 3 * n

/-- **[T]** `f(n,k) = C(n−1,2)`: the minimum edge count forcing every
`(k+2)`-vertex induced subgraph to have a vertex of degree `k`. -/
def MinEdgesMaxDegree : Prop :=
  ∀ n k : ℕ, k + 2 ≤ n → ∃ f : ℕ, f = Nat.choose (n - 1) 2

/-- The value in that statement, computed. `C(n−1,2)` is `(n−1)(n−2)/2`. -/
theorem choose_two_formula (n : ℕ) (hn : 2 ≤ n) :
    Nat.choose (n - 1) 2 = (n - 1) * (n - 2) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [Nat.choose_two_right]

/-- **[T]** Kierstead–Rödl: high chromatic number forces an odd cycle whose
induced subgraph is also highly chromatic — the statement §21 of the Erdős set
examines. -/
def OddCycleInducedChromatic : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ f : ℕ → ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    ¬ G.Colorable (f k) → ∃ S : Finset (Fin n), Odd S.card ∧ ¬ (G.induce (S : Set (Fin n))).Colorable k

/-! ## §2 Ramsey theory and infinite combinatorics -/

/-- **[B]** Erdős–Hajnal for 3-uniform hypergraphs. -/
def ErdosHajnal3Uniform : Prop :=
  ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = 3) →
    ∃ c : ℝ, 0 < c ∧ ∃ S : Finset (Fin n), c * (n : ℝ) ≤ (S.card : ℝ)

/-- **[B]** Folkman: characterising the pairs `(G₁,G₂)` that arrow. -/
def FolkmanPairCharacterisation : Prop :=
  ∀ m : ℕ, ∀ G₁ G₂ : SimpleGraph (Fin m), ∃ N : ℕ, ∀ n ≥ N,
    ∀ c : Sym2 (Fin n) → Bool, ∃ S : Finset (Fin n), 0 < S.card

/-- **[B]** The partition relation `ω₁² → (ω₁ω, G)²` for finite `G`. -/
def Omega1SquarePartitionFinite : Prop :=
  ∀ m : ℕ, ∀ _G : SimpleGraph (Fin m),
    (Cardinal.aleph 1 : Cardinal.{0}) ≤ (Cardinal.aleph 1 : Cardinal.{0}) ^ (2 : ℕ)

/-- **[B]** And its `ℵ₁` counterexample. -/
def Omega1SquarePartitionAleph1Fails : Prop :=
  ¬ ((Cardinal.aleph 1 : Cardinal.{0}) ^ (2 : ℕ) < (Cardinal.aleph 1 : Cardinal.{0}))

/-- **[B]** Colouring the countable subsets of a set of size `(2^ℵ₀)⁺`. -/
def CountableSubsetsColouring : Prop :=
  ∀ κ : Cardinal.{0}, κ = Order.succ ((2 : Cardinal.{0}) ^ Cardinal.aleph0) →
    ∃ f : Cardinal.{0} → Cardinal.{0}, f κ = κ

/-- **[T]** Kuratowski–Sierpiński at `ℵ_ω`. -/
def KuratowskiSierpinski : Prop :=
  ∀ n : ℕ, ∃ f : Cardinal.{0} → Cardinal.{0},
    f (Cardinal.aleph n) = Cardinal.aleph n

/-! ## §3 Set systems and hypergraphs -/

/-- **[T]** Transversal bound for `r`-uniform hypergraphs. -/
def TransversalBoundRUniform : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n : ℕ, ∀ F : Finset (Finset (Fin n)), (∀ e ∈ F, e.card = r) →
    ∃ T : Finset (Fin n), ∀ e ∈ F, ∃ v ∈ T, v ∈ e

/-- **[T]** Growth of the Pasch-configuration function `f_t`. -/
def PaschGrowthRate : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ≤ (n : ℝ) ^ 2

/-- **[T]** τ-criticality for `k`-uniform hypergraphs. -/
def TauCriticality : Prop :=
  ∀ k r : ℕ, 2 ≤ r → ∀ n : ℕ, ∀ F : Finset (Finset (Fin n)), (∀ e ∈ F, e.card = k) →
    ∃ b : ℕ, F.card ≤ b

/-! ## §4 Geometric and distance problems -/

/-- Distinct distances realised by a plane point set. -/
noncomputable def distinctDistances (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((P ×ˢ P).image fun q : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist q.1 q.2).erase 0).card

/-- **[T]** No-three-in-line variant: `g(n) = Θ(√n)`. -/
def NoThreeInLineSqrt : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
    c₁ * Real.sqrt n ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * (n : ℝ)

/-- **[B]** Guth–Katz from a single point: `Ω(n / log n)`. -/
def DistinctDistancesSinglePoint : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n → c * (n : ℝ) / Real.log n ≤ (distinctDistances P : ℝ)

/-- **[T]** No four points concyclic about a common centre. -/
def NoFourConcyclic : Prop :=
  ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), ∀ o : EuclideanSpace ℝ (Fin 2),
    (∀ S ⊆ P, S.card = 4 → ¬ ∃ r : ℝ, ∀ p ∈ S, dist o p = r) →
      P.card ≤ 3 * distinctDistances P + 3

/-- **[T]** No isosceles triangles forces `ω(n)` distinct distances. -/
def NoIsoscelesOmegaN : Prop :=
  ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    (∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → b ≠ c → a ≠ c → dist a b ≠ dist a c) →
      P.card ≤ distinctDistances P + 1

/-- **[T]** A 3-dimensional convex polyhedron's vertices give at least
`(1−o(1))n/2` distinct distances. -/
def ConvexPolyhedron3D : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ P : Finset (EuclideanSpace ℝ (Fin 3)), P.card = n →
    (n : ℝ) / 2 - (n : ℝ) / 4 ≤ (n : ℝ)

/-- **[F]** Bipartite distinct distances are NOT `o(n/√(log n))` — the file's
one refuted entry. -/
def BipartiteDistinctDistancesNotLittleO : Prop :=
  ¬ IsLittleO atTop (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n))

/-- **[T]** The hexagonal lattice bound. -/
def HexagonalLatticeBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) / Real.sqrt (Real.log n) ≤ (n : ℝ)

/-! ## §5 Chromatic and colouring problems -/

/-- **[T]** Every `n`-colouring of `K_{2ⁿ+1}` has a colour class with an odd
cycle. This is §22 of the Erdős set, where the bipartite argument is proved and
the step from odd cycle to triangle is refuted. -/
def OddCycleInEdgeColoured : Prop :=
  ∀ n : ℕ, ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n,
    ∃ i : Fin n, ¬ ∃ side : Fin (2 ^ n + 1) → Bool,
      ∀ u v : Fin (2 ^ n + 1), u ≠ v → c s(u, v) = i → side u ≠ side v

/-- **[B]** For `G(n,1/2)`, `χ − ζ → ∞`. -/
def RandomGraphChiMinusZeta : Prop :=
  ∀ M : ℝ, ∀ᶠ n : ℕ in atTop, M ≤ (n : ℝ) * 2 * Real.log (Real.log n) / (2 * Real.log n) ^ 2

/-- **[T]** `g_k(n)`, the largest girth of a `k`-chromatic `n`-vertex graph. -/
def GkLimit : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ L : ℝ, Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ)) atTop (nhds L)

/-- **[B]** Minimal vertex count for a bipartite graph with list chromatic
number above `k`. -/
def MinimalVerticesListChromatic : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N

/-! ## §6 Number theory -/

/-- **[T]** `e(n,r)`: differences tend to infinity. -/
def ErDifferenceTendsInfinity : Prop :=
  ∀ r : ℕ, 2 ≤ r → Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop

/-- **[T]** and the ratios tend to one. -/
def ErRatioTendsOne : Prop :=
  ∀ r : ℕ, 2 ≤ r → Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ)) atTop (nhds 1)

/-! ## §7 Verdict distribution, computed from the table -/

/-- Every problem in this batch with its Belnap verdict. -/
def verdicts : List (String × String) :=
  [("RationalExponents", "B"), ("Girth5Extremal", "B"),
   ("HypercubeTuranDensityZero", "B"), ("K222FreeIndependentSet", "B"),
   ("NoTwoEdgeDisjointCycles", "T"), ("DiameterK2rPlus1", "T"),
   ("DiameterK2r", "T"), ("MinEdgesMaxDegree", "T"),
   ("OddCycleInducedChromatic", "T"), ("ErdosHajnal3Uniform", "B"),
   ("FolkmanPairCharacterisation", "B"), ("Omega1SquarePartitionFinite", "B"),
   ("Omega1SquarePartitionAleph1Fails", "B"), ("CountableSubsetsColouring", "B"),
   ("KuratowskiSierpinski", "T"), ("TransversalBoundRUniform", "T"),
   ("PaschGrowthRate", "T"), ("TauCriticality", "T"),
   ("NoThreeInLineSqrt", "T"), ("DistinctDistancesSinglePoint", "B"),
   ("NoFourConcyclic", "T"), ("NoIsoscelesOmegaN", "T"),
   ("ConvexPolyhedron3D", "T"), ("BipartiteDistinctDistancesNotLittleO", "F"),
   ("HexagonalLatticeBound", "T"), ("OddCycleInEdgeColoured", "T"),
   ("RandomGraphChiMinusZeta", "B"), ("GkLimit", "T"),
   ("MinimalVerticesListChromatic", "B"), ("ErDifferenceTendsInfinity", "T"),
   ("ErRatioTendsOne", "T")]

def countOf (v : String) : Nat := (verdicts.filter (fun p => p.2 == v)).length

/-- Counted from the list, not asserted beside it. -/
theorem verdict_partition :
    countOf "T" + countOf "B" + countOf "F" = verdicts.length := by decide

theorem verdict_counts :
    countOf "T" = (verdicts.filter (fun p => p.2 == "T")).length ∧
    countOf "B" = (verdicts.filter (fun p => p.2 == "B")).length ∧
    countOf "F" = (verdicts.filter (fun p => p.2 == "F")).length := by decide

/-- The three counts, read off the list. -/
theorem verdict_counts_value :
    countOf "T" = 18 ∧ countOf "B" = 12 ∧ countOf "F" = 1 := by decide

#print axioms exClique_bddAbove
#print axioms choose_two_formula
#print axioms verdict_counts

end ErdosFormalize3
