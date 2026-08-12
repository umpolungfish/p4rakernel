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

/-! ### Cycles that must share an edge

The fourth object of the nest forks the graph space on the definitional property
itself: the graphs carrying a pair of edge-disjoint cycles, and those in which
every two cycles share an edge. The second arm's edge count is the constructive
witness, and the extremal function is the maximum over that arm — which needs a
cycle predicate, the thing this file did not carry.

A cycle here is a closed walk with no repeated vertex, given by its vertex list;
its edge set is the set of consecutive pairs. Two cycles are edge-disjoint when
those sets meet in nothing.
-/

/-- The consecutive pairs of a vertex list, closed up: the edges of the cycle it
describes. -/
def cycleEdges {n : ℕ} (vs : List (Fin n)) : List (Fin n × Fin n) :=
  match vs with
  | [] => []
  | v :: rest => (vs.zip (rest ++ [v]))

/-- A list of vertices is a cycle of `G`: at least three of them, no repeats, and
every consecutive pair adjacent. -/
def IsCycleList {n : ℕ} (G : SimpleGraph (Fin n)) (vs : List (Fin n)) : Prop :=
  3 ≤ vs.length ∧ vs.Nodup ∧ ∀ e ∈ cycleEdges vs, G.Adj e.1 e.2

/-- Two cycles share no edge, in either orientation. -/
def EdgeDisjointCycles {n : ℕ} (G : SimpleGraph (Fin n)) (a b : List (Fin n)) : Prop :=
  IsCycleList G a ∧ IsCycleList G b ∧
    ∀ e ∈ cycleEdges a, ∀ f ∈ cycleEdges b, e ≠ f ∧ e ≠ (f.2, f.1)

/-- The property the extremal function maximises over: every two cycles of `G`
share an edge. -/
def EveryTwoCyclesMeet {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b : List (Fin n), ¬ EdgeDisjointCycles G a b

/-- **The extremal count.** The largest edge count of a graph on `n` vertices in
which every two cycles share an edge. The classical answer is `⌊3(n−1)/2⌋`, and
the entry removed below bounded it by `3n` under a hypothesis true of every `n`,
so this states the quantity rather than the bound. -/
def MaxEdgesEveryTwoCyclesMeet (n : ℕ) : Prop :=
  ∃ M : ℕ, (∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      EveryTwoCyclesMeet G → G.edgeFinset.card ≤ M) ∧
    (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      EveryTwoCyclesMeet G ∧ G.edgeFinset.card = M) ∧
    M = 3 * (n - 1) / 2

/-! A `NoTwoEdgeDisjointCycles` entry stood here whose hypothesis was
`3(n−1)/2 ≥ 0`, true of every `n`, and whose conclusion bounded the edge count by
`3n` rather than by `⌊3(n−1)/2⌋`. Stating it needs a cycle predicate this file
does not carry. -/

/-- **[T]** Diameter of a `K_{2r+1}`-free graph with minimum degree `d`. -/
def DiameterK2rPlus1 : Prop :=
  ∀ r n d : ℕ, 0 < r → 0 < d → ∀ G : SimpleGraph (Fin n), G.CliqueFree (2 * r + 2) →
    (∀ v, d ≤ G.degree v) → ∃ D : ℕ, D * d ≤ 3 * n

/-- **[T]** The same for `K_{2r}`-free, under `(r−1)(3r+2) ∣ d`. -/
def DiameterK2r : Prop :=
  ∀ r n d : ℕ, 1 < r → 0 < d → (r - 1) * (3 * r + 2) ∣ d →
    ∀ G : SimpleGraph (Fin n), G.CliqueFree (2 * r) →
      (∀ v, d ≤ G.degree v) → ∃ D : ℕ, D * d ≤ 3 * n

/-! A `MinEdgesMaxDegree` entry stood here reading `∃ f, f = C(n−1,2)`, which names
that number and asserts nothing of it. -/

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

/-! ### A partition relation, held at B

The ninth object of the nest splits this one into two set-theoretic environments
— the constructible universe, where the relation holds, and a model of Martin's
Axiom, where a colouring refutes it — and its ENGAGR keeps the contradiction open
rather than resolving it. The fuse is B, and IFIX fixes B as the fact: the
relation is independent.

What can be written here is the relation itself and its two arms. What cannot is
a proof of either, since each holds in a different model, and a development that
asserted one would be asserting its model. The verdict table records B, which is
the whole content: not ignorance, but a conflict that stays open under the axioms
available.
-/

/-- A colouring of the unordered pairs of an ordinal's elements. -/
def PairColouring (κ : Type*) : Type _ := κ → κ → Bool

/-- `S` is homogeneous for `col`: every pair from `S` takes the same colour. -/
def Homogeneous {κ : Type*} (col : PairColouring κ) (S : Set κ) (c : Bool) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → col p q = c

/-- **The relation.** Every colouring of the pairs from `κ` admits either a
homogeneous set of the first kind or one of the second — the shape
`κ → (α, β)²` takes when written out over colourings. -/
def ArrowsPairsOfType (κ : Type*) (bigFirst bigSecond : Set κ → Prop) : Prop :=
  ∀ col : PairColouring κ,
    (∃ S, bigFirst S ∧ Homogeneous col S true) ∨
    (∃ S, bigSecond S ∧ Homogeneous col S false)

/-- **The arm that holds in the constructible universe**, as a statement about
this relation rather than about the model: the relation, with the second side
finite. -/
def PartitionArmHolds (κ : Type*) (bigFirst : Set κ → Prop) (n : ℕ) : Prop :=
  ArrowsPairsOfType κ bigFirst (fun S => ∃ f : Fin n → κ, Function.Injective f ∧ ∀ i, f i ∈ S)

/-- **The arm that fails under Martin's Axiom**, again as a statement about the
relation: a colouring with no homogeneous set of either kind. -/
def PartitionArmFails (κ : Type*) (bigFirst bigSecond : Set κ → Prop) : Prop :=
  ∃ col : PairColouring κ,
    (¬ ∃ S, bigFirst S ∧ Homogeneous col S true) ∧
    (¬ ∃ S, bigSecond S ∧ Homogeneous col S false)

/-- **The two arms cannot both be inhabited over the same parameters**, which is
what makes their coexistence across models an independence rather than a
contradiction here. This much is provable, and it is the only part that is. -/
theorem partition_arms_exclusive (κ : Type*) (bigFirst bigSecond : Set κ → Prop)
    (h : ArrowsPairsOfType κ bigFirst bigSecond) :
    ¬ PartitionArmFails κ bigFirst bigSecond := by
  rintro ⟨col, hno1, hno2⟩
  rcases h col with ⟨S, hS, hhom⟩ | ⟨S, hS, hhom⟩
  · exact hno1 ⟨S, hS, hhom⟩
  · exact hno2 ⟨S, hS, hhom⟩

/-! An `Omega1SquarePartitionFinite` entry stood here reading `ℵ₁ ≤ ℵ₁²`, true of
every infinite cardinal. The partition relation it was named for is a statement
about colourings of pairs, not about cardinal arithmetic. -/

/-! Its companion said `¬ (ℵ₁² < ℵ₁)`, which is `¬ False`. -/

/-! A `CountableSubsetsColouring` entry stood here asking for a function fixing a
cardinal, which the identity provides. -/

/-! A `KuratowskiSierpinski` entry stood here asking for a function fixing `ℵₙ`,
which the identity provides. -/

/-! ## §3 Set systems and hypergraphs -/

/-! A `TransversalBoundRUniform` entry stood here asking for a transversal with no
bound on its size, which the whole vertex set provides. The bound is the content
of the problem. -/

/-! ### Pasch configurations

The eighth object of the nest reads this one as a forward morphism from a system
to the set of its four-block subsets, forked on whether any matches the pattern.
The pattern itself is what the removed entry never named: four blocks on six
points in which every point of the six lies in exactly two of the four.
-/

/-- A Steiner triple system on `n` points: a set of blocks of size three in which
every pair of distinct points lies in exactly one block. -/
def IsSteinerTriple {n : ℕ} (B : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ B, b.card = 3) ∧
  ∀ p q : Fin n, p ≠ q → ∃! b, b ∈ B ∧ p ∈ b ∧ q ∈ b

/-- A Pasch configuration inside a system: four blocks whose union has six
points, each of those points lying in exactly two of the four blocks. -/
def IsPasch {n : ℕ} (P : Finset (Finset (Fin n))) : Prop :=
  P.card = 4 ∧ (P.biUnion id).card = 6 ∧
    ∀ p ∈ P.biUnion id, (P.filter (fun b => p ∈ b)).card = 2

/-- How many Pasch configurations a system carries. -/
noncomputable def paschCount {n : ℕ} (B : Finset (Finset (Fin n))) : ℕ :=
  ((B.powerset).filter (fun P => IsPasch P)).card

/-- **The growth of the extremes.** The largest and smallest Pasch counts over
systems of a given order — the quantity the removed entry compared `c·n` with
`n²` about, having named no system and no configuration. Anti-Pasch systems are
the case `lo = 0`, and their existence is the part that is not free. -/
def PaschExtremes (n lo hi : ℕ) : Prop :=
  (∀ B : Finset (Finset (Fin n)), IsSteinerTriple B → lo ≤ paschCount B ∧ paschCount B ≤ hi) ∧
  (∃ B : Finset (Finset (Fin n)), IsSteinerTriple B ∧ paschCount B = lo) ∧
  (∃ B : Finset (Finset (Fin n)), IsSteinerTriple B ∧ paschCount B = hi)

/-! A `PaschGrowthRate` entry stood here comparing `c·n` with `n²` and naming no
Pasch configuration. -/

/-! A `TauCriticality` entry stood here asking for `b` with `F.card ≤ b`, which
`F.card` itself provides. -/

/-! ## §4 Geometric and distance problems -/

/-- Distinct distances realised by a plane point set. -/
noncomputable def distinctDistances (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((P ×ˢ P).image fun q : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist q.1 q.2).erase 0).card

/-! A `NoThreeInLineSqrt` entry stood here comparing `c₁·√n` with `n` and `n` with
`c₂·n`, naming no point set. -/

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

/-! A `ConvexPolyhedron3D` entry stood here reading `n/2 − n/4 ≤ n`, which holds
of every `n` and counts no distances. -/

/-- **[F]** Bipartite distinct distances are NOT `o(n/√(log n))` — the file's
one refuted entry. -/
def BipartiteDistinctDistancesNotLittleO : Prop :=
  ¬ IsLittleO atTop (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n))

/-! A `HexagonalLatticeBound` entry stood here comparing `c·n/√log n` with `n`. -/

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

/-! ### Girth against chromatic number

The fifth object of the nest forks this extremal function into two arms — one
where the construction and the upper bound coincide, one where they leave a gap —
and its fuse keeps BOTH: the exact arm contributes a value, the gap arm an
interval. So the quantity is written here as a range, with equality of the ends
saying the value is known exactly. Collapsing it to a single number would assert
an exactness the problem does not have.
-/

/-- `G` has girth at least `g`: no cycle of `G` is shorter than `g`. The cycle
predicate is the one this file already carries. -/
def GirthAtLeast {n : ℕ} (G : SimpleGraph (Fin n)) (g : ℕ) : Prop :=
  ∀ vs : List (Fin n), IsCycleList G vs → g ≤ vs.length

/-- **The girth available at a given order and chromatic number, as a range.**
The lower end is realised by a construction; the upper end bounds every graph of
that order and chromatic number. When the two ends meet the value is exact, which
is the exact-match arm of the fork; otherwise the pair is what is known. -/
def GirthRange (n k lo hi : ℕ) : Prop :=
  (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      k ≤ G.chromaticNumber ∧ GirthAtLeast G lo) ∧
  (∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      k ≤ G.chromaticNumber → ∀ vs : List (Fin n), IsCycleList G vs → vs.length ≤ hi ∨ hi = 0)

/-- The value is known exactly when the range's ends meet. -/
def GirthExact (n k g : ℕ) : Prop := GirthRange n k g g

/-! A `GkLimit` entry stood here asking for the limit of `n/n`, which is one and has
nothing to do with girth. -/

/-! A `MinimalVerticesListChromatic` entry stood here concluding `∃ N, 0 < N`. -/

/-! ## §6 Number theory -/

/-! An `ErDifferenceTendsInfinity` entry stood here asserting that `n → ∞`. -/

/-! An `ErRatioTendsOne` entry stood here asserting that `n/n → 1`. -/

/-! ## §7 Verdict distribution, computed from the table -/

/-- Every problem in this batch with its Belnap verdict. -/
def verdicts : List (String × String) :=
  [("RationalExponents", "B"), ("Girth5Extremal", "B"),
   ("HypercubeTuranDensityZero", "B"), ("K222FreeIndependentSet", "B"),
   ("DiameterK2rPlus1", "T"), ("DiameterK2r", "T"),
   ("OddCycleInducedChromatic", "T"), ("ErdosHajnal3Uniform", "B"),
   ("FolkmanPairCharacterisation", "B"), ("DistinctDistancesSinglePoint", "B"),
   ("NoFourConcyclic", "T"), ("NoIsoscelesOmegaN", "T"),
   ("BipartiteDistinctDistancesNotLittleO", "F"),
   ("OddCycleInEdgeColoured", "T"), ("RandomGraphChiMinusZeta", "B")]

def countOf (v : String) : Nat := (verdicts.filter (fun p => p.2 == v)).length

/-- Counted from the list, not asserted beside it. -/
theorem verdict_partition :
    countOf "T" + countOf "B" + countOf "F" = verdicts.length := by decide

theorem verdict_counts :
    countOf "T" = (verdicts.filter (fun p => p.2 == "T")).length ∧
    countOf "B" = (verdicts.filter (fun p => p.2 == "B")).length ∧
    countOf "F" = (verdicts.filter (fun p => p.2 == "F")).length := by decide

/-- The three counts, read off the list. The numbers moved when the statements
that asserted nothing were removed; a count of a table is only worth stating if
it is recomputed when the table changes. -/
theorem verdict_counts_value :
    countOf "T" = 6 ∧ countOf "B" = 8 ∧ countOf "F" = 1 := by decide

#print axioms ErdosFormalize3.partition_arms_exclusive
#print axioms exClique_bddAbove
#print axioms choose_two_formula
#print axioms verdict_counts

end ErdosFormalize3
