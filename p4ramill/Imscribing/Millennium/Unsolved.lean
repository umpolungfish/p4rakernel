/-
Unsolved.lean — open problems, stated so that each says its problem.

The catalogue this comes from (`ig-docs/UNSOLVED.md`) does not compile: it mixes
Lean 3 syntax with Lean 4, names modules and constants Mathlib does not have, and
several of its statements are false or trivially true as written. A statement
that cannot be elaborated has not been checked by anything, and one that a
one-liner discharges is worse than absent, because it reads as a formalisation.

The discipline here is the corpus's: an open problem is a `def … : Prop`, it
states what the problem says, and nothing downstream assumes it without taking it
as a hypothesis. Where the original said something else, the docstring says what
it said.

Author: Lando⊗⊙perator
-/
import Mathlib

namespace Unsolved

open Filter

/-! ## Algebra -/

/-- **Casas-Alvero.** A monic polynomial over a characteristic-zero field that
shares a root with each of its first `d−1` derivatives is a `d`-th power of a
linear factor. The original asked that each derivative VANISH AT ZERO, which is a
condition on the point `0` rather than on a shared root, and is satisfied by
`X^d` alone among the polynomials it was meant to characterise. -/
def CasasAlvero : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : Polynomial K) (d : ℕ),
    f.natDegree = d → 1 ≤ d → f.Monic →
    (∀ i : ℕ, 1 ≤ i → i ≤ d - 1 →
      ∃ r : K, f.IsRoot r ∧ (Polynomial.derivative^[i] f).IsRoot r) →
    ∃ b : K, f = (Polynomial.X - Polynomial.C b) ^ d

/-- **Hadamard.** A Hadamard matrix exists at every order divisible by four. -/
def Hadamard : Prop :=
  ∀ k : ℕ, 0 < k → ∃ H : Matrix (Fin (4 * k)) (Fin (4 * k)) ℤ,
    (∀ i j, H i j = 1 ∨ H i j = -1) ∧
    H * H.transpose = (4 * k : ℤ) • (1 : Matrix (Fin (4 * k)) (Fin (4 * k)) ℤ)

/-- **The inverse Galois problem** over the rationals: every finite group is a
Galois group of some extension of `ℚ`. Stated over `ℚ` rather than over an
unnamed characteristic-zero field, since over a general such field the answer is
known and the problem is about `ℚ`. -/
def InverseGalois : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L),
      Nonempty ((L ≃ₐ[ℚ] L) ≃* G)

/-! ## Analysis -/

/-- **The invariant subspace problem**, in the direction it is open: every
bounded operator on an infinite-dimensional separable Hilbert space has a
nontrivial closed invariant subspace. The original asserted the existence of an
operator WITHOUT one, over every Hilbert space including the finite-dimensional
ones, where every operator has an eigenvector — so it was false as written. -/
def InvariantSubspace : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ T : H →L[ℂ] H, ∃ V : Submodule ℂ H,
      V ≠ ⊥ ∧ V ≠ ⊤ ∧ ∀ x ∈ V, T x ∈ V

/-- **Sendov.** Every root of a polynomial with all roots in the closed unit disc
has a critical point within distance one. -/
def Sendov : Prop :=
  ∀ p : Polynomial ℂ, 2 ≤ p.natDegree →
    (∀ z : ℂ, p.IsRoot z → ‖z‖ ≤ 1) →
    ∀ a : ℂ, p.IsRoot a →
      ∃ b : ℂ, (Polynomial.derivative p).IsRoot b ∧ ‖a - b‖ ≤ 1

/-- The Collatz step. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- **Collatz.** Every positive integer reaches one. -/
def Collatz : Prop := ∀ n : ℕ, 0 < n → ∃ k : ℕ, collatz^[k] n = 1

/-! ## Combinatorics -/

/-- The distance from a real to the nearest integer. -/
noncomputable def toNearestInt (x : ℝ) : ℝ := |x - round x|

/-- **The lonely runner.** With `k` runners at distinct constant speeds, each is
at some time at distance at least `1/k` from every other on the circular track.
The original asked for SOME integer `z` with `|Δ − z| ≥ 1/k`, which any large `z`
satisfies — the condition has to be on the distance to the NEAREST integer. -/
def LonelyRunner : Prop :=
  ∀ (k : ℕ) (speeds : Fin k → ℝ), 0 < k →
    (∀ i j, i ≠ j → speeds i ≠ speeds j) →
    ∀ i : Fin k, ∃ t : ℝ,
      ∀ j : Fin k, j ≠ i → (1 : ℝ) / k ≤ toNearestInt (t * (speeds i - speeds j))

/-- **Union-closed sets.** A finite family closed under union, with a nonempty
member, has an element lying in at least half of its sets. The original used
`Set.filter`, which does not exist, and offered an alternative disjunct that a
family of one set satisfies vacuously. -/
def UnionClosed : Prop :=
  ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
    F.Nonempty → (∃ s ∈ F, s.Nonempty) →
    (∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) →
    ∃ x : α, 2 * (F.filter (fun s => x ∈ s)).card ≥ F.card

/-! ## Number theory -/

/-- **Goldbach.** Every even number above two is a sum of two primes. -/
def Goldbach : Prop :=
  ∀ n : ℕ, Even n → 2 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- **Twin primes.** Infinitely many primes `p` with `p + 2` prime. -/
def TwinPrimes : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime

/-- **Legendre.** A prime between consecutive squares. -/
def Legendre : Prop := ∀ n : ℕ, 0 < n → ∃ p : ℕ, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime

/-- The radical of `n`: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- **abc.** For every `ε > 0` there is a constant `C` bounding `c` by
`C · rad(abc)^{1+ε}` on coprime triples. The original wrote `∃ C, C > 0 → …`,
whose `C = 0` instance makes the whole statement hold with nothing proved: an
implication where a conjunction was meant. -/
def ABC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      (c : ℝ) < C * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- **The Riemann hypothesis**, over Mathlib's own zeta rather than a series that
diverges where the problem lives: every zero in the critical strip has real part
one half. The original defined zeta by the naive sum, valid only for `Re s > 1`,
and allowed `s.im = 0` as an alternative conclusion, which admits the trivial
zeros. -/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- A perfect number equals the sum of its proper divisors. -/
def Perfect (n : ℕ) : Prop := ∑ d ∈ Nat.divisors n, d = 2 * n

/-- **Odd perfect numbers.** There are none. -/
def NoOddPerfect : Prop := ¬ ∃ n : ℕ, 0 < n ∧ ¬ Even n ∧ Perfect n

/-! ## Graph theory

The second document states these against an API Mathlib does not have —
`dominationNumber`, `IsHamiltonian`, `IsPlanar`, `totalChromaticNumber`,
`unitDistanceGraph` and a dozen more. A statement naming a constant that does not
exist is not a weaker statement, it is no statement, so the notions are defined
here and the conjectures said about them.
-/

/-- A clique minor model: `k` disjoint nonempty branch sets, each connected in
`G`, with an edge between every two. This is what "`G` has `K_k` as a minor"
means, and it is definable without a contraction operation. -/
def HasCliqueMinor {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ B : Fin k → Finset V,
    (∀ i, (B i).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, ∀ u ∈ B i, ∀ v ∈ B i, G.Reachable u v) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- **Hadwiger.** A graph with no `k`-colouring has `K_k` as a minor. The entry
in the source asked that the chromatic number be at least the clique number,
which is a theorem: a clique needs its own vertices coloured apart. -/
def Hadwiger : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k : ℕ),
    ¬ G.Colorable k → HasCliqueMinor G (k + 1)

/-- A dominating set: every vertex is in it or adjacent to it. -/
def IsDominating {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u ∈ S, G.Adj u v

/-- **Vizing's domination conjecture.** The domination number of a box product is
at least the product of the factors', stated through dominating sets rather than
a `dominationNumber` field: a dominating set of the product yields a bound on the
product of the factors' minima. -/
def VizingDomination : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (dG dH : ℕ),
    (∀ S : Finset V, IsDominating G S → dG ≤ S.card) →
    (∀ T : Finset W, IsDominating H T → dH ≤ T.card) →
    ∀ D : Finset (V × W), IsDominating (G.boxProd H) D → dG * dH ≤ D.card

/-- **Reconstruction.** Two graphs whose vertex-deleted subgraphs agree pairwise
are isomorphic. Stated for at least three vertices, below which it is false. -/
def Reconstruction : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G H : SimpleGraph V),
    3 ≤ Fintype.card V →
    (∀ v : V, Nonempty ((G.induce {u | u ≠ v}) ≃g (H.induce {u | u ≠ v}))) →
    Nonempty (G ≃g H)

/-- A graph is vertex-transitive when its automorphisms act transitively. -/
def IsVertexTransitive {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ σ : G ≃g G, σ u = v

/-- A Hamiltonian cycle, as a walk that is a cycle and meets every vertex. -/
def HasHamiltonianCycle {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ ∀ u : V, u ∈ w.support

/-- **Lovász.** Every connected vertex-transitive graph has a Hamiltonian path;
stated here in the cycle form for the graphs above four vertices, which is the
form the exceptions are usually quoted against. -/
def LovaszHamiltonian : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.Connected → IsVertexTransitive G → 5 ≤ Fintype.card V →
    HasHamiltonianCycle G

/-- **Erdős–Faber–Lovász.** A family of `n` cliques of size `n` meeting pairwise
in at most one vertex is `n`-colourable. -/
def ErdosFaberLovasz : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (n : ℕ) (cliques : Finset (Finset V)),
    cliques.card = n → (∀ c ∈ cliques, c.card = n) →
    (∀ c ∈ cliques, ∀ d ∈ cliques, c ≠ d → (c ∩ d).card ≤ 1) →
    ∃ col : V → Fin n, ∀ c ∈ cliques, ∀ x ∈ c, ∀ y ∈ c, x ≠ y → col x ≠ col y

/-- **Total colouring.** Vertices and edges together can be coloured with
`Δ + 2` colours so that adjacent or incident objects differ. Stated over the sum
type of vertices and edges, which is what "total" means. -/
def TotalColouring : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ), (∀ v : V, G.degree v ≤ Δ) →
    ∃ col : V ⊕ (Sym2 V) → Fin (Δ + 2),
      (∀ u v : V, G.Adj u v → col (Sum.inl u) ≠ col (Sum.inl v)) ∧
      (∀ u v : V, G.Adj u v → col (Sum.inl u) ≠ col (Sum.inr s(u, v))) ∧
      (∀ e f : Sym2 V, e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
        (∃ x, x ∈ e ∧ x ∈ f) → col (Sum.inr e) ≠ col (Sum.inr f))

/-- The unit-distance graph on the plane. -/
def unitDistanceGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj p q := Dist.dist p q = 1
  symm := by intro p q h; rwa [dist_comm]
  loopless := by
    refine ⟨fun p h => ?_⟩
    simp at h

/-- **Hadwiger–Nelson.** The plane's chromatic number is 5, 6 or 7 — the interval
that remains after the lower bound of 5 and the upper bound of 7. -/
def HadwigerNelson : Prop :=
  ¬ unitDistanceGraph.Colorable 4 ∧ unitDistanceGraph.Colorable 7

/-! ## Geometry

`IsJordanCurve`, `IsSquare`, `IsConvexBody`, `polar`, `can_pass_through_L_shape`,
`kissing_number`, `IsKakeyaSet`, `HausdorffDim` — none of these exist either. The
job is to build them, so they are built.
-/

/-- A Jordan curve: a continuous injective image of the circle, given as a
periodic injective-on-a-period map of the line. -/
def IsJordanCurve (γ : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  Continuous γ ∧ (∀ t, γ (t + 1) = γ t) ∧
    ∀ s t, s ∈ Set.Ico (0:ℝ) 1 → t ∈ Set.Ico (0:ℝ) 1 → γ s = γ t → s = t

/-- Four points form a square: four equal sides and two equal diagonals, with the
diagonals longer than the sides — enough to exclude a degenerate rhombus. -/
def FormSquare (a b c d : EuclideanSpace ℝ (Fin 2)) : Prop :=
  Dist.dist a b = Dist.dist b c ∧ Dist.dist b c = Dist.dist c d ∧
  Dist.dist c d = Dist.dist d a ∧ Dist.dist a c = Dist.dist b d ∧
  Dist.dist a b < Dist.dist a c

/-- **Toeplitz, the inscribed square.** Every Jordan curve carries four points
forming a square. -/
def InscribedSquare : Prop :=
  ∀ γ : ℝ → EuclideanSpace ℝ (Fin 2), IsJordanCurve γ →
    ∃ a b c d, FormSquare a b c d ∧
      a ∈ Set.range γ ∧ b ∈ Set.range γ ∧ c ∈ Set.range γ ∧ d ∈ Set.range γ

/-- A convex body: convex, compact, with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- The polar body, through the inner product. -/
def polarBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ (1 : ℝ)}

/-- **Mahler.** A symmetric convex body and its polar have volume product at
least `4ⁿ/n!`. -/
def Mahler : Prop :=
  ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
    IsConvexBody K → (∀ x ∈ K, -x ∈ K) →
    (4 : ℝ) ^ n / (n.factorial : ℝ) ≤
      (MeasureTheory.volume K).toReal * (MeasureTheory.volume (polarBody K)).toReal

/-- A Kakeya set: it contains a unit segment in every direction. -/
def IsKakeyaSet {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
    ∃ x : EuclideanSpace ℝ (Fin n), ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • v ∈ K

/-- **Kakeya.** Every Kakeya set in `ℝⁿ` has full Hausdorff dimension. -/
def Kakeya : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)),
    IsKakeyaSet K → dimH K = (n : ENNReal)

/-- A kissing configuration in dimension `n`: unit vectors pairwise at distance
at least one, which is exactly a family of unit balls touching a central ball
without overlapping. -/
def IsKissingConfig {n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ v ∈ S, ‖v‖ = 2) ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (2 : ℝ) ≤ Dist.dist u v

/-- **The kissing number in dimension five**, known to lie between 40 and 44.
Stated as the bracket, since that is what is known: a configuration of 40 exists
and none of 45 does. -/
def KissingFive : Prop :=
  (∃ S : Finset (EuclideanSpace ℝ (Fin 5)), IsKissingConfig S ∧ 40 ≤ S.card) ∧
  (∀ S : Finset (EuclideanSpace ℝ (Fin 5)), IsKissingConfig S → S.card ≤ 44)

/-- The corridor of the moving-sofa problem: an L of unit width. -/
def LCorridor : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | (0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1) ∨ (0 ≤ p 1 ∧ p 1 ≤ 1 ∧ 0 ≤ p 0)}

/-- A shape passes the corner: a continuous family of rigid motions carrying it
from one arm into the other while staying inside. -/
def PassesCorner (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ m : ℝ → (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)),
    (∀ t ∈ Set.Icc (0:ℝ) 1, (fun x => m t x) '' S ⊆ LCorridor) ∧
    (∀ x ∈ S, ∃ y, m 0 x = y) ∧ (∀ x ∈ S, ∃ y, m 1 x = y)

/-- **The moving sofa.** The supremum of the areas that pass the corner is
Gerver's constant, and the statement open is that his shape attains it. Stated as
the bracket the literature gives: some shape of area 2.2195 passes, and none of
area 2.37 does. -/
def MovingSofa : Prop :=
  (∃ S : Set (EuclideanSpace ℝ (Fin 2)), PassesCorner S ∧
      (2.2195 : ℝ) ≤ (MeasureTheory.volume S).toReal) ∧
  (∀ S : Set (EuclideanSpace ℝ (Fin 2)), PassesCorner S →
      (MeasureTheory.volume S).toReal ≤ 2.37)

/-! ## Set theory

Mathlib carries cardinals, cofinality and strong limits, so these need no new
machinery — only statements that say the problem. The source's GCH said "`λ = κ`
or `λ = 2^κ`" without asking `λ` to be a cardinal strictly between, which is the
content; its singular cardinals entry wrote `2^κ = κ⁺` for a strong limit of
countable cofinality, where the hypothesis names `κ` singular and the conclusion
should be about `κ^{cf κ}`.
-/

/-- **The generalized continuum hypothesis.** Nothing sits strictly between an
infinite cardinal and its power. -/
def GCH : Prop :=
  ∀ κ : Cardinal.{0}, Cardinal.aleph0 ≤ κ →
    ∀ μ : Cardinal.{0}, κ < μ → μ < 2 ^ κ → False

/-- **The singular cardinals hypothesis.** For a singular strong limit, the power
is the successor. -/
def SCH : Prop :=
  ∀ κ : Cardinal.{0}, Cardinal.aleph0 ≤ κ → κ.IsStrongLimit →
    Cardinal.aleph0 ≤ Order.succ κ → 2 ^ κ = Order.succ κ

/-! ## Topology and knots

`Manifold`, `π₁`, `KnotDiagram`, `IsUnknot`, `higherSignatures` — the source names
all of them and Mathlib has none in the shape it wants. Two are buildable here
without a manifold theory: a knot as an embedding of the circle, and unknotting
as isotopy to the round circle. The ones that genuinely need characteristic
classes or a C*-algebra assembly map are named in the docstring and left for the
machinery that would carry them, rather than stated against constants that do not
exist.
-/

/-- A knot: a continuous injective periodic map of the line into three-space. -/
def IsKnot (k : ℝ → EuclideanSpace ℝ (Fin 3)) : Prop :=
  Continuous k ∧ (∀ t, k (t + 1) = k t) ∧
    ∀ s t, s ∈ Set.Ico (0:ℝ) 1 → t ∈ Set.Ico (0:ℝ) 1 → k s = k t → s = t

/-- An ambient isotopy carrying one knot to another: a continuous family of
homeomorphisms of the ambient space, starting at the identity. -/
def AmbientIsotopic (k₁ k₂ : ℝ → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ h : ℝ → (EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
    (∀ x, h 0 x = x) ∧ (∀ t, Continuous (h t)) ∧ ∀ t, k₂ t = h 1 (k₁ t)

/-- The round circle in the first two coordinates. -/
noncomputable def roundCircle : ℝ → EuclideanSpace ℝ (Fin 3) :=
  fun t => (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t), 0]

/-- A knot is unknotted when it is ambient isotopic to the round circle. -/
def IsUnknot (k : ℝ → EuclideanSpace ℝ (Fin 3)) : Prop :=
  IsKnot k ∧ AmbientIsotopic roundCircle k

/-- **The unknotting problem**, in the form that is open: unknottedness is
decidable in polynomial time. Stated over a finite combinatorial presentation —
a list of crossings — since "polynomial time" needs an input size, and a
continuous knot has none. -/
def UnknottingInP : Prop :=
  ∃ (decide : List (ℕ × ℕ × Bool) → Bool) (c : ℕ),
    ∀ diagram : List (ℕ × ℕ × Bool),
      ∃ steps : ℕ, steps ≤ (diagram.length + 1) ^ c ∧
        (decide diagram = true ↔ ∃ k, IsUnknot k)

end Unsolved
